import Mathlib
import OAI.Combinatorics.IndependentSets.Reduction.WalkLength

namespace OAI

namespace LargeIndependentSets
open scoped ENNReal NNReal

structure LabelCoverData (U V L R C : Type*) where
  left : C → U
  right : C → V
  project : C → L → R

def LabelCoverData.Satisfied {U V L R C : Type*} (lc : LabelCoverData U V L R C)
    (ℓ : U → L) (ρ : V → R) : Prop :=
  ∀ c, lc.project c (ℓ (lc.left c)) = ρ (lc.right c)

def MixedTuple (A B : Type*) (n i : ℕ) :=
  {x : Fin n → B ⊕ A // ∀ h, (x h).isLeft = decide (h.val < i)}

noncomputable def MixedTuple.map {A B A' B' : Type*} {n i : ℕ}
    (l : A → A') (r : B → B') (x : MixedTuple A B n i) : MixedTuple A' B' n i :=
  ⟨fun h => Sum.map r l (x.val h), by
    intro h
    simpa only [Sum.isLeft_map] using x.property h⟩

def mixedProject {L R : Type*} {n : ℕ} (h : Fin n) (π : L → R)
    (x : MixedTuple L R n h.val) : MixedTuple L R n (h.val + 1) :=
  ⟨fun k => if k = h then Sum.inl ((x.val k).elim id π) else x.val k, by
    intro k
    by_cases hk : k = h
    · subst k
      simp
    · simp only [ite_eq_right hk, x.property k]
      have hne : k.val ≠ h.val := fun e => hk (Fin.ext e)
      have he : (k.val < h.val) = (k.val < h.val + 1) := propext (by omega)
      simp only [he]⟩

abbrev LayerQuestion (U V : Type*) (n : ℕ) :=
  Σ i : Fin (n + 1), MixedTuple U V n i.val

abbrev LayerAnswer {U V : Type*} (L R : Type*) {n : ℕ}
    (q : LayerQuestion U V n) := MixedTuple L R n q.1.val

inductive LayerImposed {U V L R C : Type*} (lc : LabelCoverData U V L R C) (n : ℕ) :
    (q q' : LayerQuestion U V n) → (LayerAnswer L R q → LayerAnswer L R q') → Prop
  | adjacent (h : Fin n) (q : MixedTuple U V n h.val)
      (q' : MixedTuple U V n (h.val + 1)) (c : C)
      (hleft : q.val h = Sum.inr (lc.left c))
      (hright : q'.val h = Sum.inl (lc.right c))
      (houtside : ∀ k, k ≠ h → q.val k = q'.val k) :
      LayerImposed lc n ⟨h.castSucc, q⟩ ⟨h.succ, q'⟩ (mixedProject h (lc.project c))

def layeredSystem {U V L R C : Type*} (lc : LabelCoverData U V L R C) (n : ℕ) :
    ProjectionSystem (LayerQuestion U V n) (LayerAnswer L R) where
  imposed := LayerImposed lc n

noncomputable def productLabeling {U V L R : Type*} {n : ℕ}
    (ℓ : U → L) (ρ : V → R) (q : LayerQuestion U V n) : LayerAnswer L R q :=
  MixedTuple.map ℓ ρ q.2

theorem productLabeling_consistent {U V L R C : Type*}
    (lc : LabelCoverData U V L R C) (n : ℕ) (ℓ : U → L) (ρ : V → R)
    (hsat : lc.Satisfied ℓ ρ) :
    (layeredSystem lc n).Consistent (productLabeling ℓ ρ) := by
  intro q q' π hπ
  cases hπ with
  | adjacent h q q' c hleft hright houtside =>
      apply Subtype.ext
      funext k
      by_cases hk : k = h
      · subst k
        simp [mixedProject, productLabeling, MixedTuple.map,
          hleft, hright, hsat c]
      · simp only [mixedProject, productLabeling, MixedTuple.map, ite_eq_right hk,
          houtside k hk]

theorem layered_completeness {U V L R C : Type*}
    (lc : LabelCoverData U V L R C) (n : ℕ) (ℓ : U → L) (ρ : V → R)
    (hsat : lc.Satisfied ℓ ρ) {D : ℕ} [NeZero D] (hD : Even D) :
    (∀ x : GridLocation (LayerAnswer L R (U := U) (V := V) (n := n)) D,
      ¬pathDistance (layeredSystem lc n).linkLength x (gridAntipode x) ≤
        ENNReal.ofReal (1 / 8)) ∧
    (∀ (W : Type*) (location : W → GridLocation (LayerAnswer L R
      (U := U) (V := V) (n := n)) D),
      ∃ color : W → Fin 3, ∀ u v, (gridGraph (layeredSystem lc n) hD location).Adj u v →
        color u ≠ color v) := by
  have h := productLabeling_consistent lc n ℓ ρ hsat
  exact ⟨(projection_grid_completeness.{_, _, 0} (layeredSystem lc n) hD _ h).1,
    fun W location => gridGraph_three_coloring (layeredSystem lc n) hD _ h location⟩

noncomputable def distanceBump (d : ℝ≥0∞) : ℝ :=
  if d = ⊤ then 0 else max (1 - 32 * d.toReal) 0

lemma distanceBump_bounds (d : ℝ≥0∞) : 0 ≤ distanceBump d ∧ distanceBump d ≤ 1 := by
  unfold distanceBump
  split_ifs
  · norm_num
  · refine ⟨le_max_right _ _, max_le ?_ (by norm_num)⟩
    have := ENNReal.toReal_nonneg (a := d)
    linarith

@[simp] lemma distanceBump_zero : distanceBump 0 = 1 := by
  norm_num [distanceBump]

lemma distanceBump_vanish {d : ℝ≥0∞} (hd : ENNReal.ofReal (1 / 32) ≤ d) :
    distanceBump d = 0 := by
  unfold distanceBump
  split_ifs with htop
  · rfl
  · have hr := ENNReal.toReal_mono htop hd
    norm_num at hr
    exact max_eq_right (by linarith)

lemma distanceBump_difference {a b c : ℝ≥0∞} (hc : c ≠ ⊤)
    (hab : a ≤ c + b) (hba : b ≤ c + a) :
    |distanceBump a - distanceBump b| ≤ 32 * c.toReal := by
  by_cases ha : a = ⊤
  · by_cases hb : b = ⊤
    · simp only [distanceBump, ha, hb, ite_eq_left, sub_self, abs_zero]
      exact mul_nonneg (by norm_num) ENNReal.toReal_nonneg
    · have htop : c + b = ⊤ := top_le_iff.mp (ha ▸ hab)
      exact False.elim ((ENNReal.add_ne_top.mpr ⟨hc, hb⟩) htop)
  · by_cases hb : b = ⊤
    · have htop : c + a = ⊤ := top_le_iff.mp (hb ▸ hba)
      exact False.elim ((ENNReal.add_ne_top.mpr ⟨hc, ha⟩) htop)
    · have har := (ENNReal.toReal_le_toReal ha (ENNReal.add_ne_top.mpr ⟨hc, hb⟩)).mpr hab
      have hbr := (ENNReal.toReal_le_toReal hb (ENNReal.add_ne_top.mpr ⟨hc, ha⟩)).mpr hba
      rw [ENNReal.toReal_add hc hb] at har
      rw [ENNReal.toReal_add hc ha] at hbr
      simp only [distanceBump, ite_eq_right ha, ite_eq_right hb]
      calc
        _ ≤ max |(1 - 32 * a.toReal) - (1 - 32 * b.toReal)| |(0 : ℝ) - 0| :=
          abs_max_sub_max_le_max _ _ _ _
        _ = |(1 - 32 * a.toReal) - (1 - 32 * b.toReal)| := by simp
        _ ≤ 32 * c.toReal := by
          rw [abs_le]
          constructor <;> linarith

noncomputable def setBump {X : Type*} [PseudoEMetricSpace X] (A : Set X) (x : X) : ℝ :=
  distanceBump (Metric.infEDist x A)

lemma setBump_lipschitz {X : Type*} [PseudoEMetricSpace X] (A : Set X) :
    LipschitzWith 32 (setBump A) := by
  intro x y
  by_cases hc : edist x y = ⊤
  · simp [hc]
  · have h := distanceBump_difference hc
      (Metric.infEDist_le_edist_add_infEDist (x := x) (y := y) (s := A))
      (by simpa only [edist_comm x y] using
        (Metric.infEDist_le_edist_add_infEDist (x := y) (y := x) (s := A)))
    have hh := ENNReal.ofReal_le_ofReal h
    simpa only [setBump, edist_dist, Real.dist_eq, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 32),
      ENNReal.ofReal_toReal hc, ENNReal.ofReal_ofNat, ENNReal.coe_ofNat] using hh

noncomputable def oddBump {X : Type*} [PseudoEMetricSpace X]
    (T : X → X) (A : Set X) (x : X) : ℝ := setBump A x - setBump A (T x)

lemma oddBump_bounds {X : Type*} [PseudoEMetricSpace X]
    (T : X → X) (A : Set X) (x : X) : -1 ≤ oddBump T A x ∧ oddBump T A x ≤ 1 := by
  have hx := distanceBump_bounds (Metric.infEDist x A)
  have htx := distanceBump_bounds (Metric.infEDist (T x) A)
  unfold oddBump setBump
  constructor <;> linarith

lemma oddBump_odd {X : Type*} [PseudoEMetricSpace X] (T : X → X)
    (hT : Function.Involutive T) (A : Set X) (x : X) :
    oddBump T A (T x) = -oddBump T A x := by
  simp only [oddBump, hT x]
  ring

lemma oddBump_lipschitz {X : Type*} [PseudoEMetricSpace X]
    (T : X → X) (hT : Isometry T) (A : Set X) : LipschitzWith 64 (oddBump T A) := by
  have h := (setBump_lipschitz A).sub ((setBump_lipschitz A).comp hT.lipschitzWith)
  norm_num only [mul_one, Nat.reduceAdd] at h
  exact h

lemma oddBump_eq_one {X : Type*} [PseudoEMetricSpace X]
    (T : X → X) (A : Set X)
    (hsep : ∀ x ∈ A, ∀ y ∈ A, ENNReal.ofReal (1 / 8) < edist x (T y))
    {x : X} (hx : x ∈ A) : oddBump T A x = 1 := by
  have hdist : ENNReal.ofReal (1 / 32) ≤ Metric.infEDist (T x) A := by
    apply Metric.le_infEDist.mpr
    intro y hy
    rw [edist_comm]
    exact (by norm_num : ENNReal.ofReal (1 / 32) ≤ ENNReal.ofReal (1 / 8)).trans
      (hsep y hy x hx).le
  simp only [oddBump, setBump, Metric.infEDist_zero_of_mem hx,
    distanceBump_zero, distanceBump_vanish hdist, sub_zero]

lemma linkLength_le_copyLength {Q : Type*} {M : Q → Type*}
    (S : ProjectionSystem Q M) {D : ℕ} [NeZero D] (x y : GridLocation M D) :
    S.linkLength x y ≤ copyLength x y := by
  classical
  unfold ProjectionSystem.linkLength
  split_ifs <;> simp

lemma grid_independent_separation {Q : Type*} {M : Q → Type*}
    (S : ProjectionSystem Q M) {D : ℕ} [NeZero D] (hD : Even D)
    (hnoclique : ∀ x : GridLocation M D,
      ¬pathDistance S.linkLength x (gridAntipode x) ≤ ENNReal.ofReal (1 / 8))
    {V : Type*} (location : V → GridLocation M D) (A : Set V)
    (hA : (gridGraph S hD location).IsIndepSet A) :
    ∀ x ∈ location '' A, ∀ y ∈ location '' A,
      ENNReal.ofReal (1 / 8) < pathDistance S.linkLength x (gridAntipode y) := by
  rintro x ⟨u, hu, rfl⟩ y ⟨v, hv, rfl⟩
  by_contra hn
  have hle := le_of_not_gt hn
  by_cases h : u = v
  · subst v
    exact hnoclique (location u) hle
  · exact ((gridGraph S hD location).isIndepSet_iff.mp hA) hu hv h ⟨h, hle⟩

noncomputable def gridBump {Q : Type*} {M : Q → Type*}
    (S : ProjectionSystem Q M) {D : ℕ} [NeZero D]
    (A : Set (GridLocation M D)) (x : GridLocation M D) : ℝ := by
  letI := linkPseudoEMetric (S.linkLength (D := D)) (linkLength_self S) (linkLength_symm S)
  exact oddBump gridAntipode A x

theorem grid_independent_bump {Q : Type*} {M : Q → Type*} [∀ q, Fintype (M q)]
    (S : ProjectionSystem Q M) {D : ℕ} [NeZero D] (hD : Even D)
    (hnoclique : ∀ x : GridLocation M D,
      ¬pathDistance S.linkLength x (gridAntipode x) ≤ ENNReal.ofReal (1 / 8))
    {V : Type*} (location : V → GridLocation M D) (A : Set V)
    (hA : (gridGraph S hD location).IsIndepSet A) :
    let f := gridBump S (location '' A)
    (∀ x, -1 ≤ f x ∧ f x ≤ 1) ∧
    (∀ x, f (gridAntipode x) = -f x) ∧
    (∀ v ∈ A, f (location v) = 1) ∧
    (∀ x y, S.ZeroLink D x y → f x = f y) ∧
    (∀ q (u v : M q → ZMod D),
      edist (f ⟨q, u⟩) (f ⟨q, v⟩) ≤ (64 : ℝ≥0∞) *
        edist (fun k => ZMod.toAddCircle (u k)) (fun k => ZMod.toAddCircle (v k))) := by
  let := linkPseudoEMetric (S.linkLength (D := D)) (linkLength_self S) (linkLength_symm S)
  have hT : Isometry (gridAntipode : GridLocation M D → GridLocation M D) :=
    pathDistance_invariant S.linkLength gridAntipode (gridAntipode_involutive hD)
      (linkLength_antipode S hD)
  have hf : LipschitzWith 64 (gridBump S (location '' A)) :=
    oddBump_lipschitz gridAntipode hT (location '' A)
  refine ⟨oddBump_bounds gridAntipode (location '' A),
    oddBump_odd gridAntipode (gridAntipode_involutive hD) (location '' A), ?_, ?_, ?_⟩
  · intro v hv
    exact oddBump_eq_one gridAntipode (location '' A)
      (grid_independent_separation S hD hnoclique location A hA) ⟨v, hv, rfl⟩
  · intro x y hxy
    have hpath : pathDistance S.linkLength x y = 0 := by
      apply le_antisymm _ bot_le
      apply (pathDistance_le_link S.linkLength x y).trans
      simp [ProjectionSystem.linkLength, hxy]
    have h := hf x y
    change edist (gridBump S (location '' A) x) (gridBump S (location '' A) y) ≤
      (64 : ℝ≥0∞) * pathDistance S.linkLength x y at h
    rw [hpath, mul_zero] at h
    exact edist_eq_zero.mp (le_antisymm h bot_le)
  · intro q u v
    apply (hf ⟨q, u⟩ ⟨q, v⟩).trans
    simp only [ENNReal.coe_ofNat]
    apply mul_le_mul_right
    change pathDistance S.linkLength ⟨q, u⟩ ⟨q, v⟩ ≤ _
    apply (pathDistance_le_link S.linkLength _ _).trans
    apply (linkLength_le_copyLength S _ _).trans_eq
    rw [copyLength_same, edist_pi_def]
    simp only [Finset.sup_univ_eq_iSup]

noncomputable def finiteMcShane {G X : Type*} [Fintype G] [Nonempty G]
    [PseudoMetricSpace X] (e : G → X) (f : G → ℝ) (L : ℝ≥0) (x : X) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (fun y => f y + L * dist x (e y))

lemma finiteMcShane_le {G X : Type*} [Fintype G] [Nonempty G]
    [PseudoMetricSpace X] (e : G → X) (f : G → ℝ) (L : ℝ≥0) (x : X) (y : G) :
    finiteMcShane e f L x ≤ f y + L * dist x (e y) :=
  Finset.inf'_le _ (Finset.mem_univ y)

lemma finiteMcShane_on_grid {G X : Type*} [Fintype G] [Nonempty G]
    [PseudoMetricSpace X] (e : G → X) (f : G → ℝ) (L : ℝ≥0)
    (hf : ∀ x y, |f x - f y| ≤ L * dist (e x) (e y)) (x : G) :
    finiteMcShane e f L (e x) = f x := by
  apply le_antisymm
  · simpa using finiteMcShane_le e f L (e x) x
  · apply Finset.le_inf'
    intro y _
    have := (abs_le.mp (hf x y)).2
    linarith

lemma finiteMcShane_lipschitz {G X : Type*} [Fintype G] [Nonempty G]
    [PseudoMetricSpace X] (e : G → X) (f : G → ℝ) (L : ℝ≥0) :
    LipschitzWith L (finiteMcShane e f L) := by
  have hle (x y : X) : finiteMcShane e f L x ≤ finiteMcShane e f L y + L * dist x y := by
    obtain ⟨g, _, hg⟩ := Finset.exists_mem_eq_inf' (s := (Finset.univ : Finset G))
      Finset.univ_nonempty (fun g => f g + L * dist y (e g))
    change finiteMcShane e f L y = _ at hg
    have hm := mul_le_mul_of_nonneg_left (dist_triangle x y (e g)) L.coe_nonneg
    have h := finiteMcShane_le e f L x g
    rw [hg]
    linarith
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq, abs_le]
  have h₁ := hle x y
  have h₂ := hle y x
  rw [dist_comm y x] at h₂
  constructor <;> linarith

def clipUnit (x : ℝ) : ℝ := max (-1) (min 1 x)

lemma clipUnit_bounds (x : ℝ) : -1 ≤ clipUnit x ∧ clipUnit x ≤ 1 := by
  exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

lemma clipUnit_eq {x : ℝ} (hx : -1 ≤ x ∧ x ≤ 1) : clipUnit x = x := by
  simp [clipUnit, min_eq_right hx.2, max_eq_right hx.1]

lemma clipUnit_lipschitz : LipschitzWith 1 clipUnit :=
  (LipschitzWith.id.const_min 1).const_max (-1)

noncomputable def finiteOddExtension {G X : Type*} [Fintype G] [Nonempty G]
    [PseudoMetricSpace X] (e : G → X) (f : G → ℝ) (L : ℝ≥0) (T : X → X) (x : X) : ℝ :=
  (clipUnit (finiteMcShane e f L x) - clipUnit (finiteMcShane e f L (T x))) / 2

lemma finiteOddExtension_bounds {G X : Type*} [Fintype G] [Nonempty G]
    [PseudoMetricSpace X] (e : G → X) (f : G → ℝ) (L : ℝ≥0) (T : X → X) (x : X) :
    -1 ≤ finiteOddExtension e f L T x ∧ finiteOddExtension e f L T x ≤ 1 := by
  have hx := clipUnit_bounds (finiteMcShane e f L x)
  have htx := clipUnit_bounds (finiteMcShane e f L (T x))
  unfold finiteOddExtension
  constructor <;> linarith

lemma finiteOddExtension_odd {G X : Type*} [Fintype G] [Nonempty G]
    [PseudoMetricSpace X] (e : G → X) (f : G → ℝ) (L : ℝ≥0) (T : X → X)
    (hT : Function.Involutive T) (x : X) :
    finiteOddExtension e f L T (T x) = -finiteOddExtension e f L T x := by
  simp only [finiteOddExtension, hT x]
  ring

lemma finiteOddExtension_on_grid {G X : Type*} [Fintype G] [Nonempty G]
    [PseudoMetricSpace X] (e : G → X) (f : G → ℝ) (L : ℝ≥0) (T : X → X) (Tg : G → G)
    (hT : ∀ x, T (e x) = e (Tg x))
    (hf : ∀ x y, |f x - f y| ≤ L * dist (e x) (e y))
    (hb : ∀ x, -1 ≤ f x ∧ f x ≤ 1) (ho : ∀ x, f (Tg x) = -f x) (x : G) :
    finiteOddExtension e f L T (e x) = f x := by
  simp only [finiteOddExtension, hT x, finiteMcShane_on_grid e f L hf,
    clipUnit_eq (hb x), clipUnit_eq (hb (Tg x))]
  rw [ho x]
  ring

lemma finiteOddExtension_lipschitz {G X : Type*} [Fintype G] [Nonempty G]
    [PseudoMetricSpace X] (e : G → X) (f : G → ℝ) (L : ℝ≥0) (T : X → X)
    (hT : Isometry T) : LipschitzWith L (finiteOddExtension e f L T) := by
  have hg : LipschitzWith L (fun x => clipUnit (finiteMcShane e f L x)) := by
    simpa only [one_mul, Function.comp_def] using clipUnit_lipschitz.comp (finiteMcShane_lipschitz e f L)
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have h₁ := hg.dist_le_mul x y
  have h₂ := hg.dist_le_mul (T x) (T y)
  rw [hT.dist_eq] at h₂
  simp only [Real.dist_eq] at h₁ h₂ ⊢
  unfold finiteOddExtension
  rw [abs_le] at h₁ h₂ ⊢
  constructor <;> linarith

noncomputable def torusAntipode {ι : Type*} (x : ι → UnitAddCircle) : ι → UnitAddCircle :=
  fun k => x k + ((1 / 2 : ℝ) : UnitAddCircle)

lemma torusAntipode_involutive {ι : Type*} :
    Function.Involutive (torusAntipode : (ι → UnitAddCircle) → (ι → UnitAddCircle)) := by
  intro x
  funext k
  simp only [torusAntipode, add_assoc, ← AddCircle.coe_add]
  norm_num

lemma torusAntipode_isometry {ι : Type*} [Fintype ι] :
    Isometry (torusAntipode : (ι → UnitAddCircle) → (ι → UnitAddCircle)) := by
  intro x y
  simp only [edist_pi_def, torusAntipode, edist_add_right]

noncomputable def torusGrid {ι : Type*} {D : ℕ} [NeZero D]
    (x : ι → ZMod D) : ι → UnitAddCircle := fun k => ZMod.toAddCircle (x k)

lemma torusGrid_antipode {ι : Type*} {D : ℕ} [NeZero D] (hD : Even D)
    (x : ι → ZMod D) :
    torusAntipode (torusGrid x) = torusGrid (fun k => x k + ((D / 2 : ℕ) : ZMod D)) := by
  funext k
  simp only [torusAntipode, torusGrid, map_add, ZMod.toAddCircle_natCast,
    grid_half_real D hD]

noncomputable def tupleExtension {Q : Type*} {M : Q → Type*} [∀ q, Fintype (M q)]
    (S : ProjectionSystem Q M) {D : ℕ} [NeZero D]
    (A : Set (GridLocation M D)) (q : Q) (x : M q → UnitAddCircle) : ℝ := by
  classical
  exact finiteOddExtension torusGrid (fun u => gridBump S A ⟨q, u⟩) 64 torusAntipode x

lemma tupleExtension_bounds {Q : Type*} {M : Q → Type*} [∀ q, Fintype (M q)]
    (S : ProjectionSystem Q M) {D : ℕ} [NeZero D]
    (A : Set (GridLocation M D)) (q : Q) (x : M q → UnitAddCircle) :
    -1 ≤ tupleExtension S A q x ∧ tupleExtension S A q x ≤ 1 := by
  classical
  exact finiteOddExtension_bounds _ _ _ _ _

end LargeIndependentSets

end OAI
