import OAI.GroupTheory.Hyperbolic.MatrixRank

namespace OAI

namespace Release075
open scoped BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable

/-- Independence of coordinates under the uniform average on a finite product. -/
theorem expect_pi_product {I D : Type*} [Fintype I] [DecidableEq I] [Fintype D]
    (f : I → D → ℝ) :
    (𝔼 ω : I → D, ∏ i, f i (ω i)) = ∏ i, 𝔼 d, f i d := by
  classical
  simp only [Fintype.expect_eq_sum_div_card]
  rw [← Fintype.prod_sum]
  simp only [Fintype.card_pi, Nat.cast_prod, Finset.prod_div_distrib]

/-- A coordinate of a uniform product has the uniform marginal. -/
theorem expect_coordinate {I D : Type*} [Fintype I] [DecidableEq I] [Fintype D] [Nonempty D]
    (i : I) (f : D → ℝ) : (𝔼 ω : I → D, f (ω i)) = 𝔼 d, f d := by
  classical
  have h := expect_pi_product (fun j d => if j = i then f d else 1)
  have hm (j : I) : (𝔼 d, if j = i then f d else (1 : ℝ)) =
      if j = i then (𝔼 d, f d) else 1 := by
    by_cases hj : j = i <;> simp [hj]
  simpa only [hm, Finset.prod_ite_eq', Finset.mem_univ, ite_true] using h

/-- Distinct coordinate functions have a factorized second moment. -/
theorem expect_two_coordinates {I D : Type*} [Fintype I] [DecidableEq I] [Fintype D] [Nonempty D]
    (i j : I) (hij : i ≠ j) (f g : D → ℝ) :
    (𝔼 ω : I → D, f (ω i) * g (ω j)) = (𝔼 d, f d) * (𝔼 d, g d) := by
  classical
  let F : I → D → ℝ := fun k d =>
    (if k = i then f d else 1) * (if k = j then g d else 1)
  have hprod (ω : I → D) : (∏ k, F k (ω k)) = f (ω i) * g (ω j) := by
    simp only [F, Finset.prod_mul_distrib]
    simp
  have hmean (k : I) : (𝔼 d, F k d) =
      (if k = i then (𝔼 d, f d) else 1) * (if k = j then (𝔼 d, g d) else 1) := by
    by_cases hi : k = i
    · subst k; simp [F, hij]
    · by_cases hj : k = j
      · subst k; simp [F, hi]
      · simp [F, hi, hj]
  have h := expect_pi_product F
  simpa only [hprod, hmean, Finset.prod_mul_distrib,
    Finset.prod_ite_eq', Finset.mem_univ, ite_true] using h

theorem expect_low_indicator_le {Ω : Type*} [Fintype Ω]
    (X : Ω → ℝ) (μ t : ℝ) (ht : t < μ) :
    (𝔼 ω, if X ω < t then (1 : ℝ) else 0) ≤
      (𝔼 ω, (X ω - μ)^2) / (μ-t)^2 := by
  classical
  have hd : 0 < (μ-t)^2 := sq_pos_of_pos (sub_pos.mpr ht)
  rw [le_div_iff₀ hd, Finset.expect_mul]
  apply Finset.expect_le_expect
  intro ω _
  split_ifs with h
  · have hh : (μ-t)^2 ≤ (μ-X ω)^2 :=
      (sq_le_sq₀ (by linarith : 0 ≤ μ-t) (by linarith : 0 ≤ μ-X ω)).mpr (by linarith)
    nlinarith
  · simpa only [zero_mul] using sq_nonneg (X ω - μ)

/-- Existence from a strict finite average bound, without measure-theoretic null sets. -/
theorem exists_of_expect_lt {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (X : Ω → ℝ) (a : ℝ) (h : (𝔼 ω, X ω) < a) : ∃ ω, X ω < a := by
  obtain ⟨ω,_,hω⟩ := Finset.exists_lt_of_expect_lt Finset.univ_nonempty h
  exact ⟨ω,hω⟩

/-- Variance of a sum of independent coordinates, proved by a finite double sum. -/
theorem expect_centered_sum_sq {I D : Type*} [Fintype I] [DecidableEq I]
    [Fintype D] [Nonempty D] (b : I → D → ℝ) (p : I → ℝ)
    (hp : ∀ i, (𝔼 d, b i d) = p i) :
    (𝔼 ω : I → D, ((∑ i, b i (ω i)) - ∑ i, p i)^2) =
      ∑ i, (𝔼 d, (b i d - p i)^2) := by
  classical
  let X : I → D → ℝ := fun i d => b i d - p i
  have hzero (i : I) : (𝔼 d, X i d) = 0 := by
    simp [X, Finset.expect_sub_distrib, hp]
  have hcross (i j : I) :
      (𝔼 ω : I → D, X i (ω i) * X j (ω j)) =
      if i = j then (𝔼 d, (X i d)^2) else 0 := by
    by_cases hij : i = j
    · subst j
      simp only [← sq]
      exact expect_coordinate i (fun d => (X i d)^2)
    · rw [ite_eq_right hij, expect_two_coordinates i j hij, hzero, zero_mul]
  calc
    _ = 𝔼 ω : I → D, ∑ i, ∑ j, X i (ω i) * X j (ω j) := by
      apply Finset.expect_congr rfl
      intro ω _
      rw [← Finset.sum_sub_distrib, sq, Finset.sum_mul_sum]
    _ = ∑ i, ∑ j, 𝔼 ω : I → D, X i (ω i) * X j (ω j) := by
      rw [Finset.expect_sum_comm]
      congr 1; ext i
      rw [Finset.expect_sum_comm]
    _ = _ := by simp [hcross, X]

theorem expect_bernoulli_sum_sq_le {I D : Type*} [Fintype I] [DecidableEq I]
    [Fintype D] [Nonempty D] (b : I → D → ℝ) (p : I → ℝ)
    (hb : ∀ i d, b i d = 0 ∨ b i d = 1)
    (hp : ∀ i, (𝔼 d, b i d) = p i) :
    (𝔼 ω : I → D, ((∑ i, b i (ω i)) - ∑ i, p i)^2) ≤ ∑ i, p i := by
  classical
  rw [expect_centered_sum_sq b p hp]
  apply Finset.sum_le_sum
  intro i _
  have heq : (𝔼 d, (b i d - p i)^2) = p i - (p i)^2 := by
    calc
      _ = 𝔼 d, (b i d - 2 * p i * b i d + (p i)^2) := by
        apply Finset.expect_congr rfl
        intro d _
        rcases hb i d with h | h <;> rw [h] <;> ring
      _ = _ := by
        rw [Finset.expect_add_distrib, Finset.expect_sub_distrib,
          ← Finset.mul_expect, hp]
        simp only [Fintype.expect_const]
        ring
  rw [heq]
  linarith [sq_nonneg (p i)]

/-- Joint moments of any injectively selected coordinates. -/
theorem expect_selected_product {A I D : Type*} [Fintype A] [Fintype I]
    [DecidableEq I] [Fintype D] [Nonempty D]
    (e : A ↪ I) (f : A → D → ℝ) :
    (𝔼 ω : I → D, ∏ a, f a (ω (e a))) = ∏ a, 𝔼 d, f a d := by
  classical
  let F : I → D → ℝ := fun i d => Function.extend e (fun a => f a d) (fun _ => 1) i
  have hin (a : A) (d : D) : F (e a) d = f a d := e.injective.extend_apply _ _ _
  have hout (i : I) (hi : i ∉ Set.range e) (d : D) : F i d = 1 :=
    Function.extend_apply' _ _ _ hi
  have hprod (ω : I → D) : (∏ a, f a (ω (e a))) = ∏ i, F i (ω i) :=
    Fintype.prod_of_injective e e.injective _ _ (fun i hi => hout i hi _) (fun a => (hin _ _).symm)
  have hmean : (∏ a, 𝔼 d, f a d) = ∏ i, 𝔼 d, F i d := by
    apply Fintype.prod_of_injective e e.injective
    · intro i hi; simp only [hout i hi, Fintype.expect_const]
    · intro a; simp only [hin]
  simp_rw [hprod, hmean]
  exact expect_pi_product F

section ProjectiveLines
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- A line through a mark, chosen by its projective direction. -/
def OnChosenLine (a z : V) (d : Projectivization K V) : Prop :=
  ∃ t : K, a + t • d.rep = z

/-- Only the chosen line's own mark is punctured. -/
def PuncturedIncidence (a z : V) (d : Projectivization K V) : Prop :=
  z ≠ a ∧ OnChosenLine a z d

/-- At a point different from the mark, exactly one direction gives incidence. -/
theorem puncturedIncidence_iff (a z : V) (hza : z ≠ a) (d : Projectivization K V) :
    PuncturedIncidence a z d ↔ d = Projectivization.mk K (z-a) (sub_ne_zero.mpr hza) := by
  have hd := d.mk_rep
  rw [PuncturedIncidence, and_iff_right hza]
  constructor
  · rintro ⟨t,ht⟩
    rw [← hd, Projectivization.mk_eq_mk_iff']
    have ht' : t • d.rep = z-a := by rw [← ht]; abel
    have ht0 : t ≠ 0 := by intro h; simp [h] at ht; exact hza ht.symm
    refine ⟨t⁻¹, ?_⟩
    rw [← ht', smul_smul, inv_mul_cancel₀ ht0, one_smul]
  · intro h
    have hh := (Projectivization.mk_eq_mk_iff' K (z-a) d.rep
      (sub_ne_zero.mpr hza) d.rep_nonzero).mp (h.symm.trans hd.symm)
    obtain ⟨t,ht⟩ := hh
    exact ⟨t, by rw [ht]; abel⟩

/-- Each geometric line contains exactly |K| points. -/
theorem lineMap_injective (a : V) (d : Projectivization K V) :
    Function.Injective (fun t : K => a + t • d.rep) := by
  intro t u h
  exact smul_left_injective K d.rep_nonzero (add_left_cancel h)

/-- The exact Bernoulli parameter of a uniformly chosen direction. -/
theorem expect_puncturedIncidence [Fintype (Projectivization K V)]
    (a z : V) (hza : z ≠ a) :
    (𝔼 d : Projectivization K V, if PuncturedIncidence a z d then (1 : ℝ) else 0) =
      1 / Fintype.card (Projectivization K V) := by
  classical
  simp only [puncturedIncidence_iff a z hza, Fintype.expect_eq_sum_div_card,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]

end ProjectiveLines

section CycleCount
variable {A K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- An attempted mark on the geometric line joining consecutive point vertices. -/
def candidateMark (σ : A → A) (p : A → V) (t : A → K) (a : A) : V :=
  p a + t a • (p (σ a) - p a)

/-- An over-count of short cycles: parameters, rather than marks, are enumerated.
Marks at punctured endpoints are deliberately permitted for the upper bound. -/
def CycleCandidate (S : Finset V) (σ : A → A) :=
  {c : (A → V) × (A → K) // Function.Injective c.1 ∧
    (∀ a, c.1 (σ a) ≠ c.1 a) ∧
    (∀ a, candidateMark σ c.1 c.2 a ∈ S) ∧
    Function.Injective (candidateMark σ c.1 c.2)}

instance [Fintype A] [Fintype K] [Fintype V] (S : Finset V) (σ : A → A) :
    Fintype (CycleCandidate (K := K) S σ) := by unfold CycleCandidate; infer_instance

namespace CycleCandidate
variable {S : Finset V} {σ : A → A}

def marks (c : CycleCandidate (K := K) S σ) : A ↪ S where
  toFun a := ⟨candidateMark σ c.val.1 c.val.2 a,c.property.2.2.1 a⟩
  inj' := fun _ _ h => c.property.2.2.2 (congrArg Subtype.val h)

def direction (c : CycleCandidate (K := K) S σ) (a : A) : Projectivization K V :=
  Projectivization.mk K (c.val.1 (σ a) - c.val.1 a) (sub_ne_zero.mpr (c.property.2.1 a))

def Occurs (c : CycleCandidate (K := K) S σ) (ω : S → Projectivization K V) : Prop :=
  ∀ a, ω (c.marks a) = c.direction a

/-- The displayed upper count still has independent prescribed directions because
its candidate marks are distinct. -/
theorem expect_occurs [Fintype A] [Fintype (Projectivization K V)] [Nontrivial V]
    (c : CycleCandidate (K := K) S σ) :
    (𝔼 ω : S → Projectivization K V, if c.Occurs ω then (1 : ℝ) else 0) =
      (1 / Fintype.card (Projectivization K V) : ℝ) ^ Fintype.card A := by
  calc
    _ = 𝔼 ω : S → Projectivization K V,
        ∏ a, if ω (c.marks a) = c.direction a then (1 : ℝ) else 0 := by
      apply Finset.expect_congr rfl
      intro ω _
      rw [Fintype.prod_boole]
      by_cases h : ∀ a : A, ω (c.marks a) = c.direction a
      · rw [ite_eq_left h]
        exact ite_eq_left h
      · rw [ite_eq_right h]
        exact ite_eq_right h
    _ = ∏ a, (𝔼 d : Projectivization K V, if d = c.direction a then (1 : ℝ) else 0) :=
      by
      exact expect_selected_product (D := Projectivization K V) c.marks
        (fun a d => if d = c.direction a then (1 : ℝ) else 0)
    _ = _ := by
      simp only [Fintype.expect_eq_sum_div_card, Finset.sum_ite_eq', Finset.mem_univ,
        ite_true, Finset.prod_const, Finset.card_univ]
end CycleCandidate

/-- All occurring encoded cycles for a given random outcome. -/
def badCycles [Fintype A] [Fintype K] [Fintype V]
    (S : Finset V) (σ : A → A) (ω : S → Projectivization K V) : Finset (CycleCandidate (K := K) S σ) :=
  Finset.univ.filter (fun c => c.Occurs ω)

/-- Expected cycle bound before specializing the finite field cardinalities. -/
theorem expect_badCycles_le [Fintype A] [Fintype K] [Fintype V]
    [Fintype (Projectivization K V)] [Nontrivial V]
    (S : Finset V) (σ : A → A) :
    (𝔼 ω : S → Projectivization K V, ((badCycles S σ ω).card : ℝ)) ≤
      (Fintype.card V : ℝ)^Fintype.card A * (Fintype.card K : ℝ)^Fintype.card A *
        (1 / Fintype.card (Projectivization K V) : ℝ)^Fintype.card A := by
  have hcard : Fintype.card (CycleCandidate (K := K) S σ) ≤
      Fintype.card V ^ Fintype.card A * Fintype.card K ^ Fintype.card A := by
    simpa [CycleCandidate] using Fintype.card_subtype_le
      (fun c : (A → V) × (A → K) => Function.Injective c.1 ∧
        (∀ a, c.1 (σ a) ≠ c.1 a) ∧ (∀ a, candidateMark σ c.1 c.2 a ∈ S) ∧
        Function.Injective (candidateMark σ c.1 c.2))
  calc
    _ = ∑ c : CycleCandidate (K := K) S σ, 𝔼 ω : S → Projectivization K V,
        if c.Occurs ω then (1 : ℝ) else 0 := by
      simp only [badCycles, ← Finset.sum_boole]
      exact Finset.expect_sum_comm _ _ _
    _ = (Fintype.card (CycleCandidate (K := K) S σ) : ℝ) *
        (1 / Fintype.card (Projectivization K V) : ℝ)^Fintype.card A := by
      simp only [CycleCandidate.expect_occurs, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast hcard

end CycleCount

section Degrees
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Fintype (Projectivization K V)] [Nontrivial V]

/-- Incidence degree before alteration, with the marked point removed from its line. -/
def pointDegree (S : Finset V) (ω : S → Projectivization K V) (z : V) : ℕ :=
  (Finset.univ.filter (fun a : S => PuncturedIncidence a.val z (ω a))).card

/-- Exact mean, including the missing self-mark when the point belongs to the grid. -/
def pointMean (S : Finset V) (z : V) : ℝ :=
  ∑ a : S, if z ≠ a.val then 1 / (Fintype.card (Projectivization K V) : ℝ) else 0

omit [Nontrivial V] in
theorem pointMean_formula (S : Finset V) (z : V) :
    pointMean (K := K) S z = (S.erase z).card / (Fintype.card (Projectivization K V) : ℝ) := by
  rw [pointMean, ← Finset.sum_subtype S (fun _ => Iff.rfl)
    (fun a : V => if z ≠ a then 1 / (Fintype.card (Projectivization K V) : ℝ) else 0)]
  rw [← Finset.sum_filter]
  have hf : S.filter (fun a => z ≠ a) = S.erase z := by
    ext a; simp [ne_comm, and_comm]
  rw [hf]
  simp [div_eq_mul_inv]

theorem expect_pointDegree (S : Finset V) (z : V) :
    (𝔼 ω : S → Projectivization K V, (pointDegree S ω z : ℝ)) = pointMean (K := K) S z := by
  have hm (a : S) : (𝔼 d : Projectivization K V,
      if PuncturedIncidence a.val z d then (1 : ℝ) else 0) =
      if z ≠ a.val then 1 / (Fintype.card (Projectivization K V) : ℝ) else 0 := by
    by_cases ha : z = a.val
    · simp [ha, PuncturedIncidence]
    · rw [ite_eq_left ha]; exact expect_puncturedIncidence a.val z ha
  simp only [pointDegree, ← Finset.sum_boole, pointMean]
  rw [Finset.expect_sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  exact (expect_coordinate a (fun d : Projectivization K V =>
    if PuncturedIncidence a.val z d then (1 : ℝ) else 0)).trans (hm a)

theorem variance_pointDegree_le (S : Finset V) (z : V) :
    (𝔼 ω : S → Projectivization K V,
      ((pointDegree S ω z : ℝ) - pointMean (K := K) S z)^2) ≤ pointMean (K := K) S z := by
  let b : S → Projectivization K V → ℝ := fun a d =>
    if PuncturedIncidence a.val z d then 1 else 0
  let p : S → ℝ := fun a => if z ≠ a.val then
    1 / (Fintype.card (Projectivization K V) : ℝ) else 0
  have hp (a : S) : (𝔼 d, b a d) = p a := by
    by_cases ha : z = a.val
    · simp [b,p,ha,PuncturedIncidence]
    · simp only [p, ite_eq_left ha, b]; exact expect_puncturedIncidence a.val z ha
  have h := expect_bernoulli_sum_sq_le b p (by intro a d; simp only [b]; split_ifs <;> simp) hp
  simpa only [b,p,Finset.sum_boole,pointDegree,pointMean] using h

/-- Expected size of the exceptional low-degree set in a completely finite form. -/
theorem expect_lowDegree_le [Fintype V] (S : Finset V) (T : ℕ) (μ : ℝ)
    (hμ : 0 < μ) (hT : 2 * (T : ℝ) ≤ μ)
    (hlower : ∀ z : V, μ ≤ pointMean (K := K) S z) :
    (𝔼 ω : S → Projectivization K V,
      ((Finset.univ.filter (fun z : V => pointDegree S ω z < T)).card : ℝ)) ≤
        4 * (Fintype.card V : ℝ) / μ := by
  have hpoint (z : V) : (𝔼 ω : S → Projectivization K V,
      if pointDegree S ω z < T then (1 : ℝ) else 0) ≤ 4 / μ := by
    have hz := hlower z
    have hm : 0 < pointMean (K := K) S z := hμ.trans_le hz
    have ht : (T : ℝ) < pointMean (K := K) S z := by linarith
    have hcheb := expect_low_indicator_le (fun ω : S → Projectivization K V =>
      (pointDegree S ω z : ℝ)) (pointMean (K := K) S z) (T : ℝ) ht
    have hvar := variance_pointDegree_le (K := K) S z
    have hden : 0 < (pointMean (K := K) S z - (T : ℝ))^2 := sq_pos_of_pos (by linarith)
    have hrat : pointMean (K := K) S z / (pointMean (K := K) S z - (T : ℝ))^2 ≤ 4 / μ := by
      apply (div_le_div_iff₀ hden hμ).mpr
      have hbound : 2 * (T : ℝ) ≤ pointMean (K := K) S z := hT.trans hz
      have hnon : 0 ≤ pointMean (K := K) S z - 2 * (T : ℝ) := by linarith
      have hsq := sq_nonneg (pointMean (K := K) S z - 2 * (T : ℝ))
      have hprod := mul_nonneg hnon (show 0 ≤ (T : ℝ) by positivity)
      have hmμ := mul_le_mul_of_nonneg_left hz hm.le
      nlinarith
    have h := hcheb.trans ((div_le_div_of_nonneg_right hvar hden.le).trans hrat)
    simpa only [Nat.cast_lt] using h
  simp only [← Finset.sum_boole]
  rw [Finset.expect_sum_comm]
  calc
    _ ≤ ∑ z : V, (4 / μ : ℝ) := Finset.sum_le_sum (fun z _ => hpoint z)
    _ = _ := by simp; ring
end Degrees

/-- The simple bipartite graph of a relation (the same definition used by the links). -/
def relationGraph {A B : Type*} (R : A → B → Prop) : SimpleGraph (A ⊕ B) where
  Adj x y := match x,y with
    | .inl a, .inr b => R a b
    | .inr b, .inl a => R a b
    | _,_ => False
  symm := ⟨by intro x y; cases x <;> cases y <;> simp⟩
  loopless := ⟨by intro x; cases x <;> simp⟩

def relationColoring {A B : Type*} (R : A → B → Prop) : (relationGraph R).Coloring Bool :=
  {toFun := Sum.elim (fun _ => false) (fun _ => true)
   map_rel' := by intro x y h; cases x <;> cases y <;> simp_all [relationGraph]}

theorem relationGraph_even_getVert {A B : Type*} (R : A → B → Prop) {a : A} {v : A ⊕ B}
    (w : (relationGraph R).Walk (.inl a) v) (k : ℕ) (hk : 2*k ≤ w.length) :
    ∃ b : A, w.getVert (2*k) = .inl b := by
  have h := (relationColoring R).even_length_iff_congr (w.take (2*k))
  rw [SimpleGraph.Walk.take_length, inf_eq_left.mpr hk] at h
  have he : Even (2*k) := ⟨k,by omega⟩
  have hh := h.mp he
  cases hv : w.getVert (2*k) with
  | inl b => exact ⟨b,rfl⟩
  | inr b => simp [hv,relationColoring] at hh

theorem relationGraph_odd_getVert {A B : Type*} (R : A → B → Prop) {a : A} {v : A ⊕ B}
    (w : (relationGraph R).Walk (.inl a) v) (k : ℕ) (hk : 2*k+1 ≤ w.length) :
    ∃ b : B, w.getVert (2*k+1) = .inr b := by
  obtain ⟨a',ha⟩ := relationGraph_even_getVert R w k (by omega)
  have h := w.adj_getVert_succ (by omega : 2*k < w.length)
  rw [ha] at h
  cases hv : w.getVert (2*k+1) with
  | inl b => rw [hv] at h; exact h.elim
  | inr b => exact ⟨b,rfl⟩

/-- The concrete alternating normal form of any simple bipartite cycle. -/
theorem relationGraph_cycle_encoding {A B : Type*} (R : A → B → Prop)
    {a : A} (w : (relationGraph R).Walk (.inl a) (.inl a)) (hw : w.IsCycle) :
    ∃ (s : ℕ) (_ : 2 ≤ s) (p : Fin s → A) (l : Fin s → B),
      w.length = 2*s ∧ Function.Injective p ∧ Function.Injective l ∧
      ∀ i, R (p i) (l i) ∧ R (p (finRotate s i)) (l i) := by
  have he := ((relationColoring R).even_length_iff_congr w).mpr Iff.rfl
  obtain ⟨s,hs⟩ := he
  have hlen : w.length = 2*s := by omega
  have hs2 : 2 ≤ s := by have := hw.three_le_length; omega
  let p : Fin s → A := fun i => (relationGraph_even_getVert R w i.val (by omega)).choose
  let l : Fin s → B := fun i => (relationGraph_odd_getVert R w i.val (by omega)).choose
  have hp (i : Fin s) : w.getVert (2*i.val) = .inl (p i) :=
    (relationGraph_even_getVert R w i.val (by omega)).choose_spec
  have hl (i : Fin s) : w.getVert (2*i.val+1) = .inr (l i) :=
    (relationGraph_odd_getVert R w i.val (by omega)).choose_spec
  have hpnext (i : Fin s) : w.getVert (2*i.val+2) = .inl (p (finRotate s i)) := by
    have hv : (finRotate s i).val = (i.val+1)%s := by
      have hs1 : 1 < s := by omega
      simp [finRotate_apply, Fin.add_def, Nat.mod_eq_of_lt hs1]
    by_cases hi : i.val+1 < s
    · rw [Nat.mod_eq_of_lt hi] at hv
      simpa only [hv, mul_add, mul_one] using hp (finRotate s i)
    · have hi' : i.val+1=s := by omega
      have hv' : (finRotate s i).val = 0 := by rw [hi',Nat.mod_self] at hv; exact hv
      have hzero := hp (finRotate s i)
      rw [hv',mul_zero,SimpleGraph.Walk.getVert_zero] at hzero
      rw [show 2*i.val+2=w.length by omega,SimpleGraph.Walk.getVert_length]
      exact hzero
  refine ⟨s,hs2,p,l,hlen,?_,?_,?_⟩
  · intro i j hij
    apply Fin.ext
    have heq : w.getVert (2*i.val) = w.getVert (2*j.val) := by rw [hp,hp,hij]
    have hh := hw.getVert_injOn' (by change 2*i.val ≤ w.length-1; omega)
      (by change 2*j.val ≤ w.length-1; omega) heq
    omega
  · intro i j hij
    apply Fin.ext
    have heq : w.getVert (2*i.val+1) = w.getVert (2*j.val+1) := by rw [hl,hl,hij]
    have hh := hw.getVert_injOn' (by change 2*i.val+1 ≤ w.length-1; omega)
      (by change 2*j.val+1 ≤ w.length-1; omega) heq
    omega
  · intro i
    have h₀ := w.adj_getVert_succ (by omega : 2*i.val < w.length)
    have h₁ := w.adj_getVert_succ (by omega : 2*i.val+1 < w.length)
    rw [hp,hl] at h₀
    rw [hl,show 2*i.val+1+1=2*i.val+2 by omega,hpnext] at h₁
    exact ⟨h₀,h₁⟩

/-- The same encoding without a restriction on the chosen starting vertex. -/
theorem relationGraph_any_cycle_encoding {A B : Type*} (R : A → B → Prop)
    {a : A ⊕ B} (w : (relationGraph R).Walk a a) (hw : w.IsCycle) :
    ∃ (s : ℕ) (_ : 2 ≤ s) (p : Fin s → A) (l : Fin s → B),
      w.length = 2*s ∧ Function.Injective p ∧ Function.Injective l ∧
      ∀ i, R (p i) (l i) ∧ R (p (finRotate s i)) (l i) := by
  cases a with
  | inl a => exact relationGraph_cycle_encoding R w hw
  | inr b =>
    have hn : 0 < w.length := by have := hw.three_le_length; omega
    have ha := w.adj_getVert_succ hn
    rw [SimpleGraph.Walk.getVert_zero] at ha
    cases hv : w.getVert 1 with
    | inr c => rw [hv] at ha; exact ha.elim
    | inl a =>
      have hm : Sum.inl a ∈ w.support := hv ▸ w.getVert_mem_support 1
      obtain ⟨s,hs,p,l,hlen,hp,hl,h⟩ := relationGraph_cycle_encoding R (w.rotate (.inl a) hm) (hw.rotate hm)
      exact ⟨s,hs,p,l,by simpa using hlen,hp,hl,h⟩

section EncodingIncidence
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- Two distinct points determine their direction and every mark on their line. -/
theorem line_two_points (a z z' : V) (d : Projectivization K V) (hzz : z' ≠ z)
    (hz : OnChosenLine a z d) (hz' : OnChosenLine a z' d) :
    ∃ t : K, a = z + t • (z'-z) ∧
      d = Projectivization.mk K (z'-z) (sub_ne_zero.mpr hzz) := by
  obtain ⟨u,hu⟩ := hz
  obtain ⟨v,hv⟩ := hz'
  have hdiff : z'-z = (v-u) • d.rep := by rw [← hu,← hv,sub_smul]; abel
  have hvu : v-u ≠ 0 := by
    intro h; rw [h,zero_smul] at hdiff; exact hzz (sub_eq_zero.mp hdiff)
  refine ⟨-u / (v-u),?_,?_⟩
  · rw [hdiff,smul_smul,div_mul_cancel₀ _ hvu,neg_smul,← hu]
    abel
  · rw [← d.mk_rep,Projectivization.mk_eq_mk_iff']
    refine ⟨(v-u)⁻¹,?_⟩
    rw [hdiff,smul_smul,inv_mul_cancel₀ hvu,one_smul]

end EncodingIncidence

/-- Rotation has no fixed point on a cycle with at least two entries. -/
theorem finRotate_ne_self {s : ℕ} (hs : 2 ≤ s) (i : Fin s) : finRotate s i ≠ i := by
  intro hi
  have hs1 : 1 < s := by omega
  have he := congrArg Fin.val hi
  have hv : (finRotate s i).val = (i.val+1)%s := by
    simp [finRotate_apply, Fin.add_def, Nat.mod_eq_of_lt hs1]
  rw [hv] at he
  by_cases h : i.val+1 < s
  · rw [Nat.mod_eq_of_lt h] at he; omega
  · have hi' : i.val+1=s := by omega
    rw [hi',Nat.mod_self] at he; omega

section Alteration
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- Any actual simple incidence cycle yields one of the counted attempts. -/
theorem cycleCandidate_of_incidence {S : Finset V} (ω : S → Projectivization K V)
    {s : ℕ} (hs : 2 ≤ s) (p : Fin s → V) (l : Fin s → S)
    (hp : Function.Injective p) (hl : Function.Injective l)
    (h : ∀ i, PuncturedIncidence (l i).val (p i) (ω (l i)) ∧
      PuncturedIncidence (l i).val (p (finRotate s i)) (ω (l i))) :
    ∃ c : CycleCandidate (K := K) S (finRotate s), c.Occurs ω ∧ ∀ i, c.marks i = l i := by
  have hneq (i : Fin s) : p (finRotate s i) ≠ p i := hp.ne (finRotate_ne_self hs i)
  have hex (i : Fin s) := line_two_points (l i).val (p i) (p (finRotate s i)) (ω (l i))
    (hneq i) (h i).1.2 (h i).2.2
  let t : Fin s → K := fun i => (hex i).choose
  have ht (i : Fin s) : candidateMark (finRotate s) p t i = (l i).val := (hex i).choose_spec.1.symm
  let c : CycleCandidate (K := K) S (finRotate s) :=
    ⟨(p,t),hp,hneq,(fun i => ht i ▸ (l i).property),by
      intro i j hij
      apply hl
      apply Subtype.ext
      simpa only [ht] using hij⟩
  have hc (i : Fin s) : c.marks i = l i := Subtype.ext (ht i)
  refine ⟨c,?_,hc⟩
  intro i
  rw [hc]
  exact (hex i).choose_spec.2

variable [Fintype K] [Fintype V]

/-- All marks lying on an occurring short-cycle attempt are discarded. -/
def deletedMarks (S : Finset V) (ω : S → Projectivization K V) : Finset S :=
  (Finset.Icc 2 6).biUnion fun s =>
    (badCycles S (finRotate s) ω).biUnion fun c => Finset.univ.image c.marks

theorem deletedMarks_card_le (S : Finset V) (ω : S → Projectivization K V) :
    (deletedMarks S ω).card ≤ 6 * ∑ s ∈ Finset.Icc 2 6, (badCycles S (finRotate s) ω).card := by
  apply Finset.card_biUnion_le.trans
  calc
    _ ≤ ∑ s ∈ Finset.Icc 2 6, 6 * (badCycles S (finRotate s) ω).card := by
      apply Finset.sum_le_sum
      intro s hs
      apply Finset.card_biUnion_le.trans
      calc
        _ ≤ ∑ _c ∈ badCycles S (finRotate s) ω, 6 := by
          apply Finset.sum_le_sum
          intro c _
          have hcard : (Finset.univ.image c.marks).card ≤ s := by
            exact Finset.card_image_le.trans (by simp)
          exact hcard.trans (Finset.mem_Icc.mp hs).2
        _ = _ := by simp [mul_comm]
    _ = _ := by rw [Finset.mul_sum]

def Retained (S : Finset V) (ω : S → Projectivization K V) := {a : S // a ∉ deletedMarks S ω}

/-- Deletion creates no cycle; exact girth >12 is obtained, including repeated
geometric lines with distinct labels. -/
theorem retained_girth (S : Finset V) (ω : S → Projectivization K V)
    (a : V ⊕ Retained S ω)
    (w : (relationGraph (fun z (i : Retained S ω) =>
      PuncturedIncidence i.val.val z (ω i.val))).Walk a a) (hw : w.IsCycle) : 12 < w.length := by
  by_contra hlen
  obtain ⟨s,hs,p,l,heq,hp,hl,h⟩ := relationGraph_any_cycle_encoding _ w hw
  have hs6 : s ≤ 6 := by omega
  let l' : Fin s → S := fun i => (l i).val
  have hl' : Function.Injective l' := by
    intro i j hh; apply hl; exact Subtype.ext hh
  obtain ⟨c,hc,hcl⟩ := cycleCandidate_of_incidence ω hs p l' hp hl' h
  let i : Fin s := ⟨0,by omega⟩
  have hdel : c.marks i ∈ deletedMarks S ω := by
    apply Finset.mem_biUnion.mpr
    refine ⟨s,Finset.mem_Icc.mpr ⟨hs,hs6⟩,?_⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨c,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hc⟩,?_⟩
    exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩
  rw [hcl] at hdel
  exact (l i).property hdel
end Alteration

section Exceptional
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable [Fintype K] [Fintype V]

instance (S : Finset V) (ω : S → Projectivization K V) : Fintype (Retained S ω) := by
  unfold Retained
  infer_instance

def chosenLinePoints (a : V) (d : Projectivization K V) : Finset V :=
  Finset.univ.image (fun t : K => a+t • d.rep)

omit [Fintype V] in
theorem mem_chosenLinePoints (a z : V) (d : Projectivization K V) :
    z ∈ chosenLinePoints a d ↔ OnChosenLine a z d := by
  simp only [chosenLinePoints, Finset.mem_image, Finset.mem_univ, true_and, OnChosenLine]

omit [Fintype V] in
theorem chosenLinePoints_card (a : V) (d : Projectivization K V) :
    (chosenLinePoints a d).card = Fintype.card K := by
  exact (Finset.card_image_iff.mpr (lineMap_injective a d).injOn).trans (Finset.card_univ)

def deletedPoints (S : Finset V) (ω : S → Projectivization K V) : Finset V :=
  (deletedMarks S ω).biUnion (fun a => chosenLinePoints a.val (ω a))

theorem deletedPoints_card_le (S : Finset V) (ω : S → Projectivization K V) :
    (deletedPoints S ω).card ≤ Fintype.card K * (deletedMarks S ω).card := by
  apply Finset.card_biUnion_le.trans
  simp only [chosenLinePoints_card,Finset.sum_const,nsmul_eq_mul, Nat.cast_id]
  exact le_of_eq (Nat.mul_comm _ _)

def exceptionalPoints (S : Finset V) (ω : S → Projectivization K V) (T : ℕ) : Finset V :=
  Finset.univ.filter (fun z => pointDegree S ω z < T) ∪ deletedPoints S ω

theorem exceptionalPoints_card_le (S : Finset V) (ω : S → Projectivization K V) (T : ℕ) :
    (exceptionalPoints S ω T).card ≤
      (Finset.univ.filter (fun z => pointDegree S ω z < T)).card +
        Fintype.card K * (deletedMarks S ω).card :=
  (Finset.card_union_le _ _).trans (Nat.add_le_add_left (deletedPoints_card_le S ω) _)

def retainedIncidence (S : Finset V) (ω : S → Projectivization K V) (z : V) : Finset (Retained S ω) :=
  Finset.univ.filter (fun a => PuncturedIncidence a.val.val z (ω a.val))

theorem incidence_not_deleted (S : Finset V) (ω : S → Projectivization K V) (z : V)
    (hz : z ∉ deletedPoints S ω) (a : S) (ha : PuncturedIncidence a.val z (ω a)) :
    a ∉ deletedMarks S ω := by
  intro hdel
  apply hz
  exact Finset.mem_biUnion.mpr ⟨a,hdel,(mem_chosenLinePoints a.val z (ω a)).mpr ha.2⟩

/-- Outside the discarded geometric lines, no incidence is changed by alteration. -/
theorem retainedIncidence_card (S : Finset V) (ω : S → Projectivization K V) (z : V)
    (hz : z ∉ deletedPoints S ω) : (retainedIncidence S ω z).card = pointDegree S ω z := by
  let e : {a : Retained S ω // PuncturedIncidence a.val.val z (ω a.val)} ≃
      {a : S // PuncturedIncidence a.val z (ω a)} :=
    {toFun := fun a => ⟨a.val.val,a.property⟩
     invFun := fun a => ⟨⟨a.val,incidence_not_deleted S ω z hz a.val a.property⟩,a.property⟩
     left_inv := fun a => rfl
     right_inv := fun a => rfl}
  have h := Fintype.card_congr e
  simpa only [Fintype.card_subtype,pointDegree,retainedIncidence] using h

/-- The exact degree threshold needed for the two-block partition. -/
theorem retainedIncidence_card_ge (S : Finset V) (ω : S → Projectivization K V) (T : ℕ)
    (z : V) (hz : z ∉ exceptionalPoints S ω T) : T ≤ (retainedIncidence S ω z).card := by
  have hz' := not_or.mp ((Finset.mem_union).not.mp hz)
  rw [retainedIncidence_card S ω z hz'.2]
  have hh := hz'.1
  simpa only [Finset.mem_filter,Finset.mem_univ,true_and,not_lt] using hh

theorem retained_card (S : Finset V) (ω : S → Projectivization K V) :
    Fintype.card (Retained S ω) = S.card - (deletedMarks S ω).card := by
  change Fintype.card {a : S // ¬ a ∈ deletedMarks S ω} = _
  rw [Fintype.card_subtype_compl]
  simp
end Exceptional

section AlterationMean
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Fintype K] [Fintype V] [Nontrivial V] [Fintype (Projectivization K V)]

/-- A uniform expectation bound for all removed labels. -/
theorem expect_deletedMarks_le (S : Finset V) (q : ℝ)
    (hcycle : ∀ s ∈ Finset.Icc 2 6,
      (Fintype.card V : ℝ)^s * (Fintype.card K : ℝ)^s *
        (1 / Fintype.card (Projectivization K V) : ℝ)^s ≤ q^12) :
    (𝔼 ω : S → Projectivization K V, ((deletedMarks S ω).card : ℝ)) ≤ 30*q^12 := by
  have hpoint (ω : S → Projectivization K V) : ((deletedMarks S ω).card : ℝ) ≤
      6 * ∑ s ∈ Finset.Icc 2 6, ((badCycles S (finRotate s) ω).card : ℝ) := by
    exact_mod_cast deletedMarks_card_le S ω
  calc
    _ ≤ 𝔼 ω : S → Projectivization K V,
        6 * ∑ s ∈ Finset.Icc 2 6, ((badCycles S (finRotate s) ω).card : ℝ) :=
      Finset.expect_le_expect (fun ω _ => hpoint ω)
    _ = 6 * ∑ s ∈ Finset.Icc 2 6, 𝔼 ω : S → Projectivization K V,
        ((badCycles S (finRotate s) ω).card : ℝ) := by
      rw [← Finset.mul_expect, Finset.expect_sum_comm]
    _ ≤ 6 * ∑ _s ∈ Finset.Icc 2 6, q^12 := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply Finset.sum_le_sum
      intro s hs
      have hh := expect_badCycles_le (K := K) S (finRotate s)
      simp only [Fintype.card_fin] at hh
      exact hh.trans (hcycle s hs)
    _ = 30*q^12 := by norm_num [Finset.sum_const]; ring

/-- One finite averaging step obtains simultaneously the strict rank budget,
the degree bound, and the cycle-free alteration; no asymptotic or external
probabilistic result is being assumed. -/
theorem exists_alteration_budget (S : Finset V) (r T : ℕ) (μ B : ℝ)
    (hμ : 0 < μ) (hT : 2 * (T : ℝ) ≤ μ)
    (hlower : ∀ z : V, μ ≤ pointMean (K := K) S z)
    (hdel : (𝔼 ω : S → Projectivization K V, ((deletedMarks S ω).card : ℝ)) ≤ B)
    (hbudget : 8 * (Fintype.card V : ℝ) + 16*r*(Fintype.card V : ℝ)/μ +
        r*(4*(Fintype.card K : ℝ)+1)*B < (S.card : ℝ)*r) :
    ∃ ω : S → Projectivization K V,
      4 * (2 * Fintype.card V + r * (exceptionalPoints S ω T).card) <
        Fintype.card (Retained S ω) * r := by
  let cost : (S → Projectivization K V) → ℝ := fun ω =>
    4*r*((Finset.univ.filter (fun z : V => pointDegree S ω z < T)).card : ℝ) +
    r*(4*(Fintype.card K : ℝ)+1)*((deletedMarks S ω).card : ℝ)
  have hexp : (𝔼 ω, cost ω) ≤ 16*r*(Fintype.card V : ℝ)/μ +
      r*(4*(Fintype.card K : ℝ)+1)*B := by
    simp only [cost, Finset.expect_add_distrib, ← Finset.mul_expect]
    have hlow := expect_lowDegree_le (K := K) S T μ hμ hT hlower
    have h₁ := mul_le_mul_of_nonneg_left hlow (show 0 ≤ 4*(r : ℝ) by positivity)
    have h₂ := mul_le_mul_of_nonneg_left hdel
      (show 0 ≤ (r : ℝ)*(4*(Fintype.card K : ℝ)+1) by positivity)
    convert add_le_add h₁ h₂ using 2; first | rfl | ring
  obtain ⟨ω,hω⟩ := exists_of_expect_lt cost ((S.card : ℝ)*r - 8*Fintype.card V)
    (hexp.trans_lt (by linarith))
  refine ⟨ω,?_⟩
  have hE := exceptionalPoints_card_le S ω T
  have hD : (deletedMarks S ω).card ≤ S.card :=
    (Finset.card_le_univ _).trans_eq (Fintype.card_coe _)
  have hN := retained_card S ω
  have hN' : (Fintype.card (Retained S ω) : ℝ) = S.card - (deletedMarks S ω).card := by
    rw [hN, Nat.cast_sub hD]
  have hE' : ((exceptionalPoints S ω T).card : ℝ) ≤
      (Finset.univ.filter (fun z : V => pointDegree S ω z < T)).card +
      (Fintype.card K : ℝ) * (deletedMarks S ω).card := by exact_mod_cast hE
  have hEm := mul_le_mul_of_nonneg_left hE' (show 0 ≤ 4*(r : ℝ) by positivity)
  have hh : 4 * (2 * (Fintype.card V : ℝ) + r*(exceptionalPoints S ω T).card) <
      (Fintype.card (Retained S ω) : ℝ) * r := by
    dsimp [cost] at hω
    rw [hN']
    nlinarith
  exact_mod_cast hh
end AlterationMean

/-- The direction-count bounds used in dimension twenty. -/
theorem geom_sum_twenty_bounds {q : ℝ} (hq : 2 ≤ q) :
    q^19 ≤ ∑ i ∈ Finset.range 20, q^i ∧
      ∑ i ∈ Finset.range 20, q^i ≤ 2*q^19 := by
  have hq0 : 0 < q := by linarith
  constructor
  · exact Finset.single_le_sum (fun i _ => pow_nonneg hq0.le i) (by norm_num)
  · have hg := geom_sum_mul q 20
    have hp : q^20 = q^19*q := by ring
    have hh : 2*q^19*(q-1) ≥ q^20-1 := by
      rw [hp]
      nlinarith [mul_nonneg (pow_nonneg hq0.le 19) (show 0 ≤ q-2 by linarith)]
    exact (mul_le_mul_iff_left₀ (show 0 < q-1 by linarith)).mp (by nlinarith [hg])

/-- A concrete bound for every short-cycle contribution. -/
theorem cycle_numeric_bound {q J : ℝ} (hq : 1 ≤ q) (hJ : q^19 ≤ J)
    {s : ℕ} (hs : s ≤ 6) : (q^20)^s * q^s * (1/J)^s ≤ q^12 := by
  have hq0 : 0 < q := by linarith
  have hJ0 : 0 < J := (pow_pos hq0 19).trans_le hJ
  have hf : q^20 * q / J ≤ q^2 := by
    apply (div_le_iff₀ hJ0).mpr
    have hj := mul_le_mul_of_nonneg_left hJ (sq_nonneg q)
    convert hj using 1; ring
  calc
    _ = (q^20*q/J)^s := by simp only [div_pow, mul_pow, one_pow]; ring
    _ ≤ (q^2)^s := pow_le_pow_left₀ (by positivity) hf s
    _ = q^(2*s) := by rw [pow_mul]
    _ ≤ q^12 := pow_le_pow_right₀ hq (by omega)

theorem incidence_numeric_budget {q d r M : ℝ} (hd : 1 ≤ d) (hr : r = 200*d)
    (hq : 1000*d*r^2 ≤ q) (hM : q^20 ≤ d*M) :
    0 < q/(4*d) ∧ 8*r^2 ≤ q/(4*d) ∧
      8*q^20 + 16*r*q^20/(q/(4*d)) + r*(4*q+1)*(30*q^12) < M*r := by
  have hd0 : 0 < d := by linarith
  have hr1 : 1 ≤ r := by rw [hr]; linarith
  have hr0 : 0 < r := by linarith
  have hrr : r ≤ r^2 := by nlinarith
  have hq128 : 128*r*d ≤ q := by
    calc
      _ ≤ 1000*d*r^2 := by nlinarith [mul_le_mul_of_nonneg_left hrr hd0.le]
      _ ≤ q := hq
  have hq300 : 300*r ≤ q := by
    have h₁ : 300*r ≤ 1000*d*r := by nlinarith
    exact h₁.trans ((mul_le_mul_of_nonneg_left hrr (by positivity : 0 ≤ 1000*d)).trans hq)
  have hq1 : 1 ≤ q := by linarith
  have hq0 : 0 < q := by linarith
  have hdp : 0 < 4*d := by positivity
  refine ⟨by positivity, (le_div_iff₀ hdp).mpr ?_, ?_⟩
  · nlinarith [mul_nonneg hd0.le (sq_nonneg r)]
  · have hfirst_eq : 16*r*q^20/(q/(4*d)) = 64*r*d*q^19 := by
      field_simp
      ring
    have hfirst : 2*(16*r*q^20/(q/(4*d))) ≤ q^20 := by
      rw [hfirst_eq]
      have h := mul_le_mul_of_nonneg_right hq128 (pow_nonneg hq0.le 19)
      nlinarith only [h]
    have hq7 : q ≤ q^7 := by simpa using pow_le_pow_right₀ hq1 (show 1 ≤ 7 by norm_num)
    have hsecond : 2*(r*(4*q+1)*(30*q^12)) ≤ q^20 := by
      calc
        _ ≤ 300*r*q^13 := by
          have hh := mul_nonneg (show 0 ≤ 60*r*q^12 by positivity) (show 0 ≤ q-1 by linarith)
          nlinarith only [hh]
        _ ≤ q^7*q^13 := by gcongr; exact hq300.trans hq7
        _ = q^20 := by ring
    have hbig : 200*q^20 ≤ M*r := by
      rw [hr]
      nlinarith [hM]
    have hpos : 0 < q^20 := pow_pos hq0 20
    linarith

/-- The grid is large enough uniformly in the prime. -/
theorem floor_grid_lower {q : ℕ} (hq : 200 ≤ q) :
    (q : ℝ)^20 ≤ (200 : ℝ)^20 * ((q/100 : ℕ) : ℝ)^20 := by
  have hh : q ≤ 200*(q/100) := by omega
  have hh' : (q : ℝ) ≤ 200*((q/100 : ℕ) : ℝ) := by exact_mod_cast hh
  have h := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ q) hh' 20
  simpa only [mul_pow] using h

section DimensionTwenty
variable (q : ℕ) [Fact q.Prime]

def gridMarks (S : Finset (ZMod q)) : Finset (Fin 20 → ZMod q) :=
  Fintype.piFinset (fun _ => S)

omit [Fact q.Prime] in
theorem gridMarks_card (S : Finset (ZMod q)) : (gridMarks q S).card = S.card^20 := by
  simp [gridMarks, Fintype.card_piFinset]

theorem directions_twenty_card [Fintype (Projectivization (ZMod q) (Fin 20 → ZMod q))] :
    Fintype.card (Projectivization (ZMod q) (Fin 20 → ZMod q)) =
      ∑ i ∈ Finset.range 20, q^i := by
  simpa only [Nat.card_eq_fintype_card,ZMod.card] using
    Projectivization.card_of_finrank (ZMod q) (Fin 20 → ZMod q)
      (Module.finrank_fin_fun (ZMod q))

variable [Fintype (Projectivization (ZMod q) (Fin 20 → ZMod q))]

theorem mean_grid_lower (hq : 200 ≤ q) (S : Finset (ZMod q)) (hS : S.card = q/100)
    (z : Fin 20 → ZMod q) :
    (q : ℝ)/(4*(200:ℝ)^20) ≤ pointMean (K := ZMod q) (gridMarks q S) z := by
  classical
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast (show 2 ≤ q by omega)
  have hJ := geom_sum_twenty_bounds hq2
  have hJcast : (Fintype.card (Projectivization (ZMod q) (Fin 20 → ZMod q)) : ℝ) =
      ∑ i ∈ Finset.range 20, (q : ℝ)^i := by
    rw [directions_twenty_card]
    push_cast
    rfl
  rw [← hJcast] at hJ
  have hJpos : (0 : ℝ) < Fintype.card (Projectivization (ZMod q) (Fin 20 → ZMod q)) := by
    have hpow : (0 : ℝ) < (q:ℝ)^19 := by positivity
    exact hpow.trans_le hJ.1
  have hM : (q : ℝ)^20 ≤ (200:ℝ)^20 * (gridMarks q S).card := by
    rw [gridMarks_card,hS,Nat.cast_pow]
    exact floor_grid_lower hq
  have hM2 : 2 ≤ (gridMarks q S).card := by
    rw [gridMarks_card,hS]
    exact (show 2 ≤ q/100 by omega).trans (Nat.le_pow (by norm_num))
  have he : ((gridMarks q S).card : ℝ) ≤ 2*((gridMarks q S).erase z).card := by
    by_cases hz : z ∈ gridMarks q S
    · rw [Finset.card_erase_of_mem hz, Nat.cast_sub (by omega), Nat.cast_one]
      have hh : (2 : ℝ) ≤ (gridMarks q S).card := by exact_mod_cast hM2
      linarith
    · rw [Finset.erase_eq_of_notMem hz]
      have hh : (0 : ℝ) ≤ (gridMarks q S).card := by positivity
      linarith
  rw [pointMean_formula]
  apply (div_le_div_iff₀ (by positivity : (0:ℝ) < 4*(200:ℝ)^20) hJpos).mpr
  have h₁ := mul_le_mul_of_nonneg_left hJ.2 (show (0:ℝ) ≤ q by positivity)
  have h₂ := mul_le_mul_of_nonneg_left he (show (0:ℝ) ≤ (200:ℝ)^20 by positivity)
  calc
    _ ≤ (q : ℝ)*(2*(q : ℝ)^19) := h₁
    _ = 2*(q : ℝ)^20 := by ring
    _ ≤ 2*((200:ℝ)^20*(gridMarks q S).card) := mul_le_mul_of_nonneg_left hM (by norm_num)
    _ ≤ 2*((200:ℝ)^20*(2*((gridMarks q S).erase z).card)) :=
      mul_le_mul_of_nonneg_left h₂ (by norm_num)
    _ = _ := by ring_nf; congr 3; ext i; simp

/-- For a sufficiently large fixed prime, the alteration really attains the
strict finite rank budget. Every subsequent quotient uses this same prime. -/
theorem large_prime_grid_outcome (r : ℕ) (hr : r = 200*200^20)
    (hq200 : 200 ≤ q) (hq : 1000*200^20*r^2 ≤ q)
    (S : Finset (ZMod q)) (hS : S.card = q/100) :
    ∃ ω : gridMarks q S → Projectivization (ZMod q) (Fin 20 → ZMod q),
      4 * (2 * Fintype.card (Fin 20 → ZMod q) +
        r * (exceptionalPoints (gridMarks q S) ω (4*r^2)).card) <
      Fintype.card (Retained (gridMarks q S) ω) * r := by
  have hM : (q : ℝ)^20 ≤ (200:ℝ)^20 * (gridMarks q S).card := by
    rw [gridMarks_card,hS,Nat.cast_pow]
    exact floor_grid_lower hq200
  have hr' : (r : ℝ) = 200*(200:ℝ)^20 := by exact_mod_cast hr
  have hq' : 1000*(200:ℝ)^20*(r:ℝ)^2 ≤ q := by exact_mod_cast hq
  have hn := incidence_numeric_budget (by norm_num : (1:ℝ) ≤ (200:ℝ)^20) hr' hq' hM
  have hJ : (q : ℝ)^19 ≤ Fintype.card (Projectivization (ZMod q) (Fin 20 → ZMod q)) := by
    rw [directions_twenty_card]
    push_cast
    exact (geom_sum_twenty_bounds (by exact_mod_cast (show 2 ≤ q by omega))).1
  have hcycle := expect_deletedMarks_le (K := ZMod q) (gridMarks q S) (q : ℝ) (by
    intro s hs
    simp only [Fintype.card_fun, Fintype.card_fin, ZMod.card, Nat.cast_pow]
    exact cycle_numeric_bound (by exact_mod_cast (show 1 ≤ q by omega)) hJ (Finset.mem_Icc.mp hs).2)
  apply exists_alteration_budget (gridMarks q S) r (4*r^2) ((q:ℝ)/(4*(200:ℝ)^20))
    (30*(q:ℝ)^12) hn.1
  · simp only [Nat.cast_mul,Nat.cast_ofNat,Nat.cast_pow]
    nlinarith only [hn.2.1]
  · exact mean_grid_lower q hq200 S hS
  · exact hcycle
  · simpa only [Fintype.card_fun,Fintype.card_fin,ZMod.card,Nat.cast_pow] using hn.2.2
end DimensionTwenty

/-- Exact finite data fixed once for all before any finite quotient is chosen.
No geometric or group-theoretic conclusion is part of these data. -/
structure MarkedLineData (q r : ℕ) [Fact q.Prime] where
  scalarGrid : Finset (ZMod q)
  grid_card : scalarGrid.card = q/100
  Label : Type
  [labelFintype : Fintype Label]
  mark : Label → Fin 20 → ZMod q
  direction : Label → Projectivization (ZMod q) (Fin 20 → ZMod q)
  marks_mem : ∀ i t, mark i t ∈ scalarGrid
  marks_injective : Function.Injective mark
  exceptional : Finset (Fin 20 → ZMod q)
  degree : ∀ z, z ∉ exceptional → 4*r^2 ≤
    (Finset.univ.filter (fun i => PuncturedIncidence (mark i) z (direction i))).card
  budget : 4*(2*q^20+r*exceptional.card) < Fintype.card Label*r
  girth : ∀ a (w : (relationGraph (fun z i =>
    PuncturedIncidence (mark i) z (direction i))).Walk a a), w.IsCycle → 12 < w.length

attribute [instance] MarkedLineData.labelFintype

theorem exists_markedLineData :
    ∃ (q r : ℕ) (hq : q.Prime), let _ : Fact q.Prime := ⟨hq⟩
      0 < r ∧ r < q ∧ 100*100^20 ≤ r ∧ Nonempty (MarkedLineData q r) := by
  classical
  let r : ℕ := 200*200^20
  obtain ⟨q,hq,hprime⟩ := Nat.exists_infinite_primes (1000*200^20*r^2+400)
  let : Fact q.Prime := ⟨hprime⟩
  let : Fintype (Projectivization (ZMod q) (Fin 20 → ZMod q)) := Fintype.ofFinite _
  have hq200 : 200 ≤ q := by omega
  have hqbig : 1000*200^20*r^2 ≤ q := by omega
  have hr : 0 < r := by norm_num [r]
  have hrq : r < q := by
    have hh : r < 1000*200^20*r^2+400 := by norm_num [r]
    exact hh.trans_le hq
  have hrc : 100*100^20 ≤ r := by norm_num [r]
  obtain ⟨S,_,hS⟩ := Finset.exists_subset_card_eq
    (s := (Finset.univ : Finset (ZMod q))) (n := q/100) (by
      simpa only [Finset.card_univ,ZMod.card] using Nat.div_le_self q 100)
  obtain ⟨ω,hω⟩ := large_prime_grid_outcome q r rfl hq200 hqbig S hS
  refine ⟨q,r,hprime,hr,hrq,hrc,⟨?_⟩⟩
  exact
    { scalarGrid := S
      grid_card := hS
      Label := Retained (gridMarks q S) ω
      mark := fun i => i.val.val
      direction := fun i => ω i.val
      marks_mem := fun i => Fintype.mem_piFinset.mp i.val.property
      marks_injective := fun _ _ h => Subtype.ext (Subtype.ext h)
      exceptional := exceptionalPoints (gridMarks q S) ω (4*r^2)
      degree := retainedIncidence_card_ge (gridMarks q S) ω (4*r^2)
      budget := by simpa only [Fintype.card_fun,Fintype.card_fin,ZMod.card] using hω
      girth := retained_girth (gridMarks q S) ω }

namespace MarkedLineData
variable {q r : ℕ} [Fact q.Prime] (d : MarkedLineData q r)

/-- The marking grid gives an a priori upper bound on the number of labels. -/
theorem card_labels_le : Fintype.card d.Label ≤ q^20 := by
  simpa only [Fintype.card_fun,Fintype.card_fin,ZMod.card] using
    Fintype.card_le_of_injective d.mark d.marks_injective

theorem exists_regular : ∃ z, z ∉ d.exceptional := by
  classical
  by_contra! h
  have hE : d.exceptional = Finset.univ := Finset.eq_univ_of_forall h
  have hc : d.exceptional.card = q^20 := by simp only [hE,Finset.card_univ,
      Fintype.card_fun,Fintype.card_fin,ZMod.card]
  have hd := d.budget
  rw [hc] at hd
  have hm := Nat.mul_le_mul_right r d.card_labels_le
  rw [Nat.mul_comm (q^20) r] at hm
  omega

theorem degree_cutoff (hq : 200 ≤ q) : 2*(20*(d.scalarGrid.card-1)) < q-1 := by
  rw [d.grid_card]
  omega
end MarkedLineData

end
end Release075

end OAI
