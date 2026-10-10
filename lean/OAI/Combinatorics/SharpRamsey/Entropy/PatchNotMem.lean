import Mathlib
import OAI.Combinatorics.SharpRamsey.Entropy.ShiftKernelSum

namespace OAI

/-! High moments, finite-field subspaces, and incidence bounds. -/

section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
namespace SharpRamseyFive.ResidualElimination
open scoped BigOperators
open Classical
variable {V H : Type} [Fintype V] [DecidableEq V] [Fintype H] [DecidableEq H]
omit [Fintype V] [Fintype H] [DecidableEq H] in
lemma patch_notMem (g : V → H) (T : Finset V) (x : T → H) (u : V) (hu : u ∉ T) :
    patch g T x u = g u := by simp [patch, hu]
omit [Fintype V] [Fintype H] [DecidableEq H] in

lemma agrees_sdiff_patch (E T : Finset V) (hT : T ⊆ E) (g f : V → H) (x : T → H) :
    Agrees (E \ T) (patch g T x) f ↔ Agrees E g f ∧ x = fun u : T => f u := by
  constructor
  · intro h
    constructor
    · intro u hu
      have hnu : u ∉ T := fun hh => hu (hT hh)
      simpa only [patch_notMem g T x u hnu] using h u (by simp [hu])
    · funext u
      have hu := h u (by simp)
      simpa only [patch_mem] using hu.symm
  · rintro ⟨h,rfl⟩ u hu
    by_cases hnu : u ∈ T
    · simp [patch, hnu]
    · rw [patch_notMem g T _ u hnu]
      exact h u (by simpa [hnu] using hu)

lemma completionSum_split (E T : Finset V) (hT : T ⊆ E) (g : V → H)
    (F : (V → H) → ℝ) :
    completionSum E g F = ∑ x : T → H, completionSum (E \ T) (patch g T x) F := by
  unfold completionSum
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro f _
  simp only [agrees_sdiff_patch E T hT]
  by_cases hf : Agrees E g f <;> simp [hf]

theorem weighted_block_exposure (E T : Finset V) (hT : T ⊆ E) (g : V → H)
    (w : (T → H) → ℝ) (hw : ∀ x, 0 ≤ w x) (F : (V → H) → ℝ)
    (C : ℝ) (hF : ∀ g, completionSum (E \ T) g F ≤ C) :
    completionSum E g (fun f => w (fun u : T => f u) * F f) ≤
      (∑ x : T → H, w x) * C := by
  rw [completionSum_split E T hT, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro x _
  calc
    _ = completionSum (E \ T) (patch g T x) (fun f => w x * F f) := by
      apply completionSum_congr
      intro f hf
      have hx := (agrees_sdiff_patch E T hT g f x).mp hf
      rw [← hx.2]
    _ = w x * completionSum (E \ T) (patch g T x) F := completionSum_mul ..
    _ ≤ _ := mul_le_mul_of_nonneg_left (hF _) (hw x)

theorem independent_positions_exposure (E T : Finset V) (hT : T ⊆ E) (g : V → H)
    (w : V → H → ℝ) (hw : ∀ u h, 0 ≤ w u h) (F : (V → H) → ℝ)
    (C : ℝ) (hF : ∀ g, completionSum (E \ T) g F ≤ C) :
    completionSum E g (fun f => (∏ u ∈ T, w u (f u)) * F f) ≤
      (∏ u ∈ T, ∑ h : H, w u h) * C := by
  let W : (T → H) → ℝ := fun x => ∏ u : T, w u (x u)
  have hW : ∀ x, 0 ≤ W x := by
    intro x
    exact Finset.prod_nonneg (fun u _ => hw _ _)
  have he (f : V → H) : (∏ u ∈ T, w u (f u)) = W (fun u : T => f u) := by
    exact (Finset.prod_coe_sort T (fun u => w u (f u))).symm
  simp_rw [he]
  apply (weighted_block_exposure E T hT g W hW F C hF).trans_eq
  have hs : (∑ x : T → H, W x) = ∏ u ∈ T, ∑ h : H, w u h := by
    rw [show (∑ x : T → H, W x) = ∏ u : T, ∑ h : H, w u h from
      (Fintype.prod_sum (fun u : T => w u)).symm]
    exact Finset.prod_coe_sort T (fun u => ∑ h : H, w u h)
  rw [hs]

end SharpRamseyFive.ResidualElimination

namespace SharpRamseyFive.ResidualElimination
open scoped BigOperators
open Classical
variable {V H : Type} [Fintype V] [DecidableEq V] [Fintype H] [DecidableEq H]

omit [Fintype V] in
lemma powerset_sdiff (E U : Finset V) :
    (E \ U).powerset = E.powerset.filter (fun S => Disjoint S U) := by
  ext S
  simp only [Finset.mem_powerset, Finset.mem_filter]
  constructor
  · intro h
    refine ⟨h.trans Finset.sdiff_subset, Finset.disjoint_left.mpr ?_⟩
    intro u hu hU
    exact (Finset.mem_sdiff.mp (h hu)).2 hU
  · rintro ⟨h,hD⟩ u hu
    exact Finset.mem_sdiff.mpr ⟨h hu, fun hU => Finset.disjoint_left.mp hD hu hU⟩
omit [Fintype V] in

lemma sum_disjoint_swap (E : Finset V) (F : Finset V → Finset V → ℝ) :
    (∑ U ∈ E.powerset, ∑ S ∈ (E \ U).powerset, F U S) =
      ∑ S ∈ E.powerset, ∑ U ∈ (E \ S).powerset, F U S := by
  simp_rw [powerset_sdiff, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro S hS
  apply Finset.sum_congr rfl
  intro U hU
  simp only [disjoint_comm]

noncomputable def badExpansion (a : V → (V → H) → ℝ)
    (B : Finset V → (V → H) → ℝ) (E : Finset V) (f : V → H) : ℝ :=
  ∑ U ∈ E.powerset, (∏ u ∈ E \ U, a u f) * B U f

omit [Fintype V] [Fintype H] [DecidableEq H] in
lemma badExpansion_nonneg (a : V → (V → H) → ℝ)
    (B : Finset V → (V → H) → ℝ) (ha : ∀ u f, 0 ≤ a u f)
    (hB : ∀ E f, 0 ≤ B E f) (E : Finset V) (f : V → H) :
    0 ≤ badExpansion a B E f := by
  apply Finset.sum_nonneg
  intro U hU
  exact mul_nonneg (Finset.prod_nonneg (fun u _ => ha u f)) (hB U f)

omit [Fintype H] [DecidableEq H] in
omit [Fintype V] in
lemma badExpansion_add (a d : V → (V → H) → ℝ)
    (B : Finset V → (V → H) → ℝ) (E : Finset V) (f : V → H) :
    badExpansion (fun u f => d u f + a u f) B E f =
      ∑ S ∈ E.powerset, (∏ u ∈ S, d u f) * badExpansion a B (E \ S) f := by
  unfold badExpansion
  simp_rw [Finset.prod_add, Finset.sum_mul]
  rw [sum_disjoint_swap]
  apply Finset.sum_congr rfl
  intro S hS
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro U hU
  have he : (E \ U) \ S = (E \ S) \ U := sdiff_sdiff_comm
  rw [he, mul_assoc]
omit [DecidableEq H] in

lemma badExpansion_sum_le (a : V → (V → H) → ℝ)
    (B : Finset V → (V → H) → ℝ) (E : Finset V) (g : V → H)
    (M : ℝ) (_hM : 0 ≤ M)
    (hterm : ∀ S, S ⊆ E → completionSum E g (term a B E S) ≤ M ^ E.card) :
    completionSum E g (badExpansion a B E) ≤ (2 * M) ^ E.card := by
  rw [show badExpansion a B E = (fun f => ∑ U ∈ E.powerset,
      (∏ u ∈ E \ U, a u f) * B U f) from rfl, completionSum_sum]
  calc
    _ ≤ ∑ _U ∈ E.powerset, M ^ E.card := by
      apply Finset.sum_le_sum
      intro U hU
      have hU : U ⊆ E := Finset.mem_powerset.mp hU
      have he : E \ (E \ U) = U := Finset.sdiff_sdiff_eq_self hU
      have ht := hterm (E \ U) Finset.sdiff_subset
      change completionSum E g (fun f => (∏ u ∈ E \ U, a u f) *
        B (E \ (E \ U)) f) ≤ M ^ E.card at ht
      simpa only [he] using ht
    _ = _ := by simp [mul_pow]

theorem all_singleton_enumeration
    (a : V → (V → H) → ℝ) (d : V → H → ℝ) (B : Finset V → (V → H) → ℝ)
    (W : H → H → ℝ) (C D : ℝ) (hC : 0 ≤ C) (_hD : 0 ≤ D)
    (ha : ∀ u f, a u f ∈ Set.Icc (0 : ℝ) 1)
    (hd : ∀ u x, 0 ≤ d u x) (hsum : ∀ u, (∑ x : H, d u x) ≤ D)
    (hW : ∀ x y, 0 ≤ W x y) (hB : ∀ A f, 0 ≤ B A f)
    (hmono : ∀ A A', A' ⊆ A → ∀ f, B A f ≤ B A' f)
    (hshift : ∀ u f, a u f ≤ ∑ v ∈ Finset.univ.erase u, W (f u) (f v))
    (hrow : ∀ y, (∑ x : H, W x y) ≤ C)
    (hpair : (∑ x : H, ∑ y : H, W x y) ≤ C ^ 2)
    (hbad : ∀ A g, completionSum A g (B A) ≤ C ^ A.card)
    (E : Finset V) (g : V → H) :
    completionSum E g (badExpansion (fun u f => d u (f u) + a u f) B E) ≤
      (D + 2 * ((Fintype.card V + 1 : ℝ) * C)) ^ E.card := by
  let M : ℝ := (Fintype.card V + 1) * C
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hbnd (A : Finset V) (g : V → H) :
      completionSum A g (badExpansion a B A) ≤ (2 * M) ^ A.card := by
    apply badExpansion_sum_le a B A g M hM
    intro S hS
    exact shift_bad_enumeration a B W C hC ha hW hB hmono hshift hrow hpair hbad A S hS g
  have he : badExpansion (fun u f => d u (f u) + a u f) B E =
      fun f => ∑ S ∈ E.powerset, (∏ u ∈ S, d u (f u)) * badExpansion a B (E \ S) f := by
    funext f
    exact badExpansion_add a (fun u f => d u (f u)) B E f
  rw [he, completionSum_sum]
  calc
    _ ≤ ∑ S ∈ E.powerset, D ^ S.card * (2 * M) ^ (E \ S).card := by
      apply Finset.sum_le_sum
      intro S hS
      apply (independent_positions_exposure E S (Finset.mem_powerset.mp hS) g d hd
        (badExpansion a B (E \ S)) ((2 * M) ^ (E \ S).card) (hbnd (E \ S))).trans
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg (by positivity) _)
      calc
        (∏ u ∈ S, ∑ x : H, d u x) ≤ ∏ _u ∈ S, D :=
          Finset.prod_le_prod₀ (fun u _ => Finset.sum_nonneg (fun x _ => hd u x))
            (fun u _ => hsum u)
        _ = _ := Finset.prod_const _
    _ = (D + 2 * M) ^ E.card := by
      have := Finset.prod_add (fun _ : V => D) (fun _ => 2 * M) E
      simpa only [Finset.prod_const] using this.symm

end SharpRamseyFive.ResidualElimination

namespace SharpRamseyFive.SingletonEnumeration
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open SharpRamseyFive.PoissonScore SharpRamseyFive.TupleComponents
open SharpRamseyFive.Designations SharpRamseyFive.AmbientDesignations
open SharpRamseyFive.SelectionBridge SharpRamseyFive.WeightedPrograms
open SharpRamseyFive.ResidualElimination
open Classical
variable {D V H : Type} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype H] [DecidableEq H]

noncomputable def independentWeight (weight rate : D → ℝ≥0) (lines : H → Finset D)
    (R J : ℕ) (base : ℝ) (h : H) : ℝ :=
  |mass weight (lines h) - base| ^ (R / 2) +
    (if R < J then 0 else ∑ d ∈ lines h, ((R : ℝ) * (rate d : ℝ)) ^ J)

omit [Fintype D] [DecidableEq D] [Fintype H] [DecidableEq H] in
lemma independentWeight_nonneg (weight rate : D → ℝ≥0) (lines : H → Finset D)
    (R J : ℕ) (base : ℝ) (h : H) : 0 ≤ independentWeight weight rate lines R J base h := by
  unfold independentWeight
  split_ifs <;> positivity

theorem actual_all_singleton_enumeration (weight rate : D → ℝ≥0) (lines : H → Finset D)
    {p : ℕ} (hp : 0 < p) (hc : Fintype.card V ≤ p)
    (R : ℕ) (denom b mass C D₀ base : ℝ)
    (hd : 0 < denom) (hb : 1 ≤ b) (hm : 0 ≤ mass) (hC : 0 ≤ C) (hD : 0 ≤ D₀)
    (hmass : ∀ u, ∑ d ∈ lines u, (rate d : ℝ) ≤ mass)
    (K J h N₁ N₂ : ℕ) (hK : 2 ≤ K) (hh : 0 < h) (low : Bool)
    (hsize : h ≤ (R / 2 - if low then 0 else J) / (2 * K))
    (herr : (Fintype.card V : ℝ) * h * (19 / 20 : ℝ) ^ (h - 1) < 1 / 2)
    (hN₁ : ∀ d, (Finset.univ.filter (fun u => d ∈ lines u)).card ≤ N₁)
    (hN₂ : ∀ d e, d ≠ e →
      (Finset.univ.filter (fun u => d ∈ lines u ∧ e ∈ lines u)).card ≤ N₂)
    (hBC : denom * (1 + branchingBound (V := V) (B := Fin R)
      (fun z : H × V => lines z.1) rate denom b mass K
      (N₁ * Fintype.card V) (N₂ * Fintype.card V) low) ≤ C)
    (hrow : ∀ y, (∑ x : H, shiftKernel weight lines p K x y) ≤ C)
    (hpair : (∑ x : H, ∑ y : H, shiftKernel weight lines p K x y) ≤ C ^ 2)
    (hDsum : (∑ x : H, independentWeight weight rate lines R J base x) ≤ D₀)
    (E : Finset V) (g : V → H) :
    completionSum E g (badExpansion
      (fun u f => independentWeight weight rate lines R J base (f u) +
        alpha weight (lines ∘ f) (1 / (100 * p)) u ^ K)
      (fun A f => vertexBadMass weight rate (lines ∘ f) (1 / (100 * p)) R J A) E) ≤
      (D₀ + 2 * ((Fintype.card V + 1 : ℝ) * C)) ^ E.card := by
  apply all_singleton_enumeration
    (fun u f => alpha weight (lines ∘ f) (1 / (100 * p)) u ^ K)
    (fun _ x => independentWeight weight rate lines R J base x)
    (fun A f => vertexBadMass weight rate (lines ∘ f) (1 / (100 * p)) R J A)
    (shiftKernel weight lines p K) C D₀ hC hD
  · intro u f
    exact ⟨pow_nonneg (alpha_nonneg _ _ _ _) _,
      pow_le_one₀ (alpha_nonneg _ _ _ _) (by
        have := source_alpha_le weight (lines ∘ f) hp hc u
        linarith)⟩
  · exact fun _ x => independentWeight_nonneg weight rate lines R J base x
  · exact fun _ => hDsum
  · exact fun x y => (shiftKernel_range weight lines p K x y).1
  · exact fun A f => vertexBadMass_nonneg _ _ _ _ _ _ _
  · exact fun A A' hh f => vertexBadMass_antitone _ _ _ _ _ _ hh
  · exact fun u f => shift_le_kernel_sum weight lines hp hc (by omega) u f
  · exact hrow
  · exact hpair
  · intro A g
    apply (actual_bad_completion weight rate lines (1 / (100 * p)) R denom b mass
      hd hb hm hmass K J h N₁ N₂ hK hh low hsize herr hN₁ hN₂ A g).trans
    apply pow_le_pow_left₀ _ hBC
    apply mul_nonneg hd.le
    have hn := branchingBound_nonneg (V := V) (B := Fin R)
      (fun z : H × V => lines z.1) rate denom b mass hd.le (by linarith) hm K
      (N₁ * Fintype.card V) (N₂ * Fintype.card V) low
    linarith

end SharpRamseyFive.SingletonEnumeration

namespace SharpRamseyFive.SingletonEnumeration
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open SharpRamseyFive.PoissonScore SharpRamseyFive.TupleComponents
open SharpRamseyFive.Designations SharpRamseyFive.AmbientDesignations
open SharpRamseyFive.SelectionBridge SharpRamseyFive.WeightedPrograms
open SharpRamseyFive.ResidualElimination
open Classical
variable {D V H : Type} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype H] [DecidableEq H]

lemma inside_sum_le {C : Type} [Fintype C] [DecidableEq C]
    (label : D → Option C) (c : C) (S : Finset D) (F : D → ℝ) (hF : ∀ d, 0 ≤ F d) :
    (∑ d ∈ inside label c S, F d) ≤ ∑ d ∈ S, F d := by
  have hi : Function.Injective (Subtype.val : IntDir label c → D) := Subtype.val_injective
  rw [← Finset.sum_image (hi.injOn)]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro d hd
    rcases Finset.mem_image.mp hd with ⟨e,he,rfl⟩
    exact (Finset.mem_filter.mp he).2
  · exact fun d _ _ => hF d

omit [Fintype H] [DecidableEq H] in
lemma extraWeight_le_independent (weight : D → ℝ≥0) (lines : H → Finset D)
    (f : V → H) (t : ℝ) (R J K : ℕ) (L : ℝ≥0) (base : ℝ)
    (c : Components weight (lines ∘ f) t) :
    extraWeight weight (lines ∘ f) t R J K L base c ≤
      independentWeight weight (fun d => L * weight d) lines R J base
        (f (vertex weight (lines ∘ f) t c)) +
      alpha weight (lines ∘ f) t (vertex weight (lines ∘ f) t c) ^ K := by
  unfold extraWeight independentWeight delta
  have h := inside_sum_le (componentLabel weight (lines ∘ f) t) c
    ((lines ∘ f) (vertex weight (lines ∘ f) t c))
    (fun d => ((R : ℝ) * ((L * weight d : ℝ≥0) : ℝ)) ^ J) (fun _ => by positivity)
  dsimp only [Function.comp_def] at *
  split_ifs <;> linarith

omit [Fintype H] [DecidableEq H] in

theorem designation_sum_le_vertex (weight : D → ℝ≥0) (lines : H → Finset D)
    (f : V → H) (t : ℝ) (R J K : ℕ) (L : ℝ≥0) (base : ℝ) :
    let s := lines ∘ f
    let S := simpleSet weight s t
    let E := S.image (vertex weight s t)
    (∑ U ∈ S.powerset, (∏ c ∈ S \ U, extraWeight weight s t R J K L base c) *
      badMass (batchMeasure (fun i : Block (componentLabel weight s t) R none => L * weight i.1.2))
        (blockTrunc (componentLabel weight s t) R J none) (isBad weight s t R) U) ≤
      badExpansion
        (fun u f => independentWeight weight (fun d => L * weight d) lines R J base (f u) +
          alpha weight (lines ∘ f) t u ^ K)
        (fun A f => vertexBadMass weight (fun d => L * weight d) (lines ∘ f) t R J A) E f := by
  dsimp only
  unfold badExpansion
  rw [Finset.powerset_image, Finset.sum_image
    (Finset.image_injective (vertex_injective weight (lines ∘ f) t)).injOn]
  apply Finset.sum_le_sum
  intro U hU
  rw [← Finset.image_sdiff _ _ (vertex_injective weight (lines ∘ f) t),
    Finset.prod_image (vertex_injective weight (lines ∘ f) t).injOn,
    component_bad_mass_eq_vertex weight (fun d => L * weight d) (lines ∘ f) t R J U]
  apply mul_le_mul_of_nonneg_right _ (vertexBadMass_nonneg _ _ _ _ _ _ _)
  apply Finset.prod_le_prod₀
  · exact fun c _ => extraWeight_nonneg _ _ _ _ _ _ _ _ c
  · exact fun c _ => extraWeight_le_independent weight lines f t R J K L base c

end SharpRamseyFive.SingletonEnumeration

namespace SharpRamseyFive.ResidualElimination
open scoped BigOperators
open Classical
variable {V H C : Type} [Fintype V] [DecidableEq V] [Fintype H] [DecidableEq H]
  [DecidableEq C]

theorem disjoint_blocks_exposure (E : Finset V) (I : Finset C) (T : C → Finset V)
    (Win : (c : C) → (T c → H) → ℝ) (M : C → ℝ)
    (hw : ∀ c x, 0 ≤ Win c x) (hM : ∀ c, 0 ≤ M c)
    (hwithin : ∀ c ∈ I, T c ⊆ E)
    (hdisj : ∀ c ∈ I, ∀ d ∈ I, c ≠ d → Disjoint (T c) (T d))
    (hsum : ∀ c ∈ I, (∑ x : T c → H, Win c x) ≤ M c)
    (F : (V → H) → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hres : ∀ g, completionSum (E \ I.biUnion T) g F ≤ K) (g : V → H) :
    completionSum E g (fun f => (∏ c ∈ I, Win c (fun v => f v)) * F f) ≤
      (∏ c ∈ I, M c) * K := by
  induction I using Finset.induction generalizing E g with
  | empty => simpa using hres g
  | @insert c I hc ih =>
    have hwi : T c ⊆ E := hwithin c (Finset.mem_insert_self c I)
    have hrwithin : ∀ d ∈ I, T d ⊆ E \ T c := by
      intro d hd v hv
      refine Finset.mem_sdiff.mpr ⟨hwithin d (Finset.mem_insert_of_mem hd) hv, ?_⟩
      intro hvc
      exact Finset.disjoint_left.mp
        (hdisj d (Finset.mem_insert_of_mem hd) c (Finset.mem_insert_self _ _)
          (by intro he; subst d; exact hc hd)) hv hvc
    have he : (E \ T c) \ I.biUnion T = E \ (insert c I).biUnion T := by
      ext v
      simp only [Finset.mem_sdiff, Finset.biUnion_insert, Finset.mem_union]
      tauto
    have hr (g : V → H) :
        completionSum (E \ T c) g
          (fun f => (∏ d ∈ I, Win d (fun v => f v)) * F f) ≤ (∏ d ∈ I, M d) * K := by
      apply ih (E \ T c) hrwithin
        (fun d hd e he hne => hdisj d (Finset.mem_insert_of_mem hd)
          e (Finset.mem_insert_of_mem he) hne)
        (fun d hd => hsum d (Finset.mem_insert_of_mem hd))
      intro g
      rw [he]
      exact hres g
    simp_rw [Finset.prod_insert hc, mul_assoc]
    apply (weighted_block_exposure E (T c) hwi g (Win c) (hw c)
      (fun f => (∏ d ∈ I, Win d (fun v => f v)) * F f)
      ((∏ d ∈ I, M d) * K) hr).trans
    exact mul_le_mul_of_nonneg_right (hsum c (Finset.mem_insert_self _ _))
      (mul_nonneg (Finset.prod_nonneg (fun d _ => hM d)) hK)

end SharpRamseyFive.ResidualElimination

namespace SharpRamseyFive.ComponentPartition
open scoped BigOperators
open Classical
variable {V C : Type} [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C]

noncomputable def fiber (r : V → C) (c : C) : Finset V :=
  Finset.univ.filter (fun v => r v = c)
noncomputable def singles (r : V → C) : Finset V :=
  Finset.univ.filter (fun v => (fiber r (r v)).card = 1)
noncomputable def largeLabels (r : V → C) : Finset C :=
  Finset.univ.filter (fun c => 2 ≤ (fiber r c).card)

omit [DecidableEq V] [Fintype C] in
@[simp] lemma mem_fiber (r : V → C) (c : C) (v : V) : v ∈ fiber r c ↔ r v = c := by
  simp [fiber]
omit [DecidableEq V] [Fintype C] in
@[simp] lemma mem_singles (r : V → C) (v : V) :
    v ∈ singles r ↔ (fiber r (r v)).card = 1 := by simp [singles]
omit [DecidableEq V] in
@[simp] lemma mem_largeLabels (r : V → C) (c : C) :
    c ∈ largeLabels r ↔ 2 ≤ (fiber r c).card := by simp [largeLabels]
omit [DecidableEq V] [Fintype C] in

lemma self_mem_fiber (r : V → C) (v : V) : v ∈ fiber r (r v) := by simp
omit [DecidableEq V] [Fintype C] in
lemma fiber_card_pos (r : V → C) (v : V) : 0 < (fiber r (r v)).card :=
  Finset.card_pos.mpr ⟨v,self_mem_fiber r v⟩
omit [DecidableEq V] [Fintype C] in

lemma fiber_disjoint (r : V → C) {c d : C} (hne : c ≠ d) :
    Disjoint (fiber r c) (fiber r d) := by
  apply Finset.disjoint_left.mpr
  intro v hc hd
  exact hne ((mem_fiber r c v).mp hc |>.symm.trans ((mem_fiber r d v).mp hd))

lemma large_union (r : V → C) : (largeLabels r).biUnion (fiber r) = Finset.univ \ singles r := by
  ext v
  simp only [Finset.mem_biUnion, mem_largeLabels, mem_fiber, Finset.mem_sdiff,
    Finset.mem_univ, true_and, mem_singles]
  constructor
  · rintro ⟨c,hc,he⟩
    rw [he]
    omega
  · intro hv
    exact ⟨r v,by have := fiber_card_pos r v; omega,rfl⟩
end SharpRamseyFive.ComponentPartition
end

end OAI
