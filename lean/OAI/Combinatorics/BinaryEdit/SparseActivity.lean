import Mathlib

namespace OAI

/-!
# Sparse activity in a finite branching construction

Sparse/dense Fourier-mass estimates for `prop:finite-lower`.
-/

namespace TreeEdit.BinaryLower.TreeDistortion.FiniteMass

open scoped BigOperators
open Classical

/-- The number of active leaves in the full `m`-ary tree of height `h`.
A node is represented by its list of child indices, starting at the root. -/
noncomputable def activeLeaves {m : ℕ} (A : List (Fin m) → Prop) : ℕ → ℕ
  | 0 => if A [] then 1 else 0
  | h + 1 => ∑ i : Fin m, activeLeaves (fun p => A (i :: p)) h

/-- There is no active internal node with fewer than `b` active children. -/
def NoSparse {m : ℕ} (b : ℕ) (A : List (Fin m) → Prop) : ℕ → Prop
  | 0 => True
  | h + 1 =>
      (A [] → b ≤ (Finset.univ.filter (fun i : Fin m => A [i])).card) ∧
      ∀ i : Fin m, NoSparse b (fun p => A (i :: p)) h

theorem activeLeaves_lower {m b h : ℕ} {A : List (Fin m) → Prop}
    (hgood : NoSparse b A h) (hroot : A []) : b ^ h ≤ activeLeaves A h := by
  classical
  induction h generalizing A with
  | zero => simp [activeLeaves, hroot]
  | succ h ih =>
      have hchild := hgood.1 hroot
      have hterm : ∀ i : Fin m, (if A [i] then b ^ h else 0) ≤
          activeLeaves (fun p => A (i :: p)) h := by
        intro i
        split_ifs with hi
        · exact ih (hgood.2 i) hi
        · exact Nat.zero_le _
      calc
        b ^ (h + 1) = b * b ^ h := by rw [pow_succ, Nat.mul_comm]
        _ ≤ (Finset.univ.filter (fun i : Fin m => A [i])).card * b ^ h :=
          Nat.mul_le_mul_right _ hchild
        _ = ∑ i : Fin m, if A [i] then b ^ h else 0 := by
          rw [← Finset.sum_filter]
          simp
        _ ≤ ∑ i : Fin m, activeLeaves (fun p => A (i :: p)) h :=
          Finset.sum_le_sum (fun i _ => hterm i)
        _ = activeLeaves A (h + 1) := rfl

/-- A weighted version of the sparse/dense activity dichotomy.
The exceptional set may overlap the inactive set.  No disjointness assumptions
on the tests used to bound exceptional mass are required. -/
theorem weighted_active_bound {ι : Type*} [Fintype ι]
    (H w μ : ι → ℝ) (active exceptional : ι → Prop)
    (M ε K : ℝ) (hK : 0 < K)
    (hH : ∀ i, 0 ≤ H i) (hw : ∀ i, 0 ≤ w i)
    (hμ : ∀ i, μ i ≤ 4)
    (hzero : ∀ i, ¬ active i → μ i = 0)
    (hdense : ∀ i, active i → ¬ exceptional i → K ≤ w i)
    (hleaf : 2 * ∑ i, w i * H i ≤ M)
    (hexceptional : (∑ i, if exceptional i then H i else 0) ≤ ε) :
    (∑ i, μ i * H i) ≤ 4 * (ε + M / (2 * K)) := by
  classical
  have hpoint : ∀ i, μ i * H i ≤
      4 * ((if exceptional i then H i else 0) + w i * H i / K) := by
    intro i
    have hmass : 0 ≤ w i * H i / K :=
      div_nonneg (mul_nonneg (hw i) (hH i)) (le_of_lt hK)
    by_cases he : exceptional i
    · simp only [ite_eq_left he]
      have := mul_le_mul_of_nonneg_right (hμ i) (hH i)
      linarith
    · simp only [ite_eq_right he, zero_add]
      by_cases ha : active i
      · have hlarge : H i ≤ w i * H i / K := by
          apply (le_div_iff₀ hK).2
          nlinarith [hdense i ha he, hH i]
        have := mul_le_mul_of_nonneg_right (hμ i) (hH i)
        linarith
      · rw [hzero i ha, zero_mul]
        positivity
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hpoint i)
  have hsum' : (∑ i, μ i * H i) ≤
      4 * ((∑ i, if exceptional i then H i else 0) + (∑ i, w i * H i) / K) := by
    simpa only [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.sum_div] using hsum
  have hleaf' : (∑ i, w i * H i) / K ≤ M / (2 * K) := by
    apply (div_le_div_iff₀ hK (mul_pos (by norm_num) hK)).2
    nlinarith
  linarith


/-- A nonnegative detector that accumulates at least one unit on every bad
frequency bounds the total Fourier weight of those frequencies. -/
theorem weighted_detection_bound {ι σ : Type*} [Fintype ι] [Fintype σ]
    (H : ι → ℝ) (a : σ → ι → ℝ) (bad : ι → Prop)
    (hH : ∀ i, 0 ≤ H i) (ha : ∀ s i, 0 ≤ a s i)
    (hdetect : ∀ i, bad i → 1 ≤ ∑ s, a s i) :
    (∑ i, if bad i then H i else 0) ≤ ∑ s, ∑ i, a s i * H i := by
  classical
  have hpoint : ∀ i, (if bad i then H i else 0) ≤ ∑ s, a s i * H i := by
    intro i
    rw [← Finset.sum_mul]
    by_cases hi : bad i
    · simp only [ite_eq_left hi]
      simpa only [one_mul] using mul_le_mul_of_nonneg_right (hdetect i hi) (hH i)
    · simp only [ite_eq_right hi]
      exact mul_nonneg (Finset.sum_nonneg (fun s _ => ha s i)) (hH i)
  calc
    (∑ i, if bad i then H i else 0) ≤ ∑ i, ∑ s, a s i * H i :=
      Finset.sum_le_sum (fun i _ => hpoint i)
    _ = ∑ s, ∑ i, a s i * H i := Finset.sum_comm

/-- Union bound for nonnegative Fourier mass. Overlap between bad-node tests
can only increase the sum on the right. -/
theorem weighted_union_bound {ι ν : Type*} [Fintype ι] [Fintype ν]
    (H : ι → ℝ) (bad : ν → ι → Prop) (hH : ∀ i, 0 ≤ H i) :
    (∑ i, if ∃ v, bad v i then H i else 0) ≤
      ∑ v, ∑ i, if bad v i then H i else 0 := by
  classical
  have hpoint : ∀ i, (if ∃ v, bad v i then H i else 0) ≤
      ∑ v, if bad v i then H i else 0 := by
    intro i
    by_cases hi : ∃ v, bad v i
    · obtain ⟨v, hv⟩ := hi
      rw [ite_eq_left (show ∃ v, bad v i from ⟨v, hv⟩)]
      calc
        H i = (if bad v i then H i else 0) := by rw [ite_eq_left hv]
        _ ≤ ∑ w, if bad w i then H i else 0 :=
          Finset.single_le_sum (f := fun w => if bad w i then H i else 0) (fun w _ => by split_ifs; exact hH i; exact le_refl 0) (Finset.mem_univ v)
    · simp only [ite_eq_right hi]
      exact Finset.sum_nonneg (fun v _ => by split_ifs; exact hH i; exact le_refl 0)
  calc
    (∑ i, if ∃ v, bad v i then H i else 0) ≤
        ∑ i, ∑ v, if bad v i then H i else 0 :=
      Finset.sum_le_sum (fun i _ => hpoint i)
    _ = ∑ v, ∑ i, if bad v i then H i else 0 := Finset.sum_comm

/-- Combining detectors at all nodes gives the exceptional-character mass
estimate used before the sparse/dense dichotomy. -/
theorem exceptional_mass_of_detectors {ι ν σ : Type*}
    [Fintype ι] [Fintype ν] [Fintype σ]
    (H : ι → ℝ) (a : ν → σ → ι → ℝ) (bad : ν → ι → Prop)
    (B : ν → ℝ) (hH : ∀ i, 0 ≤ H i)
    (ha : ∀ v s i, 0 ≤ a v s i)
    (hdetect : ∀ v i, bad v i → 1 ≤ ∑ s, a v s i)
    (hcost : ∀ v, (∑ s, ∑ i, a v s i * H i) ≤ B v) :
    (∑ i, if ∃ v, bad v i then H i else 0) ≤ ∑ v, B v := by
  classical
  apply (weighted_union_bound H bad hH).trans
  apply Finset.sum_le_sum
  intro v _
  exact (weighted_detection_bound H (a v) (bad v) hH (ha v) (hdetect v)).trans (hcost v)


/-- At each depth there are `m^j` nodes, each with reciprocal-size budget.
Thus the total over `k` internal levels is exactly `k` times the level budget. -/
theorem sum_level_budget (m k : ℕ) (hm : m ≠ 0) (C : ℝ) :
    (∑ j : Fin k, ∑ _v : Fin (m ^ (j : ℕ)), C / (m : ℝ) ^ (j : ℕ)) = k * C := by
  have hm' : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm
  have hlevel : ∀ j : Fin k,
      (∑ _v : Fin (m ^ (j : ℕ)), C / (m : ℝ) ^ (j : ℕ)) = C := by
    intro j
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      Nat.cast_pow]
    rw [mul_comm, div_mul_cancel₀ _ (pow_ne_zero _ hm')]
  simp only [hlevel, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- The finite obstruction's root estimate in terms of nonnegative Fourier
weights and geometric detector bounds. -/
theorem root_bound_of_detectors {ι ν σ : Type*}
    [Fintype ι] [Fintype ν] [Fintype σ]
    (H w μ : ι → ℝ) (active : ι → Prop) (bad : ν → ι → Prop)
    (a : ν → σ → ι → ℝ) (B : ν → ℝ) (M ε K : ℝ)
    (hK : 0 < K) (hH : ∀ i, 0 ≤ H i) (hw : ∀ i, 0 ≤ w i)
    (hμ : ∀ i, μ i ≤ 4) (hzero : ∀ i, ¬ active i → μ i = 0)
    (hdense : ∀ i, active i → (¬ ∃ v, bad v i) → K ≤ w i)
    (hleaf : 2 * ∑ i, w i * H i ≤ M)
    (ha : ∀ v s i, 0 ≤ a v s i)
    (hdetect : ∀ v i, bad v i → 1 ≤ ∑ s, a v s i)
    (hcost : ∀ v, (∑ s, ∑ i, a v s i * H i) ≤ B v)
    (hbudget : (∑ v, B v) ≤ ε) :
    (∑ i, μ i * H i) ≤ 4 * (ε + M / (2 * K)) := by
  classical
  apply weighted_active_bound H w μ active (fun i => ∃ v, bad v i)
    M ε K hK hH hw hμ hzero hdense hleaf
  convert (exceptional_mass_of_detectors H a bad B hH ha hdetect hcost).trans hbudget using 1
  congr 1
  funext i
  by_cases hi : ∃ v, bad v i <;> simp [hi]


/-- Counting active coordinates commutes with summing nonnegative Fourier
weights. The identity itself does not require weight nonnegativity. -/
theorem support_mass_identity {ι κ : Type*} [Fintype ι] [Fintype κ]
    (H : ι → ℝ) (activeLeaf : κ → ι → Prop) :
    (∑ i, ((Finset.univ.filter (fun u => activeLeaf u i)).card : ℝ) * H i) =
      ∑ u, ∑ i, if activeLeaf u i then H i else 0 := by
  classical
  have hpoint : ∀ i,
      ((Finset.univ.filter (fun u => activeLeaf u i)).card : ℝ) * H i =
        ∑ u, if activeLeaf u i then H i else 0 := by
    intro i
    rw [← Finset.sum_filter]
    simp
  simp_rw [hpoint]
  exact Finset.sum_comm

/-- The per-leaf cyclic-average cost estimates imply the weighted leaf-mass
bound. This is equation (finite-leaf-mass) before insertion of the tree costs. -/
theorem leaf_mass_bound {ι κ : Type*} [Fintype ι] [Fintype κ]
    (H : ι → ℝ) (activeLeaf : κ → ι → Prop) (C : κ → ℝ) (M : ℝ)
    (hleaf : ∀ u, 2 * (∑ i, if activeLeaf u i then H i else 0) ≤ C u)
    (hbudget : (∑ u, C u) ≤ M) :
    2 * (∑ i, ((Finset.univ.filter (fun u => activeLeaf u i)).card : ℝ) * H i) ≤ M := by
  classical
  rw [support_mass_identity, Finset.mul_sum]
  exact (Finset.sum_le_sum (fun u _ => hleaf u)).trans hbudget

/-- Unnormalized version of the detector bound, directly usable with a
short interval of `J` translates. The index type need not itself have size
`J`; the explicit lower average and total cost are the necessary hypotheses. -/
theorem weighted_average_detection_bound {ι σ : Type*} [Fintype ι] [Fintype σ]
    (H : ι → ℝ) (a : σ → ι → ℝ) (bad : ι → Prop) (V : σ → ℝ)
    (J : ℝ) (hJ : 0 < J) (hH : ∀ i, 0 ≤ H i)
    (ha : ∀ s i, 0 ≤ a s i)
    (hdetect : ∀ i, bad i → J ≤ ∑ s, a s i)
    (hcost : ∀ s, (∑ i, a s i * H i) ≤ V s) :
    (∑ i, if bad i then H i else 0) ≤ (∑ s, V s) / J := by
  classical
  have hnormalized : ∀ i, bad i → 1 ≤ ∑ s, a s i / J := by
    intro i hi
    rw [← Finset.sum_div]
    exact (le_div_iff₀ hJ).2 (by simpa using hdetect i hi)
  have hmass := weighted_detection_bound H (fun s i => a s i / J) bad hH
    (fun s i => div_nonneg (ha s i) (le_of_lt hJ)) hnormalized
  have hterm : ∀ s, (∑ i, a s i / J * H i) ≤ V s / J := by
    intro s
    have heq : (∑ i, a s i / J * H i) = (∑ i, a s i * H i) / J := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [heq]
    exact div_le_div_of_nonneg_right (hcost s) (le_of_lt hJ)
  calc
    (∑ i, if bad i then H i else 0) ≤ ∑ s, ∑ i, a s i / J * H i := hmass
    _ ≤ ∑ s, V s / J := Finset.sum_le_sum (fun s _ => hterm s)
    _ = (∑ s, V s) / J := (Finset.sum_div _ _ _).symm


/-- Every spectral multiplier of a finite-group character is at most four. -/
theorem character_multiplier_le_four {A : Type*} [AddCommGroup A] [Fintype A]
    (χ : AddChar A ℂ) (z : A) : ‖1 - χ z‖ ^ 2 ≤ 4 := by
  have hnorm := norm_sub_le (1 : ℂ) (χ z)
  rw [norm_one, χ.norm_apply] at hnorm
  nlinarith [norm_nonneg (1 - χ z)]

/-- Character-specialized root estimate. The root activity and multiplier
are the actual complex character values, rather than unrelated predicates.
This is the spectral aggregation step in the finite-tree obstruction. -/
theorem character_root_bound {A κ ν σ : Type*}
    [AddCommGroup A] [Fintype A] [Fintype κ] [Fintype ν] [Fintype σ]
    (H : AddChar A ℂ → ℝ) (root : A)
    (activeLeaf : κ → AddChar A ℂ → Prop) (bad : ν → AddChar A ℂ → Prop)
    (a : ν → σ → AddChar A ℂ → ℝ) (B : ν → ℝ) (C : κ → ℝ)
    (M ε K : ℝ) (hK : 0 < K) (hH : ∀ χ, 0 ≤ H χ)
    (hdense : ∀ χ, χ root ≠ 1 → (¬ ∃ v, bad v χ) →
      K ≤ ((Finset.univ.filter (fun u => activeLeaf u χ)).card : ℝ))
    (hleaf : ∀ u, 2 * (∑ χ, if activeLeaf u χ then H χ else 0) ≤ C u)
    (hleafBudget : (∑ u, C u) ≤ M)
    (ha : ∀ v s χ, 0 ≤ a v s χ)
    (hdetect : ∀ v χ, bad v χ → 1 ≤ ∑ s, a v s χ)
    (hcost : ∀ v, (∑ s, ∑ χ, a v s χ * H χ) ≤ B v)
    (hbudget : (∑ v, B v) ≤ ε) :
    (∑ χ : AddChar A ℂ, ‖1 - χ root‖ ^ 2 * H χ) ≤
      4 * (ε + M / (2 * K)) := by
  classical
  apply root_bound_of_detectors H
    (fun χ => ((Finset.univ.filter (fun u => activeLeaf u χ)).card : ℝ))
    (fun χ => ‖1 - χ root‖ ^ 2) (fun χ => χ root ≠ 1)
    bad a B M ε K hK hH
  · intro χ
    exact Nat.cast_nonneg _
  · intro χ
    exact character_multiplier_le_four χ root
  · intro χ hχ
    have heq : χ root = 1 := not_not.mp hχ
    simp [heq]
  · exact hdense
  · exact leaf_mass_bound H activeLeaf C M hleaf hleafBudget
  · exact ha
  · exact hdetect
  · exact hcost
  · exact hbudget


/-- Full-period averaging detects a nontrivial character with multiplier two.
Applied to a cyclic coordinate subgroup, this is the source's leaf test. -/
theorem character_multiplier_average {A : Type*} [AddCommGroup A] [Fintype A]
    (χ : AddChar A ℂ) :
    (∑ z : A, ‖1 - χ z‖ ^ 2) / (Fintype.card A : ℝ) =
      if χ = 0 then 0 else 2 := by
  classical
  by_cases hχ : χ = 0
  · simp [hχ]
  · rw [ite_eq_right hχ]
    have hsum : (∑ z : A, χ z) = 0 := AddChar.sum_eq_zero_iff_ne_zero.mpr hχ
    have hre : (∑ z : A, (χ z).re) = 0 := by
      simpa using congrArg Complex.re hsum
    have hpoint : ∀ z : A, ‖1 - χ z‖ ^ 2 = 2 * (1 - (χ z).re) := by
      intro z
      rw [norm_sub_rev, Complex.norm_sub_one_sq_eq_of_norm_eq_one (χ.norm_apply z)]
    simp_rw [hpoint]
    rw [← Finset.mul_sum, Finset.sum_sub_distrib]
    have hcard : (Fintype.card A : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    simp [hre, hcard]

/-- Averaging the Fourier expansion along any finite subgroup homomorphism
is twice the Fourier weight of characters nontrivial on that subgroup. -/
theorem subgroup_average_spectral_mass {A G : Type*}
    [AddCommGroup A] [Fintype A] [AddCommGroup G] [Fintype G]
    (φ : G →+ A) (H : AddChar A ℂ → ℝ) :
    (∑ z : G, ∑ χ : AddChar A ℂ, ‖1 - χ (φ z)‖ ^ 2 * H χ) /
        (Fintype.card G : ℝ) =
      2 * ∑ χ : AddChar A ℂ, if χ.compAddMonoidHom φ = 0 then 0 else H χ := by
  classical
  rw [Finset.sum_comm, Finset.sum_div, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro χ _
  rw [← Finset.sum_mul]
  have havg := character_multiplier_average (χ.compAddMonoidHom φ)
  change (∑ z : G, ‖1 - χ (φ z)‖ ^ 2) / (Fintype.card G : ℝ) =
    (if χ.compAddMonoidHom φ = 0 then 0 else 2) at havg
  calc
    (∑ z : G, ‖1 - χ (φ z)‖ ^ 2) * H χ / (Fintype.card G : ℝ) =
        ((∑ z : G, ‖1 - χ (φ z)‖ ^ 2) / (Fintype.card G : ℝ)) * H χ := by ring
    _ = (if χ.compAddMonoidHom φ = 0 then 0 else 2) * H χ := by rw [havg]
    _ = 2 * (if χ.compAddMonoidHom φ = 0 then 0 else H χ) := by split_ifs <;> simp


/-- A character on the finite cyclic group is trivial exactly when its value
at the standard generator is one. -/
theorem zmod_character_eq_zero_iff (Q : ℕ) [NeZero Q]
    (χ : AddChar (ZMod Q) ℂ) : χ = 0 ↔ χ 1 = 1 := by
  constructor
  · intro h
    simp [h]
  · intro h
    apply AddChar.eq_zero_iff.mpr
    intro z
    have hz : z.val • (1 : ZMod Q) = z := by
      simp
    rw [← hz, χ.map_nsmul_eq_pow, h, one_pow]

/-- The coordinate version of the full-period leaf test, expressed using
the image of the cyclic generator. No injectivity of the subgroup map is needed. -/
theorem cyclic_average_spectral_mass {A : Type*}
    [AddCommGroup A] [Fintype A]
    (Q : ℕ) [NeZero Q] (φ : ZMod Q →+ A) (H : AddChar A ℂ → ℝ) :
    (∑ z : ZMod Q, ∑ χ : AddChar A ℂ, ‖1 - χ (φ z)‖ ^ 2 * H χ) /
        (Fintype.card (ZMod Q) : ℝ) =
      2 * ∑ χ : AddChar A ℂ, if χ (φ 1) = 1 then 0 else H χ := by
  classical
  rw [subgroup_average_spectral_mass]
  congr 1
  apply Finset.sum_congr rfl
  intro χ _
  simp only [zmod_character_eq_zero_iff, AddChar.compAddMonoidHom_apply]

/-- A uniform upper bound on the displacement along a cyclic coordinate
bounds twice the spectral mass active on that coordinate. -/
theorem cyclic_active_mass_le {A : Type*} [AddCommGroup A] [Fintype A]
    (Q : ℕ) [NeZero Q] (φ : ZMod Q →+ A) (H : AddChar A ℂ → ℝ) (C : ℝ)
    (hcost : ∀ z : ZMod Q, (∑ χ, ‖1 - χ (φ z)‖ ^ 2 * H χ) ≤ C) :
    2 * (∑ χ : AddChar A ℂ, if χ (φ 1) = 1 then 0 else H χ) ≤ C := by
  classical
  rw [← cyclic_average_spectral_mass Q φ H]
  have hcard : (0 : ℝ) < Fintype.card (ZMod Q) :=
    Nat.cast_pos.mpr Fintype.card_pos
  apply (div_le_iff₀ hcard).2
  calc
    (∑ z : ZMod Q, ∑ χ, ‖1 - χ (φ z)‖ ^ 2 * H χ) ≤ ∑ _z : ZMod Q, C :=
      Finset.sum_le_sum (fun z _ => hcost z)
    _ = C * Fintype.card (ZMod Q) := by simp [nsmul_eq_mul, mul_comm]


/-- Cyclic leaf-coordinate translation bounds imply the character
root estimate. -/
theorem root_bound_of_cyclic_leaf_tests {A κ ν σ : Type*}
    [AddCommGroup A] [Fintype A] [Fintype κ] [Fintype ν] [Fintype σ]
    (Q : κ → ℕ) [∀ u, NeZero (Q u)] (φ : ∀ u, ZMod (Q u) →+ A)
    (H : AddChar A ℂ → ℝ) (root : A) (bad : ν → AddChar A ℂ → Prop)
    (a : ν → σ → AddChar A ℂ → ℝ) (B : ν → ℝ) (C : κ → ℝ)
    (M ε K : ℝ) (hK : 0 < K) (hH : ∀ χ, 0 ≤ H χ)
    (hdense : ∀ χ, χ root ≠ 1 → (¬ ∃ v, bad v χ) →
      K ≤ ((Finset.univ.filter (fun u => χ (φ u 1) ≠ 1)).card : ℝ))
    (hleaf : ∀ u (z : ZMod (Q u)),
      (∑ χ, ‖1 - χ (φ u z)‖ ^ 2 * H χ) ≤ C u)
    (hleafBudget : (∑ u, C u) ≤ M)
    (ha : ∀ v s χ, 0 ≤ a v s χ)
    (hdetect : ∀ v χ, bad v χ → 1 ≤ ∑ s, a v s χ)
    (hcost : ∀ v, (∑ s, ∑ χ, a v s χ * H χ) ≤ B v)
    (hbudget : (∑ v, B v) ≤ ε) :
    (∑ χ : AddChar A ℂ, ‖1 - χ root‖ ^ 2 * H χ) ≤
      4 * (ε + M / (2 * K)) := by
  classical
  apply character_root_bound H root (fun u χ => χ (φ u 1) ≠ 1)
    bad a B C M ε K hK hH
  · intro χ hr hb
    convert hdense χ hr hb using 1
    congr 1
    congr 1
    ext u
    simp
  · intro u
    convert cyclic_active_mass_le (Q u) (φ u) H (C u) (hleaf u) using 1
    congr 1
    congr 1
    funext χ
    by_cases hχ : χ (φ u 1) = 1 <;> simp [hχ]
  · exact hleafBudget
  · exact ha
  · exact hdetect
  · exact hcost
  · exact hbudget


/-- Normalizing finitely many tests preserves a uniform test budget. -/
theorem normalized_weighted_test_bound {ι σ : Type*}
    [Fintype ι] [Fintype σ] [Nonempty σ]
    (H : ι → ℝ) (a : σ → ι → ℝ) (B : ℝ)
    (hcost : ∀ s, (∑ i, a s i * H i) ≤ B) :
    (∑ s, ∑ i, (a s i / (Fintype.card σ : ℝ)) * H i) ≤ B := by
  have hcard : (0 : ℝ) < Fintype.card σ := Nat.cast_pos.mpr Fintype.card_pos
  have heq : (∑ s, ∑ i, (a s i / (Fintype.card σ : ℝ)) * H i) =
      (∑ s, ∑ i, a s i * H i) / (Fintype.card σ : ℝ) := by
    simp_rw [div_mul_eq_mul_div, ← Finset.sum_div]
  rw [heq]
  apply (div_le_iff₀ hcard).2
  calc
    (∑ s, ∑ i, a s i * H i) ≤ ∑ _s : σ, B :=
      Finset.sum_le_sum (fun s _ => hcost s)
    _ = B * Fintype.card σ := by simp [nsmul_eq_mul, mul_comm]

/-- Complete finite spectral aggregation with concrete leaf and internal
translations. Geometry supplies the stated translation budgets; short-period
averaging supplies `hdetect`; branching supplies `hdense`. No additional
Fourier-mass or exceptional-union assertion is assumed. -/
theorem finite_spectral_root_bound {A κ ν σ : Type*}
    [AddCommGroup A] [Fintype A] [Fintype κ] [Fintype ν]
    [Fintype σ] [Nonempty σ]
    (Q : κ → ℕ) [∀ u, NeZero (Q u)] (φ : ∀ u, ZMod (Q u) →+ A)
    (H : AddChar A ℂ → ℝ) (root : A) (bad : ν → AddChar A ℂ → Prop)
    (shift : ν → σ → A) (B : ν → ℝ) (C : κ → ℝ)
    (M ε K : ℝ) (hK : 0 < K) (hH : ∀ χ, 0 ≤ H χ)
    (hdense : ∀ χ, χ root ≠ 1 → (¬ ∃ v, bad v χ) →
      K ≤ ((Finset.univ.filter (fun u => χ (φ u 1) ≠ 1)).card : ℝ))
    (hleaf : ∀ u (z : ZMod (Q u)),
      (∑ χ, ‖1 - χ (φ u z)‖ ^ 2 * H χ) ≤ C u)
    (hleafBudget : (∑ u, C u) ≤ M)
    (hdetect : ∀ v χ, bad v χ →
      (Fintype.card σ : ℝ) ≤ ∑ s, ‖1 - χ (shift v s)‖ ^ 2)
    (hcost : ∀ v s, (∑ χ, ‖1 - χ (shift v s)‖ ^ 2 * H χ) ≤ B v)
    (hbudget : (∑ v, B v) ≤ ε) :
    (∑ χ : AddChar A ℂ, ‖1 - χ root‖ ^ 2 * H χ) ≤
      4 * (ε + M / (2 * K)) := by
  classical
  have hcard : (0 : ℝ) < Fintype.card σ := Nat.cast_pos.mpr Fintype.card_pos
  apply root_bound_of_cyclic_leaf_tests Q φ H root bad
    (fun v s χ => ‖1 - χ (shift v s)‖ ^ 2 / (Fintype.card σ : ℝ))
    B C M ε K hK hH hdense hleaf hleafBudget
  · intro v s χ
    exact div_nonneg (sq_nonneg _) (le_of_lt hcard)
  · intro v χ hb
    rw [← Finset.sum_div]
    exact (le_div_iff₀ hcard).2 (by simpa using hdetect v χ hb)
  · intro v
    exact normalized_weighted_test_bound H (fun s χ => ‖1 - χ (shift v s)‖ ^ 2)
      (B v) (hcost v)
  · exact hbudget

end TreeEdit.BinaryLower.TreeDistortion.FiniteMass

end OAI
