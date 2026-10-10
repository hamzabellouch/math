import OAI.Combinatorics.LowSpaceSubsetSum.Separators.SeparatorIncidence
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Data.Fintype.Pi

namespace OAI

/-!
# Finite random separating families

For one fixed disjoint pair of masks, the separating subsets are counted
exactly. A family is a uniformly chosen function from its index
set to the set of eligible subsets: repeated sets retain distinct indices.
Its point probabilities factor, so this is independent sampling with
replacement, as required in the manuscript.
-/

namespace LowSpaceSubsetSum

open scoped BigOperators

/-- Cardinal-ratio form of the uniform law on a finite sample space. -/
noncomputable def finiteUniformProbability {Ω : Type*} [Fintype Ω] (P : Ω → Prop) : ℝ := by
  classical
  exact (Fintype.card {ω // P ω} : ℝ) / Fintype.card Ω

theorem finiteUniformProbability_eq_pmf {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (P : Ω → Prop) :
    finiteUniformProbability P =
      ((PMF.uniformOfFintype Ω).toOuterMeasure {ω | P ω}).toReal := by
  classical
  rw [PMF.toOuterMeasure_uniformOfFintype_apply, ENNReal.toReal_div,
    ENNReal.toReal_natCast, ENNReal.toReal_natCast]
  rfl

theorem finiteUniformProbability_nonneg {Ω : Type*} [Fintype Ω] (P : Ω → Prop) :
    0 ≤ finiteUniformProbability P := by
  classical
  unfold finiteUniformProbability
  positivity

theorem finiteUniformProbability_le_one {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (P : Ω → Prop) : finiteUniformProbability P ≤ 1 := by
  classical
  unfold finiteUniformProbability
  apply (div_le_one (by exact_mod_cast Fintype.card_pos)).mpr
  exact_mod_cast Fintype.card_subtype_le P

theorem finiteUniformProbability_compl {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (P : Ω → Prop) :
    finiteUniformProbability (fun ω => ¬P ω) = 1 - finiteUniformProbability P := by
  classical
  unfold finiteUniformProbability
  rw [Fintype.card_subtype_compl, Nat.cast_sub (Fintype.card_subtype_le P)]
  have hcard : (Fintype.card Ω : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp

/-- Every coordinate has the uniform law and the joint point mass is their product. -/
theorem uniform_family_point_probability {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (ν : ℕ) (f : Fin ν → Ω) :
    PMF.uniformOfFintype (Fin ν → Ω) f =
      ∏ i : Fin ν, PMF.uniformOfFintype Ω (f i) := by
  simp [PMF.uniformOfFintype_apply, ENNReal.inv_pow]

/-- Exact failure probability for independent uniform draws, including repeated samples. -/
theorem uniform_family_failure {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (P : Ω → Prop) (ν : ℕ) :
    finiteUniformProbability (fun f : Fin ν → Ω => ∀ i, ¬P (f i)) =
      (1 - finiteUniformProbability P) ^ ν := by
  classical
  let : DecidablePred (fun f : Fin ν → Ω => ∀ i, ¬P (f i)) :=
    fun _ => Classical.propDecidable _
  let : DecidablePred (fun ω : Ω => ¬P ω) := fun _ => Classical.propDecidable _
  let equiv : {f : Fin ν → Ω // ∀ i, ¬P (f i)} ≃ (Fin ν → {ω : Ω // ¬P ω}) :=
    { toFun := fun f i => ⟨f.1 i, f.2 i⟩
      invFun := fun f => ⟨fun i => (f i).1, fun i => (f i).2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← finiteUniformProbability_compl P]
  unfold finiteUniformProbability
  calc
    _ = (Fintype.card (Fin ν → {ω : Ω // ¬P ω}) : ℝ) /
        Fintype.card (Fin ν → Ω) := by
      congr 1
      norm_cast
      exact @Fintype.card_congr _ _ _ _ equiv
    _ = _ := by
      simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow, div_pow]

theorem uniform_family_coverage {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (P : Ω → Prop) (ν : ℕ) :
    finiteUniformProbability (fun f : Fin ν → Ω => ∃ i, P (f i)) =
      1 - (1 - finiteUniformProbability P) ^ ν := by
  classical
  have hpred : (fun f : Fin ν → Ω => ∃ i, P (f i)) =
      (fun f => ¬(∀ i, ¬P (f i))) := by ext f; simp
  rw [hpred, finiteUniformProbability_compl, uniform_family_failure]

/-- Finite union bound; the events need not be independent. -/
theorem finiteUniformProbability_exists_le_sum {Ω K : Type*}
    [Fintype Ω] [Nonempty Ω] [Fintype K] (P : K → Ω → Prop) :
    finiteUniformProbability (fun ω => ∃ i, P i ω) ≤
      ∑ i, finiteUniformProbability (P i) := by
  classical
  have hset : (Finset.univ.filter fun ω : Ω => ∃ i, P i ω) =
      Finset.univ.biUnion (fun i : K => Finset.univ.filter (P i)) := by
    ext ω
    simp
  have hcard : (Finset.univ.filter fun ω : Ω => ∃ i, P i ω).card ≤
      ∑ i : K, (Finset.univ.filter (P i)).card := by
    rw [hset]
    exact Finset.card_biUnion_le
  simp only [finiteUniformProbability, Fintype.card_subtype]
  rw [← Finset.sum_div]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg (Fintype.card Ω))
  exact_mod_cast hcard

/-- The four-block coverage conclusion uses only the four marginal bounds. -/
theorem four_family_union_bound {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (Q : Fin 4 → Ω → Prop)
    (hQ : ∀ i, 1 - Real.exp (-10) ≤ finiteUniformProbability (Q i)) :
    1 - 4 * Real.exp (-10) ≤ finiteUniformProbability (fun ω => ∀ i, Q i ω) := by
  classical
  have hfail (i : Fin 4) : finiteUniformProbability (fun ω => ¬Q i ω) ≤ Real.exp (-10) := by
    rw [finiteUniformProbability_compl]
    linarith [hQ i]
  have h := (finiteUniformProbability_exists_le_sum (fun i ω => ¬Q i ω)).trans
    (Finset.sum_le_sum (fun i _ => hfail i))
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
  norm_num at h
  have hpred : (fun ω => ∀ i, Q i ω) = (fun ω => ¬∃ i, ¬Q i ω) := by
    ext ω
    simp
  rw [hpred, finiteUniformProbability_compl]
  linarith

theorem separating_family_failure_bound {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) :
    (1 - θ) ^ (⌈10 / θ⌉₊) ≤ Real.exp (-10) := by
  let ν := ⌈10 / θ⌉₊
  have hceil : 10 / θ ≤ (ν : ℝ) := Nat.le_ceil _
  have hten : (10 : ℝ) ≤ (ν : ℝ) * θ := (div_le_iff₀ hθ0).mp hceil
  have hν : (0 : ℝ) < ν := by nlinarith
  have hnorm : 1 - θ ≤ 1 - 10 / (ν : ℝ) := by
    have := (div_le_iff₀ hν).mpr (show (10 : ℝ) ≤ θ * ν by nlinarith)
    linarith
  have hn10 : (10 : ℝ) ≤ ν := by nlinarith
  exact (pow_le_pow_left₀ (by linarith) hnorm ν).trans
    (Real.one_sub_div_pow_le_exp_neg hn10)

variable {ι : Type*} [DecidableEq ι]

/-- Eligible subsets that contain the left mask and avoid the right mask. -/
def separatingSubsets (U L R : Finset ι) (e : ℕ) : Finset (Finset ι) :=
  (U.powersetCard e).filter fun S => L ⊆ S ∧ Disjoint S R

theorem separatingSubsets_eq (U L R : Finset ι) (e : ℕ) :
    separatingSubsets U L R e = ((U \ R).powersetCard e).filter (L ⊆ ·) := by
  ext S
  simp only [separatingSubsets, Finset.mem_filter, Finset.mem_powersetCard,
    Finset.subset_sdiff]
  tauto

theorem card_separatingSubsets (U L R : Finset ι) (e : ℕ)
    (hL : L ⊆ U) (hR : R ⊆ U) (hdisj : Disjoint L R) (he : L.card ≤ e) :
    (separatingSubsets U L R e).card =
      Nat.choose (U.card - R.card - L.card) (e - L.card) := by
  rw [separatingSubsets_eq, Finset.card_filter_powersetCard_subset]
  · rw [Finset.card_sdiff_of_subset hR]
  · exact Finset.subset_sdiff.mpr ⟨hL, hdisj⟩
  · exact he

/-- The exact one-draw probability for a fixed disjoint pair of masks. -/
theorem uniform_separation_probability (U L R : Finset ι) (e : ℕ)
    (hL : L ⊆ U) (hR : R ⊆ U) (hdisj : Disjoint L R)
    (he0 : L.card ≤ e) (he : e ≤ U.card) :
    ((PMF.uniformOfFinset (U.powersetCard e) (Finset.powersetCard_nonempty.mpr he)).toOuterMeasure
      {S | L ⊆ S ∧ Disjoint S R}).toReal =
      (Nat.choose (U.card - R.card - L.card) (e - L.card) : ℝ) / Nat.choose U.card e := by
  classical
  simp only [PMF.toOuterMeasure_uniformOfFinset_apply, ENNReal.toReal_div,
    ENNReal.toReal_natCast, Set.mem_ofPred_eq, Finset.card_powersetCard]
  rw [← separatingSubsets, card_separatingSubsets U L R e hL hR hdisj he0]

theorem card_separatingSubsets_half (U L R : Finset ι) (e : ℕ)
    (hL : L ⊆ U) (hR : R ⊆ U) (hdisj : Disjoint L R) (he : L.card ≤ e)
    (heven : 2 ∣ U.card) (hhalf : L.card + R.card = U.card / 2) :
    (separatingSubsets U L R e).card = Nat.choose (U.card / 2) (e - L.card) := by
  rw [card_separatingSubsets U L R e hL hR hdisj he]
  congr 1
  have h := Nat.div_mul_cancel heven
  omega

/-- One sample is an indexed, fixed-size subset of the block. -/
abbrev SeparatorSample (U : Finset ι) (e : ℕ) := {S : Finset ι // S ∈ U.powersetCard e}

theorem separatorSample_success_probability (U L R : Finset ι) (e : ℕ)
    (hL : L ⊆ U) (hR : R ⊆ U) (hdisj : Disjoint L R) (he : L.card ≤ e)
    (heven : 2 ∣ U.card) (hhalf : L.card + R.card = U.card / 2) :
    finiteUniformProbability (fun S : SeparatorSample U e => L ⊆ S.val ∧ Disjoint S.val R) =
      (Nat.choose (U.card / 2) (e - L.card) : ℝ) / Nat.choose U.card e := by
  classical
  let : DecidablePred (fun S : SeparatorSample U e => L ⊆ S.val ∧ Disjoint S.val R) :=
    fun _ => Classical.propDecidable _
  let equiv : {S : SeparatorSample U e // L ⊆ S.val ∧ Disjoint S.val R} ≃
      {S : Finset ι // S ∈ separatingSubsets U L R e} :=
    { toFun := fun S => ⟨S.1.1, Finset.mem_filter.mpr ⟨S.1.2, S.2⟩⟩
      invFun := fun S => ⟨⟨S.1, (Finset.mem_filter.mp S.2).1⟩, (Finset.mem_filter.mp S.2).2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  unfold finiteUniformProbability
  calc
    _ = (Fintype.card {S : Finset ι // S ∈ separatingSubsets U L R e} : ℝ) /
        Fintype.card (SeparatorSample U e) := by
      congr 1
      norm_cast
      exact @Fintype.card_congr _ _ _ _ equiv
    _ = _ := by simp only [Fintype.card_coe, Finset.card_powersetCard,
      card_separatingSubsets_half U L R e hL hR hdisj he heven hhalf]

/-- Coverage of a fixed mask pair by the paper's sampled family. -/
theorem separator_family_coverage (U L R : Finset ι) (e : ℕ)
    (hL : L ⊆ U) (hR : R ⊆ U) (hdisj : Disjoint L R)
    (he0 : L.card ≤ e) (he : e ≤ U.card)
    (heven : 2 ∣ U.card) (hhalf : L.card + R.card = U.card / 2)
    (hfeas : e - L.card ≤ U.card / 2) :
    let θ : ℝ := (Nat.choose (U.card / 2) (e - L.card) : ℝ) / Nat.choose U.card e
    1 - Real.exp (-10) ≤ finiteUniformProbability
      (fun f : Fin (⌈10 / θ⌉₊) → SeparatorSample U e =>
        ∃ i, L ⊆ (f i).val ∧ Disjoint (f i).val R) := by
  classical
  dsimp only
  have : Nonempty (SeparatorSample U e) := (Finset.powersetCard_nonempty.mpr he).to_subtype
  let θ : ℝ := (Nat.choose (U.card / 2) (e - L.card) : ℝ) / Nat.choose U.card e
  have hθ : finiteUniformProbability
      (fun S : SeparatorSample U e => L ⊆ S.val ∧ Disjoint S.val R) = θ :=
    separatorSample_success_probability U L R e hL hR hdisj he0 heven hhalf
  have hθ0 : 0 < θ := div_pos
    (by exact_mod_cast Nat.choose_pos hfeas) (by exact_mod_cast Nat.choose_pos he)
  have hθ1 : θ ≤ 1 := hθ ▸ finiteUniformProbability_le_one _
  have hcov := uniform_family_coverage
    (fun S : SeparatorSample U e => L ⊆ S.val ∧ Disjoint S.val R) ⌈10 / θ⌉₊
  rw [hθ] at hcov
  rw [hcov]
  have h := separating_family_failure_bound hθ0 hθ1
  linarith

end LowSpaceSubsetSum

end OAI
