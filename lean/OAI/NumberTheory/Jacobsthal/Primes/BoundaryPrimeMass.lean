import OAI.NumberTheory.Jacobsthal.Estimates.ReferenceWeightedQuadrature

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.VariablePrimeTilt

open _root_.Finset
open ReferenceAdmission FinitePathGeometry
open ErdosPrimeInputs.PrimePrefixMass ErdosPrimeInputs.PrimePrefixTail

theorem variable_tilt_weight (t : ℝ) (ps : List ℕ) :
    (ps.map (fun p : ℕ => t*(p:ℝ)⁻¹)).prod=t^ps.length*prefixWeight ps := by
  induction ps with
  | nil => simp [prefixWeight]
  | cons p ps ih =>
    simp only [List.map_cons,List.prod_cons,List.length_cons,pow_succ,prefixWeight] at ih ⊢
    rw [ih]
    ring

theorem long_prefix_variable_tilt (P : Finset ℕ) (m : ℕ) {t : ℝ} (ht : 1 ≤ t) :
    longPrefixMass P m ≤ Real.exp (t*∑ p ∈ P,(p:ℝ)⁻¹)/t^m := by
  have ht0 : 0 < t := by linarith
  apply (le_div_iff₀ (pow_pos ht0 m)).mpr
  rw [mul_comm,longPrefixMass,Finset.mul_sum]
  calc
    _ ≤ ∑ ps ∈ (decreasingPrefixes P).filter (fun ps => m ≤ ps.length),t^ps.length*prefixWeight ps := by
      apply Finset.sum_le_sum
      intro ps hp
      exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ ht (Finset.mem_filter.mp hp).2) (prefixWeight_nonneg ps)
    _ ≤ ∑ ps ∈ decreasingPrefixes P,t^ps.length*prefixWeight ps := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro ps _ _
      exact mul_nonneg (pow_nonneg ht0.le _) (prefixWeight_nonneg ps)
    _ = ∏ p ∈ P,(1+t*(p:ℝ)⁻¹) := by
      simp_rw [← variable_tilt_weight t]
      exact sum_sorted_products P _
    _ ≤ ∏ p ∈ P,Real.exp (t*(p:ℝ)⁻¹) := by
      apply Finset.prod_le_prod₀
      · intro p _hp
        positivity
      · intro p _hp
        simpa only [add_comm] using Real.add_one_le_exp (t*(p:ℝ)⁻¹)
    _ = _ := by rw [← Real.exp_sum,← Finset.mul_sum]

noncomputable def omissionMass (w r : ℝ) (i : Side) : ℝ :=
  ∑ ps ∈ firstOmissions w (boundaryPrimes w) i r,prefixWeight ps

theorem omission_mass_le_long {w r : ℝ} (hw : 1 < w) (hr : 4 ≤ r) (i : Side) :
    omissionMass w r i ≤ longPrefixMass (boundaryPrimes w) (⌊(r-4)/2⌋₊+1) := by
  classical
  unfold omissionMass longPrefixMass
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro ps hp
    have hlen := actual_first_omission_length hw i hp
    have hf : ((⌊(r-4)/2⌋₊:ℕ):ℝ) < (ps.length:ℝ) :=
      (Nat.floor_le (by linarith : 0 ≤ (r-4)/2)).trans_lt hlen
    have hn : ⌊(r-4)/2⌋₊+1 ≤ ps.length := by
      have hh : ⌊(r-4)/2⌋₊ < ps.length := by exact_mod_cast hf
      omega
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hp).1,hn⟩
  · intro ps _ _
    exact prefixWeight_nonneg ps

theorem actual_omission_variable_tilt {w r t : ℝ} (hw : 1 < w) (hr : 4 ≤ r) (ht : 1 ≤ t) (i : Side) :
    omissionMass w r i ≤ Real.exp (t*∑ p ∈ boundaryPrimes w,(p:ℝ)⁻¹)/t^(⌊(r-4)/2⌋₊+1) :=
  (omission_mass_le_long hw hr i).trans (long_prefix_variable_tilt _ _ ht)

end NumberTheoryLean.VariablePrimeTilt

end

section

namespace NumberTheoryLean.BoundaryPrimeMass

open _root_.Finset
open FinitePathGeometry ReferenceAdmission VariablePrimeTilt
open ErdosPrimeInputs.PrimePrefixMass ErdosPrimeInputs.PrimePrefixTail

theorem prime_sum_le_prefix_mass (P : Finset ℕ) :
    (∑ p ∈ P,(p:ℝ)⁻¹) ≤ ∑ ps ∈ decreasingPrefixes P,prefixWeight ps := by
  classical
  have hsub : P.image (fun p => [p]) ⊆ decreasingPrefixes P := by
    intro ps hps
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hps
    apply mem_decreasingPrefixes.mpr
    constructor
    · simp
    · intro q hq
      simpa using List.mem_singleton.mp hq ▸ hp
  have h := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun ps _ _ => prefixWeight_nonneg ps)
  have he : (∑ ps ∈ P.image (fun p => [p]),prefixWeight ps) = ∑ p ∈ P,(p:ℝ)⁻¹ := by
    rw [Finset.sum_image]
    · simp [prefixWeight]
    · intro p _ q _ hpq
      simpa using hpq
  rwa [he] at h

theorem uniform_boundary_mass : ∃ T w₀ : ℝ,0 < T ∧ 1 < w₀ ∧
    ∀ w : ℝ,w₀ ≤ w →
      (∑ p ∈ boundaryPrimes w,(p:ℝ)⁻¹) ≤ T ∧
      (∑ ps ∈ decreasingPrefixes (boundaryPrimes w),prefixWeight ps) ≤ T ∧
      ∀ r i,omissionMass w r i ≤ T := by
  classical
  obtain ⟨M,w₀,hM,hw₀,h⟩ := total_prime_prefix_mass
  refine ⟨2*M,w₀,by positivity,hw₀,?_⟩
  intro w hw
  have hmass : (∑ ps ∈ decreasingPrefixes (boundaryPrimes w),prefixWeight ps) ≤ 2*M := by
    simpa [boundaryPrimes,Real.rpow_one,mul_comm] using h w hw 1 2 le_rfl (by norm_num)
  refine ⟨(prime_sum_le_prefix_mass _).trans hmass,hmass,?_⟩
  intro r i
  apply le_trans _ hmass
  unfold omissionMass firstOmissions
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun ps _ _ => prefixWeight_nonneg ps)

end NumberTheoryLean.BoundaryPrimeMass

end

end Erdos970

end OAI
