import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.AmplitudeGeOne
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.LocalUnlitCount

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter
open scoped Topology

namespace OrdinaryCorrelations.GraphKernel.PrimeSystem
open OrdinaryCorrelations.SignedTrace OrdinaryCorrelations.FiniteIntegration
open Finset Classical
noncomputable section
variable {S : PrimeSystem} {B τ C₀ : ℝ} {D : S.DivisorFamily B τ C₀} {h ℓ L : ℕ}

lemma tilted_list_local_mean (w : ClosedLine h ℓ) (𝔏 : List (AttachedSpec w D L))
    (p : S.Index) (z : ℝ) (hz : 1 ≤ z) (hzp : z^2 ≤ (p:ℝ)) :
    avg (fun r => |localWithList w 𝔏 p r| * z^(repeatedUnlitLocal w p r)) ≤
      S.amplitude p ^ S.occurrenceCount w p *
        (if p ∈ fullUsedIndices w 𝔏 then ((ℓ:ℝ)+2)*(p:ℝ)⁻¹ else 1) := by
  by_cases hr : ¬S.IsCore p ∧ 2 ≤ S.occurrenceCount w p
  · have he : ∃ i, (p:ℕ) ∣ w.label i := by
      have hm : (univ.filter (fun i : Fin ℓ => (p:ℕ) ∣ w.label i)).Nonempty := by
        rw [←card_pos]; exact lt_of_lt_of_le (by norm_num) hr.2
      obtain ⟨i,hi⟩ := hm
      exact ⟨i,(mem_filter.mp hi).2⟩
    have hp : p ∈ fullUsedIndices w 𝔏 := mem_filter.mpr ⟨mem_univ _,Or.inl he⟩
    simp only [repeatedUnlitLocal,hr,amplitude,ite_false,one_pow,
      one_mul,ite_eq_left hp]
    calc
      _ ≤ avg (fun r => |S.primeFactor w p r| *z^(localUnlitCount w p r)) := by
        apply avg_mono
        intro r
        apply mul_le_mul_of_nonneg_right _ (pow_nonneg (zero_le_one.trans hz) _)
        rw [localWithList,abs_mul,abs_of_nonneg (listLocal_nonneg w 𝔏 p r)]
        exact mul_le_of_le_one_right (abs_nonneg _) (listLocal_le_one w 𝔏 p r)
      _ ≤ ((ℓ:ℝ)+1)*(p:ℝ)⁻¹ := center_tilt_mean w p hr.1 hr.2 z hz hzp
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  · simp only [repeatedUnlitLocal,hr,ite_false,pow_zero,mul_one]
    apply (crude_prime_mean w 𝔏 p).trans
    apply mul_le_mul_of_nonneg_left _ (pow_nonneg (zero_le_one.trans (amplitude_ge_one p)) _)
    split_ifs
    · apply mul_le_mul_of_nonneg_right _ (by positivity)
      linarith [(Nat.cast_nonneg ℓ : (0:ℝ) ≤ (ℓ:ℝ))]
    · exact le_rfl

lemma repeated_unlit_tail_integral (w : ClosedLine h ℓ)
    (hl : ∀ i, w.label i ∈ D.members) {T : ℝ} (cut : S.Cutoffs T)
    (𝔏 : List (AttachedSpec w D L)) (z : ℝ) (hz : 1 ≤ z)
    (hzp : ∀ p : S.Index, z^2 ≤ (p:ℝ)) (t : ℕ) :
    (avg (fun r : S.Residues => if t ≤ repeatedUnlitTotal w r then
      |S.kernel w cut r| *listIndicator w 𝔏 r else 0))*z^t ≤
      A^(ℓ*⌈C₀*Real.log B⌉₊)*((ℓ:ℝ)+2)^(fullUsedIndices w 𝔏).card *
        ∏ p ∈ fullUsedIndices w 𝔏,(p:ℝ)⁻¹ := by
  have hz0 : 0 ≤ z := zero_le_one.trans hz
  have hpt (r : S.Residues) :
      (if t ≤ repeatedUnlitTotal w r then |S.kernel w cut r| *listIndicator w 𝔏 r else 0)*z^t ≤
        ∏ p : S.Index, |localWithList w 𝔏 p (r p)| *z^(repeatedUnlitLocal w p (r p)) := by
    rw [prod_mul_distrib,prod_pow_eq_pow_sum]
    by_cases ht : t ≤ repeatedUnlitTotal w r
    · rw [ite_eq_left ht,absolute_list_factorization]
      apply mul_le_mul
      · exact mul_le_of_le_one_left (prod_nonneg (fun p hp => abs_nonneg _)) (cutoffProduct_le_one w cut _)
      · exact pow_le_pow_right₀ hz ht
      · exact pow_nonneg hz0 _
      · exact prod_nonneg (fun p hp => abs_nonneg _)
    · rw [ite_eq_right ht,zero_mul]
      exact mul_nonneg (prod_nonneg (fun p hp => abs_nonneg _)) (pow_nonneg hz0 _)
  calc
    _ = avg (fun r : S.Residues => (if t ≤ repeatedUnlitTotal w r then
      |S.kernel w cut r| *listIndicator w 𝔏 r else 0)*z^t) := (avg_mul_right _ _).symm
    _ ≤ avg (fun r : S.Residues => ∏ p : S.Index,
        |localWithList w 𝔏 p (r p)| *z^(repeatedUnlitLocal w p (r p))) := avg_mono hpt
    _ = ∏ p : S.Index, avg (fun r => |localWithList w 𝔏 p r| *z^(repeatedUnlitLocal w p r)) := by
      convert avg_product (Ω := fun p : S.Index => ZMod (p:ℕ))
        (fun p r => |localWithList w 𝔏 p r| *z^(repeatedUnlitLocal w p r)) using 1
      congr 1
      exact Subsingleton.elim _ _
    _ ≤ ∏ p : S.Index, S.amplitude p ^ S.occurrenceCount w p *
        (if p ∈ fullUsedIndices w 𝔏 then ((ℓ:ℝ)+2)*(p:ℝ)⁻¹ else 1) :=
      prod_le_prod₀ (fun p hp => avg_nonneg (fun r => mul_nonneg (abs_nonneg _) (pow_nonneg hz0 _)))
        (fun p hp => tilted_list_local_mean w 𝔏 p z hz (hzp p))
    _ = (∏ p : S.Index, S.amplitude p ^ S.occurrenceCount w p)*
        (((ℓ:ℝ)+2)^(fullUsedIndices w 𝔏).card * ∏ p ∈ fullUsedIndices w 𝔏,(p:ℝ)⁻¹) := by
      rw [prod_mul_distrib,prod_ite_mem,univ_inter,prod_mul_distrib,prod_const]
    _ ≤ _ := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right (crude_amplitude_product w hl)
        (by positivity : 0 ≤ ((ℓ:ℝ)+2)^(fullUsedIndices w 𝔏).card * ∏ p ∈ fullUsedIndices w 𝔏,(p:ℝ)⁻¹)

end
end OrdinaryCorrelations.GraphKernel.PrimeSystem

end

end OAI
