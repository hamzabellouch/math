import OAI.NumberTheory.Ostmann.Tree.AffineFibers

namespace OAI

namespace Ostmann.FiniteField
noncomputable section
open scoped BigOperators ComplexConjugate

theorem norm_sum_sq_le_card {ι : Type*} (S : Finset ι) (v : ι → ℂ) :
    ‖∑ i ∈ S, v i‖ ^ 2 ≤ (S.card : ℝ) * ∑ i ∈ S, ‖v i‖ ^ 2 := by
  calc
    _ ≤ (∑ i ∈ S, ‖v i‖)^2 := by
      exact pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
    _ ≤ _ := by
      simpa using Finset.sum_mul_sq_le_sq_mul_sq S (fun _ => (1:ℝ)) (fun i => ‖v i‖)

variable {F : Type*} [Field F] [Fintype F]
variable [DecidableEq F]

def affineCoefficient (G : Fˣ → ℂ) (K : F × F) : ℂ :=
  ∑ rs : Fˣ × Fˣ with affinePair rs.1 rs.2 = K, conj (G rs.1) * G rs.2

theorem affineCoefficient_nonidentity (G : Fˣ → ℂ) (K : F × F) (hK : K ≠ (1,0)) :
    ‖affineCoefficient G K‖^2 ≤
      2 * ∑ rs : Fˣ × Fˣ with affinePair rs.1 rs.2 = K,
        ‖G rs.1‖^2 * ‖G rs.2‖^2 := by
  let S : Finset (Fˣ × Fˣ) := Finset.univ.filter (fun rs => affinePair rs.1 rs.2 = K)
  have hc : S.card ≤ 2 := affinePair_fiber_card_le_two S K hK
    (fun rs hrs => (Finset.mem_filter.mp hrs).2)
  have he := norm_sum_sq_le_card S (fun rs => conj (G rs.1)*G rs.2)
  simp only [norm_mul, Complex.norm_conj, mul_pow] at he
  have hcR : (S.card : ℝ) ≤ 2 := by exact_mod_cast hc
  exact he.trans (mul_le_mul_of_nonneg_right hcR
    (Finset.sum_nonneg (fun _ _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))))

omit [Fintype F] [DecidableEq F] in
theorem affinePair_eq_identity_iff (r s : Fˣ) : affinePair r s = (1,0) ↔ r=s := by
  constructor
  · intro h
    have hs := congrArg Prod.snd h
    change (s:F) - (s:F)^2/(r:F)=0 at hs
    have hh : (s:F)*(r:F)=(s:F)*(s:F) := by
      have := (eq_div_iff (Units.ne_zero r)).mp (sub_eq_zero.mp hs)
      simpa only [pow_two] using this
    exact Units.ext (mul_left_cancel₀ (Units.ne_zero s) hh)
  · rintro rfl
    apply affinePair_eq_identity_of_ratio_one
    exact div_self (Units.ne_zero r)

theorem affineCoefficient_identity (G : Fˣ → ℂ) :
    affineCoefficient G (1,0) = ∑ r : Fˣ, conj (G r)*G r := by
  simp only [affineCoefficient, affinePair_eq_identity_iff]
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  simp

theorem norm_affineCoefficient_identity (G : Fˣ → ℂ) :
    ‖affineCoefficient G (1,0)‖ = ∑ r : Fˣ, ‖G r‖^2 := by
  rw [affineCoefficient_identity]
  simp only [Complex.conj_mul', ← Complex.ofReal_pow]
  rw [← Complex.ofReal_sum, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Finset.sum_nonneg (fun _ _ => sq_nonneg _))]

theorem affineFiberEnergy_sum (G : Fˣ → ℂ) :
    (∑ K : F × F, ∑ rs : Fˣ × Fˣ with affinePair rs.1 rs.2 = K,
      ‖G rs.1‖^2 * ‖G rs.2‖^2) = (∑ r : Fˣ, ‖G r‖^2)^2 := by
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [Fintype.sum_prod_type]
  simp only [← Finset.mul_sum, ← Finset.sum_mul, pow_two]

theorem affineCoefficient_energy (G : Fˣ → ℂ) :
    ∑ K : F × F, ‖affineCoefficient G K‖^2 ≤ 3 * (∑ r : Fˣ, ‖G r‖^2)^2 := by
  let A := (∑ r : Fˣ, ‖G r‖^2)^2
  let E := fun K : F × F => ∑ rs : Fˣ × Fˣ with affinePair rs.1 rs.2 = K,
    ‖G rs.1‖^2 * ‖G rs.2‖^2
  have hE : ∀ K, 0 ≤ E K := fun K =>
    Finset.sum_nonneg (fun _ _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))
  have hn : ∑ K ∈ Finset.univ.erase (1,0), ‖affineCoefficient G K‖^2 ≤ 2*A := by
    calc
      _ ≤ ∑ K ∈ Finset.univ.erase (1,0), 2*E K := by
        apply Finset.sum_le_sum
        intro K hK
        exact affineCoefficient_nonidentity G K (Finset.ne_of_mem_erase hK)
      _ = 2 * ∑ K ∈ Finset.univ.erase (1,0), E K := by rw [Finset.mul_sum]
      _ ≤ 2 * ∑ K : F × F, E K := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
          (fun K _ _ => hE K)
      _ = 2*A := by rw [affineFiberEnergy_sum]
  have hid : ‖affineCoefficient G (1,0)‖^2 = A := by
    rw [norm_affineCoefficient_identity]
  have hsplit := Finset.sum_erase_add Finset.univ
    (fun K : F × F => ‖affineCoefficient G K‖^2) (Finset.mem_univ (1,0))
  rw [← hsplit, hid]
  change _ ≤ 3*A
  linarith

end
end Ostmann.FiniteField

end OAI
