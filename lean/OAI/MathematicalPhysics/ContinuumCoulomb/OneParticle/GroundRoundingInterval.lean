import OAI.MathematicalPhysics.ContinuumCoulomb.Reduction.FormStability

namespace OAI

/-! Rounding a cloud using an already proved two-sided ground-energy
interval. No minimizing eigenvector or independent kinetic bound is needed. -/

noncomputable section
namespace ContinuumCoulomb

theorem formGroundEnergy_exists_trial_of_upper {m n : ℕ} (S : Coulomb.Nuclei m)
    {C : ℝ} (hC : formGroundEnergy S n ≤ (C:EReal)) :
    ∃ trial : FormState n, normSq trial = 1 := by
  have htop : formGroundEnergy S n < ⊤ := hC.trans_lt (EReal.coe_lt_top C)
  obtain ⟨e,⟨trial,ht,_⟩,_⟩ := sInf_lt_iff.mp htop
  exact ⟨trial,ht⟩

theorem formGroundEnergy_position_stability_of_upper {m n : ℕ} (S T : Coulomb.Nuclei m)
    {C δ : ℝ} (hC : formGroundEnergy S n ≤ (C:EReal))
    (hδ : 0 ≤ δ) (hcharge : S.charge=T.charge)
    (hmove : ∀ a, ‖S.position a-T.position a‖ ≤ δ)
    (hsmall : 32*δ*Coulomb.totalCharge S ≤ 1) :
    |(formGroundEnergy T n).toReal-(formGroundEnergy S n).toReal| ≤
      32*δ*Coulomb.totalCharge S*(C+4*(n:ℝ)*Coulomb.totalCharge S^2) := by
  obtain ⟨trial,ht⟩ := formGroundEnergy_exists_trial_of_upper S hC
  have hf := formGroundEnergy_finite S trial ht
  have hCr : (formGroundEnergy S n).toReal ≤ C := by
    apply EReal.coe_le_coe_iff.mp
    simpa only [EReal.coe_toReal hf.1 hf.2] using hC
  exact (formGroundEnergy_position_stability S T trial ht hδ hcharge hmove hsmall).trans
    (mul_le_mul_of_nonneg_left (add_le_add hCr le_rfl)
      (by exact mul_nonneg (mul_nonneg (by norm_num) hδ) (Coulomb.totalCharge_pos S).le))

theorem formGroundEnergy_rounding_interval {m n : ℕ} (S T : Coulomb.Nuclei m)
    {center error δ roundError : ℝ}
    (hlower : ((center-error:ℝ):EReal) ≤ formGroundEnergy S n)
    (hupper : formGroundEnergy S n ≤ ((center+error:ℝ):EReal))
    (hδ : 0 ≤ δ) (hcharge : S.charge=T.charge)
    (hmove : ∀ a, ‖S.position a-T.position a‖ ≤ δ)
    (hsmall : 32*δ*Coulomb.totalCharge S ≤ 1)
    (hbudget : 32*δ*Coulomb.totalCharge S*
      (center+error+4*(n:ℝ)*Coulomb.totalCharge S^2) ≤ roundError) :
    ((center-error-roundError:ℝ):EReal) ≤ formGroundEnergy T n ∧
      formGroundEnergy T n ≤ ((center+error+roundError:ℝ):EReal) := by
  obtain ⟨trial,ht⟩ := formGroundEnergy_exists_trial_of_upper S hupper
  have hfS := formGroundEnergy_finite S trial ht
  have hfT := formGroundEnergy_finite T trial ht
  have hslo : center-error ≤ (formGroundEnergy S n).toReal := by
    apply EReal.coe_le_coe_iff.mp
    simpa only [EReal.coe_toReal hfS.1 hfS.2] using hlower
  have hshi : (formGroundEnergy S n).toReal ≤ center+error := by
    apply EReal.coe_le_coe_iff.mp
    simpa only [EReal.coe_toReal hfS.1 hfS.2] using hupper
  have hdiff := (formGroundEnergy_position_stability_of_upper S T hupper hδ hcharge hmove hsmall).trans hbudget
  obtain ⟨hdlo,hdhi⟩ := abs_le.mp hdiff
  constructor
  · rw [← EReal.coe_toReal hfT.1 hfT.2]
    exact EReal.coe_le_coe_iff.mpr (by linarith only [hslo,hdlo])
  · rw [← EReal.coe_toReal hfT.1 hfT.2]
    exact EReal.coe_le_coe_iff.mpr (by linarith only [hshi,hdhi])

end ContinuumCoulomb

end

end OAI
