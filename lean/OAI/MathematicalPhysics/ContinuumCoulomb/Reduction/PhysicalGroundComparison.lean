import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.ShiftedPhysicalForm
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.RayleighGround

namespace OAI

/-! Transfer manufactured-form estimates to the actual full-domain physical
ground energy. Inverse dilation covers every weak-H1 state; upper bounds use
positive-mass trial states and do not assume an attained continuum minimum. -/

noncomputable section
open scoped BigOperators
namespace ContinuumCoulomb

section PhysicalComparison
variable {M n : ℕ} (nuc : Coulomb.Nuclei M) (W F : Position → ℝ)
  {scale : ℝ} (hscale : 0 < scale) (offset : ℝ)
  (hsplit : ∀ y, W y+F y = -scale⁻¹*Coulomb.attraction nuc y-offset)
  (hI : ∀ w : Coulomb.H1Vector n, nuclearFormIntegrable F w)

include hsplit hI

theorem formGroundEnergy_dilated_lower (a : ℝ)
    (hbound : ∀ w : Coulomb.H1Vector n, Coulomb.Antisymmetric w →
      a*Coulomb.mass w ≤
        nuclearPerturbedForm (fun x => ∑ i, W (Coulomb.position x i)) F w+
          scale⁻¹*Coulomb.pairEnergy w) :
    ((scale^2*(a+(n:ℝ)*offset):ℝ):EReal) ≤
      formGroundEnergy (dilatedNuclei nuc scale hscale.ne') n := by
  apply formGroundEnergy_lower_of_forall
  intro state hnorm
  change Coulomb.mass state.val=1 at hnorm
  let w := normalizedDilation state.val scale⁻¹ (inv_ne_zero hscale.ne')
  have hw : Coulomb.Antisymmetric w :=
    normalizedDilation_antisymmetric state.val state.property _ _
  have hm : Coulomb.mass w=1 :=
    (mass_normalizedDilation state.val _ _).trans hnorm
  have hinv : normalizedDilation w scale hscale.ne'=state.val := by
    simpa only [w,inv_inv] using
      normalizedDilation_inverse state.val scale⁻¹ (inv_ne_zero hscale.ne')
  have hb := mul_le_mul_of_nonneg_left (hbound w hw) (sq_nonneg scale)
  rw [hm,mul_one] at hb
  have he := dilated_physicalForm_shift nuc W F hscale offset hsplit w (hI w)
  rw [hinv,hm,mul_one] at he
  nlinarith only [hb,he]

theorem formGroundEnergy_dilated_trial (a : ℝ) (w : Coulomb.H1Vector n)
    (hw : Coulomb.Antisymmetric w) (hm : 0 < Coulomb.mass w)
    (hbound : nuclearPerturbedForm (fun x => ∑ i, W (Coulomb.position x i)) F w+
      scale⁻¹*Coulomb.pairEnergy w ≤ a*Coulomb.mass w) :
    formGroundEnergy (dilatedNuclei nuc scale hscale.ne') n ≤
      ((scale^2*(a+(n:ℝ)*offset):ℝ):EReal) := by
  let v := normalizedDilation w scale hscale.ne'
  have hv := normalizedDilation_antisymmetric w hw scale hscale.ne'
  have hmass : Coulomb.mass v=Coulomb.mass w := mass_normalizedDilation w _ _
  have hmv : 0 < Coulomb.mass v := by rw [hmass]; exact hm
  apply (formGroundEnergy_le_rayleigh _ v hv hmv).trans
  apply EReal.coe_le_coe
  apply (div_le_iff₀ hmv).mpr
  have he := dilated_physicalForm_shift nuc W F hscale offset hsplit w (hI w)
  have hb := mul_le_mul_of_nonneg_left hbound (sq_nonneg scale)
  change Coulomb.form _ v = _ at he
  rw [hmass]
  nlinarith only [hb,he]

theorem formGroundEnergy_dilated_upper (a : ℝ)
    (hnear : ∀ ε : ℝ, 0 < ε → ∃ w : Coulomb.H1Vector n,
      Coulomb.Antisymmetric w ∧ 0 < Coulomb.mass w ∧
      nuclearPerturbedForm (fun x => ∑ i, W (Coulomb.position x i)) F w+
        scale⁻¹*Coulomb.pairEnergy w ≤ (a+ε)*Coulomb.mass w) :
    formGroundEnergy (dilatedNuclei nuc scale hscale.ne') n ≤
      ((scale^2*(a+(n:ℝ)*offset):ℝ):EReal) := by
  obtain ⟨w,hw,hm,_⟩ := hnear 1 zero_lt_one
  have hfin := formGroundEnergy_finite_of_positive_mass
    (dilatedNuclei nuc scale hscale.ne') (normalizedDilation w scale hscale.ne')
    (normalizedDilation_antisymmetric w hw _ _) (by
      rw [mass_normalizedDilation]; exact hm)
  have hcoe := EReal.coe_toReal hfin.1 hfin.2
  rw [← hcoe]
  apply EReal.coe_le_coe
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨v,hv,hmv,hb⟩ := hnear (ε/scale^2) (div_pos hε (sq_pos_of_pos hscale))
  have hu := formGroundEnergy_dilated_trial nuc W F hscale offset hsplit hI
    (a+ε/scale^2) v hv hmv hb
  have he : scale^2*(a+ε/scale^2+(n:ℝ)*offset) = scale^2*(a+(n:ℝ)*offset)+ε := by
    field_simp [ne_of_gt hscale]
    ring
  rw [he,← hcoe] at hu
  exact EReal.coe_le_coe_iff.mp hu

end PhysicalComparison
end ContinuumCoulomb

end

end OAI
