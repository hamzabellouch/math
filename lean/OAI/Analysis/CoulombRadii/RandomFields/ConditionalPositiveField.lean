import Mathlib
import OAI.Analysis.CoulombRadii.FieldAnalysis.PositiveField
import OAI.Analysis.CoulombRadii.Screening.ScreeningNormalization

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical SchwartzMap Pointwise
noncomputable section
namespace Coulomb

lemma potentialForm_normalized_eq {n : ℕ} (V : Configuration n → ℝ) (u : H1Vector n) :
    potentialForm V u.normalized = (mass u)⁻¹*potentialForm V u := by
  rw [H1Vector.normalized,potentialForm_rsmul,inv_pow,Real.sq_sqrt (mass_nonneg u)]

lemma normalized_corePotential_aestronglyMeasurable {m k : ℕ} (ψ : H1Vector (m+k))
    (s : Spins m) (y : Space) : AEStronglyMeasurable
      (fun x => coreCoulombPotential (ψ.coreSlice s x).normalized y) volume := by
  simp only [←nuclearEnergy_unit_eq_coreCoulomb]
  change AEStronglyMeasurable (fun x => potentialForm (nuclearPotential (unitNucleus y))
    (ψ.coreSlice s x).normalized) _
  simp only [potentialForm_normalized_eq]
  exact (mass_coreSlice_integrable ψ s).aestronglyMeasurable.inv₀.mul
    (potentialForm_coreSlice_integrable ψ s (nuclearPotential (unitNucleus y))
      (fun t => ψ.core_nuclear_integrable (unitNucleus y) (Fin.append s t))).aestronglyMeasurable

lemma coreField_positive_le {J k : ℕ} (S : Nuclei J) (u : H1Vector k) (y : Space) :
    max (coreScreenedField S u y) 0 ≤ attraction S y := by
  apply max_le _ (attraction_nonneg S y)
  unfold coreScreenedField
  linarith [coreCoulombPotential_nonneg u y]

lemma coreField_positive_square_weight_integrable {J m k : ℕ} (S : Nuclei J)
    (ψ : H1Vector (m+k)) (s : Spins m) (y : Space) :
    Integrable (fun x => mass (ψ.coreSlice s x)*(max (coreScreenedField S (ψ.coreSlice s x).normalized y) 0)^2) := by
  have hm : AEStronglyMeasurable (fun x => (max (coreScreenedField S (ψ.coreSlice s x).normalized y) 0)^2) volume := by
    exact ((aestronglyMeasurable_const.sub (normalized_corePotential_aestronglyMeasurable ψ s y)).sup
      aestronglyMeasurable_const).pow 2
  have hb : ∀ᵐ x ∂volume, ‖(max (coreScreenedField S (ψ.coreSlice s x).normalized y) 0)^2‖ ≤ (attraction S y)^2 := by
    filter_upwards [] with x
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (le_max_right _ _) (coreField_positive_le S _ y) 2
  exact (mass_coreSlice_integrable ψ s).mul_bdd hm hb

theorem conditional_positive_field_gain {J m k : ℕ} (S : Nuclei J) (ψ : H1Vector (m+k))
    (hanti : ∀ s, ∀ᵐ x, Antisymmetric (ψ.coreSlice s x))
    {a : ℝ} (ha : 0 < a) (y : Space) (A : Set Space) (hA : IsClosed A)
    (hs : ∀ s, ∀ᵐ x, SpatiallySupported (ψ.coreSlice s x).normalized A)
    (hcore : ∀ z ∈ A, 3*a ≤ ‖z-y‖) (hnuc : ∀ j, 3*a ≤ ‖S.position j-y‖)
    {E : ℝ} (hE : (E : EReal) ≤ unrestrictedFormBottom S) :
    a/(16*ballTrialCoefficient)*sliceExpectation ψ (fun s x =>
      (max (coreScreenedField S (ψ.coreSlice s x).normalized y) 0)^2) ≤
      sliceExpectation ψ (fun s x => form S (ψ.coreSlice s x).normalized)-E*mass ψ+
        (4*ballTrialCoefficient*(screenBaseMass a)^2/a)*mass ψ := by
  have hi := normalized_coreForm_weight_integrable S ψ
  have hp := coreField_positive_square_weight_integrable S ψ
  let c : ℝ := a/(16*ballTrialCoefficient)
  let d : ℝ := 4*ballTrialCoefficient*(screenBaseMass a)^2/a
  have HD (s : Spins m) : Integrable (fun x => mass (ψ.coreSlice s x)*(form S (ψ.coreSlice s x).normalized-
      c*(max (coreScreenedField S (ψ.coreSlice s x).normalized y) 0)^2+d-E)) := by
    apply (((hi s).sub (by simpa only [mul_left_comm (mass _) c] using (hp s y).const_mul c)).add
      (by simpa only [mul_comm (mass _) d] using (mass_coreSlice_integrable ψ s).const_mul d)).sub
      (by simpa only [mul_comm (mass _) E] using (mass_coreSlice_integrable ψ s).const_mul E) |>.congr
    exact Eventually.of_forall (fun x => by dsimp only [Pi.sub_apply,Pi.add_apply]; ring)
  have H : 0 ≤ sliceExpectation ψ (fun s x => form S (ψ.coreSlice s x).normalized-
      c*(max (coreScreenedField S (ψ.coreSlice s x).normalized y) 0)^2+d-E) := by
    apply Finset.sum_nonneg
    intro s _
    apply integral_nonneg_of_ae
    filter_upwards [hanti s,hs s] with x hax hsx
    by_cases hz : mass (ψ.coreSlice s x)=0
    · simp [hz]
    · have hpx : 0 < mass (ψ.coreSlice s x) := lt_of_le_of_ne (mass_nonneg _) (Ne.symm hz)
      have HG := positive_field_core_gain S (ψ.coreSlice s x).normalized hax.normalized
        (mass_normalized _ hpx) ha (screenBaseMass_nonneg a) (screenBaseMass_scale ha)
        (screenBaseMass_cuberoot_scale ha) y A hA hsx hcore hnuc
      have HE := EReal.coe_le_coe_iff.mp (hE.trans HG)
      apply mul_nonneg hpx.le
      dsimp [c,d]
      convert sub_nonneg.mpr HE using 1
      first | rfl | ring
  have HH : sliceExpectation ψ (fun s x => form S (ψ.coreSlice s x).normalized-
      c*(max (coreScreenedField S (ψ.coreSlice s x).normalized y) 0)^2+d-E) =
      sliceExpectation ψ (fun s x => form S (ψ.coreSlice s x).normalized)-
      c*sliceExpectation ψ (fun s x => (max (coreScreenedField S (ψ.coreSlice s x).normalized y) 0)^2)+
      d*mass ψ-E*mass ψ := by
    have hconst (v : ℝ) (s : Spins m) : Integrable (fun x => mass (ψ.coreSlice s x)*v) :=
      (mass_coreSlice_integrable ψ s).mul_const v
    have hc (s : Spins m) : Integrable (fun x => mass (ψ.coreSlice s x)*(c*
        (max (coreScreenedField S (ψ.coreSlice s x).normalized y) 0)^2)) := by
      simpa only [mul_left_comm (mass _) c] using (hp s y).const_mul c
    have hd (s : Spins m) : Integrable (fun x => mass (ψ.coreSlice s x)*(form S (ψ.coreSlice s x).normalized-
        c*(max (coreScreenedField S (ψ.coreSlice s x).normalized y) 0)^2)) := by
      exact ((hi s).sub (hc s)).congr (Eventually.of_forall (fun x => by dsimp; ring))
    have he (s : Spins m) : Integrable (fun x => mass (ψ.coreSlice s x)*(form S (ψ.coreSlice s x).normalized-
        c*(max (coreScreenedField S (ψ.coreSlice s x).normalized y) 0)^2+d)) := by
      exact ((hd s).add (hconst d s)).congr (Eventually.of_forall (fun x => by dsimp; ring))
    rw [sliceExpectation_sub ψ _ _ he (hconst E),sliceExpectation_add ψ _ _ hd (hconst d),
      sliceExpectation_sub ψ _ _ hi hc,sliceExpectation_const_mul,
      sliceExpectation_number,sliceExpectation_number]
  rw [HH] at H
  dsimp [c,d] at H
  linarith

end Coulomb
end

end
end

end OAI
