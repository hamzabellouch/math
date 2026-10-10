import Mathlib
import OAI.Analysis.CoulombIonization.Variational.CutCoreExcess
import OAI.Analysis.CoulombIonization.Variational.WeightedCauchy
import OAI.Analysis.CoulombIonization.FieldAnalysis.FreshFieldTower

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped BigOperators

lemma coreSlice_envelope_first_integrable {N M : ℕ} {ψ : FormVector (N+M)}
    (ha : CoreAntisymmetric ψ) (hψ : SobolevVector ψ) {Z lam B : ℝ}
    (hZ : 0 ≤ Z) (hlam : 0 < lam) (hB : 0 < B) (t : Spins M) :
    Integrable (fun u => coreCapEnvelope Z lam B (coreSlice ψ t u)*formMass (coreSlice ψ t u)) := by
  have hi := (hψ.coreSlice_mass_integrable t).add
    (coreSlice_envelope_square_integrable ha hψ hZ hlam hB t)
  apply hi.mono' ((hψ.coreSlice_envelope_measurable Z lam B t).mul
    (hψ.coreSlice_mass_integrable t).aestronglyMeasurable)
  filter_upwards [] with u
  dsimp only [Pi.mul_apply, Pi.add_apply]
  rw [Real.norm_of_nonneg (mul_nonneg (coreCapEnvelope_nonneg Z lam hB _) (formMass_nonneg _))]
  have hh : coreCapEnvelope Z lam B (coreSlice ψ t u) ≤
      1+(coreCapEnvelope Z lam B (coreSlice ψ t u))^2 := by
    nlinarith [sq_nonneg (coreCapEnvelope Z lam B (coreSlice ψ t u)-1)]
  nlinarith [mul_le_mul_of_nonneg_right hh (formMass_nonneg (coreSlice ψ t u))]

lemma fock_cut_envelope_first_le_sqrt {L : ℕ}
    (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ a, (p a).value x^2 = 1) {ψ : FormVector L}
    (hψ : SobolevFermion ψ) (hm : formMass ψ = 1) {Z lam B : ℝ}
    (hZ : 0 ≤ Z) (hlam : 0 < lam) (hB : 0 < B) :
    (∑ c : Fin L → Fin 2, ∑ t : Spins (cutOutNumber c), ∫ u,
      coreCapEnvelope Z lam B (coreSlice (orderedCutForm p hp ψ c) t u)*
        formMass (coreSlice (orderedCutForm p hp ψ c) t u)) ≤
      Real.sqrt (∑ c : Fin L → Fin 2, ∑ t : Spins (cutOutNumber c), ∫ u,
        formMass (coreSlice (orderedCutForm p hp ψ c) t u)*
          (coreCapEnvelope Z lam B (coreSlice (orderedCutForm p hp ψ c) t u))^2) := by
  have hh := weighted_sum_integral_cauchy
    (ι := Σ c : Fin L → Fin 2, Spins (cutOutNumber c))
    (X := fun cs => Configuration (cutOutNumber cs.1)) (fun _ => volume)
    (fun cs u => formMass (coreSlice (orderedCutForm p hp ψ cs.1) cs.2 u))
    (fun cs u => coreCapEnvelope Z lam B (coreSlice (orderedCutForm p hp ψ cs.1) cs.2 u))
    (fun _ _ => (1:ℝ)) (fun _ _ => formMass_nonneg _)
    (fun cs => by simpa only [mul_comm] using (coreSlice_envelope_square_integrable
      (orderedCutForm_core_antisymmetric p hp hψ cs.1)
      (orderedCutForm_sobolev p hp hψ.sobolevVector cs.1) hZ hlam hB cs.2))
    (fun cs => by simpa only [one_pow,one_mul] using
      (orderedCutForm_sobolev p hp hψ.sobolevVector cs.1).coreSlice_mass_integrable cs.2)
    (fun cs => by simpa only [mul_one] using (coreSlice_envelope_first_integrable
      (orderedCutForm_core_antisymmetric p hp hψ cs.1)
      (orderedCutForm_sobolev p hp hψ.sobolevVector cs.1) hZ hlam hB cs.2))
  simpa only [Fintype.sum_sigma,mul_one,one_pow,one_mul,
    SobolevVector.integral_coreSlice_mass (orderedCutForm_sobolev p hp hψ.sobolevVector _),
    orderedCutForm_mass_sum p hp hψ.sobolevVector,hm,Real.sqrt_one,mul_comm] using hh

lemma normalizedCoreField_le_cut_envelope {L : ℕ}
    (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ a, (p a).value x^2 = 1) {ψ : FormVector L}
    (hψ : SobolevFermion ψ) (hm : formMass ψ = 1) (y : Space) {B : ℝ}
    (hB : 0 < B) (hnuc : 2*B ≤ ‖y‖)
    (hv : ∀ x ∈ ball y (2*B), (p 0).value x = 0)
    (hd : ∀ x ∈ ball y (2*B), ∀ a, lineDeriv ℝ (p 0).value x (spaceDirections a) = 0)
    {Z lam : ℝ} (hZ : 0 ≤ Z) (hlam : 0 < lam) :
    normalizedCoreField Z lam ψ y ≤
      ∑ c : Fin L → Fin 2, ∑ t : Spins (cutOutNumber c), ∫ u,
        coreCapEnvelope Z lam B (coreSlice (orderedCutForm p hp ψ c) t u)*
          formMass (coreSlice (orderedCutForm p hp ψ c) t u) := by
  have ht := fresh_cut_field_tower p hp hψ.sobolevVector Z lam y
  rw [integral_rawPotential_formRawLaw hψ.sobolevVector] at ht
  have he : (Z/‖y‖-lam)*formMass ψ-coreCoulombAt ψ y = normalizedCoreField Z lam ψ y := by
    simp only [normalizedCoreField,hm,mul_one,div_one]
    ring
  rw [he] at ht
  rw [←ht]
  apply Finset.sum_le_sum; intro c _
  apply Finset.sum_le_sum; intro t _
  have hχ := orderedCutForm_sobolev p hp hψ.sobolevVector c
  have hleft : Integrable (fun u =>
      (normalizedCoreField Z lam (coreSlice (orderedCutForm p hp ψ c) t u) y-rawPotential y u)*
        formMass (coreSlice (orderedCutForm p hp ψ c) t u)) := by
    have hi := (normalizedCoreField_weighted_integrable hχ t Z lam y).sub
      (rawPotential_coreSlice_integrable hχ t y)
    convert hi using 1
    ext u
    simp only [Pi.sub_apply]
    ring
  apply integral_mono_ae hleft
    (coreSlice_envelope_first_integrable (orderedCutForm_core_antisymmetric p hp hψ c) hχ hZ hlam hB t)
  apply (fresh_cut_field_envelope p hp hψ c y hB hnuc hv hd hZ hlam t).mono
  intro u hu
  apply mul_le_mul_of_nonneg_right _ (formMass_nonneg _)
  exact (sub_le_self _ (rawPotential_nonneg y u)).trans
    (hu y (mem_closedBall_self hB.le))

theorem parent_field_sq_le_fresh_core_excess {L : ℕ}
    (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ a, (p a).value x^2 = 1) {ψ : FormVector L}
    (hψ : SobolevFermion ψ) (hm : formMass ψ = 1) (y : Space) {B : ℝ}
    (hB : 0 < B) (hnuc : 2*B ≤ ‖y‖)
    (hv : ∀ x ∈ ball y (2*B), (p 0).value x = 0)
    (hd : ∀ x ∈ ball y (2*B), ∀ a, lineDeriv ℝ (p 0).value x (spaceDirections a) = 0)
    {Z lam : ℝ} (hZ : 0 ≤ Z) (hlam : 0 < lam) :
    (max (normalizedCoreField Z lam ψ y) 0)^2 ≤
      2*packetFieldConstant^2*((1/B^4+1/B)^2+
        (∑ c : Fin L → Fin 2, cutCoreExcess p hp Z lam ψ c)/B) := by
  let Q := ∑ c : Fin L → Fin 2, ∑ t : Spins (cutOutNumber c), ∫ u,
    formMass (coreSlice (orderedCutForm p hp ψ c) t u)*
      (coreCapEnvelope Z lam B (coreSlice (orderedCutForm p hp ψ c) t u))^2
  have hQ : 0 ≤ Q := Finset.sum_nonneg (fun c _ => Finset.sum_nonneg
    (fun t _ => integral_nonneg (fun u => mul_nonneg (formMass_nonneg _) (sq_nonneg _))))
  have hh : max (normalizedCoreField Z lam ψ y) 0 ≤ Real.sqrt Q :=
    max_le ((normalizedCoreField_le_cut_envelope p hp hψ hm y hB hnuc hv hd hZ hlam).trans
      (fock_cut_envelope_first_le_sqrt p hp hψ hm hZ hlam hB)) (Real.sqrt_nonneg Q)
  have hsq : (max (normalizedCoreField Z lam ψ y) 0)^2 ≤ Q := by
    have h := (sq_le_sq₀ (le_max_right _ _) (Real.sqrt_nonneg Q)).mpr hh
    rwa [Real.sq_sqrt hQ] at h
  apply hsq.trans
  simpa only [hm,mul_one] using fock_cut_envelope_square p hp hψ hZ hlam hB

open MeasureTheory Filter Set Metric
open scoped BigOperators

lemma fock_cut_envelope_first_le_sqrt_mass {L : ℕ}
    (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ a, (p a).value x^2 = 1) {ψ : FormVector L}
    (hψ : SobolevFermion ψ) {Z lam B : ℝ}
    (hZ : 0 ≤ Z) (hlam : 0 < lam) (hB : 0 < B) :
    (∑ c : Fin L → Fin 2, ∑ t : Spins (cutOutNumber c), ∫ u,
      coreCapEnvelope Z lam B (coreSlice (orderedCutForm p hp ψ c) t u)*
        formMass (coreSlice (orderedCutForm p hp ψ c) t u)) ≤
      Real.sqrt (∑ c : Fin L → Fin 2, ∑ t : Spins (cutOutNumber c), ∫ u,
        formMass (coreSlice (orderedCutForm p hp ψ c) t u)*
          (coreCapEnvelope Z lam B (coreSlice (orderedCutForm p hp ψ c) t u))^2)*
          Real.sqrt (formMass ψ) := by
  have hh := weighted_sum_integral_cauchy
    (ι := Σ c : Fin L → Fin 2, Spins (cutOutNumber c))
    (X := fun cs => Configuration (cutOutNumber cs.1)) (fun _ => volume)
    (fun cs u => formMass (coreSlice (orderedCutForm p hp ψ cs.1) cs.2 u))
    (fun cs u => coreCapEnvelope Z lam B (coreSlice (orderedCutForm p hp ψ cs.1) cs.2 u))
    (fun _ _ => (1:ℝ)) (fun _ _ => formMass_nonneg _)
    (fun cs => by simpa only [mul_comm] using (coreSlice_envelope_square_integrable
      (orderedCutForm_core_antisymmetric p hp hψ cs.1)
      (orderedCutForm_sobolev p hp hψ.sobolevVector cs.1) hZ hlam hB cs.2))
    (fun cs => by simpa only [one_pow,one_mul] using
      (orderedCutForm_sobolev p hp hψ.sobolevVector cs.1).coreSlice_mass_integrable cs.2)
    (fun cs => by simpa only [mul_one] using (coreSlice_envelope_first_integrable
      (orderedCutForm_core_antisymmetric p hp hψ cs.1)
      (orderedCutForm_sobolev p hp hψ.sobolevVector cs.1) hZ hlam hB cs.2))
  simpa only [Fintype.sum_sigma,mul_one,one_pow,one_mul,
    SobolevVector.integral_coreSlice_mass (orderedCutForm_sobolev p hp hψ.sobolevVector _),
    orderedCutForm_mass_sum p hp hψ.sobolevVector,mul_comm] using hh

lemma normalizedCoreField_mass_le_cut_envelope {L : ℕ}
    (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ a, (p a).value x^2 = 1) {ψ : FormVector L}
    (hψ : SobolevFermion ψ) (y : Space) {B : ℝ}
    (hB : 0 < B) (hnuc : 2*B ≤ ‖y‖)
    (hv : ∀ x ∈ ball y (2*B), (p 0).value x = 0)
    (hd : ∀ x ∈ ball y (2*B), ∀ a, lineDeriv ℝ (p 0).value x (spaceDirections a) = 0)
    {Z lam : ℝ} (hZ : 0 ≤ Z) (hlam : 0 < lam) :
    normalizedCoreField Z lam ψ y*formMass ψ ≤
      ∑ c : Fin L → Fin 2, ∑ t : Spins (cutOutNumber c), ∫ u,
        coreCapEnvelope Z lam B (coreSlice (orderedCutForm p hp ψ c) t u)*
          formMass (coreSlice (orderedCutForm p hp ψ c) t u) := by
  have ht := fresh_cut_field_tower p hp hψ.sobolevVector Z lam y
  rw [integral_rawPotential_formRawLaw hψ.sobolevVector] at ht
  have he : (Z/‖y‖-lam)*formMass ψ-coreCoulombAt ψ y = normalizedCoreField Z lam ψ y*formMass ψ := by
    rw [normalizedCoreField_mul_mass hψ.sobolevVector]
    ring
  rw [he] at ht
  rw [←ht]
  apply Finset.sum_le_sum; intro c _
  apply Finset.sum_le_sum; intro t _
  have hχ := orderedCutForm_sobolev p hp hψ.sobolevVector c
  have hleft : Integrable (fun u =>
      (normalizedCoreField Z lam (coreSlice (orderedCutForm p hp ψ c) t u) y-rawPotential y u)*
        formMass (coreSlice (orderedCutForm p hp ψ c) t u)) := by
    have hi := (normalizedCoreField_weighted_integrable hχ t Z lam y).sub
      (rawPotential_coreSlice_integrable hχ t y)
    convert hi using 1
    ext u
    simp only [Pi.sub_apply]
    ring
  apply integral_mono_ae hleft
    (coreSlice_envelope_first_integrable (orderedCutForm_core_antisymmetric p hp hψ c) hχ hZ hlam hB t)
  apply (fresh_cut_field_envelope p hp hψ c y hB hnuc hv hd hZ hlam t).mono
  intro u hu
  apply mul_le_mul_of_nonneg_right _ (formMass_nonneg _)
  exact (sub_le_self _ (rawPotential_nonneg y u)).trans
    (hu y (mem_closedBall_self hB.le))

theorem parent_field_sq_mass_le_fresh_core_excess {L : ℕ}
    (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ a, (p a).value x^2 = 1) {ψ : FormVector L}
    (hψ : SobolevFermion ψ) (y : Space) {B : ℝ}
    (hB : 0 < B) (hnuc : 2*B ≤ ‖y‖)
    (hv : ∀ x ∈ ball y (2*B), (p 0).value x = 0)
    (hd : ∀ x ∈ ball y (2*B), ∀ a, lineDeriv ℝ (p 0).value x (spaceDirections a) = 0)
    {Z lam : ℝ} (hZ : 0 ≤ Z) (hlam : 0 < lam) :
    (max (normalizedCoreField Z lam ψ y) 0)^2*formMass ψ ≤
      2*packetFieldConstant^2*((1/B^4+1/B)^2*formMass ψ+
        (∑ c : Fin L → Fin 2, cutCoreExcess p hp Z lam ψ c)/B) := by
  let Q := ∑ c : Fin L → Fin 2, ∑ t : Spins (cutOutNumber c), ∫ u,
    formMass (coreSlice (orderedCutForm p hp ψ c) t u)*
      (coreCapEnvelope Z lam B (coreSlice (orderedCutForm p hp ψ c) t u))^2
  have hQ : 0 ≤ Q := Finset.sum_nonneg (fun c _ => Finset.sum_nonneg
    (fun t _ => integral_nonneg (fun u => mul_nonneg (formMass_nonneg _) (sq_nonneg _))))
  have hsq : (max (normalizedCoreField Z lam ψ y) 0)^2*formMass ψ ≤ Q := by
    by_cases hm : formMass ψ = 0
    · simpa only [hm,mul_zero] using hQ
    have hmass : 0 < formMass ψ := lt_of_le_of_ne (formMass_nonneg _) (Ne.symm hm)
    have hh : max (normalizedCoreField Z lam ψ y) 0*formMass ψ ≤
        Real.sqrt Q*Real.sqrt (formMass ψ) := by
      rw [max_mul_of_nonneg _ _ hmass.le,zero_mul]
      exact max_le
        ((normalizedCoreField_mass_le_cut_envelope p hp hψ y hB hnuc hv hd hZ hlam).trans
          (fock_cut_envelope_first_le_sqrt_mass p hp hψ hZ hlam hB))
        (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    have hh2 := (sq_le_sq₀
      (mul_nonneg (le_max_right _ _) hmass.le)
      (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).mpr hh
    rw [mul_pow, mul_pow, Real.sq_sqrt hQ, Real.sq_sqrt hmass.le] at hh2
    exact (mul_le_mul_iff_left₀ hmass).mp (by nlinarith only [hh2])
  exact hsq.trans (fock_cut_envelope_square p hp hψ hZ hlam hB)

end CoulombAtom

end

end OAI
