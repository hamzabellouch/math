import Mathlib
import OAI.Analysis.CoulombRadii.RandomFields.JointSlice
import OAI.Analysis.CoulombRadii.RandomFields.LocalizedEnsemble

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
noncomputable section
namespace Coulomb

lemma positive_square_ballCloud_integral_le {J : ℕ} (S : Nuclei J) (f : Space → ℝ)
    (hm : AEStronglyMeasurable f volume) (hbound : ∀ z, f z ≤ attraction S z)
    {a : ℝ} (ha : 0 < a) (y : Space) (hnuc : ∀ j, 2*a ≤ ‖S.position j-y‖) :
    (∫ z, (max (f z) 0)^2*ballCloud y a 1 z) ≤ (totalCharge S/a)^2 := by
  calc
    _ ≤ ∫ z, (totalCharge S/a)^2*ballCloud y a 1 z := by
      apply integral_mono (positive_square_ballCloud_integrable S f hm hbound ha y hnuc)
        ((ballCloud_integrable a 1 y).const_mul _)
      intro z
      by_cases hz : z-y ∈ Metric.ball (0:Space) a
      · have hdist : ‖z-y‖ < a := by simpa only [Metric.mem_ball,dist_zero_right] using hz
        have hsep (j : Fin J) : a ≤ ‖z-S.position j‖ := by
          have ht : ‖S.position j-y‖ ≤ ‖S.position j-z‖+‖z-y‖ := by
            simpa only [dist_eq_norm] using dist_triangle (S.position j) z y
          rw [norm_sub_rev (S.position j) z] at ht
          linarith [hnuc j]
        have hP : max (f z) 0 ≤ totalCharge S/a :=
          (max_le (hbound z) (attraction_nonneg S z)).trans (attraction_le_totalCharge_div S ha z hsep)
        exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (le_max_right _ _) hP 2)
          (uniformBall_nonneg ha zero_le_one (z-y))
      · simp only [ballCloud,uniformBall,indicator_of_notMem hz,mul_zero,le_refl]
    _ = _ := by rw [integral_const_mul,ballCloud_mass ha,mul_one]

def localFarCap {J m k : ℕ} (S : Nuclei J) (u : H1Vector k)
    (x : Configuration m) (y : Space) (a : ℝ) : ℝ :=
  Real.sqrt (8*(∫ v, (max (recordedFarField S u x {z | 4*a ≤ ‖z-y‖} v) 0)^2*
    ballCloud y (2*a) 1 v))

lemma localFarCap_nonneg {J m k : ℕ} (S : Nuclei J) (u : H1Vector k)
    (x : Configuration m) (y : Space) (a : ℝ) : 0 ≤ localFarCap S u x y a := Real.sqrt_nonneg _

lemma localFarCap_sq {J m k : ℕ} (S : Nuclei J) (u : H1Vector k)
    (x : Configuration m) (y : Space) {a : ℝ} (ha : 0 < a) :
    (localFarCap S u x y a)^2=8*(∫ v,
      (max (recordedFarField S u x {z | 4*a ≤ ‖z-y‖} v) 0)^2*ballCloud y (2*a) 1 v) := by
  apply Real.sq_sqrt
  apply mul_nonneg (by norm_num)
  exact integral_nonneg (fun v => mul_nonneg (sq_nonneg _) (uniformBall_nonneg (by linarith) zero_le_one (v-y)))

lemma localFarCap_le {J m k : ℕ} (S : Nuclei J) (u : H1Vector k)
    (x : Configuration m) (y : Space) {a : ℝ} (ha : 0 < a)
    (hnuc : ∀ j, 4*a ≤ ‖S.position j-y‖) :
    localFarCap S u x y a ≤ Real.sqrt (8*(totalCharge S/(2*a))^2) := by
  apply Real.sqrt_le_sqrt
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply positive_square_ballCloud_integral_le S _
    (recordedFarField_aestronglyMeasurable S u x (isClosed_le continuous_const (by fun_prop)).measurableSet)
    (recordedFarField_le_attraction S u x _) (by positivity) y
  intro j
  nlinarith [hnuc j]

lemma localFarCap_normalized_slice_aestronglyMeasurable {J m k : ℕ} (S : Nuclei J)
    (u : H1Vector (m+k)) (s : Spins m) (y : Space) (a : ℝ) :
    AEStronglyMeasurable (fun x => localFarCap S (u.coreSlice s x).normalized x y a) volume := by
  have hf := recordedFarField_normalized_slice_joint S u s
    (isClosed_le continuous_const (by fun_prop) : IsClosed {z : Space | 4*a ≤ ‖z-y‖}).measurableSet
  have H : AEStronglyMeasurable (fun z : Configuration m × Space =>
      (max (recordedFarField S (u.coreSlice s z.1).normalized z.1 {z | 4*a ≤ ‖z-y‖} z.2) 0)^2*
        ballCloud y (2*a) 1 z.2) (volume.prod volume) :=
    ((hf.sup aestronglyMeasurable_const).pow 2).mul
      ((ballCloud_measurable (2*a) 1 y).comp measurable_snd).aestronglyMeasurable
  exact Real.continuous_sqrt.comp_aestronglyMeasurable (H.integral_prod_right'.const_mul 8)

lemma localFarCap_weight_integrable {J m k : ℕ} (S : Nuclei J)
    (u : H1Vector (m+k)) (s : Spins m) {a : ℝ} (ha : 0 < a) (y : Space)
    (hnuc : ∀ j, 4*a ≤ ‖S.position j-y‖) (q : ℕ) :
    Integrable (fun x => mass (u.coreSlice s x)*(localFarCap S (u.coreSlice s x).normalized x y a)^q) := by
  apply (mass_coreSlice_integrable u s).mul_bdd ((localFarCap_normalized_slice_aestronglyMeasurable S u s y a).pow q)
  filter_upwards [] with x
  change ‖(localFarCap S (u.coreSlice s x).normalized x y a)^q‖ ≤ (Real.sqrt (8*(totalCharge S/(2*a))^2))^q
  rw [Real.norm_of_nonneg (pow_nonneg (localFarCap_nonneg _ _ _ _ _) q)]
  exact pow_le_pow_left₀ (localFarCap_nonneg _ _ _ _ _) (localFarCap_le S _ x y ha hnuc) q

theorem sliceExpectation_localFarCap_sq {J m k : ℕ} (S : Nuclei J)
    (u : H1Vector (m+k)) {a : ℝ} (ha : 0 < a) (y : Space)
    (hnuc : ∀ j, 4*a ≤ ‖S.position j-y‖) :
    sliceExpectation u (fun s x => (localFarCap S (u.coreSlice s x).normalized x y a)^2) =
      8*(∫ v, (sliceExpectation u (fun s x =>
        (max (recordedFarField S (u.coreSlice s x).normalized x {z | 4*a ≤ ‖z-y‖} v) 0)^2))*
          ballCloud y (2*a) 1 v) := by
  simp only [localFarCap_sq S _ _ y ha]
  rw [sliceExpectation_const_mul,sliceExpectation_farSquare_ballCloud S u
    (isClosed_le continuous_const (by fun_prop)).measurableSet (by positivity) y (fun j => by nlinarith [hnuc j])]

lemma pairPotential_nonneg_pointwise {m : ℕ} (x : Configuration m) : 0 ≤ pairPotential x := by
  unfold pairPotential
  apply Finset.sum_nonneg
  intro i hi
  apply Finset.sum_nonneg
  intro j hj
  split_ifs <;> first | exact inv_nonneg.mpr (norm_nonneg _) | exact le_rfl

theorem conditionalOutCost_lower_local {J m k : ℕ} (S : Nuclei J)
    (u : H1Vector (m+k)) {a : ℝ} (ha : 0 < a) (y : Space)
    (hnuc : ∀ j, 4*a ≤ ‖S.position j-y‖)
    (hsupp : ∀ s, ∀ᵐ x, mass (u.coreSlice s x) ≠0 → ∀ i, ‖position x i-y‖ ≤ a) :
    -(m:ℝ)*sliceExpectation u (fun s x => localFarCap S (u.coreSlice s x).normalized x y a)-
      (m:ℝ)^2/(3*a)*mass u ≤ conditionalOutCost S u := by
  have H (s : Spins m) :
      ∫ x, mass (u.coreSlice s x)*(-(m:ℝ)*localFarCap S (u.coreSlice s x).normalized x y a-(m:ℝ)^2/(3*a)) ≤
      ∫ x, mass (u.coreSlice s x)*(pairPotential x-
        ∑ i : Fin m, coreScreenedField S (u.coreSlice s x).normalized (position x i)) := by
    have hic : Integrable (fun x => mass (u.coreSlice s x)*localFarCap S (u.coreSlice s x).normalized x y a) := by
      simpa only [pow_one] using localFarCap_weight_integrable S u s ha y hnuc 1
    apply integral_mono_ae
    · convert (hic.const_mul (-(m:ℝ))).sub ((mass_coreSlice_integrable u s).mul_const ((m:ℝ)^2/(3*a))) using 1
      funext x
      dsimp
      ring
    · exact conditionalOutCost_weight_integrable S u s
    · filter_upwards [hsupp s] with x hx
      by_cases hm : mass (u.coreSlice s x)=0
      · simp only [hm,zero_mul,le_refl]
      · apply mul_le_mul_of_nonneg_left _ (mass_nonneg _)
        have hcap : (∑ i : Fin m, coreScreenedField S (u.coreSlice s x).normalized (position x i)) ≤
            (m:ℝ)*(localFarCap S (u.coreSlice s x).normalized x y a+(m:ℝ)/(3*a)) := by
          calc
            _ ≤ ∑ _i : Fin m, (localFarCap S (u.coreSlice s x).normalized x y a+(m:ℝ)/(3*a)) := by
              apply Finset.sum_le_sum
              intro i hi
              exact coreField_le_local_far_cap S (u.coreSlice s x).normalized x ha y (position x i) (hx hm i) hnuc
            _ = _ := by simp; ring
        have hp := pairPotential_nonneg_pointwise x
        have he : (m:ℝ)*((m:ℝ)/(3*a))=(m:ℝ)^2/(3*a) := by ring
        nlinarith
  have HH := Finset.sum_le_sum (fun s (_ : s ∈ Finset.univ) => H s)
  have hc (s : Spins m) : Integrable (fun x => mass (u.coreSlice s x)*localFarCap S (u.coreSlice s x).normalized x y a) := by
    simpa only [pow_one] using localFarCap_weight_integrable S u s ha y hnuc 1
  have he (s : Spins m) :
      (∫ x, mass (u.coreSlice s x)*(-(m:ℝ)*localFarCap S (u.coreSlice s x).normalized x y a-(m:ℝ)^2/(3*a))) =
      -(m:ℝ)*(∫ x, mass (u.coreSlice s x)*localFarCap S (u.coreSlice s x).normalized x y a)-
        (m:ℝ)^2/(3*a)*(∫ x, mass (u.coreSlice s x)) := by
    simp only [mul_sub,mul_left_comm (mass _) (-(m:ℝ))]
    rw [integral_sub ((hc s).const_mul _) ((mass_coreSlice_integrable u s).mul_const _),integral_const_mul,integral_mul_const]
    ring
  simp only [he,Finset.sum_sub_distrib,←Finset.mul_sum,integral_mass_coreSlice] at HH
  exact HH.trans (le_add_of_nonneg_left (outerKinetic_nonneg u))

end Coulomb
end

end
end

end OAI
