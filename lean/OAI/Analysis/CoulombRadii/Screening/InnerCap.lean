import Mathlib
import OAI.Analysis.CoulombRadii.RandomFields.InnerFieldRMS

namespace OAI

section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical Topology
noncomputable section
namespace Coulomb

def innerLocalCap {J m k : ℕ} (S : Nuclei J) (v : H1Vector k)
    (x : Configuration m) (h : ℝ) (z : Space) (a : ℝ) : ℝ :=
  Real.sqrt (8*(∫ w, (max (recordedFarField S v x (Metric.ball 0 h) w) 0)^2*
    ballCloud z (2*a) 1 w))
lemma innerLocalCap_nonneg {J m k : ℕ} (S : Nuclei J) (v : H1Vector k)
    (x : Configuration m) (h : ℝ) (z : Space) (a : ℝ) :
    0 ≤ innerLocalCap S v x h z a := Real.sqrt_nonneg _
lemma innerLocalCap_sq {J m k : ℕ} (S : Nuclei J) (v : H1Vector k)
    (x : Configuration m) (h : ℝ) (z : Space) {a : ℝ} (ha : 0<a) :
    (innerLocalCap S v x h z a)^2 =
      8*(∫ w, (max (recordedFarField S v x (Metric.ball 0 h) w) 0)^2*ballCloud z (2*a) 1 w) := by
  apply Real.sq_sqrt
  exact mul_nonneg (by norm_num) (integral_nonneg (fun w => mul_nonneg (sq_nonneg _)
    (uniformBall_nonneg (by positivity) zero_le_one (w-z))))
lemma innerLocalCap_le {J m k : ℕ} (S : Nuclei J) (v : H1Vector k)
    (x : Configuration m) (h : ℝ) (z : Space) {a : ℝ} (ha : 0<a)
    (hnuc : ∀ j, 4*a ≤ ‖S.position j-z‖) :
    innerLocalCap S v x h z a ≤ Real.sqrt (8*(totalCharge S/(2*a))^2) := by
  apply Real.sqrt_le_sqrt
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  exact positive_square_ballCloud_integral_le S _
    (recordedFarField_aestronglyMeasurable S v x measurableSet_ball)
    (recordedFarField_le_attraction S v x _) (by positivity) z (fun j => by nlinarith [hnuc j])
lemma innerLocalCap_normalized_slice_aestronglyMeasurable {J m k : ℕ} (S : Nuclei J)
    (v : H1Vector (m+k)) (s : Spins m) (h : ℝ) (z : Space) (a : ℝ) :
    AEStronglyMeasurable (fun x => innerLocalCap S (v.coreSlice s x).normalized x h z a) volume := by
  have hf := recordedFarField_normalized_slice_joint S v s (measurableSet_ball (x:=(0:Space)) (ε:=h))
  have H : AEStronglyMeasurable (fun p : Configuration m × Space =>
      (max (recordedFarField S (v.coreSlice s p.1).normalized p.1 (Metric.ball 0 h) p.2) 0)^2*
        ballCloud z (2*a) 1 p.2) (volume.prod volume) :=
    ((hf.sup aestronglyMeasurable_const).pow 2).mul
      ((ballCloud_measurable (2*a) 1 z).comp measurable_snd).aestronglyMeasurable
  exact Real.continuous_sqrt.comp_aestronglyMeasurable (H.integral_prod_right'.const_mul 8)
lemma innerLocalCap_weight_integrable {J m k : ℕ} (S : Nuclei J) (v : H1Vector (m+k))
    (s : Spins m) (h : ℝ) (z : Space) {a : ℝ} (ha : 0<a)
    (hnuc : ∀ j, 4*a ≤ ‖S.position j-z‖) (q : ℕ) :
    Integrable (fun x => mass (v.coreSlice s x)*(innerLocalCap S (v.coreSlice s x).normalized x h z a)^q) := by
  apply (mass_coreSlice_integrable v s).mul_bdd ((innerLocalCap_normalized_slice_aestronglyMeasurable S v s h z a).pow q)
  filter_upwards [] with x
  change ‖(innerLocalCap S (v.coreSlice s x).normalized x h z a)^q‖ ≤ (Real.sqrt (8*(totalCharge S/(2*a))^2))^q
  rw [Real.norm_of_nonneg (pow_nonneg (innerLocalCap_nonneg _ _ _ _ _ _) q)]
  exact pow_le_pow_left₀ (innerLocalCap_nonneg _ _ _ _ _ _) (innerLocalCap_le S _ x h z ha hnuc) q

lemma innerLocalCap_dominates {J m k : ℕ} (S : Nuclei J) (v : H1Vector k)
    (x : Configuration m) (h : ℝ) (z w : Space) {a : ℝ} (ha : 0<a)
    (hw : ‖w-z‖≤a) (hcore : ∀ q∈Metric.ball (0:Space) h, 4*a≤‖q-z‖)
    (hnuc : ∀ j, 4*a≤‖S.position j-z‖) :
    max (recordedFarField S v x (Metric.ball 0 h) w) 0 ≤ innerLocalCap S v x h z a := by
  apply (sq_le_sq₀ (le_max_right _ _) (innerLocalCap_nonneg _ _ _ _ _ _)).mp
  rw [innerLocalCap_sq S v x h z ha]
  exact recordedFarField_positive_submean_square S v x measurableSet_ball ha z w hw hcore hnuc

lemma sliceExpectation_innerLocalCap_sq {J m k : ℕ} (S : Nuclei J)
    (v : H1Vector (m+k)) (h : ℝ) (z : Space) {a : ℝ} (ha : 0<a)
    (hnuc : ∀ j, 4*a≤‖S.position j-z‖) :
    sliceExpectation v (fun s x => (innerLocalCap S (v.coreSlice s x).normalized x h z a)^2) =
      8*(∫ w, (sliceExpectation v (fun s x =>
        (max (recordedFarField S (v.coreSlice s x).normalized x (Metric.ball 0 h) w) 0)^2))*ballCloud z (2*a) 1 w) := by
  simp only [innerLocalCap_sq S _ _ h z ha]
  rw [sliceExpectation_const_mul,sliceExpectation_farSquare_ballCloud S v measurableSet_ball
    (by positivity) z (fun j => by nlinarith [hnuc j])]

namespace RecordedEnsemble
variable {n J : ℕ}
lemma innerSquare_eq_recorded (T : RecordedEnsemble n) (S : Nuclei J) (h : ℝ) (w : Space)
    {r : ℝ} (hr : 0<r) (hsep : ∀ q∈Metric.ball (0:Space) h, r≤‖q-w‖) :
    T.innerSquare S h w = ∑ p, sliceExpectation (T.vector p) (fun s x =>
      (max (recordedFarField S ((T.vector p).coreSlice s x).normalized x (Metric.ball 0 h) w) 0)^2) := by
  unfold innerSquare sliceExpectation
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro s hs
  apply integral_congr_ae
  exact Eventually.of_forall (fun x => coreConditionalObservable_raw_positive_weight (T.vector p)
    (attraction S w) measurableSet_ball w hr hsep s x)

theorem innerLocalCap_second_moment (T : RecordedEnsemble n) (S : Nuclei J)
    (h : ℝ) (z : Space) {a r K : ℝ} (ha : 0<a) (hr : 0<r)
    (hnuc : ∀ j, 4*a≤‖S.position j-z‖)
    (hsep : ∀ w : Space, ‖w-z‖≤2*a → ∀ q∈Metric.ball (0:Space) h, r≤‖q-w‖)
    (hraw : ∀ w : Space, ‖w-z‖≤2*a → T.innerSquare S h w ≤ K) :
    (∑ p, sliceExpectation (T.vector p) (fun s x =>
      (innerLocalCap S ((T.vector p).coreSlice s x).normalized x h z a)^2)) ≤ 8*K := by
  let F := fun p w => sliceExpectation (T.vector p) (fun s x =>
    (max (recordedFarField S ((T.vector p).coreSlice s x).normalized x (Metric.ball 0 h) w) 0)^2)
  have hi p : Integrable (fun w => F p w*ballCloud z (2*a) 1 w) :=
    sliceFarSquare_ballCloud_integrable S (T.vector p) measurableSet_ball (by positivity) z (fun j => by nlinarith [hnuc j])
  have hb : Integrable (fun w => K*ballCloud z (2*a) 1 w) := (ballCloud_integrable _ _ _).const_mul K
  have hsum : (∫ w, ∑ p, F p w*ballCloud z (2*a) 1 w) ≤ K := by
    calc
      _ ≤ ∫ w, K*ballCloud z (2*a) 1 w := by
        apply integral_mono (integrable_finsetSum _ (fun p _ => hi p)) hb
        intro w
        change (∑ p, F p w*ballCloud z (2*a) 1 w) ≤ K*ballCloud z (2*a) 1 w
        rw [←Finset.sum_mul]
        by_cases hw : w-z ∈ Metric.ball (0:Space) (2*a)
        · have hd : ‖w-z‖≤2*a := (by simpa only [Metric.mem_ball,dist_zero_right] using hw : ‖w-z‖<2*a).le
          apply mul_le_mul_of_nonneg_right _ (uniformBall_nonneg (by positivity) zero_le_one (w-z))
          rw [←T.innerSquare_eq_recorded S h w hr (hsep w hd)]
          exact hraw w hd
        · simp only [ballCloud,uniformBall,indicator_of_notMem hw,mul_zero,le_refl]
      _ = K := by rw [integral_const_mul,ballCloud_mass (by positivity) 1 z,mul_one]
  calc
    _ = ∑ p, 8*(∫ w, F p w*ballCloud z (2*a) 1 w) := by
      apply Finset.sum_congr rfl
      intro p hp
      exact sliceExpectation_innerLocalCap_sq S (T.vector p) h z ha hnuc
    _ = 8*(∫ w, ∑ p, F p w*ballCloud z (2*a) 1 w) := by
      rw [←Finset.mul_sum,integral_finsetSum _ (fun p _ => hi p)]
    _ ≤ _ := mul_le_mul_of_nonneg_left hsum (by norm_num)
end RecordedEnsemble
end Coulomb
end

end

end OAI
