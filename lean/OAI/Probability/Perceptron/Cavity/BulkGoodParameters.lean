import Mathlib
import OAI.Probability.Perceptron.Cavity.BulkReplicaStein
import OAI.Probability.Perceptron.Variational.DiagonalDeviation

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

def bulkDeviationAt (n M : ℕ) (f : ℝ→ᵇℝ) (p : ℕ) (v : ℕ→ℝ) : ℝ :=
  if hp : p<n+1 then bulkNormalizedDeviation n M f ⟨p,hp⟩ v else 0

lemma bulkDeviationAt_nonneg (n M : ℕ) (f : ℝ→ᵇℝ) (p : ℕ) (v : ℕ→ℝ) :
    0≤bulkDeviationAt n M f p v := by
  unfold bulkDeviationAt
  split_ifs with h
  · exact bulkNormalizedDeviation_nonneg n M f _ v
  · exact le_rfl

lemma bulkDeviationAt_measurable (n M : ℕ) (f : ℝ→ᵇℝ) (p : ℕ) :
    Measurable (bulkDeviationAt n M f p) := by
  unfold bulkDeviationAt
  split_ifs with h
  · exact bulkNormalizedDeviation_measurable n M f _
  · exact measurable_const

lemma bulkDeviationAt_integrable (n M : ℕ) (f : ℝ→ᵇℝ) (p : ℕ) :
    Integrable (bulkDeviationAt n M f p) bulkParameterLaw := by
  unfold bulkDeviationAt
  split_ifs with h
  · exact bulkNormalizedDeviation_integrable n M f _
  · exact integrable_const _

lemma bulkDeviationAt_integral_tendsto (M : ℕ→ℕ) (f : ℝ→ᵇℝ) {A : ℝ}
    (hA : 0≤A) (hM : ∀ n, (M n:ℝ)≤A*(n+1:ℕ)) (p : ℕ) :
    Tendsto (fun n => ∫ v, bulkDeviationAt n (M n) f p v ∂bulkParameterLaw) atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall fun n => integral_nonneg (bulkDeviationAt_nonneg n (M n) f p)) _
    (bulkDeviationRate_tendsto A f p)
  filter_upwards [eventually_ge_atTop p] with n hn
  have hp : p<n+1 := Nat.lt_succ_of_le hn
  simp only [bulkDeviationAt,dite_eq_left hp]
  exact bulkNormalizedDeviation_integral_bound n (M n) f ⟨p,hp⟩ hA (hM n)

def omittedBulkDeviation (α : ℝ) (f : ℝ→ᵇℝ) (n p : ℕ) (v : ℕ→ℝ) : ℝ :=
  bulkDeviationAt n (patternCount α (n+1)-2) f p v

lemma omittedBulkDeviation_integral_tendsto {α : ℝ} (hα : 0≤α) (f : ℝ→ᵇℝ) (p : ℕ) :
    Tendsto (fun n => ∫ v, omittedBulkDeviation α f n p v ∂bulkParameterLaw) atTop (𝓝 0) := by
  apply bulkDeviationAt_integral_tendsto _ f hα _ p
  intro n
  calc
    _ ≤ (patternCount α (n+1):ℝ) := by exact_mod_cast Nat.sub_le (patternCount α (n+1)) 2
    _ ≤ α*(n+1:ℕ) := Nat.floor_le (mul_nonneg hα (Nat.cast_nonneg _))

def bulkGoodSet (α : ℝ) (f : ℝ→ᵇℝ) (J : ℕ→ℕ) (n : ℕ) : Set (ℕ→ℝ) :=
  diagonalGoodSet bulkParameterLaw (omittedBulkDeviation α f) J n ∩ {v | ∀ p, v p∈Icc (1:ℝ) 2}

lemma bulkGoodSet_measurable (α : ℝ) (f : ℝ→ᵇℝ) (J : ℕ→ℕ) (n : ℕ) :
    MeasurableSet (bulkGoodSet α f J n) := by
  refine (diagonalGoodSet_measurable _ _ (fun n p => bulkDeviationAt_measurable _ _ _ _) J n).inter ?_
  simp only [ofPred_forall]
  exact MeasurableSet.iInter fun p => (measurable_pi_apply p) measurableSet_Icc

lemma bulkGoodSet_compl_measure (α : ℝ) (f : ℝ→ᵇℝ) (J : ℕ→ℕ) (n : ℕ) :
    bulkParameterLaw.real (bulkGoodSet α f J n)ᶜ =
      bulkParameterLaw.real (diagonalGoodSet bulkParameterLaw (omittedBulkDeviation α f) J n)ᶜ := by
  simp only [measureReal_def]
  congr 1
  apply measure_congr
  filter_upwards [bulkParameterLaw_ae] with v hv
  apply propext
  change ¬(v∈diagonalGoodSet bulkParameterLaw (omittedBulkDeviation α f) J n ∧ ∀ p, v p∈Icc (1:ℝ) 2) ↔ _
  exact not_congr ⟨fun h => h.1, fun h => ⟨h,hv⟩⟩

theorem exists_bulkGoodParameters {α : ℝ} (hα : 0≤α) (f : ℝ→ᵇℝ) :
    ∃ J : ℕ→ℕ, Monotone J ∧ (∀ n, J n≤n) ∧ Tendsto J atTop atTop ∧
      (∀ n, MeasurableSet (bulkGoodSet α f J n)) ∧
      Tendsto (fun n => bulkParameterLaw.real (bulkGoodSet α f J n)ᶜ) atTop (𝓝 0) ∧
      (∀ v : ℕ→(ℕ→ℝ), (∀ᶠ n in atTop, v n∈bulkGoodSet α f J n) →
        ∀ p, Tendsto (fun n => omittedBulkDeviation α f n p (v n)) atTop (𝓝 0)) := by
  have hn : ∀ n p v, 0≤omittedBulkDeviation α f n p v := fun n p v => bulkDeviationAt_nonneg _ _ _ _ _
  have hi : ∀ n p, Integrable (omittedBulkDeviation α f n p) bulkParameterLaw :=
    fun n p => bulkDeviationAt_integrable _ _ _ _
  obtain ⟨J,hmon,hbound,hlim,hmass⟩ := exists_slow_diagonal
    (fun n p => integral_nonneg (hn n p)) (omittedBulkDeviation_integral_tendsto hα f)
  refine ⟨J,hmon,hbound,hlim,bulkGoodSet_measurable α f J,?_,?_⟩
  · simpa only [bulkGoodSet_compl_measure] using
      diagonalGoodSet_compl_tendsto bulkParameterLaw (omittedBulkDeviation α f) hn hi J hmass
  · intro v hv p
    exact diagonalGoodSet_deviation_tendsto bulkParameterLaw (omittedBulkDeviation α f) hn J hlim hmass v
      (hv.mono fun n h => h.1) p


lemma bulk_pairTest_measurable (n r : ℕ) (p : ℕ) (j : Fin r)
    {G : (Fin r→NormalizedSpin (n+1))→ℝ} (hG : Measurable G) :
    Measurable (fun x : Fin (r+1)→NormalizedSpin (n+1) =>
      G (fun l => x l.succ)*spinOverlap (x j.succ) (x 0)^p) :=
  (hG.comp (Measurable.of_eval (fun replica => measurable_pi_apply replica.succ))).mul (bulkPowerPair_measurable _ _ _ _ _)

lemma bulk_pairTest_bound (n r : ℕ) (p : ℕ) (j : Fin r)
    {G : (Fin r→NormalizedSpin (n+1))→ℝ} {B : ℝ} (hB : 0≤B) (hGB : ∀ x, |G x|≤B)
    (x : Fin (r+1)→NormalizedSpin (n+1)) :
    |G (fun l => x l.succ)*spinOverlap (x j.succ) (x 0)^p|≤B := by
  rw [abs_mul]
  exact (mul_le_mul (hGB _) (bulkPowerPair_bound _ _ _ _ _ x) (abs_nonneg _) hB).trans_eq (mul_one B)

lemma bulk_replica_ibp (n M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ) (p : Fin (n+1)) (r : ℕ) (j : Fin r)
    {G : (Fin r→NormalizedSpin (n+1))→ℝ} (hG : Measurable G) {B : ℝ} (hB : 0≤B) (hGB : ∀ x, |G x|≤B) :
    (∫ a, gibbsReplicaMean (unitSphereLaw (n+1)) (bulkHamiltonian (n+1) M f v a.1 a.2) r
      (fun x => bulkY (n+1) p a.2 (x j)*G x) ∂bulkDisorderLaw (n+1) M) =
    bulkAmplitude (n+1) v p*(
      bulkMoment n M f v r (fun x => G x*∑ l, spinOverlap (x j) (x l)^(p.val+1))-
      r*bulkMoment n M f v (r+1) (fun x => G (fun l => x l.succ)*spinOverlap (x j.succ) (x 0)^(p.val+1))) := by
  have hUm : Measurable (fun x : Fin r→NormalizedSpin (n+1) => G x*∑ l, spinOverlap (x j) (x l)^(p.val+1)) :=
    hG.mul (Finset.measurable_sum _ fun l _ => bulkPowerPair_measurable _ _ _ _ _)
  have hUI := bulkReplicaMean_integrable n M f v r hUm (mul_nonneg hB (Nat.cast_nonneg r))
    (bulkReplicaSum_bound (n+1) r (p.val+1) j hGB)
  have hWI := bulkReplicaMean_integrable n M f v (r+1) (bulk_pairTest_measurable n r (p.val+1) j hG) hB
    (bulk_pairTest_bound n r (p.val+1) j hB hGB)
  rw [bulkDisorderLaw,integral_prod _ (bulkReplicaY_integrable n M f v p r j hG hB hGB)]
  simp_rw [bulk_fixed_replica_ibp n M f v p r j hG hB hGB]
  rw [integral_const_mul, integral_sub hUI.integral_prod_left (hWI.integral_prod_left.const_mul r),integral_const_mul]
  rw [←integral_prod _ hUI,←integral_prod _ hWI]
  rfl

lemma bulk_energy_factorization (n M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ) (p : Fin (n+1)) (r : ℕ) (j : Fin r)
    {G : (Fin r→NormalizedSpin (n+1))→ℝ} (hG : Measurable G) {B : ℝ} (hB : 0≤B) (hGB : ∀ x, |G x|≤B) :
    |bulkCoefficient (n+1) p*(∫ a, gibbsReplicaMean (unitSphereLaw (n+1))
        (bulkHamiltonian (n+1) M f v a.1 a.2) r (fun x => bulkY (n+1) p a.2 (x j)*G x) ∂bulkDisorderLaw (n+1) M)-
      (∫ a, bulkCouplingSlope n M f v p (v (p.val+1)) a ∂bulkDisorderLaw (n+1) M)*bulkMoment n M f v r G|≤
        B*bulkDegreeDeviation n M f p v := by
  have hc := (bulkCoefficient_pos n p).le
  have hi : Integrable (fun a : BulkDisorder (n+1) M => bulkCoefficient (n+1) p*‖a.2‖) (bulkDisorderLaw (n+1) M) :=
    ((bulkMarkNorm_memLp n M).integrable (by norm_num)).const_mul _
  have hf := annealed_replica_energy_factorization_bound (unitSphereLaw (n+1)) (bulkDisorderLaw (n+1) M)
    (H:=fun a x => bulkHamiltonian (n+1) M f v a.1 a.2 x)
    (Y:=fun a x => bulkCoefficient (n+1) p*bulkY (n+1) p a.2 x)
    (bulkHamiltonian_continuous _ _ _ _).measurable ((bulkY_joint_measurable _ _ _).const_mul _)
    (A:=fun a => M*‖f‖+bulkFeatureBound (n+1) v*‖a.2‖)
    (B:=fun a => bulkCoefficient (n+1) p*‖a.2‖)
    (fun a => by unfold bulkFeatureBound; positivity) (fun a => mul_nonneg hc (norm_nonneg _))
    (bulkHamiltonian_bound _ _ _ _) (fun a x => by
      rw [abs_mul,abs_of_nonneg hc]
      exact mul_le_mul_of_nonneg_left (bulkY_bound _ _ _ _) hc) hi j hG hB hGB
    (∫ a, bulkCouplingSlope n M f v p (v (p.val+1)) a ∂bulkDisorderLaw (n+1) M)
  simp only [mul_assoc,gibbsReplicaMean,tiltMean_const_mul_general,integral_const_mul] at hf
  simpa only [bulkDegreeDeviation,bulkEnergyDeviation,Function.update_eq_self,bulkMoment,gibbsReplicaMean] using hf

def bulkGGDefect (n M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ) (p r : ℕ) (j : Fin r)
    (G : (Fin r→NormalizedSpin (n+1))→ℝ) : ℝ :=
  bulkMoment n M f v r (fun x => G x*∑ l, spinOverlap (x j) (x l)^p)-bulkMoment n M f v r G+
    bulkMoment n M f v r G*bulkMoment n M f v 2 (fun x => spinOverlap (x 1) (x 0)^p)-
    r*bulkMoment n M f v (r+1) (fun x => G (fun l => x l.succ)*spinOverlap (x j.succ) (x 0)^p)

lemma bulkGG_weighted_bound (n M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ) (p : Fin (n+1)) (r : ℕ) (j : Fin r)
    {G : (Fin r→NormalizedSpin (n+1))→ℝ} (hG : Measurable G) {B : ℝ} (hB : 0≤B) (hGB : ∀ x, |G x|≤B) :
    |bulkCoefficient (n+1) p^2*v (p.val+1)*bulkGGDefect n M f v (p.val+1) r j G|≤B*bulkDegreeDeviation n M f p v := by
  have hf := bulk_energy_factorization n M f v p r j hG hB hGB
  rw [bulk_replica_ibp n M f v p r j hG hB hGB,bulk_expected_slope_eq] at hf
  simp only [Function.update_eq_self] at hf
  convert hf using 1
  congr 1
  unfold bulkGGDefect bulkMoment bulkAmplitude bulkCoefficient
  ring

lemma bulkGG_bound (n M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ) (p : Fin (n+1)) (r : ℕ) (j : Fin r)
    {G : (Fin r→NormalizedSpin (n+1))→ℝ} (hG : Measurable G) {B : ℝ} (hB : 0≤B) (hGB : ∀ x, |G x|≤B)
    (hv : 1≤v (p.val+1)) :
    |bulkGGDefect n M f v (p.val+1) r j G|≤B/(2:ℝ)^(-((p.val+1:ℕ):ℤ))*bulkNormalizedDeviation n M f p v := by
  let c := bulkCoefficient (n+1) p
  let θ : ℝ := (2:ℝ)^(-((p.val+1:ℕ):ℤ))
  have hc : 0<c := bulkCoefficient_pos n p
  have hθ : 0<θ := by dsimp [θ]; positivity
  have hs : 0<bulkScale (n+1) := by unfold bulkScale; positivity
  have hcv : 0<c^2*v (p.val+1) := mul_pos (sq_pos_of_pos hc) (lt_of_lt_of_le zero_lt_one hv)
  have hf := bulkGG_weighted_bound n M f v p r j hG hB hGB
  rw [abs_mul,abs_of_pos hcv] at hf
  calc
    _ ≤ B*bulkDegreeDeviation n M f p v/(c^2*v (p.val+1)) := (le_div_iff₀ hcv).2 (by simpa only [mul_comm] using hf)
    _ ≤ B*bulkDegreeDeviation n M f p v/c^2 := by
      apply div_le_div_of_nonneg_left (mul_nonneg hB (bulkDegreeDeviation_nonneg _ _ _ _ _)) (sq_pos_of_pos hc)
      nlinarith [sq_nonneg c]
    _ = _ := by
      unfold bulkNormalizedDeviation
      change B*bulkDegreeDeviation n M f p v/c^2 = B/θ*(bulkDegreeDeviation n M f p v/(c*bulkScale (n+1)))
      have he : c=bulkScale (n+1)*θ := rfl
      rw [he]
      field_simp

end SphericalPerceptronFreeEnergy
end

end OAI
