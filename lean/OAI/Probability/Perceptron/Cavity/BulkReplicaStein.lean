import Mathlib
import OAI.Probability.Perceptron.Cavity.BulkParameterDeviation
import OAI.Probability.Perceptron.Interpolation.FiniteVectorReplica

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

def bulkMoment (n M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ) (r : ℕ) (G : (Fin r→NormalizedSpin (n+1))→ℝ) : ℝ :=
  ∫ a, gibbsReplicaMean (unitSphereLaw (n+1)) (bulkHamiltonian (n+1) M f v a.1 a.2) r G ∂bulkDisorderLaw (n+1) M

lemma bulkReplicaMean_integrable (n M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ) (r : ℕ)
    {G : (Fin r→NormalizedSpin (n+1))→ℝ} (hG : Measurable G) {B : ℝ} (hB : 0≤B) (hGB : ∀ x, |G x|≤B) :
    Integrable (fun a : BulkDisorder (n+1) M => gibbsReplicaMean (unitSphereLaw (n+1))
      (bulkHamiltonian (n+1) M f v a.1 a.2) r G) (bulkDisorderLaw (n+1) M) :=
  kernel_replicaMean_bounded_integrable (bulkSpinKernel n M) _
    (H := fun a x => bulkHamiltonian (n+1) M f v a.1 a.2 x) (G := fun _ x => G x)
    (bulkHamiltonian_continuous _ _ _ _).measurable (hG.comp measurable_snd) hB (fun _ x => hGB x)

lemma bulkReplicaY_measurable (n M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ) (p : Fin (n+1)) (r : ℕ) (j : Fin r)
    {G : (Fin r→NormalizedSpin (n+1))→ℝ} (hG : Measurable G) :
    Measurable (fun a : BulkDisorder (n+1) M => gibbsReplicaMean (unitSphereLaw (n+1))
      (bulkHamiltonian (n+1) M f v a.1 a.2) r (fun x => bulkY (n+1) p a.2 (x j)*G x)) := by
  have hH : Measurable (Function.uncurry (fun (a : BulkDisorder (n+1) M) x =>
      bulkHamiltonian (n+1) M f v a.1 a.2 x)) := (bulkHamiltonian_continuous _ _ _ _).measurable
  have hY : Measurable (Function.uncurry (fun (a : BulkDisorder (n+1) M) (x : Fin r→NormalizedSpin (n+1)) =>
      bulkY (n+1) p a.2 (x j)*G x)) :=
    (((bulkY_joint_measurable (n+1) M p).comp
      (measurable_fst.prodMk ((measurable_pi_apply j).comp measurable_snd))).mul (hG.comp measurable_snd))
  exact measurable_replicaMean_param (unitSphereLaw (n+1)) hH hY

lemma bulkReplicaY_bound (n M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ) (p : Fin (n+1)) (r : ℕ) (j : Fin r)
    {G : (Fin r→NormalizedSpin (n+1))→ℝ} (hG : Measurable G) {B : ℝ} (hB : 0≤B) (hGB : ∀ x, |G x|≤B)
    (a : BulkDisorder (n+1) M) :
    |gibbsReplicaMean (unitSphereLaw (n+1)) (bulkHamiltonian (n+1) M f v a.1 a.2) r
      (fun x => bulkY (n+1) p a.2 (x j)*G x)|≤‖a.2‖*B := by
  apply tiltMean_bound_general _
    (replicaPotential_measurable (bulkHamiltonian_section_measurable _ _ _ _ a) r)
    (((bulkY_measurable (n+1) p).of_uncurry_left.comp (measurable_pi_apply j)).mul hG)
    (mul_nonneg (norm_nonneg _) hB)
  intro x
  change |bulkY (n+1) p a.2 (x j)*G x|≤_
  rw [abs_mul]
  exact mul_le_mul (bulkY_bound _ _ _ _) (hGB x) (abs_nonneg _) (norm_nonneg _)

lemma bulkReplicaY_integrable (n M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ) (p : Fin (n+1)) (r : ℕ) (j : Fin r)
    {G : (Fin r→NormalizedSpin (n+1))→ℝ} (hG : Measurable G) {B : ℝ} (hB : 0≤B) (hGB : ∀ x, |G x|≤B) :
    Integrable (fun a : BulkDisorder (n+1) M => gibbsReplicaMean (unitSphereLaw (n+1))
      (bulkHamiltonian (n+1) M f v a.1 a.2) r (fun x => bulkY (n+1) p a.2 (x j)*G x))
      (bulkDisorderLaw (n+1) M) := by
  have hi : Integrable (fun a : BulkDisorder (n+1) M => ‖a.2‖) (bulkDisorderLaw (n+1) M) :=
    (((IsGaussian.memLp_id (stdGaussian (BulkMark (n+1))) 2 (by simp)).norm).integrable (by norm_num)).comp_snd _
  apply (hi.mul_const B).mono' (bulkReplicaY_measurable n M f v p r j hG).aestronglyMeasurable
  exact ae_of_all _ fun a => by
    rw [Real.norm_eq_abs]
    exact bulkReplicaY_bound n M f v p r j hG hB hGB a

lemma bulkPowerPair_measurable (N r p : ℕ) (j l : Fin r) :
    Measurable (fun x : Fin r→NormalizedSpin N => spinOverlap (x j) (x l)^p) :=
  (((measurable_pi_apply j).subtype_val).inner ((measurable_pi_apply l).subtype_val)).pow_const p

lemma bulkPowerPair_bound (N r p : ℕ) (j l : Fin r) (x : Fin r→NormalizedSpin N) :
    |spinOverlap (x j) (x l)^p|≤1 := by
  rw [abs_pow]
  exact (pow_le_pow_left₀ (abs_nonneg _) (spinOverlap_abs_le _ _) p).trans_eq (one_pow p)

lemma bulkReplicaSum_bound (N r p : ℕ) (j : Fin r)
    {G : (Fin r→NormalizedSpin N)→ℝ} {B : ℝ} (hGB : ∀ x, |G x|≤B) (x : Fin r→NormalizedSpin N) :
    |G x*∑ l, spinOverlap (x j) (x l)^p|≤B*r := by
  rw [abs_mul]
  apply mul_le_mul (hGB x) _ (abs_nonneg _) (le_trans (abs_nonneg (G x)) (hGB x))
  calc
    _ ≤ ∑ l, |spinOverlap (x j) (x l)^p| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ : Fin r, (1:ℝ) := Finset.sum_le_sum fun l _ => bulkPowerPair_bound N r p j l x
    _ = _ := by simp

lemma bulk_fixed_replica_ibp (n M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ) (p : Fin (n+1)) (r : ℕ) (j : Fin r)
    {G : (Fin r→NormalizedSpin (n+1))→ℝ} (hG : Measurable G) {B : ℝ} (hB : 0≤B) (hGB : ∀ x, |G x|≤B)
    (a : Fin M→Fin (n+1)→ℝ) :
    (∫ g, gibbsReplicaMean (unitSphereLaw (n+1)) (bulkHamiltonian (n+1) M f v a g) r
      (fun x => bulkY (n+1) p g (x j)*G x) ∂stdGaussian (BulkMark (n+1))) =
    bulkAmplitude (n+1) v p*(
      (∫ g, gibbsReplicaMean (unitSphereLaw (n+1)) (bulkHamiltonian (n+1) M f v a g) r
        (fun x => G x*∑ l, spinOverlap (x j) (x l)^(p.val+1)) ∂stdGaussian (BulkMark (n+1)))-
      r*(∫ g, gibbsReplicaMean (unitSphereLaw (n+1)) (bulkHamiltonian (n+1) M f v a g) (r+1)
        (fun x => G (fun l => x l.succ)*spinOverlap (x j.succ) (x 0)^(p.val+1)) ∂stdGaussian (BulkMark (n+1)))) := by
  have he := euclideanGaussian_replica_ibp (unitSphereLaw (n+1)) r j
    (((normalizedPatternEnergy_continuous (n+1) M f).comp (continuous_const.prodMk continuous_id)).measurable)
    (bulkFeature_continuous (n+1) v).measurable (bulkDirection_continuous (n+1) p).measurable hG
    (normalizedPatternEnergy_bound (n+1) M f a)
    (fun x => le_of_eq (bulkFeature_norm_sq (n+1) v x))
    (fun x => by rw [bulkDirection_norm]; norm_num : ∀ x, ‖bulkDirection (n+1) p x‖^2≤(1:ℝ)) hB hGB
  have hUm : Measurable (fun x : Fin r→NormalizedSpin (n+1) => G x*∑ l, spinOverlap (x j) (x l)^(p.val+1)) :=
    hG.mul (Finset.measurable_sum _ fun l _ => bulkPowerPair_measurable _ _ _ _ _)
  have hWm : Measurable (fun x : Fin (r+1)→NormalizedSpin (n+1) =>
      G (fun l => x l.succ)*spinOverlap (x j.succ) (x 0)^(p.val+1)) :=
    (hG.comp (Measurable.of_eval (fun replica => measurable_pi_apply replica.succ))).mul (bulkPowerPair_measurable _ _ _ _ _)

  have hUIf := kernel_replicaMean_bounded_integrable (Kernel.const (BulkMark (n+1)) (unitSphereLaw (n+1)))
    (stdGaussian (BulkMark (n+1))) (H:=fun g x => bulkHamiltonian (n+1) M f v a g x)
    (G:=fun _ x => G x*∑ l,spinOverlap (x j) (x l)^(p.val+1))
    (((bulkHamiltonian_continuous _ _ _ _).comp
      ((continuous_const.prodMk continuous_fst).prodMk continuous_snd)).measurable)
    (hUm.comp measurable_snd) (mul_nonneg hB (Nat.cast_nonneg r))
    (fun _ x => bulkReplicaSum_bound (n+1) r (p.val+1) j hGB x)
  have hWIf := kernel_replicaMean_bounded_integrable (Kernel.const (BulkMark (n+1)) (unitSphereLaw (n+1)))
    (stdGaussian (BulkMark (n+1))) (H:=fun g x => bulkHamiltonian (n+1) M f v a g x)
    (G:=fun _ x => G (fun l => x l.succ)*spinOverlap (x j.succ) (x 0)^(p.val+1))
    (((bulkHamiltonian_continuous _ _ _ _).comp
      ((continuous_const.prodMk continuous_fst).prodMk continuous_snd)).measurable)
    (hWm.comp measurable_snd) hB (fun _ x => by
      rw [abs_mul]
      exact (mul_le_mul (hGB _) (bulkPowerPair_bound _ _ _ _ _ x) (abs_nonneg _) hB).trans_eq (mul_one B))
  simp only [bulkFeature_direction_inner,←Finset.mul_sum] at he
  have heU : (fun x : Fin r→NormalizedSpin (n+1) => G x*(bulkAmplitude (n+1) v p*∑ l, spinOverlap (x j) (x l)^(p.val+1))) =
      (fun x => bulkAmplitude (n+1) v p*(G x*∑ l, spinOverlap (x j) (x l)^(p.val+1))) := by funext x; ring
  have heW : (fun x : Fin (r+1)→NormalizedSpin (n+1) => G (fun l => x l.succ)*(bulkAmplitude (n+1) v p*spinOverlap (x j.succ) (x 0)^(p.val+1))) =
      (fun x => bulkAmplitude (n+1) v p*(G (fun l => x l.succ)*spinOverlap (x j.succ) (x 0)^(p.val+1))) := by funext x; ring
  rw [heU,heW] at he
  simp only [gibbsReplicaMean,tiltMean_const_mul_general] at he
  change (∫ g, gibbsReplicaMean (unitSphereLaw (n+1)) (bulkHamiltonian (n+1) M f v a g) r
    (fun x => bulkY (n+1) p g (x j)*G x) ∂stdGaussian (BulkMark (n+1))) =
    ∫ g, bulkAmplitude (n+1) v p*gibbsReplicaMean (unitSphereLaw (n+1)) (bulkHamiltonian (n+1) M f v a g) r
      (fun x => G x*∑ l,spinOverlap (x j) (x l)^(p.val+1)) -
    r*(bulkAmplitude (n+1) v p*gibbsReplicaMean (unitSphereLaw (n+1)) (bulkHamiltonian (n+1) M f v a g) (r+1)
      (fun x => G (fun l => x l.succ)*spinOverlap (x j.succ) (x 0)^(p.val+1))) ∂stdGaussian (BulkMark (n+1)) at he
  simp only [Kernel.const_apply] at hUIf hWIf
  rw [integral_sub (hUIf.const_mul _) ((hWIf.const_mul _).const_mul _),integral_const_mul,integral_const_mul,integral_const_mul] at he
  rw [he]
  ring


lemma bulk_rate_identity {x θ C : ℝ} (hx : 0<x) (hθ : θ≠0) (hC : 0≤C) :
    (Real.sqrt 6*(x^((3:ℝ)/8)*θ)+24*(x^((3:ℝ)/8)*θ)^2*x^(-(1:ℝ)/8)+
      4*Real.sqrt (C*x)/x^(-(1:ℝ)/8))/(x^((3:ℝ)/8)*θ*x^((3:ℝ)/8)) =
      Real.sqrt 6*x^(-(3:ℝ)/8)+(24*θ+4*Real.sqrt C/θ)*x^(-(1:ℝ)/8) := by
  have hp1 : x^(-(3:ℝ)/8)*x^((3:ℝ)/8)=1 := by rw [←Real.rpow_add hx]; norm_num
  have hp2 : x^((1:ℝ)/2) = x^(-(1:ℝ)/8)*x^(-(1:ℝ)/8)*(x^((3:ℝ)/8))^2 := by
    rw [← Real.rpow_mul_natCast hx.le,←Real.rpow_add hx,←Real.rpow_add hx]
    congr 1
    norm_num
  rw [Real.sqrt_mul hC,Real.sqrt_eq_rpow x, hp2]
  have h1 : x^((3:ℝ)/8)≠0 := (Real.rpow_pos_of_pos hx _).ne'
  have h2 : x^(-(1:ℝ)/8)≠0 := (Real.rpow_pos_of_pos hx _).ne'
  field_simp
  simp only [neg_div] at hp1
  linear_combination -(Real.sqrt 6*θ)*hp1

lemma bulkScale_sq_le (n : ℕ) : bulkScale (n+1)^2≤(n+1:ℕ) := by
  have hx : (1:ℝ)≤(n+1:ℕ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  unfold bulkScale
  rw [←Real.rpow_mul_natCast (by positivity : (0:ℝ)≤(n+1:ℕ))]
  calc
    _ ≤ ((n+1:ℕ):ℝ)^((1:ℝ)) := Real.rpow_le_rpow_of_exponent_le hx (by norm_num)
    _ = _ := Real.rpow_one _

def bulkNormalizedDeviation (n M : ℕ) (f : ℝ→ᵇℝ) (p : Fin (n+1)) (v : ℕ→ℝ) : ℝ :=
  bulkDegreeDeviation n M f p v/(bulkCoefficient (n+1) p*bulkScale (n+1))

lemma bulkNormalizedDeviation_nonneg (n M : ℕ) (f : ℝ→ᵇℝ) (p : Fin (n+1)) (v : ℕ→ℝ) :
    0≤bulkNormalizedDeviation n M f p v := by
  unfold bulkNormalizedDeviation
  exact div_nonneg (bulkDegreeDeviation_nonneg n M f p v)
    (mul_nonneg (bulkCoefficient_pos n p).le (by unfold bulkScale; positivity))

lemma bulkNormalizedDeviation_measurable (n M : ℕ) (f : ℝ→ᵇℝ) (p : Fin (n+1)) :
    Measurable (bulkNormalizedDeviation n M f p) := (bulkDegreeDeviation_measurable n M f p).div_const _

lemma bulkNormalizedDeviation_integrable (n M : ℕ) (f : ℝ→ᵇℝ) (p : Fin (n+1)) :
    Integrable (bulkNormalizedDeviation n M f p) bulkParameterLaw := (bulkDegreeDeviation_integrable n M f p).div_const _

def bulkDeviationRate (A : ℝ) (f : ℝ→ᵇℝ) (p : ℕ) (x : ℝ) : ℝ :=
  Real.sqrt 6*x^(-(3:ℝ)/8)+(24*(2:ℝ)^(-((p+1:ℕ):ℤ))+
    4*Real.sqrt (Real.pi^2/8*3^2+A*(2*‖f‖)^2)/(2:ℝ)^(-((p+1:ℕ):ℤ)))*x^(-(1:ℝ)/8)

lemma bulkNormalizedDeviation_integral_bound (n M : ℕ) (f : ℝ→ᵇℝ) (p : Fin (n+1))
    {A : ℝ} (hA : 0≤A) (hM : (M:ℝ)≤A*(n+1:ℕ)) :
    (∫ v, bulkNormalizedDeviation n M f p v ∂bulkParameterLaw)≤bulkDeviationRate A f p.val (n+1:ℕ) := by
  let x : ℝ := (n+1:ℕ)
  let s : ℝ := x^(-(1:ℝ)/8)
  let C := Real.pi^2/8*3^2+A*(2*‖f‖)^2
  have hx : 0<x := by dsimp [x]; positivity
  have hx1 : 1≤x := by dsimp [x]; exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  have hs : 0<s := Real.rpow_pos_of_pos hx _
  have hs1 : s≤1 := Real.rpow_le_one_of_one_le_of_nonpos hx1 (by norm_num)
  have hC : 0≤C := by dsimp [C]; positivity
  have hV : Real.pi^2/8*3^2*bulkScale (n+1)^2+M*(2*‖f‖)^2≤C*x := by
    calc
      _ ≤ Real.pi^2/8*3^2*x+(A*x)*(2*‖f‖)^2 :=
        add_le_add (mul_le_mul_of_nonneg_left (bulkScale_sq_le n) (by positivity))
          (mul_le_mul_of_nonneg_right hM (sq_nonneg _))
      _ = _ := by dsimp [C]; ring
  have hden : 0<bulkCoefficient (n+1) p*bulkScale (n+1) := mul_pos (bulkCoefficient_pos n p) (Real.rpow_pos_of_pos hx _)
  unfold bulkNormalizedDeviation
  rw [integral_div]
  calc
    _ ≤ (Real.sqrt 6*bulkCoefficient (n+1) p+24*bulkCoefficient (n+1) p^2*s+
        4*Real.sqrt (Real.pi^2/8*3^2*bulkScale (n+1)^2+M*(2*‖f‖)^2)/s)/
          (bulkCoefficient (n+1) p*bulkScale (n+1)) :=
      div_le_div_of_nonneg_right (bulkDegreeDeviation_integral_bound n M f p hs hs1) hden.le
    _ ≤ (Real.sqrt 6*bulkCoefficient (n+1) p+24*bulkCoefficient (n+1) p^2*s+
        4*Real.sqrt (C*x)/s)/(bulkCoefficient (n+1) p*bulkScale (n+1)) := by gcongr
    _ = _ := bulk_rate_identity hx (by positivity) hC

lemma bulkDeviationRate_tendsto (A : ℝ) (f : ℝ→ᵇℝ) (p : ℕ) :
    Tendsto (fun n : ℕ => bulkDeviationRate A f p (n+1:ℕ)) atTop (𝓝 0) := by
  have hN : Tendsto (fun n : ℕ => (n+1:ℕ) : ℕ→ℝ) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have h3 := (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<3/8)).comp hN
  have h1 := (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<1/8)).comp hN
  unfold bulkDeviationRate
  convert (h3.const_mul (Real.sqrt 6)).add (h1.const_mul (24*(2:ℝ)^(-((p+1:ℕ):ℤ))+
    4*Real.sqrt (Real.pi^2/8*3^2+A*(2*‖f‖)^2)/(2:ℝ)^(-((p+1:ℕ):ℤ)))) using 1 <;> norm_num

end SphericalPerceptronFreeEnergy
end

end OAI
