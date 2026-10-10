import Mathlib
import OAI.Probability.Perceptron.Interpolation.TerminalReplicaRestoration
import OAI.Probability.Perceptron.Cavity.AmbientBulkFeature
import OAI.Probability.Perceptron.Interpolation.VectorReplicaDirectionBound

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators BoundedContinuousFunction ContDiff

lemma bulkCovarianceDerivative_bound (N : ℕ) (v : ℕ→ℝ) {C r : ℝ}
    (hC : 0≤C) (hv : ∀ j, |v (j+1)|≤C) (hr : |r|≤1) :
    |bulkCovarianceDerivative N v r|≤C^2*bulkScale N^2 := by
  have hb (j : Fin N) : bulkAmplitude N v j^2*(j.val+1)≤C^2*bulkScale N^2*(1/2:ℝ)^(j.val+1) := by
    let w : ℝ := (1/2:ℝ)^(j.val+1)
    have hw : 0≤w := by dsimp [w]; positivity
    have hwp : w*(j.val+1)≤1 := by
      have hk : (j.val+1:ℝ)≤(2:ℝ)^(j.val+1) := by exact_mod_cast (Nat.lt_two_pow_self (n:=j.val+1)).le
      dsimp [w]
      rw [div_pow,one_pow,one_div_mul_eq_div]
      exact (div_le_one (by positivity)).mpr (by simpa only [Nat.cast_add,Nat.cast_one] using hk)
    have hv2 : v (j.val+1)^2≤C^2 := by simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hv j.val) 2
    unfold bulkAmplitude
    rw [perturbationWeight_eq]
    change (bulkScale N*w*v (j.val+1))^2*(j.val+1)≤C^2*bulkScale N^2*w
    calc
      _ = bulkScale N^2*w^2*(j.val+1)*v (j.val+1)^2 := by ring
      _ ≤ bulkScale N^2*w^2*(j.val+1)*C^2 := mul_le_mul_of_nonneg_left hv2 (by positivity)
      _ = C^2*bulkScale N^2*w*(w*(j.val+1)) := by ring
      _ ≤ C^2*bulkScale N^2*w*1 := mul_le_mul_of_nonneg_left hwp (by positivity)
      _ = _ := mul_one _
  unfold bulkCovarianceDerivative
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ j : Fin N, C^2*bulkScale N^2*(1/2:ℝ)^(j.val+1) := by
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul,abs_mul,abs_sq,abs_of_nonneg (by positivity : (0:ℝ)≤j.val+1),abs_pow]
      exact (mul_le_mul_of_nonneg_left (pow_le_one₀ (abs_nonneg r) hr) (by positivity)).trans (by simpa only [mul_one] using hb j)
    _ = C^2*bulkScale N^2*(∑ j : Fin N, (1/2:ℝ)^(j.val+1)) := (Finset.mul_sum _ _ _).symm
    _ ≤ C^2*bulkScale N^2*1 := mul_le_mul_of_nonneg_left (half_power_sum_le_one N)
      (mul_nonneg (pow_nonneg hC 2) (sq_nonneg _))
    _ = _ := mul_one _

def bulkTangentDirection (N : ℕ) (v : ℕ→ℝ) (G : ℝ→ᵇℝ) (x : Fin 2→NormalizedSpin N) : BulkMark N :=
  G (spinOverlap (x 0) (x 1)) •
    fderiv ℝ (ambientBulkFeature N v) (x 0).val
      ((x 1).val-spinOverlap (x 0) (x 1) • (x 0).val)

lemma bulkTangentDirection_continuous (N : ℕ) (v : ℕ→ℝ) (G : ℝ→ᵇℝ) :
    Continuous (bulkTangentDirection N v G) := by
  have hr : Continuous (fun x : Fin 2→NormalizedSpin N => spinOverlap (x 0) (x 1)) := by
    unfold spinOverlap; fun_prop
  apply (G.continuous.comp hr).smul
  have h0 : Continuous (fun x : Fin 2→NormalizedSpin N => (x 0).val) := by fun_prop
  have h1 : Continuous (fun x : Fin 2→NormalizedSpin N => (x 1).val) := by fun_prop
  exact (((ambientBulkFeature_contDiff N v).continuous_fderiv (by norm_num)).comp h0).clm_apply
    (h1.sub (hr.smul h0))

lemma bulkTangentDirection_cross (N : ℕ) (v : ℕ→ℝ) (G : ℝ→ᵇℝ)
    (x : Fin 2→NormalizedSpin N) (y : NormalizedSpin N) :
    inner ℝ (bulkTangentDirection N v G x) (bulkFeature N v y)=
      G (spinOverlap (x 0) (x 1))*bulkCovarianceDerivative N v (spinOverlap (x 0) y)*
        (spinOverlap (x 1) y-spinOverlap (x 0) (x 1)*spinOverlap (x 0) y) := by
  unfold bulkTangentDirection
  rw [← ambientBulkFeature_eq,inner_smul_left,starRingEnd_apply,star_trivial,ambientBulkFeature_deriv_inner]
  simp only [inner_sub_left,inner_smul_left,starRingEnd_apply,star_trivial,spinOverlap]
  ring

lemma bulkTangentDirection_cross_bound (N : ℕ) (v : ℕ→ℝ) (G : ℝ→ᵇℝ) {C : ℝ}
    (hC : 0≤C) (hv : ∀ j, |v (j+1)|≤C)
    (x : Fin 2→NormalizedSpin N) (y : NormalizedSpin N) :
    |inner ℝ (bulkTangentDirection N v G x) (bulkFeature N v y)|≤2*‖G‖*C^2*bulkScale N^2 := by
  rw [bulkTangentDirection_cross,abs_mul,abs_mul]
  have hb : |spinOverlap (x 1) y-spinOverlap (x 0) (x 1)*spinOverlap (x 0) y|≤2 := by
    apply (abs_sub _ _).trans
    rw [abs_mul]
    have hm := mul_le_mul (spinOverlap_abs_le (x 0) (x 1)) (spinOverlap_abs_le (x 0) y) (abs_nonneg _) (by norm_num : (0:ℝ)≤1)
    linarith [spinOverlap_abs_le (x 1) y]
  have hc := bulkCovarianceDerivative_bound N v hC hv (spinOverlap_abs_le (x 0) y)
  calc
    _ ≤ (‖G‖*(C^2*bulkScale N^2))*2 :=
      mul_le_mul (mul_le_mul (G.norm_coe_le_norm _) hc (abs_nonneg _) (norm_nonneg _)) hb (abs_nonneg _) (by positivity)
    _ = _ := by ring

lemma bulk_tangent_perturbation_bound (n M : ℕ) (f G : ℝ→ᵇℝ) (v : ℕ→ℝ)
    (a : Fin M→Fin (n+1)→ℝ) {C : ℝ} (hC : 0≤C) (hv : ∀ j, |v (j+1)|≤C) :
    |∫ g, gibbsReplicaMean (unitSphereLaw (n+1))
      (bulkHamiltonian (n+1) M f v a g) 2
      (fun x => inner ℝ (bulkTangentDirection (n+1) v G x) g) ∂stdGaussian (BulkMark (n+1))|≤
        8*‖G‖*C^2*bulkScale (n+1)^2 := by
  obtain ⟨D,hD⟩ := (isCompact_univ : IsCompact (univ : Set (Fin 2→NormalizedSpin (n+1)))).bddAbove_image
    (bulkTangentDirection_continuous (n+1) v G).norm.continuousOn
  have hWD (x : Fin 2→NormalizedSpin (n+1)) : ‖bulkTangentDirection (n+1) v G x‖≤ max D 0 :=
    (hD (mem_image_of_mem _ (mem_univ x))).trans (le_max_left _ _)
  have he := euclideanGaussian_replica_direction_bound (unitSphereLaw (n+1)) 2
    ((normalizedPatternEnergy_continuous (n+1) M f).measurable.comp (measurable_const.prodMk measurable_id))
    (bulkFeature_continuous (n+1) v).measurable
    (bulkTangentDirection_continuous (n+1) v G).measurable
    (Real.sqrt_nonneg _) (le_max_right D 0) (by positivity : 0≤2*‖G‖*C^2*bulkScale (n+1)^2)
    (normalizedPatternEnergy_bound (n+1) M f a)
    (fun x => le_of_eq (by simpa only [bulkFeatureBound] using bulkFeature_norm (n+1) v x))
    hWD (bulkTangentDirection_cross_bound (n+1) v G hC hv)
  apply he.trans_eq
  norm_num
  ring

def bulkPatternLinear {N : ℕ} (a : Fin N→ℝ) : Spin N→L[ℝ]ℝ :=
  ∑ i, a i • EuclideanSpace.proj i

lemma bulkPatternLinear_apply {N : ℕ} (a : Fin N→ℝ) (x : Spin N) :
    bulkPatternLinear a x=∑ i,a i*x i := by
  simp only [bulkPatternLinear,sum_apply,smul_apply,
    smul_eq_mul]
  rfl

def ambientBulkHamiltonian (N M : ℕ) (f : Jet3) (v : ℕ→ℝ)
    (a : Fin M→Fin N→ℝ) (g : BulkMark N) (x : Spin N) : ℝ :=
  (∑ j,f.f (bulkPatternLinear (a j) x))+inner ℝ g (ambientBulkFeature N v x)

lemma ambientBulkHamiltonian_eq (N M : ℕ) (f : Jet3) (v : ℕ→ℝ)
    (a : Fin M→Fin N→ℝ) (g : BulkMark N) (x : NormalizedSpin N) :
    ambientBulkHamiltonian N M f v a g x.val=bulkHamiltonian N M f.f v a g x := by
  simp only [ambientBulkHamiltonian,bulkHamiltonian,normalizedPatternEnergy,
    bulkPatternLinear_apply,ambientBulkFeature_eq,real_inner_comm g]

lemma ambientBulkHamiltonian_contDiff (N M : ℕ) (f : Jet3) (v : ℕ→ℝ)
    (a : Fin M→Fin N→ℝ) (g : BulkMark N) :
    ContDiff ℝ 1 (ambientBulkHamiltonian N M f v a g) := by
  apply (ContDiff.sum (fun j _ => (f.contDiff.of_le (by norm_num)).comp (bulkPatternLinear (a j)).contDiff)).add
  exact (innerSL ℝ g).contDiff.comp ((ambientBulkFeature_contDiff N v).of_le (by norm_num))

lemma ambientBulkHamiltonian_deriv (N M : ℕ) (f : Jet3) (v : ℕ→ℝ)
    (a : Fin M→Fin N→ℝ) (g : BulkMark N) (x z : Spin N) :
    fderiv ℝ (ambientBulkHamiltonian N M f v a g) x z =
      (∑ j,f.d1 (bulkPatternLinear (a j) x)*bulkPatternLinear (a j) z)+
        inner ℝ (fderiv ℝ (ambientBulkFeature N v) x z) g := by
  have hd := HasFDerivAt.fun_sum (fun j (_ : j∈(Finset.univ : Finset (Fin M))) =>
    (f.has1 (bulkPatternLinear (a j) x)).comp_hasFDerivAt x (bulkPatternLinear (a j)).hasFDerivAt)
  have hg := (innerSL ℝ g).hasFDerivAt.comp x
    (((ambientBulkFeature_contDiff N v).differentiable (by norm_num)) x).hasFDerivAt
  have he := (hd.add hg).fderiv
  change fderiv ℝ (ambientBulkHamiltonian N M f v a g) x z=_
  rw [show fderiv ℝ (ambientBulkHamiltonian N M f v a g) x = _ from he]
  simp only [add_apply,sum_apply,
    smul_apply,smul_eq_mul,ContinuousLinearMap.comp_apply,coe_innerSL_apply]
  rw [real_inner_comm g]

lemma bulk_gibbs_replica_tangent (n M : ℕ) (f : Jet3) (v : ℕ→ℝ)
    (a : Fin M→Fin (n+1)→ℝ) (g : BulkMark (n+1))
    (G : ℝ→ᵇℝ) (hG : ContDiff ℝ 1 (G : ℝ→ℝ)) :
    (n:ℝ)*gibbsReplicaMean (unitSphereLaw (n+1)) (bulkHamiltonian (n+1) M f.f v a g) 2
      (fun x => spinOverlap (x 0) (x 1)*G (spinOverlap (x 0) (x 1))) =
    gibbsReplicaMean (unitSphereLaw (n+1)) (bulkHamiltonian (n+1) M f.f v a g) 2
      (fun x => deriv (G : ℝ→ℝ) (spinOverlap (x 0) (x 1))*(1-spinOverlap (x 0) (x 1)^2)+
        (∑ j,G (spinOverlap (x 0) (x 1))*f.d1 (∑ i,a j i*(x 0).val i)*
          ((∑ i,a j i*(x 1).val i)-spinOverlap (x 0) (x 1)*(∑ i,a j i*(x 0).val i)))+
        inner ℝ (bulkTangentDirection (n+1) v G x) g) := by
  have he := unitSphere_gibbs_replica_tangent n (ambientBulkHamiltonian_contDiff (n+1) M f v a g) hG
  simp only [ambientBulkHamiltonian_eq] at he
  rw [he]
  apply congrArg (gibbsReplicaMean (unitSphereLaw (n+1)) (bulkHamiltonian (n+1) M f.f v a g) 2)
  funext x
  rw [ambientBulkHamiltonian_deriv]
  have hs : (∑ j,G (spinOverlap (x 0) (x 1))*
      (f.d1 (bulkPatternLinear (a j) (x 0).val)*
        bulkPatternLinear (a j) ((x 1).val-spinOverlap (x 0) (x 1) • (x 0).val))) =
      ∑ j,G (spinOverlap (x 0) (x 1))*f.d1 (∑ i,a j i*(x 0).val i)*
        ((∑ i,a j i*(x 1).val i)-spinOverlap (x 0) (x 1)*(∑ i,a j i*(x 0).val i)) := by
    apply Finset.sum_congr rfl
    intro j _
    simp only [map_sub,map_smul,smul_eq_mul,bulkPatternLinear_apply]
    ring
  simp only [bulkTangentDirection,inner_smul_left,starRingEnd_apply,star_trivial]
  rw [mul_add,Finset.mul_sum,hs]
  ring

end SphericalPerceptronFreeEnergy
end

end OAI
