import OAI.MathematicalPhysics.CriticalSK.CubeOverlap
import OAI.MathematicalPhysics.CriticalSK.OverlapMoments

namespace OAI

noncomputable section

open scoped BigOperators Topology NNReal ENNReal

open MeasureTheory ProbabilityTheory

open scoped ENNReal NNReal

open scoped BigOperators InnerProductSpace

open Module

open scoped BigOperators ENNReal NNReal Real Topology

open MeasureTheory ProbabilityTheory Filter

open scoped BigOperators NNReal

open scoped BigOperators

open Matrix Polynomial

open scoped BigOperators Topology

open Filter

open scoped BigOperators NNReal ENNReal Topology Pointwise Matrix.Norms.Elementwise

open Set Metric MeasureTheory MeasureTheory.Measure

open scoped ENNReal NNReal Topology

open MeasureTheory MeasureTheory.Measure Set Metric

open scoped BigOperators ENNReal Topology

open Set MeasureTheory

open scoped BigOperators ENNReal

open MeasureTheory

open Finset Real

open Finset Real Filter

open scoped Topology

open MeasureTheory Filter Set Real

open scoped ENNReal NNReal BigOperators

open scoped NNReal ENNReal BigOperators

open scoped NNReal ENNReal

open ProbabilityTheory

open Metric Set MeasureTheory

open scoped ENNReal Pointwise

open MeasureTheory Filter Set
namespace CriticalSK

section

def rotatedCubePair {n : ℕ} (lam : Fin n → ℝ) (g : ℝ → ℝ)
    (U : Matrix.orthogonalGroup (Fin n) ℝ) : ℝ :=
  (Fintype.card (Spin n) : ℝ)⁻¹^2 * ∑ x : Spin n, ∑ y : Spin n,
    g (cubeOverlap x y)*Real.exp ((diagonalEnergy lam (orthogonalIsometry U (cubeVector x))+
      diagonalEnergy lam (orthogonalIsometry U (cubeVector y)))/2)

lemma rotatedCubePair_continuous {n : ℕ} (lam : Fin n → ℝ) (g : ℝ → ℝ) :
    Continuous (rotatedCubePair lam g) := by
  apply Continuous.const_mul
  apply continuous_finsetSum
  intro x _
  apply continuous_finsetSum
  intro y _
  exact (cube_pair_energy_continuous lam x y).const_mul _

lemma rotatedCubePair_haar {n : ℕ} (hn : 0 < n) (lam : Fin n → ℝ) (g : ℝ → ℝ)
    {u v : EuclideanSpace ℝ (Fin n)} (hu : ‖u‖ = Real.sqrt n) (hv : ‖v‖ = Real.sqrt n)
    (horth : inner ℝ u v = 0) :
    (∫ U, rotatedCubePair lam g U ∂orthogonalHaar (Fin n)) =
      (2:ℝ)⁻¹^n * ∑ j ∈ Finset.range (n+1), (Nat.choose n j:ℝ)*
        (g (-1+2*(j:ℝ)/n)*pairMoment lam u v (-1+2*(j:ℝ)/n)) := by
  have hi (x y : Spin n) := (orthogonalHaar_integrable (cube_pair_energy_continuous lam x y)).const_mul
    (g (cubeOverlap x y))
  simp_rw [rotatedCubePair]
  rw [integral_const_mul]
  rw [integral_finsetSum _ (fun x _ => integrable_finsetSum _ (fun y _ => hi x y))]
  have hinner (x : Spin n) : (∫ U, ∑ y : Spin n,
      g (cubeOverlap x y)*Real.exp ((diagonalEnergy lam (orthogonalIsometry U (cubeVector x))+
        diagonalEnergy lam (orthogonalIsometry U (cubeVector y)))/2) ∂orthogonalHaar (Fin n)) =
      ∑ y : Spin n, g (cubeOverlap x y)*pairMoment lam u v (cubeOverlap x y) := by
    rw [integral_finsetSum _ (fun y _ => hi x y)]
    apply Finset.sum_congr rfl
    intro y _
    rw [integral_const_mul,pair_energy_orbit lam (cubeVector_norm x) (cubeVector_norm y) hu hv horth
      (cubeOverlap_abs_le_one x y) (cubeOverlap_gram hn x y)]
  simp_rw [hinner]
  exact cubeOverlap_binomial_sum hn (fun q => g q*pairMoment lam u v q)

lemma rotatedCubePair_lattice {n : ℕ} (hn : 0 < n) (lam : Fin n → ℝ) (g : ℝ → ℝ)
    {u v : EuclideanSpace ℝ (Fin n)} (hu : ‖u‖ = Real.sqrt n) (hv : ‖v‖ = Real.sqrt n)
    (horth : inner ℝ u v = 0) :
    (∫ U, rotatedCubePair lam g U ∂orthogonalHaar (Fin n)) =
      ∑ j ∈ Finset.range (n+1), cubeOverlapMass n j*
        (g (latticeOverlap n j)*pairMoment lam u v (latticeOverlap n j)) := by
  rw [rotatedCubePair_haar hn lam g hu hv horth,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [cubeOverlapMass,latticeOverlap,mul_assoc]

lemma squaredPairMoment_mono_abs {ι : Type*} [Fintype ι] [DecidableEq ι]
    (lam : ι → ℝ) {u v : EuclideanSpace ℝ ι} (huv : ‖u‖ = ‖v‖)
    {q t : ℝ} (hqt : |q| ≤ |t|) : q^2*pairMoment lam u v q ≤ t^2*pairMoment lam u v t := by
  have hsq : q^2 ≤ t^2 := by simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg q) hqt 2
  exact mul_le_mul hsq (pairMoment_mono_abs lam huv hqt) (pairMoment_nonneg lam u v q) (sq_nonneg t)

lemma sphereOverlap_density_weighted_moment (n : ℕ) (lam : Fin (n+4) → ℝ)
    {u v : EuclideanSpace ℝ (Fin (n+4))} {r : ℝ}
    (hr : 0 < r) (hu : ‖u‖ = r) (hv : ‖v‖ = r) (horth : inner ℝ u v = 0) :
    (∫ q : ℝ, (q^2*pairMoment lam u v q)*sphereOverlapDensity (n+4) q) / spherePartition lam 1 r^2 =
      (∑ i, (∫ x : unitSphere (Fin (n+4)), ((r • x.val) i)^2 ∂sphereTilted lam 1 r)^2)/r^4 := by
  rw [← normalizedOverlapShape_integral (by omega : 4 ≤ n+4),← sphereOverlapLaw_density (n+1)]
  exact sphereOverlap_square_moment lam hr hu hv horth

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

lemma orthogonal_radial_integral (F : EuclideanSpace ℝ ι → ℝ) (hF : Measurable F)
    {r : ℝ} (hr : 0 < r) (x : EuclideanSpace ℝ ι) (hx : ‖x‖ = r) :
    (∫ U, F (orthogonalIsometry U x) ∂orthogonalHaar ι) =
      sphereAverage (fun u => F (r • u.val)) := by
  have hu : ‖r⁻¹ • x‖ = 1 := by
    rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hr.le),hx,inv_mul_cancel₀ hr.ne']
  let u : unitSphere ι := ⟨r⁻¹ • x,mem_sphere_zero_iff_norm.mpr hu⟩
  have he : r • u.val = x := by
    change r • (r⁻¹ • x) = x
    rw [smul_smul,mul_inv_cancel₀ hr.ne',one_smul]
  have hf : (fun U : Matrix.orthogonalGroup ι ℝ => F (orthogonalIsometry U x)) =
      fun U => F (r • (orthogonalSphere U u).val) := by
    funext U
    rw [← he,(orthogonalIsometry U).map_smul]
    rfl
  rw [hf,← sphereUniform_integral,← (orthogonal_sphere_preserving u).map_eq]
  exact (integral_map (orthogonal_sphere_preserving u).measurable.aemeasurable
    (hF.comp (show Measurable (fun v : unitSphere ι => r • v.val) by fun_prop)).aestronglyMeasurable).symm

omit [DecidableEq ι] in
lemma sphereRestricted_as_tilted (lam : ι → ℝ) (a r b : ℝ) (i : ι) :
    sphereAverage (fun u => if |(r • u.val) i| ≤ b then
      Real.exp (a/2*diagonalEnergy lam (r • u.val)) else 0) =
      spherePartition lam a r * (sphereTilted lam a r).real
        {u : unitSphere ι | |(r • u.val) i| ≤ b} := by
  have hA : MeasurableSet {u : unitSphere ι | |(r • u.val) i| ≤ b} :=
    measurableSet_le (by fun_prop) measurable_const
  rw [Measure.real,sphereTilted_apply_real lam a r hA,← integral_indicator hA]
  unfold spherePartition sphereAverage
  have hZ := (sphereWeight_integral_pos lam a r).ne'
  have he : (fun u : unitSphere ι => if |(r • u.val) i| ≤ b then
      Real.exp (a/2*diagonalEnergy lam (r • u.val)) else 0) =
      {u : unitSphere ι | |(r • u.val) i| ≤ b}.indicator
        (fun u => Real.exp (a/2*diagonalEnergy lam (r • u.val))) := rfl
  rw [he]
  simp only [div_mul_eq_mul_div] at hZ ⊢
  field_simp [hZ]

end

def rotatedCubeRestricted {n : ℕ} (lam : Fin n → ℝ) (a b : ℝ) (i : Fin n)
    (U : Matrix.orthogonalGroup (Fin n) ℝ) : ℝ :=
  (Fintype.card (Spin n):ℝ)⁻¹ * ∑ x : Spin n,
    if |(orthogonalIsometry U (cubeVector x)) i| ≤ b then
      Real.exp (a/2*diagonalEnergy lam (orthogonalIsometry U (cubeVector x))) else 0

lemma rotatedCubeRestricted_measurable {n : ℕ} (lam : Fin n → ℝ) (a b : ℝ) (i : Fin n) :
    Measurable (rotatedCubeRestricted lam a b i) := by
  unfold rotatedCubeRestricted
  apply Measurable.const_mul
  apply Finset.measurable_sum
  intro x _
  have hc := orthogonalIsometry_fixed_continuous (cubeVector x)
  apply Measurable.ite (measurableSet_le ((EuclideanSpace.proj i).continuous.comp hc).abs.measurable measurable_const)
  · exact ((continuous_const.mul ((diagonalEnergy_continuous lam).comp hc)).rexp).measurable
  · exact measurable_const

lemma rotatedCubeRestricted_nonneg {n : ℕ} (lam : Fin n → ℝ) (a b : ℝ) (i : Fin n)
    (U : Matrix.orthogonalGroup (Fin n) ℝ) : 0 ≤ rotatedCubeRestricted lam a b i U := by
  unfold rotatedCubeRestricted
  positivity

lemma rotatedCubeRestricted_le {n : ℕ} (lam : Fin n → ℝ) (a b : ℝ) (i : Fin n)
    (U : Matrix.orthogonalGroup (Fin n) ℝ) : rotatedCubeRestricted lam a b i U ≤ rotatedCubePartition lam a U := by
  unfold rotatedCubeRestricted rotatedCubePartition
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Finset.sum_le_sum
  intro x _
  split_ifs
  · exact le_rfl
  · exact (Real.exp_pos _).le

lemma rotatedCubeRestricted_integrable {n : ℕ} (lam : Fin n → ℝ) (a b : ℝ) (i : Fin n) :
    Integrable (rotatedCubeRestricted lam a b i) (orthogonalHaar (Fin n)) := by
  apply (orthogonalHaar_integrable (rotatedCubePartition_continuous lam a)).mono'
    (rotatedCubeRestricted_measurable lam a b i).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun U => by
    rw [Real.norm_eq_abs,abs_of_nonneg (rotatedCubeRestricted_nonneg lam a b i U)]
    exact rotatedCubeRestricted_le lam a b i U)

lemma rotatedCubeRestricted_first_moment {n : ℕ} (hn : 0 < n) (lam : Fin n → ℝ) (a b : ℝ) (i : Fin n) :
    (∫ U, rotatedCubeRestricted lam a b i U ∂orthogonalHaar (Fin n)) =
      spherePartition lam a (Real.sqrt n)*(sphereTilted lam a (Real.sqrt n)).real
        {u : unitSphere (Fin n) | |(Real.sqrt n • u.val) i| ≤ b} := by
  classical
  let : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  let F : EuclideanSpace ℝ (Fin n) → ℝ := fun x =>
    if |x i| ≤ b then Real.exp (a/2*diagonalEnergy lam x) else 0
  have hF : Measurable F := Measurable.ite (measurableSet_le (by fun_prop) measurable_const)
    (continuous_const.mul (diagonalEnergy_continuous lam)).rexp.measurable measurable_const
  have hint (x : Spin n) : Integrable (fun U : Matrix.orthogonalGroup (Fin n) ℝ => F (orthogonalIsometry U (cubeVector x)))
      (orthogonalHaar (Fin n)) := by
    have hc := orthogonalIsometry_fixed_continuous (cubeVector x)
    apply (orthogonalHaar_integrable (((continuous_const (y := a/2)).mul ((diagonalEnergy_continuous lam).comp hc)).rexp)).mono'
      (hF.comp hc.measurable).aestronglyMeasurable
    filter_upwards [] with U
    dsimp only [F,Function.comp_apply,Pi.mul_apply]
    split_ifs
    · simp only [Real.norm_eq_abs,abs_of_nonneg (Real.exp_pos _).le,le_refl]
    · simpa only [norm_zero] using (Real.exp_pos (a/2*diagonalEnergy lam (orthogonalIsometry U (cubeVector x)))).le
  have he (x : Spin n) : (∫ U, F (orthogonalIsometry U (cubeVector x)) ∂orthogonalHaar (Fin n)) =
      spherePartition lam a (Real.sqrt n)*(sphereTilted lam a (Real.sqrt n)).real
        {u : unitSphere (Fin n) | |(Real.sqrt n • u.val) i| ≤ b} := by
    rw [orthogonal_radial_integral F hF (Real.sqrt_pos.mpr (by exact_mod_cast hn)) _ (cubeVector_norm x)]
    exact sphereRestricted_as_tilted lam a (Real.sqrt n) b i
  unfold rotatedCubeRestricted
  change (∫ U, (Fintype.card (Spin n):ℝ)⁻¹*∑ x : Spin n, F (orthogonalIsometry U (cubeVector x))
    ∂orthogonalHaar (Fin n)) = _
  rw [integral_const_mul,integral_finsetSum _ (fun x _ => hint x)]
  simp only [he,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  rw [← mul_assoc,inv_mul_cancel₀ (by positivity : (Fintype.card (Spin n):ℝ) ≠ 0),one_mul]

lemma divided_mass_variance_bound {A Z S : ℝ} (hA : 0 ≤ A) (hAZ : A ≤ Z)
    (hZ : 0 < Z) (hS : 0 < S) : A/Z ≤ 2*A/S+4*(Z/S-1)^2 := by
  by_cases hz : S/2 ≤ Z
  · have hh : A/Z ≤ 2*A/S := by
      rw [div_le_div_iff₀ hZ hS]
      nlinarith [mul_nonneg hA (sub_nonneg.mpr hz)]
    linarith [sq_nonneg (Z/S-1)]
  · have hratio : A/Z ≤ 1 := (div_le_one hZ).mpr hAZ
    have hfrac : Z/S < 1/2 := (div_lt_iff₀ hS).mpr (by linarith)
    have hfrac0 : 0 ≤ Z/S := div_nonneg hZ.le hS.le
    have he : 1 ≤ 4*(Z/S-1)^2 := by nlinarith [sq_nonneg (Z/S)]
    have hnon : 0 ≤ 2*A/S := by positivity
    linarith

lemma normalized_pair_event_bound {B Z S K : ℝ} (hB : 0 ≤ B) (hZ : 0 < Z)
    (hS : 0 < S) (hK : 0 < K) (hlarge : K ≤ B/Z^2) :
    1 ≤ 4*(Z/S-1)^2+4*(B/S^2)/K := by
  by_cases hz : S/2 ≤ Z
  · have hf : 1 ≤ 4*(B/S^2)/K := by
      have hb := (le_div_iff₀ (sq_pos_of_pos hZ)).mp hlarge
      have hsq : S^2 ≤ 4*Z^2 := by nlinarith
      apply (le_div_iff₀ hK).mpr
      rw [← mul_div_assoc]
      apply (le_div_iff₀ (sq_pos_of_pos hS)).mpr
      nlinarith [mul_le_mul_of_nonneg_left hsq hK.le]
    linarith [sq_nonneg (Z/S-1)]
  · have hfrac : Z/S < 1/2 := (div_lt_iff₀ hS).mpr (by linarith)
    have hfrac0 : 0 ≤ Z/S := div_nonneg hZ.le hS.le
    have he : 1 ≤ 4*(Z/S-1)^2 := by nlinarith [sq_nonneg (Z/S)]
    have hnon : 0 ≤ 4*(B/S^2)/K := by positivity
    linarith

lemma integral_dominates_event {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ] {E : Set Ω} {f : Ω → ℝ}
    (hi : Integrable f μ) (hf : ∀ x, 0 ≤ f x) (he : ∀ x ∈ E, 1 ≤ f x) :
    μ.real E ≤ ∫ x, f x ∂μ := by
  apply (measureReal_mono (show E ⊆ {x | 1 ≤ f x} from he)).trans
  simpa only [one_mul] using mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall hf) hi 1

lemma rotatedCubePartition_pos {n : ℕ} (lam : Fin n → ℝ) (a : ℝ)
    (U : Matrix.orthogonalGroup (Fin n) ℝ) : 0 < rotatedCubePartition lam a U := by
  unfold rotatedCubePartition
  apply mul_pos (by positivity)
  exact Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty

def rotatedCubeSmallBall {n : ℕ} (lam : Fin n → ℝ) (b : ℝ) (i : Fin n)
    (U : Matrix.orthogonalGroup (Fin n) ℝ) : ℝ :=
  rotatedCubeRestricted lam 1 b i U/rotatedCubePartition lam 1 U

lemma rotatedCubeSmallBall_measurable {n : ℕ} (lam : Fin n → ℝ) (b : ℝ) (i : Fin n) :
    Measurable (rotatedCubeSmallBall lam b i) :=
  (rotatedCubeRestricted_measurable lam 1 b i).div (rotatedCubePartition_continuous lam 1).measurable

lemma rotatedCubeSmallBall_nonneg {n : ℕ} (lam : Fin n → ℝ) (b : ℝ) (i : Fin n)
    (U : Matrix.orthogonalGroup (Fin n) ℝ) : 0 ≤ rotatedCubeSmallBall lam b i U :=
  div_nonneg (rotatedCubeRestricted_nonneg lam 1 b i U) (rotatedCubePartition_pos lam 1 U).le

lemma rotatedCubeSmallBall_le_one {n : ℕ} (lam : Fin n → ℝ) (b : ℝ) (i : Fin n)
    (U : Matrix.orthogonalGroup (Fin n) ℝ) : rotatedCubeSmallBall lam b i U ≤ 1 :=
  (div_le_one (rotatedCubePartition_pos lam 1 U)).mpr (rotatedCubeRestricted_le lam 1 b i U)

lemma rotatedCubeSmallBall_integrable {n : ℕ} (lam : Fin n → ℝ) (b : ℝ) (i : Fin n) :
    Integrable (rotatedCubeSmallBall lam b i) (orthogonalHaar (Fin n)) := by
  apply (integrable_const (1:ℝ)).mono' (rotatedCubeSmallBall_measurable lam b i).aestronglyMeasurable
  filter_upwards [] with U
  rw [Real.norm_eq_abs,abs_of_nonneg (rotatedCubeSmallBall_nonneg lam b i U)]
  exact rotatedCubeSmallBall_le_one lam b i U

lemma rotatedCubeSmallBall_expectation {n : ℕ} (hn : 0 < n) (lam : Fin n → ℝ) (b : ℝ) (i : Fin n) :
    (∫ U, rotatedCubeSmallBall lam b i U ∂orthogonalHaar (Fin n)) ≤
      2*(sphereTilted lam 1 (Real.sqrt n)).real {u : unitSphere (Fin n) | |(Real.sqrt n • u.val) i| ≤ b}+
      4*(∫ U, (rotatedCubePartition lam 1 U/spherePartition lam 1 (Real.sqrt n)-1)^2
        ∂orthogonalHaar (Fin n)) := by
  let : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  let S := spherePartition lam 1 (Real.sqrt n)
  have hS : 0 < S := spherePartition_pos _ _ _
  have hA := (rotatedCubeRestricted_integrable lam 1 b i).const_mul 2
  have hV : Integrable (fun U => (rotatedCubePartition lam 1 U / S - 1)^2) (orthogonalHaar (Fin n)) := orthogonalHaar_integrable (((rotatedCubePartition_continuous lam 1).div_const S).sub continuous_const |>.pow 2)
  have hh := integral_mono (rotatedCubeSmallBall_integrable lam b i) ((hA.div_const S).add (hV.const_mul 4))
    (fun U => divided_mass_variance_bound (rotatedCubeRestricted_nonneg lam 1 b i U)
      (rotatedCubeRestricted_le lam 1 b i U) (rotatedCubePartition_pos lam 1 U) hS)
  simp only [Pi.add_apply] at hh
  rw [integral_add (hA.div_const S) (hV.const_mul 4),integral_div,integral_const_mul,integral_const_mul,
    rotatedCubeRestricted_first_moment hn,show spherePartition lam 1 (Real.sqrt n) = S from rfl] at hh
  have heq : 2*(S*(sphereTilted lam 1 (Real.sqrt n)).real {u : unitSphere (Fin n) | |(Real.sqrt n • u.val) i| ≤ b})/S =
      2*(sphereTilted lam 1 (Real.sqrt n)).real {u : unitSphere (Fin n) | |(Real.sqrt n • u.val) i| ≤ b} := by
    field_simp
  rw [heq] at hh
  exact hh

def rotatedCubeOverlap {n : ℕ} (lam : Fin n → ℝ)
    (U : Matrix.orthogonalGroup (Fin n) ℝ) : ℝ :=
  rotatedCubePair lam (fun q => q^2) U/rotatedCubePartition lam 1 U^2

lemma rotatedCubePair_square_nonneg {n : ℕ} (lam : Fin n → ℝ)
    (U : Matrix.orthogonalGroup (Fin n) ℝ) : 0 ≤ rotatedCubePair lam (fun q => q^2) U := by
  unfold rotatedCubePair
  positivity

lemma rotatedCubeOverlap_probability {n : ℕ} (hn : 0 < n) (lam : Fin n → ℝ) {K : ℝ} (hK : 0 < K) :
    (orthogonalHaar (Fin n)).real {U | K ≤ rotatedCubeOverlap lam U} ≤
      4*(∫ U, (rotatedCubePartition lam 1 U/spherePartition lam 1 (Real.sqrt n)-1)^2 ∂orthogonalHaar (Fin n))+
      4*((∫ U, rotatedCubePair lam (fun q => q^2) U ∂orthogonalHaar (Fin n))/spherePartition lam 1 (Real.sqrt n)^2)/K := by
  let : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  let S := spherePartition lam 1 (Real.sqrt n)
  have hS : 0 < S := spherePartition_pos _ _ _
  have hV : Integrable (fun U => (rotatedCubePartition lam 1 U / S - 1)^2) (orthogonalHaar (Fin n)) := orthogonalHaar_integrable (((rotatedCubePartition_continuous lam 1).div_const S).sub continuous_const |>.pow 2)
  have hB := orthogonalHaar_integrable (rotatedCubePair_continuous lam (fun q => q^2))
  have hh := integral_dominates_event ((hV.const_mul 4).add (((hB.div_const (S^2)).const_mul 4).div_const K))
    (fun U => by dsimp; have := rotatedCubePair_square_nonneg lam U; positivity) (fun U hU => normalized_pair_event_bound
      (rotatedCubePair_square_nonneg lam U) (rotatedCubePartition_pos lam 1 U) hS hK hU)
  simp only [Pi.add_apply] at hh
  rw [integral_add (hV.const_mul 4) (((hB.div_const (S^2)).const_mul 4).div_const K),
    integral_const_mul,integral_div,integral_const_mul,integral_div] at hh
  exact hh

end CriticalSK

end

end OAI
