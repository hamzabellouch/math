import Mathlib

namespace OAI

section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology
namespace SKValue
variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
  {μ : Measure Ω} {g : ι → Ω → ℝ}

lemma memLp_linearCombination (hg : ∀ i, MemLp (g i) 2 μ) (b : ι → ℝ) :
    MemLp (fun ω ↦ ∑ i, b i*g i ω) 2 μ := by
  exact memLp_finsetSum Finset.univ (fun i _ ↦ (hg i).const_mul (b i))

lemma integral_linearCombination_mul (hg : ∀ i, MemLp (g i) 2 μ)
    {R : Ω → ℝ} (hR : MemLp R 2 μ) (b : ι → ℝ) :
    (∫ ω, (∑ i, b i*g i ω)*R ω ∂μ) =
      ∑ i, b i*(∫ ω, g i ω*R ω ∂μ) := by
  have hi : ∀ i, Integrable (fun ω ↦ g i ω*R ω) μ := fun i ↦ (hg i).integrable_mul hR
  simp only [Finset.sum_mul, mul_assoc]
  rw [integral_finsetSum Finset.univ (fun i _ ↦ (hi i).const_mul (b i))]
  simp only [integral_const_mul]

variable [DecidableEq ι]

lemma orthogonal_linearCombination_coefficient (hg : ∀ i, MemLp (g i) 2 μ)
    (horth : ∀ i j, (∫ ω, g i ω*g j ω ∂μ) = if i=j then 1 else 0)
    (b : ι → ℝ) (j : ι) :
    (∫ ω, (∑ i, b i*g i ω)*g j ω ∂μ) = b j := by
  rw [integral_linearCombination_mul hg (hg j)]
  simp [horth]

lemma orthogonal_linearCombination_square (hg : ∀ i, MemLp (g i) 2 μ)
    (horth : ∀ i j, (∫ ω, g i ω*g j ω ∂μ) = if i=j then 1 else 0)
    (b : ι → ℝ) :
    (∫ ω, (∑ i, b i*g i ω)^2 ∂μ) = ∑ i, (b i)^2 := by
  simp only [pow_two]
  rw [integral_linearCombination_mul hg (memLp_linearCombination hg b)]
  apply Finset.sum_congr rfl
  intro j _
  rw [show (fun ω ↦ g j ω*(∑ i, b i*g i ω)) =
      (fun ω ↦ (∑ i, b i*g i ω)*g j ω) from funext (fun _ ↦ mul_comm _ _),
    orthogonal_linearCombination_coefficient hg horth]

lemma finite_bessel (hg : ∀ i, MemLp (g i) 2 μ)
    (horth : ∀ i j, (∫ ω, g i ω*g j ω ∂μ) = if i=j then 1 else 0)
    {R : Ω → ℝ} (hR : MemLp R 2 μ) :
    (∑ i, (∫ ω, R ω*g i ω ∂μ)^2) ≤ ∫ ω, (R ω)^2 ∂μ := by
  let b : ι → ℝ := fun i ↦ ∫ ω, R ω*g i ω ∂μ
  let V : Ω → ℝ := fun ω ↦ ∑ i, b i*g i ω
  have hV : MemLp V 2 μ := memLp_linearCombination hg b
  have hRR : Integrable (fun ω ↦ (R ω)^2) μ := by
    convert hR.integrable_mul hR using 1
    ext ω
    simp [pow_two]
  have hVV : Integrable (fun ω ↦ (V ω)^2) μ := by
    convert hV.integrable_mul hV using 1
    ext ω
    simp [pow_two]
  have hVR : Integrable (fun ω ↦ V ω*R ω) μ := hV.integrable_mul hR
  have hVRval : (∫ ω, V ω*R ω ∂μ) = ∑ i, (b i)^2 := by
    rw [show V = (fun ω ↦ ∑ i, b i*g i ω) from rfl,
      integral_linearCombination_mul hg hR]
    apply Finset.sum_congr rfl
    intro i _
    dsimp only [b]
    rw [show (fun ω ↦ g i ω*R ω) = (fun ω ↦ R ω*g i ω) from funext (fun _ ↦ mul_comm _ _)]
    ring
  have hVVval : (∫ ω, (V ω)^2 ∂μ) = ∑ i, (b i)^2 :=
    orthogonal_linearCombination_square hg horth b
  have hdif : Integrable (fun ω ↦ (R ω)^2 - 2*(V ω*R ω)) μ := by
    exact hRR.sub (hVR.const_mul 2)
  have hs : (∫ ω, (R ω-V ω)^2 ∂μ) =
      (∫ ω, (R ω)^2 ∂μ) - ∑ i, (b i)^2 := by
    rw [show (fun ω ↦ (R ω-V ω)^2) =
        (fun ω ↦ (R ω)^2 - 2*(V ω*R ω) + (V ω)^2) from funext (fun _ ↦ by ring),
      integral_add hdif hVV,
      integral_sub hRR (hVR.const_mul 2), integral_const_mul, hVRval, hVVval]
    ring
  have hp : 0 ≤ ∫ ω, (R ω-V ω)^2 ∂μ := integral_nonneg (fun _ ↦ sq_nonneg _)
  rw [hs] at hp
  exact sub_nonneg.mp hp

lemma finite_projection_error (hg : ∀ i, MemLp (g i) 2 μ)
    (horth : ∀ i j, (∫ ω, g i ω*g j ω ∂μ) = if i=j then 1 else 0)
    {R M : Ω → ℝ} (hR : MemLp R 2 μ) (hM : MemLp M 2 μ) :
    (∑ i, ((∫ ω, R ω*g i ω ∂μ)-(∫ ω, M ω*g i ω ∂μ))^2) ≤
      ∫ ω, (R ω-M ω)^2 ∂μ := by
  have h := finite_bessel hg horth (hR.sub hM)
  have hi : ∀ i, (∫ ω, (R ω-M ω)*g i ω ∂μ) =
      (∫ ω, R ω*g i ω ∂μ)-(∫ ω, M ω*g i ω ∂μ) := by
    intro i
    have hRi : Integrable (fun ω ↦ R ω*g i ω) μ := hR.integrable_mul (hg i)
    have hMi : Integrable (fun ω ↦ M ω*g i ω) μ := hM.integrable_mul (hg i)
    simp_rw [sub_mul]
    exact integral_sub hRi hMi
  simpa only [Pi.sub_apply, hi] using h

end SKValue

end

end OAI
