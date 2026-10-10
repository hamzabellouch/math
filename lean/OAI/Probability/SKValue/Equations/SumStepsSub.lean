import Mathlib
import OAI.Probability.SKValue.Gaussian.GaussianSquareVariance

namespace OAI

section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators
namespace SKValue
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

lemma sum_steps_sub {N : ℕ} (U : ℕ → ℝ) :
    (∑ i : Fin N, (U (i+1)-U i))=U N-U 0 := by
  rw [Fin.sum_univ_eq_sum_range (fun j ↦ U (j+1)-U j)]
  exact Finset.sum_range_sub U N

lemma sum_local_residual {N : ℕ} (U : ℕ → ℝ) (V W : Fin N → ℝ) :
    (∑ i : Fin N, (U (i+1)-U i-V i-W i)) = U N-U 0-(∑ i, V i)-(∑ i, W i) := by
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, sum_steps_sub]

lemma sum_local_residual_bound {N : ℕ} {U : ℕ → ℝ} {V W P : Fin N → ℝ}
    {Γ : ℕ → ℝ} {α β : ℝ}
    (hlocal : ∀ i : Fin N, |U (i+1)-U i-V i-W i|≤α*P i+β*(Γ (i+1)-Γ i)) :
    |U N-U 0-(∑ i, V i)-(∑ i, W i)|≤α*(∑ i, P i)+β*(Γ N-Γ 0) := by
  rw [← sum_local_residual]
  calc
    _ ≤ ∑ i : Fin N, |U (i+1)-U i-V i-W i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin N, (α*P i+β*(Γ (i+1)-Γ i)) := Finset.sum_le_sum (fun i _ ↦ hlocal i)
    _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, sum_steps_sub]

lemma finite_envelope_memLp [IsProbabilityMeasure μ] {ι : Type*} [Fintype ι]
    {P : ι → Ω → ℝ} {R : Ω → ℝ} {α β : ℝ}
    (hα : 0≤α) (hβ : 0≤β) (hPm : ∀ i, MemLp (P i) 2 μ)
    (hPpos : ∀ i ω, 0≤P i ω) (hRm : AEStronglyMeasurable R μ)
    (hR : ∀ ω, |R ω|≤α*(∑ i, P i ω)+β) : MemLp R 2 μ := by
  have hsum : MemLp (fun ω ↦ ∑ i, P i ω) 2 μ := memLp_finsetSum _ (fun i _ ↦ hPm i)
  have henv := (hsum.const_mul α).add (memLp_const β)
  apply henv.mono hRm
  filter_upwards [] with ω
  have hs : 0≤∑ i, P i ω := Finset.sum_nonneg (fun i _ ↦ hPpos i ω)
  have he : 0≤α*(∑ i, P i ω)+β := add_nonneg (mul_nonneg hα hs) hβ
  simpa only [Pi.add_apply, Real.norm_eq_abs, abs_of_nonneg he] using hR ω

lemma integral_square_add_le {R Q : Ω → ℝ} (hR : MemLp R 2 μ) (hQ : MemLp Q 2 μ) :
    (∫ ω, (R ω+Q ω)^2 ∂μ)≤2*(∫ ω, (R ω)^2 ∂μ)+2*(∫ ω, (Q ω)^2 ∂μ) := by
  calc
    _ ≤ ∫ ω, 2*(R ω)^2+2*(Q ω)^2 ∂μ := by
      apply integral_mono (hR.add hQ).integrable_sq
        ((hR.integrable_sq.const_mul 2).add (hQ.integrable_sq.const_mul 2))
      intro ω
      change (R ω+Q ω)^2≤2*(R ω)^2+2*(Q ω)^2
      nlinarith [sq_nonneg (R ω-Q ω)]
    _ = _ := by
      rw [integral_add (hR.integrable_sq.const_mul 2) (hQ.integrable_sq.const_mul 2),
        integral_const_mul, integral_const_mul]

lemma discrete_gradient_residual_L2 {N : ℕ} {δ G K C : ℝ} {Γ : ℕ → ℝ}
    {U : ℕ → (Fin (N+1) → ℝ) → ℝ}
    {A H : Fin N → (Fin (N+1) → ℝ) → ℝ}
    (hδ : 0≤δ) (hG : 0≤G) (hK : 0≤K) (hC : 0≤C)
    (hΓ : Γ 0≤Γ N)
    (hUm : ∀ j ≤ N, Measurable (U j))
    (hAm : ∀ i, Measurable (A i))
    (hHm : ∀ i, Measurable (H i)) (hHp : ∀ i : Fin N, DependsBefore (i : ℕ) (H i))
    (hHb : ∀ i z, |H i z|≤K)
    (hloc : ∀ (i : Fin N) z,
      |U (i+1) z-U i z-Real.sqrt δ*A i z*coordinate N i z-
        (δ/2)*H i z*((coordinate N i z)^2-1)| ≤
      δ*Real.sqrt δ*cubicEnvelope G K C (coordinate N i z)+δ*K*(Γ (i+1)-Γ i)) :
    (∫ z, (U N z-U 0 z-∑ i : Fin N, Real.sqrt δ*A i z*coordinate N i z)^2
      ∂gaussianProduct (Fin (N+1))) ≤
      2*((δ/2)^2*(N : ℝ)*K^2*gaussianSquareVariance)+
      4*(δ*Real.sqrt δ)^2*(N : ℝ)^2*cubicEnvelopeMoment G K C+
      4*(δ*K*(Γ N-Γ 0))^2 := by
  let P (i : Fin N) (z : Fin (N+1) → ℝ) := cubicEnvelope G K C (coordinate N i z)
  let Q (z : Fin (N+1) → ℝ) :=
    (δ/2)*(∑ i : Fin N, H i z*((coordinate N i z)^2-1))
  let R (z : Fin (N+1) → ℝ) :=
    U N z-U 0 z-(∑ i : Fin N, Real.sqrt δ*A i z*coordinate N i z)-Q z
  have hPm (i : Fin N) : MemLp (P i) 2 (gaussianProduct (Fin (N+1))) :=
    cubicEnvelope_memLp_two (coordinate_hasLaw N i) hG K C
  have hPpos (i : Fin N) z : 0≤P i z := cubicEnvelope_nonneg hG hK hC _
  have hPval (i : Fin N) : (∫ z, (P i z)^2 ∂gaussianProduct (Fin (N+1)))≤cubicEnvelopeMoment G K C :=
    le_of_eq (cubicEnvelope_moment_eq (coordinate_hasLaw N i) G K C)
  have hQm : MemLp Q 2 (gaussianProduct (Fin (N+1))) :=
    (memLp_finsetSum Finset.univ (fun (i : Fin N) _ ↦
      predictableCenteredSquare_memLp (j := (i:ℕ)) (hHm i) (hHb i))).const_mul (δ/2)
  have hRm : Measurable R := by
    dsimp only [R, Q]
    exact ((hUm N le_rfl).sub (hUm 0 (Nat.zero_le _))).sub (Finset.measurable_fun_sum _ (fun i _ ↦
      ((hAm i).const_mul _).mul (measurable_coordinate N i))) |>.sub
        ((Finset.measurable_fun_sum _ (fun i _ ↦
          (hHm i).mul (((measurable_coordinate N i).pow_const 2).sub measurable_const))).const_mul _)
  have hRbound (z : Fin (N+1) → ℝ) :
      |R z|≤(δ*Real.sqrt δ)*(∑ i, P i z)+δ*K*(Γ N-Γ 0) := by
    have hb := sum_local_residual_bound (U := fun j ↦ U j z)
      (V := fun i ↦ Real.sqrt δ*A i z*coordinate N i z)
      (W := fun i ↦ (δ/2)*H i z*((coordinate N i z)^2-1))
      (P := fun i ↦ P i z) (Γ := Γ) (fun i ↦ hloc i z)
    simpa only [R, Q, P, mul_assoc, Finset.mul_sum] using hb
  have hβ : 0≤δ*K*(Γ N-Γ 0) := mul_nonneg (mul_nonneg hδ hK) (sub_nonneg.mpr hΓ)
  have hRmem := finite_envelope_memLp (by positivity : 0≤δ*Real.sqrt δ) hβ hPm hPpos
    hRm.aestronglyMeasurable hRbound
  have hRb := finite_envelope_L2_bound (by positivity : 0≤δ*Real.sqrt δ) hβ hPm hPpos hPval
    hRm.aestronglyMeasurable hRbound
  have hQb := predictableCenteredSquare_sum_bound (δ := δ) hK hHm hHp hHb
  have heq (z : Fin (N+1) → ℝ) : (U N z-U 0 z-∑ i : Fin N, Real.sqrt δ*A i z*coordinate N i z)=
      R z+Q z := by dsimp only [R]; ring
  simp_rw [heq]
  have hb := integral_square_add_le hRmem hQm
  simp only [Fintype.card_fin] at hRb
  dsimp only [Q] at hb
  nlinarith

end SKValue

end

end OAI
