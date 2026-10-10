import OAI.Analysis.LipschitzHilbert.Estimates.AmplitudeEnergy
import Mathlib.MeasureTheory.SpecificCodomains.WithLp
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex

namespace OAI

/-! The restricted-to-strong estimate for the actual finite amplitude
approximations of Hilbert-valued functions. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace LipschitzHilbert
variable {X κ : Type*} [MeasurableSpace X] [Fintype κ]

def amplitudePiece (f : X → EuclideanSpace ℂ κ) (i : ℤ) : X → EuclideanSpace ℂ κ :=
  (2:ℝ)^(-i) • (amplitudeLevel f i).indicator f

def amplitudeApprox (f : X → EuclideanSpace ℂ κ) (I : Finset ℤ) : X → EuclideanSpace ℂ κ :=
  ∑ i∈I, (2:ℝ)^i • amplitudePiece f i

theorem amplitudePiece_measurable {f : X → EuclideanSpace ℂ κ} (hf : Measurable f) (i : ℤ) :
    Measurable (amplitudePiece f i) :=
  measurable_const.smul (hf.indicator (amplitudeLevel_measurable hf.norm i))

omit [MeasurableSpace X] in
theorem amplitudePiece_bounded (f : X → EuclideanSpace ℂ κ) (i : ℤ) (x : X) :
    ‖amplitudePiece f i x‖≤1 := by
  by_cases hx : x∈amplitudeLevel f i
  · change ‖(2:ℝ)^(-i) • (amplitudeLevel f i).indicator f x‖≤1
    rw [Set.indicator_of_mem hx,norm_smul,Real.norm_of_nonneg (zpow_pos (by norm_num) _).le]
    calc
      _ ≤ (2:ℝ)^(-i)*(2:ℝ)^i := mul_le_mul_of_nonneg_left hx.2 (zpow_pos (by norm_num) _).le
      _ = _ := by rw [←zpow_add₀ (by norm_num : (2:ℝ)≠0)]; simp
  · simp only [amplitudePiece,Pi.smul_apply,Set.indicator_of_notMem hx,smul_zero,norm_zero,zero_le_one]

omit [MeasurableSpace X] in
theorem amplitudePiece_supported (f : X → EuclideanSpace ℂ κ) (i : ℤ) (x : X)
    (hx : x∉amplitudeLevel f i) : amplitudePiece f i x=0 := by
  simp only [amplitudePiece,Pi.smul_apply,Set.indicator_of_notMem hx,smul_zero]

omit [MeasurableSpace X] in
theorem amplitudeApprox_bilinear
    (B : (X → EuclideanSpace ℂ κ) →ₗ[ℝ] (X → EuclideanSpace ℂ κ) →ₗ[ℝ] ℂ)
    (f g : X → EuclideanSpace ℂ κ) (I J : Finset ℤ) :
    B (amplitudeApprox f I) (amplitudeApprox g J)=
      ∑ i∈I, ∑ j∈J, ((2:ℝ)^i*(2:ℝ)^j) • B (amplitudePiece f i) (amplitudePiece g j) := by
  simp only [amplitudeApprox,map_sum,map_smul,LinearMap.sum_apply,LinearMap.smul_apply,
    Finset.smul_sum,smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_comm]

theorem restricted_strong_finite_amplitudes (μ : Measure X)
    (B : (X → EuclideanSpace ℂ κ) →ₗ[ℝ] (X → EuclideanSpace ℂ κ) →ₗ[ℝ] ℂ)
    (C : ℝ) (hC : 0≤C)
    (hB : ∀ F G : Set X, MeasurableSet F → MeasurableSet G → μ F≠∞ → μ G≠∞ →
      0<μ.real F → 0<μ.real G →
      ∀ (u v : X → EuclideanSpace ℂ κ), Measurable u → Measurable v →
        (∀ x, ‖u x‖≤1) → (∀ x, ‖v x‖≤1) →
        (∀ x, x∉F → u x=0) → (∀ x, x∉G → v x=0) →
        ‖B u v‖≤C*((1+|Real.log (μ.real F/μ.real G)|)^3)⁻¹*Real.sqrt (μ.real F)*Real.sqrt (μ.real G))
    (f g : X → EuclideanSpace ℂ κ) (hf : Measurable f) (hg : Measurable g)
    (hf2 : MemLp f 2 μ) (hg2 : MemLp g 2 μ) (I J : Finset ℤ)
    (hI : ∀ i∈I, 0<μ.real (amplitudeLevel f i))
    (hJ : ∀ j∈J, 0<μ.real (amplitudeLevel g j)) :
    ‖B (amplitudeApprox f I) (amplitudeApprox g J)‖≤
      4*C*restrictedStrongConstant*Real.sqrt (∫ x, ‖f x‖^2 ∂μ)*Real.sqrt (∫ x, ‖g x‖^2 ∂μ) := by
  have h := finite_restricted_strong I J
    (fun i => μ.real (amplitudeLevel f i)) (fun j => μ.real (amplitudeLevel g j))
    (fun i j => B (amplitudePiece f i) (amplitudePiece g j)) C hC hI hJ
    (fun i hi j hj => hB _ _ (amplitudeLevel_measurable hf.norm i) (amplitudeLevel_measurable hg.norm j)
      (amplitudeLevel_finite μ hf2 i) (amplitudeLevel_finite μ hg2 j) (hI i hi) (hJ j hj)
      _ _ (amplitudePiece_measurable hf i) (amplitudePiece_measurable hg j)
      (amplitudePiece_bounded f i) (amplitudePiece_bounded g j)
      (amplitudePiece_supported f i) (amplitudePiece_supported g j))
  rw [←amplitudeApprox_bilinear] at h
  have hEf := amplitude_energy_budget μ hf2 hf.norm I
  have hEg := amplitude_energy_budget μ hg2 hg.norm J
  have hrootf : Real.sqrt (∑ i∈I, ((2:ℝ)^i*Real.sqrt (μ.real (amplitudeLevel f i)))^2)≤
      2*Real.sqrt (∫ x, ‖f x‖^2 ∂μ) := by
    calc
      _ ≤ Real.sqrt (4*(∫ x, ‖f x‖^2 ∂μ)) := Real.sqrt_le_sqrt hEf
      _ = _ := by rw [Real.sqrt_mul (by norm_num : (0:ℝ)≤4)]; norm_num
  have hrootg : Real.sqrt (∑ j∈J, ((2:ℝ)^j*Real.sqrt (μ.real (amplitudeLevel g j)))^2)≤
      2*Real.sqrt (∫ x, ‖g x‖^2 ∂μ) := by
    calc
      _ ≤ Real.sqrt (4*(∫ x, ‖g x‖^2 ∂μ)) := Real.sqrt_le_sqrt hEg
      _ = _ := by rw [Real.sqrt_mul (by norm_num : (0:ℝ)≤4)]; norm_num
  apply h.trans
  calc
    _ ≤ C*restrictedStrongConstant*(2*Real.sqrt (∫ x, ‖f x‖^2 ∂μ))*(2*Real.sqrt (∫ x, ‖g x‖^2 ∂μ)) := by
      have hconst := restrictedStrongConstant_pos.le
      gcongr
    _ = _ := by ring

end LipschitzHilbert

end

end OAI
