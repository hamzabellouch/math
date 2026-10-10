import OAI.Analysis.Laughlin.Spin.CompactAverage

namespace OAI

namespace Laughlin.Rotation
open scoped BigOperators
open MeasureTheory MeasureTheory.Measure
variable {G I J : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] [CompactSpace G]
  [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

noncomputable def rectangularIntegral (μ : Measure G) (f : G → Matrix I J ℂ) : Matrix I J ℂ :=
  fun i j => ∫ g, f g i j ∂μ
noncomputable def rectangularOrbit (ρ : G →* Matrix I I ℂ) (σ : G →* Matrix J J ℂ)
    (M : Matrix I J ℂ) (g : G) : Matrix I J ℂ := ρ g*M*σ g⁻¹

omit [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
  [CompactSpace G] in
theorem rectangularOrbit_mul (ρ : G →* Matrix I I ℂ) (σ : G →* Matrix J J ℂ)
    (M : Matrix I J ℂ) (g h : G) :
    rectangularOrbit ρ σ M (g*h)=ρ g*rectangularOrbit ρ σ M h*σ g⁻¹ := by
  simp only [rectangularOrbit,map_mul,mul_inv_rev,Matrix.mul_assoc]

theorem compact_rectangularOrbit_integrable (μ : Measure G) [IsFiniteMeasure μ]
    (ρ : G →* Matrix I I ℂ) (σ : G →* Matrix J J ℂ)
    (hρ : ∀ i j, Continuous (fun g => ρ g i j)) (hσ : ∀ i j, Continuous (fun g => σ g i j))
    (M : Matrix I J ℂ) (i : I) (j : J) : Integrable (fun g => rectangularOrbit ρ σ M g i j) μ := by
  have hc : Continuous (fun g => rectangularOrbit ρ σ M g i j) := by
    simp only [rectangularOrbit,Matrix.mul_apply]
    fun_prop
  exact hc.integrable_of_hasCompactSupport (isClosed_tsupport _).isCompact

omit [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G] [CompactSpace G]
  [DecidableEq I] [Fintype J] [DecidableEq J] in
theorem rectangularIntegral_mul_left (μ : Measure G) (f : G → Matrix I J ℂ)
    (hf : ∀ i j, Integrable (fun g => f g i j) μ) (A : Matrix I I ℂ) :
    rectangularIntegral μ (fun g => A*f g)=A*rectangularIntegral μ f := by
  ext i j
  simp only [rectangularIntegral,Matrix.mul_apply]
  rw [integral_finsetSum _ (fun k hk => (hf k j).const_mul (A i k))]
  simp only [integral_const_mul]

omit [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G] [CompactSpace G]
  [Fintype I] [DecidableEq I] [DecidableEq J] in
theorem rectangularIntegral_mul_right (μ : Measure G) (f : G → Matrix I J ℂ)
    (hf : ∀ i j, Integrable (fun g => f g i j) μ) (A : Matrix J J ℂ) :
    rectangularIntegral μ (fun g => f g*A)=rectangularIntegral μ f*A := by
  ext i j
  simp only [rectangularIntegral,Matrix.mul_apply]
  rw [integral_finsetSum _ (fun k hk => (hf i k).mul_const (A k j))]
  simp only [integral_mul_const]

theorem compact_rectangular_average_intertwines (μ : Measure G) [IsProbabilityMeasure μ]
    [IsMulLeftInvariant μ] (ρ : G →* Matrix I I ℂ) (σ : G →* Matrix J J ℂ)
    (hρ : ∀ i j, Continuous (fun g => ρ g i j)) (hσ : ∀ i j, Continuous (fun g => σ g i j))
    (M : Matrix I J ℂ) (h : G) :
    ρ h*rectangularIntegral μ (rectangularOrbit ρ σ M)=
      rectangularIntegral μ (rectangularOrbit ρ σ M)*σ h := by
  have hf := compact_rectangularOrbit_integrable μ ρ σ hρ hσ M
  have hl : ∀ i j, Integrable (fun g => (ρ h*rectangularOrbit ρ σ M g) i j) μ := by
    intro i j
    simp only [Matrix.mul_apply]
    exact integrable_finsetSum _ (fun k hk => (hf k j).const_mul _)
  have he : ρ h*rectangularIntegral μ (rectangularOrbit ρ σ M)*σ h⁻¹ =
      rectangularIntegral μ (rectangularOrbit ρ σ M) := by
    rw [← rectangularIntegral_mul_left μ _ hf,← rectangularIntegral_mul_right μ _ hl]
    ext i j
    simp only [rectangularIntegral,← rectangularOrbit_mul]
    exact integral_mul_left_eq_self (fun g => rectangularOrbit ρ σ M g i j) h
  have hh := congrArg (fun A : Matrix I J ℂ => A*σ h) he
  simpa only [Matrix.mul_assoc,← map_mul,inv_mul_cancel,map_one,Matrix.mul_one] using hh

end Laughlin.Rotation

end OAI
