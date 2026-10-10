import OAI.Analysis.KadisonSimilarity.Representation.VectorSpectralMeasure
import Mathlib.MeasureTheory.Function.ContinuousMapDense

namespace OAI

/-! The cyclic spectral isometry gives scalar L² coordinates for the closed
cyclic orbit, as required for central cyclic decomposition. -/

noncomputable section
open MeasureTheory
open scoped ComplexConjugate InnerProductSpace
namespace KadisonSimilarity.VectorSpectralMeasure
variable {X H : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [MeasurableSpace X] [BorelSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (Φ : C(X,ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (v : H)
lemma inner_toLp (f g : C(X,ℂ)) :
    ⟪ContinuousMap.toLp 2 (measure Φ v) ℂ f, ContinuousMap.toLp 2 (measure Φ v) ℂ g⟫_ℂ =
      ⟪Φ f v,Φ g v⟫_ℂ := by
  rw [L2.inner_def]
  calc
    _ = ∫ x, (star f*g) x ∂measure Φ v := by
      apply integral_congr_ae
      filter_upwards [ContinuousMap.coeFn_toLp (μ := measure Φ v) (p := 2) (𝕜 := ℂ) f,
        ContinuousMap.coeFn_toLp (μ := measure Φ v) (p := 2) (𝕜 := ℂ) g] with x hx hy
      simp only [hx,hy,RCLike.inner_apply,ContinuousMap.mul_apply,ContinuousMap.star_apply,Complex.star_def]
      ring
    _ = ⟪v,Φ (star f*g) v⟫_ℂ := integral_complex Φ v _
    _ = _ := by
      rw [map_mul,map_star]
      change ⟪v,star (Φ f) (Φ g v)⟫_ℂ = _
      rw [ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_right]
def vectorLinear : C(X,ℂ) →ₗ[ℂ] H where
  toFun f := Φ f v
  map_add' f g := by simp
  map_smul' c f := by simp
lemma norm_toLp (f : C(X,ℂ)) :
    ‖ContinuousMap.toLp 2 (measure Φ v) ℂ f‖ = ‖vectorLinear Φ v f‖ := by
  have he := congrArg Complex.re (inner_toLp Φ v f f)
  change RCLike.re (⟪ContinuousMap.toLp 2 (measure Φ v) ℂ f,ContinuousMap.toLp 2 (measure Φ v) ℂ f⟫_ℂ) =
    RCLike.re (⟪Φ f v,Φ f v⟫_ℂ) at he
  rw [inner_self_eq_norm_sq,inner_self_eq_norm_sq] at he
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp he
def cyclicMap : Lp ℂ 2 (measure Φ v) →L[ℂ] H :=
  (vectorLinear Φ v).extendOfNorm (ContinuousMap.toLp 2 (measure Φ v) ℂ).toLinearMap
lemma cyclicMap_toLp (f : C(X,ℂ)) :
    cyclicMap Φ v (ContinuousMap.toLp 2 (measure Φ v) ℂ f) = Φ f v := by
  apply LinearMap.extendOfNorm_eq
  · exact ContinuousMap.toLp_denseRange (E := ℂ) (p := 2) (μ := measure Φ v) (𝕜 := ℂ) (by norm_num)
  · exact ⟨1,fun g => by simp only [one_mul]; exact le_of_eq (norm_toLp Φ v g).symm⟩
lemma norm_cyclicMap (f : Lp ℂ 2 (measure Φ v)) : ‖cyclicMap Φ v f‖ = ‖f‖ := by
  refine (ContinuousMap.toLp_denseRange (E := ℂ) (p := 2) (μ := measure Φ v) (𝕜 := ℂ) (by norm_num)).induction
    (fun y hy => ?_) (isClosed_eq (by fun_prop) (by fun_prop)) f
  obtain ⟨g,rfl⟩ := hy
  rw [cyclicMap_toLp]
  exact (norm_toLp Φ v g).symm
def cyclicIsometry : Lp ℂ 2 (measure Φ v) →ₗᵢ[ℂ] H :=
  ⟨(cyclicMap Φ v).toLinearMap,norm_cyclicMap Φ v⟩

/-- The scalar spectral map identifies L² with exactly the closed cyclic orbit. -/
lemma cyclicMap_range : Set.range (cyclicMap Φ v) =
    closure (Set.range (fun f : C(X, ℂ) => Φ f v)) := by
  apply Set.Subset.antisymm
  · rintro _ ⟨ξ, rfl⟩
    have hξ := (ContinuousMap.toLp_denseRange (E := ℂ) (p := 2)
      (μ := measure Φ v) (𝕜 := ℂ) (by norm_num)) ξ
    exact map_mem_closure (cyclicMap Φ v).continuous hξ (by
      rintro _ ⟨f, rfl⟩
      exact ⟨f, (cyclicMap_toLp Φ v f).symm⟩)
  · apply closure_minimal
    · rintro _ ⟨f, rfl⟩
      exact ⟨ContinuousMap.toLp 2 (measure Φ v) ℂ f, cyclicMap_toLp Φ v f⟩
    · exact (cyclicIsometry Φ v).isometry.isClosedEmbedding.isClosed_range

end KadisonSimilarity.VectorSpectralMeasure

end

end OAI
