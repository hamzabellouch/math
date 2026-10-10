import OAI.Analysis.AncientFlat.Evolution.TimeRescaling
import OAI.Analysis.AncientFlat.Evolution.DilationDerivatives

namespace OAI
noncomputable section
open Set Filter
open scoped ContDiff ZeroAtInfty BoundedContinuousFunction Laplacian
namespace ParabolicSchauder
open ParametrixEvolution ParametrixDilation
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
def scaleSpace (r : ℝ) (hr : r≠0) : C₀(V,ℂ) →L[ℝ] C₀(V,ℂ) :=
  (ZeroAtInftyContinuousMap.compLinearMap (R := ℝ)
    (Homeomorph.smulOfNeZero r hr : V ≃ₜ V).toCocompactMap).mkContinuous 1 (fun f => by
      change ‖f.toBCF.compContinuous ⟨fun x => r • x,continuous_const.smul continuous_id⟩‖≤1*‖f.toBCF‖
      simpa only [one_mul] using f.toBCF.norm_compContinuous_le ⟨fun x => r • x,continuous_const.smul continuous_id⟩)
@[simp] lemma scaleSpace_apply (r : ℝ) (hr : r≠0) (f : C₀(V,ℂ)) (x : V) :
    scaleSpace r hr f x=f (r • x) := rfl
def spaceSource (r : ℝ) (hr : r≠0) (f : ℝ →ᵇ C₀(V,ℂ)) : ℝ →ᵇ C₀(V,ℂ) :=
  BoundedContinuousFunction.comp (scaleSpace r hr) (scaleSpace r hr).lipschitzWith f
lemma space_source_evolves [FiniteDimensional ℝ V] {T c r : ℝ} (hr : r≠0) (f : ℝ →ᵇ C₀(V,ℂ))
    (u : ℝ → C₀(V,ℂ)) (hu : SourceEvolves (coefficientLine c) 0 f 0 T 0 u) :
    SourceEvolves (coefficientLine (c/r^4)) 0 (spaceSource r hr f) 0 T 0
      (fun t => scaleSpace r hr (u t)) := by
  refine ⟨by change scaleSpace r hr (u 0)=0; rw [hu.1,map_zero],(scaleSpace r hr).continuous.comp_continuousOn hu.2.1,
    fun t ht => (hu.2.2.1 t ht).comp (contDiff_const.smul contDiff_id),
    fun t ht => bounded_jets_scale r _ (hu.2.2.1 t ht) (hu.2.2.2.1 t ht),?_⟩
  intro t ht
  obtain ⟨p,hp,hpe⟩ := hu.2.2.2.2 t ht
  let Q : (V →ᵇ ℂ) →L[ℝ] (V →ᵇ ℂ) := BoundedContinuousFunction.compContinuousCLM ℂ ℝ
    ⟨fun x => r • x,continuous_const.smul continuous_id⟩
  refine ⟨Q p,?_,?_⟩
  · exact Q.hasFDerivAt.comp_hasDerivAt t hp
  · intro x
    change p (r • x)=f t (r • x)-((c/r^4:ℝ):ℂ)*Δ (Δ (fun y => u t (r • y))) x-0*_
    rw [hpe (r • x),bilaplacian_scale r _ (hu.2.2.1 t ht)]
    change f t (r • x)-(c:ℂ)*Δ (Δ (fun y => u t y)) (r • x)-0*_=_
    simp only [zero_mul,sub_zero,Complex.ofReal_div,Complex.ofReal_pow,Complex.real_smul]
    have hrC : (r:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hr
    field_simp
lemma spaceSource_holder {T α H r : ℝ} (hr : 0<r) (f : ℝ →ᵇ C₀(V,ℂ))
    (hf : ∀ t∈Icc 0 T, ∀ x y, ‖f t x-f t y‖≤H*‖x-y‖^α) :
    ∀ t∈Icc 0 T, ∀ x y, ‖spaceSource r hr.ne' f t x-spaceSource r hr.ne' f t y‖≤
      (H*r^α)*‖x-y‖^α := by
  intro t ht x y
  have hh := hf t ht (r • x) (r • y)
  rw [←smul_sub,norm_smul,Real.norm_of_nonneg hr.le,Real.mul_rpow hr.le (norm_nonneg _)] at hh
  exact hh.trans_eq (by ring)
end ParabolicSchauder

end

end OAI
