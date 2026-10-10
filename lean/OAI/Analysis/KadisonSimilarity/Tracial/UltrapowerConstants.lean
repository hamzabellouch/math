import OAI.Analysis.KadisonSimilarity.Tracial.UltrapowerCommutators

namespace OAI

/-! Constant Hilbert vectors retain both their norm and the action of every
constant bounded operator inside the actual Hilbert ultrapower. -/

noncomputable section
namespace KadisonSimilarity

open NuclearUltrapower
open scoped ENNReal Topology

variable {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A constant bounded family, with the ordinary supremum-norm domain. -/
def boundedConstant {E : Type*} [NormedAddCommGroup E] (x : E) : lp (fun _ : ι => E) ∞ :=
  ⟨fun _ => x, memℓp_infty ⟨‖x‖, by rintro _ ⟨i, rfl⟩; exact le_rfl⟩⟩

@[simp] theorem boundedConstant_apply {E : Type*} [NormedAddCommGroup E] (x : E) (i : ι) :
    boundedConstant (ι := ι) x i = x := rfl

/-- The ultralimit seminorm of a constant family is its original norm. -/
def constantPreHilbert (ω : Ultrafilter ι) : H →ₗᵢ[ℂ] UltraPreHilbert (fun _ : ι => H) ω where
  toFun := fun x => boundedConstant x
  map_add' x y := by apply Subtype.ext; funext i; rfl
  map_smul' c x := by apply Subtype.ext; funext i; rfl
  norm_map' x := by
    exact tendsto_nhds_unique (UltraPreHilbert.norm_tendsto ω (boundedConstant x))
      tendsto_const_nhds

/-- The isometric constant-vector inclusion in the completed Hilbert ultrapower. -/
def constantHilbertInclusion (ω : Ultrafilter ι) :
    H →ₗᵢ[ℂ] HilbertUltraproduct (fun _ : ι => H) ω :=
  UniformSpace.Completion.toComplₗᵢ.comp (constantPreHilbert ω)

omit [CompleteSpace H] in
@[simp] theorem constantHilbertInclusion_apply (ω : Ultrafilter ι) (x : H) :
    constantHilbertInclusion ω x =
      ((constantPreHilbert ω x : UltraPreHilbert (fun _ : ι => H) ω) :
        HilbertUltraproduct (fun _ : ι => H) ω) := rfl

omit [CompleteSpace H] in
/-- The coordinatewise action of a fixed operator preserves the constant subspace. -/
theorem map_constant_operator (ω : Ultrafilter ι) (T : H →L[ℂ] H) (x : H) :
    HilbertUltraproduct.map ω (boundedConstant T) (constantHilbertInclusion ω x) =
      constantHilbertInclusion ω (T x) := by
  rw [constantHilbertInclusion_apply, HilbertUltraproduct.map_coe,
    constantHilbertInclusion_apply]
  congr 1

omit [CompleteSpace H] in
/-- No operator norm is lost on a constant family. -/
theorem norm_map_constant_operator (ω : Ultrafilter ι) (T : H →L[ℂ] H) :
    ‖HilbertUltraproduct.map ω (boundedConstant T)‖ = ‖T‖ :=
  tendsto_nhds_unique (HilbertUltraproduct.map_norm_tendsto ω (boundedConstant T))
    tendsto_const_nhds

/-- Compressing the ultrapower operator back to the constant subspace
recovers the original operator exactly. -/
theorem compression_map_constant_operator (ω : Ultrafilter ι) (T : H →L[ℂ] H) :
    (constantHilbertInclusion (H := H) ω).toContinuousLinearMap.adjoint.comp
      ((HilbertUltraproduct.map ω (boundedConstant T)).comp
        (constantHilbertInclusion ω).toContinuousLinearMap) = T := by
  ext x
  change (constantHilbertInclusion ω).toContinuousLinearMap.adjoint
    (HilbertUltraproduct.map ω (boundedConstant T) (constantHilbertInclusion ω x)) = T x
  rw [map_constant_operator]
  exact congrArg (fun L : H →L[ℂ] H => L (T x))
    (constantHilbertInclusion ω).adjoint_comp_self

end KadisonSimilarity

end

end OAI
