import Mathlib
import OAI.Analysis.SymmetricDomains.ImagPartLieReal

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open Set Filter Topology
open Filter Topology
open Filter Topology
open Filter Topology
open Filter Topology
open Polynomial
open Filter Topology
open scoped TensorProduct
open Set Filter Topology
open scoped TensorProduct
open scoped TensorProduct
open Filter Topology
open Filter Topology
open scoped TensorProduct
open Filter Topology
open scoped TensorProduct
open scoped TensorProduct
open scoped TensorProduct
open Filter Topology
open scoped TensorProduct
namespace Release061
open Set Filter Topology
namespace Biholomorph
variable {n m : ℕ} {U : Set (Affine n)} {D : Set (Affine m)}

 theorem coordinateField_value_zero_iff (hU : IsOpen U) (hD : IsOpen D)
    (e : Biholomorph U D) (X : Affine n → Affine n) (p : D) :
    coordinateField e X p.val=0 ↔ X (e.toHomeomorph.symm p).val=0 := by
  rw [coordinateField_apply]
  change mapDerivativeEquiv hU hD e (e.toHomeomorph.symm p) (X (e.toHomeomorph.symm p).val)=0 ↔ _
  exact (mapDerivativeEquiv hU hD e (e.toHomeomorph.symm p)).map_eq_zero_iff

 theorem coordinateField_fderiv_of_zero (hU : IsOpen U) (hD : IsOpen D)
    (e : Biholomorph U D) {X : Affine n → Affine n} (hX : AnalyticOnNhd ℂ X U)
    (p : D) (hp : X (e.toHomeomorph.symm p).val=0) :
    fderiv ℂ (coordinateField e X) p.val=
      (e.mapDerivative (e.toHomeomorph.symm p)).comp
        ((fderiv ℂ X (e.toHomeomorph.symm p).val).comp (e.symm.mapDerivative p)) := by
  let g := e.symm.ambientMap
  have hg : AnalyticAt ℂ g p.val := e.symm.ambientMap_analytic hD p.val p.property
  have he : g p.val=(e.toHomeomorph.symm p).val := ambientMap_apply e.symm p
  have hh : AnalyticAt ℂ e.ambientMap (g p.val) := by
    rw [he]; exact e.ambientMap_analytic hU _ (e.toHomeomorph.symm p).property
  have hx : AnalyticAt ℂ X (g p.val) := by
    rw [he]; exact hX _ (e.toHomeomorph.symm p).property
  have hz := (hh.fderiv.differentiableAt.hasFDerivAt.comp p.val hg.differentiableAt.hasFDerivAt).clm_apply
    (hx.differentiableAt.hasFDerivAt.comp p.val hg.differentiableAt.hasFDerivAt)
  have hf : coordinateField e X =ᶠ[𝓝 p.val] fun x => fderiv ℂ e.ambientMap (g x) (X (g x)) := by
    filter_upwards [hD.mem_nhds p.property] with x hx'
    rw [coordinateField_apply e X ⟨x,hx'⟩]
    simp only [g,ambientMap_apply e.symm ⟨x,hx'⟩,mapDerivative]
    rfl
  rw [hf.fderiv_eq]
  change fderiv ℂ (fun y => ((fderiv ℂ e.ambientMap ∘ g) y) ((X ∘ g) y)) p.val = _
  rw [hz.fderiv]
  ext v
  simp [he,hp,mapDerivative,g]

variable (hU : IsOpen U) [LocallyCompactSpace U] (hc : IsConnected U) (hbd : Bornology.IsBounded U)
    (hD : IsOpen D) (e : Biholomorph U D)
include hU hc hbd hD
 theorem model_complete_generator_zero_of_zero_jet {X : Affine n → Affine n}
    (hX : IsCompleteGenerator U X) (p : D)
    (hval : coordinateField e X p.val=0) (hder : fderiv ℂ (coordinateField e X) p.val=0) : X=0 := by
  have hx := (coordinateField_value_zero_iff hU hD e X p).mp hval
  apply IsCompleteGenerator.eq_zero_of_zero_jet hU hc hbd hX (e.toHomeomorph.symm p) hx
  rw [coordinateField_fderiv_of_zero hU hD e (hX.analyticOnNhd hU hbd) p hx] at hder
  let A := mapDerivativeEquiv hU hD e (e.toHomeomorph.symm p)
  let B := mapDerivativeEquiv hD hU e.symm p
  apply ContinuousLinearMap.ext
  intro v
  have hz := congrArg (fun L : Affine m →L[ℂ] Affine m => L (B.symm v)) hder
  change A (fderiv ℂ X (e.toHomeomorph.symm p).val (B (B.symm v)))=0 at hz
  rw [B.apply_symm_apply] at hz
  exact A.injective (by simpa using hz)

variable (Γ : Type*) [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]
    [MulAction Γ U] [ProperSMul Γ U] [CompactSpace (Quotient (MulAction.orbitRel Γ U))]
    (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun p => (γ • p : U).val))
include Γ hhol
 theorem model_isotropy_totally_real {X Y : Affine n → Affine n}
    (hX : IsCompleteGenerator U X) (hY : IsCompleteGenerator U Y) (p : D)
    (hx : coordinateField e X p.val=0) (hy : coordinateField e Y p.val=0)
    (hrel : fderiv ℂ (coordinateField e Y) p.val=Complex.I • fderiv ℂ (coordinateField e X) p.val) : X=0 := by
  have hx0 := (coordinateField_value_zero_iff hU hD e X p).mp hx
  have hy0 := (coordinateField_value_zero_iff hU hD e Y p).mp hy
  apply isotropy_complete_generators_totally_real hU hc hbd Γ hhol hX hY (e.toHomeomorph.symm p) hx0 hy0
  rw [coordinateField_fderiv_of_zero hU hD e (hX.analyticOnNhd hU hbd) p hx0,
    coordinateField_fderiv_of_zero hU hD e (hY.analyticOnNhd hU hbd) p hy0] at hrel
  let A := mapDerivativeEquiv hU hD e (e.toHomeomorph.symm p)
  let B := mapDerivativeEquiv hD hU e.symm p
  apply ContinuousLinearMap.ext
  intro v
  have hz := congrArg (fun L : Affine m →L[ℂ] Affine m => L (B.symm v)) hrel
  change A (fderiv ℂ Y (e.toHomeomorph.symm p).val (B (B.symm v)))=
    Complex.I • A (fderiv ℂ X (e.toHomeomorph.symm p).val (B (B.symm v))) at hz
  rw [B.apply_symm_apply,←map_smul] at hz
  exact A.injective hz

end Biholomorph
end Release061

end

end OAI
