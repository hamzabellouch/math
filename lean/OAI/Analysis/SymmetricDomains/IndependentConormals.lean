import Mathlib
import OAI.Analysis.SymmetricDomains.BoundaryParameterPeakMaximizer
import OAI.Analysis.SymmetricDomains.PositiveMaximizerFiber

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
namespace Release061
open Set Filter Topology MeasureTheory
open scoped Classical

theorem original_boundary_positive_fiber {N : ℕ} {V U : Set (Affine N)}
    (hV : IsAffineAlgebraic V) (hUV : U ⊆ V)
    (hU : IsOpen ((Subtype.val : V → Affine N) ⁻¹' U))
    (hc : IsPreconnected U) (hn : ¬ U.Subsingleton) (hb : Bornology.IsBounded U)
    (hs : IsSemialgebraic U) :
    ∃ C : Finset (NashPatch (N+N)),
      (∀ z, z ∈ closure U \ U ↔ ∃ p ∈ C, z ∈ p.complexMap '' p.domain) ∧
      ∀ (P : MvPolynomial (Fin N) ℂ), (∃ q ∈ U, MvPolynomial.eval q P ≠ 0) →
        ∀ (bad : ∀ p : C, Set (Fin p.val.dim → ℝ)), (∀ p, volume (bad p) = 0) →
        ∃ p : C, ∃ (c : ActualCriticalChart P p.val.complexMap) (x : Fin p.val.dim → ℝ),
          x ∈ c.base ∧ x ∈ p.val.domain ∧ p.val.complexMap x ∈ closure U \ U ∧
          MvPolynomial.eval (p.val.complexMap x) P ≠ 0 ∧ x ∉ bad p ∧
          volume (Prod.mk x ⁻¹' c.maxLocus (closure U)) ≠ 0 := by
  obtain ⟨C,hC⟩ := semialgebraic_boundary_finite_nash_cover hs
  refine ⟨C,hC,?_⟩
  intro P hP bad hbad
  let B (p : C) : Set (Fin p.val.dim → ℝ) :=
    {x | x ∈ p.val.domain ∧ MvPolynomial.eval (p.val.complexMap x) P ≠ 0}
  have hBo (p : C) : IsOpen (B p) := by
    apply isOpen_iff_mem_nhds.mpr
    intro x hx
    exact inter_mem (p.val.isOpen_domain.mem_nhds hx.1)
      (((MvPolynomial.continuous_eval P).continuousAt.comp
        (p.val.analytic_complexMap x hx.1).continuousAt).eventually_ne hx.2)
  have hq (p : C) : ContDiffOn ℝ 2 p.val.complexMap (B p) :=
    fun x hx => (p.val.analytic_complexMap x hx.1).contDiffAt.contDiffWithinAt
  have hboundary (p : C) {x : Fin p.val.dim → ℝ} (hx : x ∈ p.val.domain) :
      p.val.complexMap x ∈ closure U \ U :=
    (hC _).mpr ⟨p.val,p.property,mem_image_of_mem _ hx⟩
  have hcover (a : Affine N →L[ℂ] ℂ) :
      ∃ p : C, ∃ x, x ∈ B p ∧ IsMaxOn (parameterPotential P a) (closure U) (p.val.complexMap x) := by
    obtain ⟨z,hz,hzP,hm⟩ := exists_boundary_parameterPeak_maximizer hV hUV hU hc hn hb P hP a
    obtain ⟨p,hp,x,hx,rfl⟩ := (hC z).mp hz
    exact ⟨⟨p,hp⟩,x,⟨hx,hzP⟩,hm⟩
  obtain ⟨p,c,x,hcB,hxc,hxgood,hxpos⟩ := actual_positive_maximizer_fiber P (closure U) isClosed_closure
    (fun p : C => p.val.dim) B hBo (fun p => p.val.complexMap) hq
    (fun p _ hx => (hboundary p hx.1).1) (fun _ _ hx => hx.2)
    (fun p _ hx => p.val.injective_fderiv_complexMap hx.1) bad hbad hcover
  exact ⟨p,c,x,hxc,(hcB hxc).1,hboundary p (hcB hxc).1,(hcB hxc).2,hxgood,hxpos⟩

noncomputable def affineMapCodRestrict
    {E G : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup G] [Module ℝ G]
    (A : E →ᵃ[ℝ] G) (W : Submodule ℝ G) (hA : ∀ x, A x ∈ W) : E →ᵃ[ℝ] W where
  toFun x := ⟨A x,hA x⟩
  linear := A.linear.codRestrict W (fun x => by
    have he : A.linear x = A x - A 0 := by
      simpa only [vsub_eq_sub,sub_zero] using A.linearMap_vsub x 0
    rw [he]
    exact W.sub_mem (hA x) (hA 0))
  map_vadd' x v := by
    apply Subtype.ext
    exact A.map_vadd x v

namespace ActualCriticalChart
variable {d N : ℕ} {P : MvPolynomial (Fin N) ℂ} {q : (Fin d → ℝ) → Affine N}

noncomputable def fiberAffine (c : ActualCriticalChart P q) (x : Fin d → ℝ) :
    (Fin c.fiberDim → ℝ) →ᵃ[ℝ] (Affine N →L[ℂ] ℂ) :=
  ((criticalBundleLinear (realCriticalMatrix q) c.split x).inverse.toLinearMap.toAffineMap).comp
    ((AffineMap.const ℝ _ (realCriticalConstant (parameterLogBase P ∘ q) x)).prod (AffineMap.id ℝ _))

lemma fiberAffine_apply (c : ActualCriticalChart P q) (x : Fin d → ℝ)
    (k : Fin c.fiberDim → ℝ) : c.fiberAffine x k = c.param (x,k) := rfl

noncomputable def ambientCovector (c : ActualCriticalChart P q) (x : Fin d → ℝ) :
    (Fin c.fiberDim → ℝ) →ᵃ[ℝ] Module.Dual ℝ (Affine N) :=
  AffineMap.const ℝ _ (fderiv ℝ (parameterLogBase P) (q x)).toLinearMap +
    ((ContinuousLinearMap.coeLM ℝ).toAffineMap).comp
      (((StrongDual.extendRCLikeL (𝕜 := ℂ) (F := Affine N)).symm.toLinearMap.toAffineMap).comp
        (c.fiberAffine x))

lemma ambientCovector_apply (c : ActualCriticalChart P q) (x : Fin d → ℝ)
    (k : Fin c.fiberDim → ℝ) (v : Affine N) :
    c.ambientCovector x k v = fderiv ℝ (parameterLogBase P) (q x) v + (c.param (x,k) v).re := rfl

lemma ambientCovector_comp (c : ActualCriticalChart P q) {x : Fin d → ℝ}
    (hx : x ∈ c.base) (hq : DifferentiableAt ℝ q x) (hP : MvPolynomial.eval (q x) P ≠ 0)
    (k : Fin c.fiberDim → ℝ) :
    (c.ambientCovector x k).comp (fderiv ℝ q x).toLinearMap = 0 := by
  have hm : c.param (x,k) ∈ range (fun t => c.param (x,t)) := mem_range_self k
  change c.param (x,k) ∈ range (fun t => criticalBundleParam (realCriticalMatrix q) c.split
    (realCriticalConstant (parameterLogBase P ∘ q)) (x,t)) at hm
  rw [c.range_param x hx] at hm
  have hb := (parameterLogBase_contDiffAt P hP (r := 1)).differentiableAt one_ne_zero
  have he := (hb.hasFDerivAt.add
    (Complex.reCLM.comp ((c.param (x,k)).restrictScalars ℝ)).hasFDerivAt).comp x hq.hasFDerivAt
  have hf : (fderiv ℝ (parameterLogBase P) (q x) +
      Complex.reCLM.comp ((c.param (x,k)).restrictScalars ℝ)).comp (fderiv ℝ q x) = 0 :=
    he.fderiv.symm.trans hm
  apply LinearMap.ext
  intro v
  exact congrArg (fun L => L v) hf

lemma ambientCovector_range (c : ActualCriticalChart P q) {x : Fin d → ℝ}
    (hx : x ∈ c.base) (hq : DifferentiableAt ℝ q x) (hP : MvPolynomial.eval (q x) P ≠ 0) :
    range (c.ambientCovector x) =
      ((LinearMap.range (fderiv ℝ q x).toLinearMap).dualAnnihilator : Set (Module.Dual ℝ (Affine N))) := by
  apply Set.Subset.antisymm
  · rintro _ ⟨k,rfl⟩
    apply (Submodule.mem_dualAnnihilator _).mpr
    rintro v ⟨w,rfl⟩
    exact congrArg (fun L : (Fin d → ℝ) →ₗ[ℝ] ℝ => L w) (c.ambientCovector_comp hx hq hP k)
  · intro l hl
    let b := fderiv ℝ (parameterLogBase P) (q x)
    let a := (StrongDual.extendRCLikeL (𝕜 := ℂ) (F := Affine N)) (l.toContinuousLinearMap-b)
    have ha : Complex.reCLM.comp (a.restrictScalars ℝ) = l.toContinuousLinearMap-b := by
      exact (StrongDual.extendRCLikeL (𝕜 := ℂ) (F := Affine N)).symm_apply_apply _
    have hm : a ∈ range (fun k => c.param (x,k)) := by
      change a ∈ range (fun t => criticalBundleParam (realCriticalMatrix q) c.split
        (realCriticalConstant (parameterLogBase P ∘ q)) (x,t))
      rw [c.range_param x hx]
      have hb := (parameterLogBase_contDiffAt P hP (r := 1)).differentiableAt one_ne_zero
      have he := (hb.hasFDerivAt.add (Complex.reCLM.comp (a.restrictScalars ℝ)).hasFDerivAt).comp x hq.hasFDerivAt
      change fderiv ℝ ((parameterLogBase P + (⇑(Complex.reCLM.comp (a.restrictScalars ℝ)))) ∘ q) x = 0
      rw [he.fderiv,ha]
      apply ContinuousLinearMap.ext
      intro v
      change b (fderiv ℝ q x v) + (l (fderiv ℝ q x v)-b (fderiv ℝ q x v)) = 0
      rw [add_sub_cancel]
      exact (Submodule.mem_dualAnnihilator _).mp hl _ ⟨v,rfl⟩
    obtain ⟨k,hk⟩ := hm
    change c.param (x,k) = a at hk
    refine ⟨k,?_⟩
    apply LinearMap.ext
    intro v
    rw [ambientCovector_apply,hk]
    have hh := congrArg (fun L : Affine N →L[ℝ] ℝ => L v) ha
    change (a v).re = l v-b v at hh
    rw [hh]
    exact add_sub_cancel _ _

theorem independent_conormals (c : ActualCriticalChart P q) {x : Fin d → ℝ}
    (hx : x ∈ c.base) (hq : DifferentiableAt ℝ q x) (hP : MvPolynomial.eval (q x) P ≠ 0)
    (V : Submodule ℝ (Affine N)) (T : Submodule ℝ V)
    (hT : T.map V.subtype = LinearMap.range (fderiv ℝ q x).toLinearMap)
    {S : Set (Fin c.fiberDim → ℝ)} (hS : volume S ≠ 0) :
    ∃ v : Fin (Module.finrank ℝ T.dualAnnihilator) → (Fin c.fiberDim → ℝ),
      (∀ i, v i ∈ S) ∧
      LinearIndependent ℝ (fun i => (c.ambientCovector x (v i)).comp V.subtype) := by
  let W := (T.map V.subtype).dualAnnihilator
  have hr : range (c.ambientCovector x) = (W : Set (Module.Dual ℝ (Affine N))) := by
    rw [show W = (T.map V.subtype).dualAnnihilator from rfl,hT]
    exact c.ambientCovector_range hx hq hP
  have hvW (k) : c.ambientCovector x k ∈ W := by
    change c.ambientCovector x k ∈ (W : Set _)
    rw [← hr]
    exact mem_range_self k
  let A := affineMapCodRestrict (c.ambientCovector x) W hvW
  have hA : Function.Surjective A := by
    intro l
    have hl : l.val ∈ range (c.ambientCovector x) := by
      rw [hr]
      exact l.property
    obtain ⟨k,hk⟩ := hl
    exact ⟨k,Subtype.ext hk⟩
  let R₀ : W →ₗ[ℝ] T.dualAnnihilator := conormalRestriction V T
  let R : (Fin c.fiberDim → ℝ) →ᵃ[ℝ] T.dualAnnihilator := R₀.toAffineMap.comp A
  have hR : Function.Surjective R := (conormalRestriction_surjective V T).comp hA
  obtain ⟨v,hv,hi⟩ := exists_independent_affine_images_of_positive_measure volume hS R hR
  refine ⟨v,hv,?_⟩
  exact hi.map' T.dualAnnihilator.subtype (Submodule.ker_subtype _)

end ActualCriticalChart
end Release061

end

end OAI
