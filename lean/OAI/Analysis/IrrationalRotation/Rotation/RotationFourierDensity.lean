import OAI.Analysis.IrrationalRotation.Model.Rotation
import OAI.Analysis.IrrationalRotation.Analysis.LpContinuousBasisDensity

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace Invariant233.Rotation

def fourierCoordinate (m n : ℤ) : Hilbert :=
  Fields.scalarVectorLp (μ := circleMeasure) (lp.single 2 m (1 : ℂ))
    (ContinuousMap.toLp 2 circleMeasure ℂ (fourier n))

theorem fourierCoordinate_ae (m n : ℤ) :
    fourierCoordinate m n =ᵐ[circleMeasure]
      fun x => fourier n x • lp.single 2 m (1 : ℂ) := by
  filter_upwards [Fields.scalarVectorLp_ae (H := Fiber) (μ := circleMeasure)
      (lp.single 2 m (1 : ℂ)) (ContinuousMap.toLp 2 circleMeasure ℂ (fourier n)),
    ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) circleMeasure (fourier n)] with x hx hy
  exact hx.trans (congrArg (fun c : ℂ => c • (lp.single 2 m (1 : ℂ) : Fiber)) hy)

theorem span_fourierCoordinate_dense :
    (Submodule.span ℂ (Set.range (fun mn : ℤ × ℤ => fourierCoordinate mn.1 mn.2))).topologicalClosure = ⊤ := by
  let K : Submodule ℂ Hilbert :=
    (Submodule.span ℂ (Set.range (fun mn : ℤ × ℤ => fourierCoordinate mn.1 mn.2))).topologicalClosure
  have hK : IsClosed (K : Set Hilbert) := Submodule.isClosed_topologicalClosure _
  let : circleMeasure.WeaklyRegular := by unfold circleMeasure; infer_instance
  apply Fields.closed_submodule_eq_top_of_continuous_basis
    (HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ Fiber)) K hK
  intro m a
  let C : C(Circle, ℂ) →L[ℂ] Hilbert :=
    (Fields.scalarVectorLp (μ := circleMeasure) (lp.single 2 m (1 : ℂ))).comp
      (ContinuousMap.toLp 2 circleMeasure ℂ)
  have hspan : Submodule.span ℂ (Set.range (fourier (T := (1 : ℝ)))) ≤
      K.comap C.toLinearMap := by
    apply Submodule.span_le.mpr
    rintro _ ⟨n, rfl⟩
    change fourierCoordinate m n ∈ K
    exact Submodule.le_topologicalClosure _
      (Submodule.subset_span (Set.mem_range.mpr ⟨(m, n), rfl⟩))
  have hclosed : IsClosed (K.comap C.toLinearMap : Set C(Circle, ℂ)) :=
    hK.preimage C.continuous
  have htop : (⊤ : Submodule ℂ C(Circle, ℂ)) ≤ K.comap C.toLinearMap := by
    rw [← span_fourier_closure_eq_top]
    exact (Submodule.span ℂ (Set.range (fourier (T := (1 : ℝ))))).topologicalClosure_minimal hspan hclosed
  have hb : (HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ Fiber) :
      HilbertBasis ℤ ℂ Fiber) m = lp.single 2 m (1 : ℂ) := by
    exact (HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ Fiber)).repr_symm_single m |>.symm
  rw [hb]
  change C a ∈ K
  exact htop (Submodule.mem_top : a ∈ (⊤ : Submodule ℂ C(Circle, ℂ)))

theorem operator_ext_fourierCoordinate {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] (A B : Hilbert →L[ℂ] E)
    (h : ∀ m n : ℤ, A (fourierCoordinate m n) = B (fourierCoordinate m n)) :
    A = B := by
  apply ContinuousLinearMap.ext_on
    (Submodule.dense_iff_topologicalClosure_eq_top.mpr span_fourierCoordinate_dense)
  rintro _ ⟨⟨m, n⟩, rfl⟩
  exact h m n

end Invariant233.Rotation

end

end OAI
