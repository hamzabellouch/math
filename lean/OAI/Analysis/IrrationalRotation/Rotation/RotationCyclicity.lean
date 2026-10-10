import OAI.Analysis.IrrationalRotation.Rotation.RotationFourierDensity
import OAI.Analysis.IrrationalRotation.Rotation.RotationMoments

namespace OAI

noncomputable section
open MeasureTheory

namespace Invariant233.Rotation

theorem monomialVector_eq_fourierCoordinate (θ : ℝ) (mn : ℤ × ℤ) :
    monomialVector θ mn = fourierCoordinate mn.1 mn.2 := by
  apply Lp.ext
  exact (monomialVector_ae θ mn).trans (fourierCoordinate_ae mn.1 mn.2).symm

theorem span_monomialVector_dense (θ : ℝ) :
    (Submodule.span ℂ (Set.range (monomialVector θ))).topologicalClosure = ⊤ := by
  have hfun : monomialVector θ = fun mn : ℤ × ℤ => fourierCoordinate mn.1 mn.2 :=
    funext (monomialVector_eq_fourierCoordinate θ)
  rw [hfun]
  exact span_fourierCoordinate_dense

def monomialHilbertBasis (θ : ℝ) : HilbertBasis (ℤ × ℤ) ℂ Hilbert :=
  HilbertBasis.mk (orthonormal_monomialVector θ) (span_monomialVector_dense θ).ge

theorem monomialHilbertBasis_apply (θ : ℝ) (mn : ℤ × ℤ) :
    monomialHilbertBasis θ mn = monomialVector θ mn := by
  simp [monomialHilbertBasis]

theorem monomialHilbertBasis_repr (θ : ℝ) (mn : ℤ × ℤ) :
    (monomialHilbertBasis θ).repr (monomialVector θ mn) = lp.single 2 mn (1 : ℂ) := by
  rw [← monomialHilbertBasis_apply θ mn]
  exact (monomialHilbertBasis θ).repr_self mn

theorem vacuum_cyclic_span (θ : ℝ) :
    (Submodule.span ℂ (Set.range (fun A : algebra θ =>
      (A : Hilbert →L[ℂ] Hilbert) vacuum))).topologicalClosure = ⊤ := by
  apply top_unique
  rw [← span_monomialVector_dense θ]
  apply Submodule.topologicalClosure_mono
  apply Submodule.span_mono
  rintro _ ⟨⟨m, n⟩, rfl⟩
  refine ⟨⟨_, unitary_monomial_mem_algebra θ m n⟩, ?_⟩
  rfl

theorem operator_ext_monomialVector {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] (θ : ℝ) (A B : Hilbert →L[ℂ] E)
    (h : ∀ mn : ℤ × ℤ, A (monomialVector θ mn) = B (monomialVector θ mn)) :
    A = B := by
  apply ContinuousLinearMap.ext_on
    (Submodule.dense_iff_topologicalClosure_eq_top.mpr (span_monomialVector_dense θ))
  rintro _ ⟨mn, rfl⟩
  exact h mn

end Invariant233.Rotation

end

end OAI
