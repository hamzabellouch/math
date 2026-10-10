import Mathlib.Analysis.InnerProductSpace.l2Space

namespace OAI

/-! Coordinate isometries preserve orthogonality when composing a Hilbert sum. -/

noncomputable section
namespace KadisonSimilarity

variable {ι : Type*} {E F : ι → Type*} {H : Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℂ (E i)]
  [∀ i, NormedAddCommGroup (F i)] [∀ i, InnerProductSpace ℂ (F i)]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem orthogonalFamily_comp_isometries (V : ∀ i, F i →ₗᵢ[ℂ] H)
    (hV : OrthogonalFamily ℂ F V) (J : ∀ i, E i →ₗᵢ[ℂ] F i) :
    OrthogonalFamily ℂ E (fun i => (V i).comp (J i)) := by
  intro i j hij x y
  exact hV hij (J i x) (J j y)

def hilbertSumTransport [∀ i, CompleteSpace (E i)] [CompleteSpace H]
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (V : ∀ i, E i →ₗᵢ[ℂ] H) (hV : IsHilbertSum ℂ E V)
    (W : ∀ i, E i →ₗᵢ[ℂ] K) (hW : OrthogonalFamily ℂ E W) : H →ₗᵢ[ℂ] K :=
  hW.linearIsometry.comp hV.linearIsometryEquiv.toLinearIsometry

theorem hilbertSum_transport_component [∀ i, CompleteSpace (E i)] [CompleteSpace H]
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (V : ∀ i, E i →ₗᵢ[ℂ] H) (hV : IsHilbertSum ℂ E V)
    (W : ∀ i, E i →ₗᵢ[ℂ] K) (hW : OrthogonalFamily ℂ E W)
    (i : ι) (x : E i) :
    hilbertSumTransport V hV W hW (V i x) = W i x := by
  classical
  rw [← hV.linearIsometryEquiv_symm_apply_single x]
  change hW.linearIsometry
    (hV.linearIsometryEquiv (hV.linearIsometryEquiv.symm
      (lp.single (E := E) 2 i x))) = _
  rw [LinearIsometryEquiv.apply_symm_apply, hW.linearIsometry_apply_single]

def hilbertSumTransportWithComponents [∀ i, CompleteSpace (E i)] [CompleteSpace H]
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (V : ∀ i, E i →ₗᵢ[ℂ] H) (hV : IsHilbertSum ℂ E V)
    (W : ∀ i, E i →ₗᵢ[ℂ] K) (hW : OrthogonalFamily ℂ E W) :
    {J : H →ₗᵢ[ℂ] K // ∀ i x, J (V i x) = W i x} :=
  ⟨hilbertSumTransport V hV W hW, hilbertSum_transport_component V hV W hW⟩

/-- Equality of bounded maps can be checked on the dense cyclic summands. -/
theorem intertwines_of_dense_summands
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (V : ∀ i, E i →ₗᵢ[ℂ] H)
    (hdense : Dense (Submodule.span ℂ (⋃ i, Set.range (V i)) : Set H))
    (I : H →ₗᵢ[ℂ] K) (W : ∀ i, E i →ₗᵢ[ℂ] K)
    (hI : ∀ i x, I (V i x) = W i x)
    (Q : ∀ i, E i →L[ℂ] E i) (S : H →L[ℂ] H) (T : K →L[ℂ] K)
    (hS : ∀ i x, S (V i x) = V i (Q i x))
    (hT : ∀ i x, W i (Q i x) = T (W i x)) :
    I.toContinuousLinearMap.comp S = T.comp I.toContinuousLinearMap := by
  apply ContinuousLinearMap.ext_on hdense
  intro x hx
  obtain ⟨i, y, rfl⟩ := Set.mem_iUnion.mp hx
  change I (S (V i y)) = T (I (V i y))
  rw [hS, hI, hI, hT]

theorem intertwines_apply_of_dense_summands
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (V : ∀ i, E i →ₗᵢ[ℂ] H)
    (hdense : Dense (Submodule.span ℂ (⋃ i, Set.range (V i)) : Set H))
    (I : H →ₗᵢ[ℂ] K) (W : ∀ i, E i →ₗᵢ[ℂ] K)
    (hI : ∀ i x, I (V i x) = W i x)
    (Q : ∀ i, E i →L[ℂ] E i) (S : H →L[ℂ] H) (T : K →L[ℂ] K)
    (hS : ∀ i x, S (V i x) = V i (Q i x))
    (hT : ∀ i x, W i (Q i x) = T (W i x)) (x : H) :
    I (S x) = T (I x) :=
  congrArg (fun R : H →L[ℂ] K => R x)
    (intertwines_of_dense_summands V hdense I W hI Q S T hS hT)

end KadisonSimilarity

end

end OAI
