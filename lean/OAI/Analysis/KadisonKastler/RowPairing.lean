import OAI.Analysis.KadisonKastler.RandomizedPairing

namespace OAI

/-! # The weak operator pairing represented by the randomized rows -/

namespace KadisonKastler

open Finset Filter
open scoped BigOperators Topology

noncomputable section

variable {H K Ω J : Type*} [Fintype Ω]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

def averageRowProduct (F G : Ω → K →L[ℂ] H) (x : Ω → H →L[ℂ] H) : K →L[ℂ] K :=
  (Fintype.card Ω : ℂ)⁻¹ • ∑ i, (G i).adjoint.comp ((x i).comp (F i))

/-- Testing the averaged row product against two vectors gives exactly
the scalar pairing used in the error estimate. -/
theorem averageRowProduct_inner (F G : Ω → K →L[ℂ] H)
    (x : Ω → H →L[ℂ] H) (ξ η : K) :
    inner ℂ (averageRowProduct F G x ξ) η =
      meanPairing x (fun i => F i ξ) (fun i => G i η) := by
  simp [averageRowProduct, meanPairing, Fintype.expect_eq_sum_div_card,
    ContinuousLinearMap.adjoint_inner_left, div_eq_inv_mul, mul_comm]

/-- Weak operator convergence, in the only form needed for scalar
recovery. It records all vector pairings of the actual operators. -/
def WeakOperatorConverges (l : Filter J) (T : J → K →L[ℂ] K) (T₀ : K →L[ℂ] K) : Prop :=
  ∀ ξ η, Tendsto (fun j => inner ℂ (T j ξ) η) l (𝓝 (inner ℂ (T₀ ξ) η))

/-- A scalar weak limit of the row product supplies the limit of the
pairing difference in the randomized commutator argument. -/
theorem WeakOperatorConverges.row_pairing_sub
    {l : Filter J} (F G : J → Ω → K →L[ℂ] H) (x : J → Ω → H →L[ℂ] H)
    {c : ℝ} (hlim : WeakOperatorConverges l
      (fun j => averageRowProduct (F j) (G j) (x j)) ((c : ℂ) • ContinuousLinearMap.id ℂ K))
    (ξ η ζ : K) :
    Tendsto (fun j => meanPairing (x j) (fun i => F j i ξ) (fun i => G j i η) -
      meanPairing (x j) (fun i => F j i ζ) (fun i => G j i ξ)) l
      (𝓝 ((c : ℂ) * (inner ℂ ξ η - inner ℂ ζ ξ))) := by
  have ht := (hlim ξ η).sub (hlim ζ ξ)
  simpa [averageRowProduct_inner, smul_apply,
    ContinuousLinearMap.id_apply, inner_smul_left, RCLike.conj_ofReal, Complex.real_smul,
    mul_sub] using ht

end

end KadisonKastler

end OAI
