import OAI.Analysis.KadisonKastler.RowPairing

namespace OAI

/-! # Extracting the unitary quadratic bound from randomized rows -/

namespace KadisonKastler

open Filter
open scoped Topology

noncomputable section

variable {H K Ω J : Type*} [Fintype Ω]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- The two drift estimates and the scalar weak limit give the real
quadratic estimate. The rows and contractions are the actual operators;
no bound on the size of the finite random space occurs. -/
theorem row_scalar_quadratic_bound
    {l : Filter J} [l.NeBot]
    (h : H →L[ℂ] H) (hh : h.IsSymmetric)
    (T : K →L[ℂ] K) (hT : IsSelfAdjoint T)
    (u : unitary (K →L[ℂ] K)) (ξ : K)
    (F G : J → Ω → K →L[ℂ] H) (x : J → Ω → H →L[ℂ] H)
    {δ c : ℝ} (hδ : 0 ≤ δ) (hc : 1 / 2 ≤ c)
    (hx : ∀ j i, ‖x j i‖ ≤ 1)
    (hcomm : ∀ j i, ‖(h * x j i - x j i * h) (F j i ξ)‖ ≤ δ * ‖F j i ξ‖)
    (hF : ∀ j, finiteRMS (fun i => F j i ξ) ≤ 1)
    (hG : ∀ j, finiteRMS (fun i => G j i ξ) ≤ 1)
    (hforward : ∀ ε > 0, ∀ᶠ j in l,
      finiteRMS (fun i => h (F j i ξ) -
        F j i ((star (u : K →L[ℂ] K)) (T ((u : K →L[ℂ] K) ξ)))) ≤ 70 * δ + ε)
    (hbackward : ∀ ε > 0, ∀ᶠ j in l,
      finiteRMS (fun i => h (G j i ξ) - G j i (T ξ)) ≤ 70 * δ + ε)
    (hlim : WeakOperatorConverges l
      (fun j => averageRowProduct (F j) (G j) (x j))
      ((c : ℂ) • ContinuousLinearMap.id ℂ K)) :
    |(inner ℂ (T ξ) ξ).re -
      (inner ℂ (T ((u : K →L[ℂ] K) ξ)) ((u : K →L[ℂ] K) ξ)).re| ≤ 282 * δ := by
  let ζ := (star (u : K →L[ℂ] K)) (T ((u : K →L[ℂ] K) ξ))
  have hb := randomized_pairing_limit_le h hh x hx
    (fun j i => F j i ξ) (fun j i => G j i ξ)
    (fun j i => F j i ζ) (fun j i => G j i (T ξ)) hδ hcomm hF hG
    hforward hbackward (hlim.row_pairing_sub F G x ξ (T ξ) ζ)
  have hs : inner ℂ ξ (T ξ) = inner ℂ (T ξ) ξ := (hT.isSymmetric.apply_clm ξ ξ).symm
  have he : inner ℂ ζ ξ =
      inner ℂ (T ((u : K →L[ℂ] K) ξ)) ((u : K →L[ℂ] K) ξ) := by
    simp only [ζ, ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.adjoint_inner_left]
  rw [hs, he] at hb
  have hr₁ : inner ℂ (T ξ) ξ = ((inner ℂ (T ξ) ξ).re : ℂ) := by
    exact (hT.isSymmetric.coe_re_inner_apply_self ξ).symm
  have hr₂ : inner ℂ (T ((u : K →L[ℂ] K) ξ)) ((u : K →L[ℂ] K) ξ) =
      ((inner ℂ (T ((u : K →L[ℂ] K) ξ)) ((u : K →L[ℂ] K) ξ)).re : ℂ) := by
    exact (hT.isSymmetric.coe_re_inner_apply_self ((u : K →L[ℂ] K) ξ)).symm
  rw [hr₁, hr₂, ← Complex.ofReal_sub, ← Complex.ofReal_mul] at hb
  exact scalar_recovery_quadratic_bound hc hb

end

end KadisonKastler

end OAI
