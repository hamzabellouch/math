import Mathlib
import OAI.Combinatorics.KMedian.Sparse.SparseCoupledPreparation

namespace OAI


                                      
section
namespace MetricKMedian.Preparation
open Finset
attribute [instance] CoupledLaw.finite
variable {E E' T I : Type} [Fintype E] [DecidableEq E]
  [Fintype E'] [DecidableEq E'] [Fintype T] [DecidableEq T]
  [Fintype I] [DecidableEq I]

noncomputable def CoupledLaw.reindexStars (e : E ≃ E')
    {D : E' → Finset T} {a w : E' → ℝ} {P : T → Finset I}
    {y : I → ℝ} {p c : T → ℝ} {g γ B : ℝ} {Δ : ℕ}
    (L : CoupledLaw (D ∘ e) (a ∘ e) (w ∘ e) P y p c g γ B Δ) :
    CoupledLaw D a w P y p c g γ B Δ where
  Ω := L.Ω
  ν := L.ν
  κ := L.κ
  O := fun z i => L.O z (e.symm i)
  N := fun z i => L.N z (e.symm i)
  R := fun z t i => L.R z t (e.symm i)
  K := L.K
  C := L.C
  open_cap := by simpa only [Function.comp_apply, e.apply_symm_apply] using
    fun z hz i => L.open_cap z hz (e.symm i)
  open_zero := by simpa only [Function.comp_apply, e.apply_symm_apply] using
    fun z hz i => L.open_zero z hz (e.symm i)
  nominal_nonneg := fun z hz i => L.nominal_nonneg z hz (e.symm i)
  nominal_cap := fun z hz i => L.nominal_cap z hz (e.symm i)
  nominal_mean := by simpa only [Function.comp_apply, e.apply_symm_apply] using
    fun i => L.nominal_mean (e.symm i)
  nominal_variance := by simpa only [Function.comp_apply, e.apply_symm_apply] using
    fun i => L.nominal_variance (e.symm i)
  nominal_pair := by
    intro i j hij
    simpa only [Function.comp_apply, e.apply_symm_apply] using
      L.nominal_pair (e.symm i) (e.symm j) (e.symm.injective.ne hij)
  request_cap := fun z hz t i => L.request_cap z hz t (e.symm i)
  request_target := by simpa only [Function.comp_apply, e.apply_symm_apply] using
    fun z t i => L.request_target z t (e.symm i)
  request_mean := by simpa only [Function.comp_apply, e.apply_symm_apply] using
    fun t i => L.request_mean t (e.symm i)
  exact_total := by
    intro z t
    rw [e.symm.sum_comp]
    exact L.exact_total z t
  half := L.half
  total_cap := L.total_cap
  total_deviation := L.total_deviation
  pieces := L.pieces
  piece_mean := L.piece_mean
  piece_pair := L.piece_pair
  piece_variance := L.piece_variance
  budget := by
    have he : ∀ z, (∑ i, a i * (g * (L.O z (e.symm i) : ℝ))) =
        ∑ j, a (e j) * (g * (L.O z j : ℝ)) := by
      intro z
      rw [← e.sum_comp]
      simp only [e.symm_apply_apply]
    simpa only [he, Function.comp_apply] using L.budget

end MetricKMedian.Preparation
end

end OAI
