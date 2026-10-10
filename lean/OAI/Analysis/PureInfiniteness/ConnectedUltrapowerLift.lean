import OAI.Analysis.PureInfiniteness.ConnectedUnitaryLift
import OAI.Analysis.JiangSu.CentralSequences.NormUltrapowerUnitaryLift

namespace OAI

/-! A connected unitary in the norm ultrapower has representatives joined
to the identity in every coordinate. The lift uses the actual quotient map. -/
noncomputable section
open scoped CStarAlgebra
open Filter
namespace WeakPureInfiniteness
open NormUltra NormUltra.QuotientAlgebra DirectComparison

variable {A : Type*} [CStarAlgebra A]

/-- The coordinate representatives preserve the identity path component. -/
theorem connected_ultrapower_unitary_representative (U : Ultrafilter ℕ)
    (u : unitary (QuotientAlgebra (fun _ : ℕ => A) U)) (hu : Joined 1 u) :
    ∃ v : ℕ → unitary A, (∀ n, Joined 1 (v n)) ∧
      mk U (boundedUnitary v) = (u : QuotientAlgebra (fun _ : ℕ => A) U) := by
  let q := Unitization.starLift (mkHom (A := fun _ : ℕ => A) (U := U))
  have hq : Function.Surjective q := by
    intro x
    obtain ⟨y, hy⟩ := mk_surjective x
    refine ⟨Unitization.inr y, ?_⟩
    have h := congrArg (fun f : BoundedFamilies (fun _ : ℕ => A) →⋆ₙₐ[ℂ]
        QuotientAlgebra (fun _ : ℕ => A) U => f y)
      (Equiv.symm_apply_apply Unitization.starLift
        (mkHom (A := fun _ : ℕ => A) (U := U)))
    exact h.trans hy
  obtain ⟨v, hvj, hv⟩ := CStarConnectedLift.connected_unitary_lift q hq u hu
  let w (n : ℕ) : unitary A :=
    Unitary.map (CStarConnectedLift.starMonoidHom
      (Unitization.starLift (boundedEvaluation (A := A) n))) v
  refine ⟨w, ?_, ?_⟩
  · intro n
    have h := hvj.map (CStarAbsorption.continuous_unitaryMap
      (Unitization.starLift (boundedEvaluation (A := A) n)))
    simpa only [map_one] using h
  · have he : boundedUnitary w =
        boundedDiagonal (algebraMap ℂ A (v : Unitization ℂ (BoundedFamilies (fun _ : ℕ => A))).fst) +
          (v : Unitization ℂ (BoundedFamilies (fun _ : ℕ => A))).snd := by
      ext n
      rfl
    have hc (c : ℂ) : mk U (boundedDiagonal (algebraMap ℂ A c)) =
        algebraMap ℂ (QuotientAlgebra (fun _ : ℕ => A) U) c :=
      (diagonalHom (A := A) U).commutes c
    rw [he, mk_add, hc]
    exact congrArg Subtype.val hv

/-- A finite family of strict conjugacy estimates descends to one connected
coordinate unitary. -/
theorem connected_finite_conjugacy_of_ultrapower (U : Ultrafilter ℕ)
    (F : Finset (A × A)) {ε : ℝ}
    (u : unitary (QuotientAlgebra (fun _ : ℕ => A) U)) (hu : Joined 1 u)
    (he : ∀ p ∈ F,
      ‖(u : QuotientAlgebra (fun _ : ℕ => A) U) * diagonalHom U p.1 *
        star (u : QuotientAlgebra (fun _ : ℕ => A) U) - diagonalHom U p.2‖ < ε) :
    ∃ v : unitary A, Joined 1 v ∧
      ∀ p ∈ F, ‖(v : A) * p.1 * star (v : A) - p.2‖ < ε := by
  classical
  obtain ⟨v, hvj, hv⟩ := connected_ultrapower_unitary_representative U u hu
  have hfin : ∀ᶠ n in (U : Filter ℕ),
      ∀ p ∈ F, ‖(v n : A) * p.1 * star (v n : A) - p.2‖ < ε := by
    apply (eventually_all_finset F).mpr
    intro p hp
    let x := boundedUnitary v * boundedDiagonal p.1 * star (boundedUnitary v) -
      boundedDiagonal p.2
    have hx : ‖mk U x‖ < ε := by
      have hd (a : A) : diagonalHom U a = mk U (boundedDiagonal a) := rfl
      simpa only [x, mk_sub, mk_mul, mk_star, hv, hd] using he p hp
    exact NonunitalGamma.eventually_norm_lt_of_quotient_norm_lt U x hx
  obtain ⟨n, hn⟩ := hfin.exists
  exact ⟨v n, hvj n, hn⟩

end WeakPureInfiniteness

end

end OAI
