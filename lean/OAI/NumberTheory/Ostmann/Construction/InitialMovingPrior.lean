import OAI.NumberTheory.Ostmann.Construction.InitialMovingAmplitude

namespace OAI

/-! # Live original tuples after the spectator coordinates are fixed -/
namespace Ostmann
open scoped Classical BigOperators

theorem initialHalfAssemble_prior {P : Type*} (b d r : ℕ)
    (μg : P → ℝ) (μb : Fin b → P → ℝ) (μd : Fin d → P → ℝ) (μc : Fin r → P → ℝ) :
    initialHalfAssemble b d r μd (Sum.elim (fun _ : Unit => μg) (Sum.elim μb μc)) =
      Fin.cons μg (Fin.append μb (Fin.append μd μc)) := by
  funext j
  obtain ⟨i, rfl⟩ := (initialSpectatorSlotEquiv b d r).surjective j
  rcases i with i | (u | (i | i)) <;>
    simp [initialHalfAssemble, initialSpectatorSlotEquiv]

theorem initial_full_prior_reindex {P : Type*} (b d r : ℕ)
    (μg : P → ℝ) (μb : Fin b → P → ℝ) (μd : Fin d → P → ℝ) (μc : Fin r → P → ℝ)
    (i : Fin (d + d) ⊕ (Bool ⊕ MovingRegularSlot 0 (r + r) (b + b))) :
    let ν : Fin (b + (d + r) + 1) → P → ℝ := Fin.cons μg (Fin.append μb (Fin.append μd μc))
    Fin.append ν ν (initialCompleteIndexEquiv b d r i) =
      Sum.elim (Fin.append μd μd)
        (Sum.elim (fun _ : Bool => μg) (initialMovingRegularPrior b r μb μc)) i := by
  intro ν
  let ρ := Sum.elim (fun _ : Unit => μg) (Sum.elim μb μc)
  have h := initialCompleteIndexEquiv_assemble b d r μd μd ρ ρ
  rw [initialHalfAssemble_prior] at h
  have hr : Sum.elim ρ ρ ∘ (initialRetainedIndexEquiv b r).symm =
      Sum.elim (fun _ : Bool => μg) (initialMovingRegularPrior b r μb μc) := by
    funext j
    have hh := initial_retained_prior b r μg μb μc ((initialRetainedIndexEquiv b r).symm j)
    rw [Equiv.apply_symm_apply] at hh
    exact hh
  rw [hr] at h
  exact congrFun h i

theorem initialMovingTuple_prior_nonzero {P : Type*} [Fintype P] (b d r : ℕ)
    (μg : P → ℝ) (μb : Fin b → P → ℝ) (μd : Fin d → P → ℝ) (μc : Fin r → P → ℝ)
    (sl sr : Fin d → P) (hs : ∀ i, μd i (sl i) ≠ 0) (ht : ∀ i, μd i (sr i) ≠ 0)
    (XL XR : P) (hXL : μg XL ≠ 0) (hXR : μg XR ≠ 0)
    (y : MovingRegularSlot 0 (r + r) (b + b) → P)
    (hy : (∏ i, initialMovingRegularPrior b r μb μc i (y i)) ≠ 0) :
    let ν : Fin (b + (d + r) + 1) → P → ℝ := Fin.cons μg (Fin.append μb (Fin.append μd μc))
    productPrior (Fin.append ν ν) (initialMovingTuple b d r sl sr XL XR y) ≠ 0 := by
  intro ν
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  obtain ⟨j, rfl⟩ := (initialCompleteIndexEquiv b d r).surjective i
  rw [initial_full_prior_reindex]
  have hx := congrFun (initialMovingTuple_reindex b d r sl sr XL XR y) j
  change initialMovingTuple b d r sl sr XL XR y (initialCompleteIndexEquiv b d r j) = _ at hx
  rw [hx]
  rcases j with j | (a | j)
  · refine Fin.addCases (fun k => ?_) (fun k => ?_) j
    · simpa only [Sum.elim_inl, Fin.append_left] using hs k
    · simpa only [Sum.elim_inl, Fin.append_right] using ht k
  · cases a <;> assumption
  · exact (Finset.prod_ne_zero_iff.mp hy) j (Finset.mem_univ _)

end Ostmann

end OAI
