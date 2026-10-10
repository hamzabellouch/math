import OAI.MeasureTheory.Falconer.Radial.ActualNoncomparableRadial

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff ComplexConjugate

theorem uniform_actual_noncomparable_radial_either {sig T : ℝ} (hsig : 0 < sig) (K : ℕ)
    {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ) (hpos : ∀ t, 0 ≤ Ψ t)
    (hs : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4)
    {W : ℝ} (hW : 0 ≤ W) (hw : ∀ t, Ψ t ≤ W) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
    ∀ {ι : Fin 2 → Type} [∀ l, DecidableEq (ι l)],
    ∀ (S : ∀ l, Finset (ι l)) (b : ∀ l, ι l → PolicyDescriptor) (k : ∀ l, ι l → ℕ),
    (∀ l, (S l).card ≤ (N+1)^3+1) → (∀ l, ∑ t ∈ S l, k l t ≤ K) →
    ∀ L ≤ N, (∀ l t, t ∈ S l → descriptorLength (b l t) ≤ L) →
    ∀ Q : Fin 2 → DyadicSquare, (∀ l, 0 < (Q l).side) →
    ∀ (ρ : Fin 2 → Measure Plane) (m : Fin 2 → ℝ → ℝ)
    (lam : Fin 2 → ℝ) (J i : Fin 2 → ℕ) (hsp : Fin 2 → Plane → ℂ),
    (∀ l, Measurable (hsp l)) → ∀ x y : Fin 2 → Plane,
    (∀ l, ‖hsp l (x l)‖ ≤ 1) → (∀ l, ‖hsp l (y l)‖ ≤ 1) →
    ∀ v h L₀ : ℝ, v-h = 2*L₀ → (L:ℝ) ≤ L₀ → 10*sig*(N:ℝ) ≤ L₀ →
    ((4*(2:ℝ)^(-h) ≤ ‖x 0-y 0‖ ∧ 2*‖x 1-y 1‖ ≤ ‖x 0-y 0‖) ∨
      (4*(2:ℝ)^(-h) ≤ ‖x 1-y 1‖ ∧ 2*‖x 0-y 0‖ ≤ ‖x 1-y 1‖)) →
    let β := fun l => inheritedCircleSymbol (S l) (b l) (k l) (Q l) (ρ l) (m l)
      N (lam l) sig (J l) (i l) (hsp l)
    ‖angularOriginalSpatialKernel (β 0) (β 1) v Ψ ![x 0,y 0,x 1,y 1]‖ ≤
      ((2:ℝ)^N)^(-T) := by
  obtain ⟨N₀,h₀⟩ := uniform_actual_noncomparable_radial (T := T) hsig K hΨ hpos hs hW hw
  refine ⟨N₀,?_⟩
  intro N hN ι inst S b k hcard hK L hLN hL Q hQ ρ m lam J i hsp hm x y hx hy
    v h L₀ hv hLL hL₀ hgeom
  rcases hgeom with hg | hg
  · exact h₀ N hN S b k hcard hK L hLN hL Q hQ ρ m lam J i hsp hm x y hx hy
      v h L₀ hv hLL hL₀ hg.1 hg.2
  · let e : Fin 2 → Fin 2 := ![1,0]
    have he := h₀ N hN (fun l => S (e l)) (fun l => b (e l)) (fun l => k (e l))
      (fun l => hcard (e l)) (fun l => hK (e l)) L hLN (fun l => hL (e l))
      (fun l => Q (e l)) (fun l => hQ (e l)) (fun l => ρ (e l)) (fun l => m (e l))
      (fun l => lam (e l)) (fun l => J (e l)) (fun l => i (e l)) (fun l => hsp (e l))
      (fun l => hm (e l)) (fun l => x (e l)) (fun l => y (e l)) (fun l => hx (e l))
      (fun l => hy (e l)) v h L₀ hv hLL hL₀ hg.1 hg.2
    simpa only [angularOriginalSpatialKernel,e,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons,mul_comm] using he

end PlanarFalconer

end OAI
