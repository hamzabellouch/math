import OAI.Geometry.NodalSets.Charts.InverseChartJets

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Metric
open scoped ContDiff
noncomputable section
variable {T : Type*} [TopologicalSpace T]

theorem compact_inverse_derivative_bounds {s : Set T} (hs : IsCompact s)
    (p : T → QuadParam Coord) (hp : Continuous p)
    (F : T → OpenPartialHomeomorph Coord Coord)
    (hF : ∀ t ∈ s, (F t : Coord → Coord) = rawQuadratic (p t))
    (hInv : ∀ t ∈ s, ContDiffOn ℝ ∞ (F t).symm (F t).target)
    (hJ : ∀ t ∈ s, ∀ x ∈ (F t).source, ∃ J : Coord ≃L[ℝ] Coord,
      fderiv ℝ (rawQuadratic (p t)) x = J.toContinuousLinearMap)
    (R : ℝ) (hR : ∀ t ∈ s, closedBall (0:Coord) R ⊆ (F t).source) (k0 : ℕ) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ t ∈ s, ∀ x ∈ closedBall (0:Coord) R,
      ∀ k : ℕ, 1 ≤ k → k ≤ k0 →
        ‖iteratedFDeriv ℝ k ((F t).symm : Coord → Coord) (F t x)‖ ≤ D^k := by
  have hcont (k : ℕ) : ContinuousOn
      (fun z : T × Coord ↦ inverseSpatialJet (p z.1) k z.2) (s ×ˢ closedBall 0 R) := by
    intro z hz
    obtain ⟨J,hJe⟩ := hJ z.1 hz.1 z.2 (hR z.1 hz.1 hz.2)
    exact (ContinuousAt.comp (x := z)
      (g := fun q : QuadParam Coord × Coord ↦ inverseSpatialJet q.1 k q.2)
      (f := fun q : T × Coord ↦ (p q.1,q.2))
      (inverseSpatialJet_smooth_at (p z.1) z.2 J hJe k).continuousAt
      ((hp.comp continuous_fst).prodMk continuous_snd).continuousAt).continuousWithinAt
  have hbound (k : Fin (k0+1)) : ∃ C : ℝ, ∀ t ∈ s, ∀ x ∈ closedBall (0:Coord) R,
      ‖iteratedFDeriv ℝ k.val ((F t).symm : Coord → Coord) (F t x)‖ ≤ C := by
    obtain ⟨C,hC⟩ := (hs.prod (isCompact_closedBall (0:Coord) R)).exists_bound_of_continuousOn (hcont k.val)
    refine ⟨C,?_⟩
    intro t ht x hx
    rw [← inverseSpatialJet_eq (p t) (F t) (hF t ht) (hInv t ht) (hJ t ht) k.val x (hR t ht hx)]
    exact hC (t,x) ⟨ht,hx⟩
  choose C hC using hbound
  let D : ℝ := max 1 (∑ k, |C k|)
  have hD : 1 ≤ D := le_max_left _ _
  refine ⟨D,hD,?_⟩
  intro t ht x hx k hk hk0
  let i : Fin (k0+1) := ⟨k,by omega⟩
  have hi : C i ≤ D := (le_abs_self _).trans
    ((Finset.single_le_sum (fun j _ ↦ abs_nonneg (C j)) (Finset.mem_univ i)).trans (le_max_right _ _))
  exact (hC i t ht x hx).trans (hi.trans (by simpa using pow_le_pow_right₀ hD hk))

end
end Yau.Geometry

end OAI
