import OAI.Computability.UniqueGames.Analysis.Identities
import OAI.Computability.UniqueGames.Inverse.KMSAffineRestrictionComplementLemmas

namespace OAI

section

/-!
# The actual hybrid selector in compressed-fiber coordinates

When the prescribed compression is onto `W`, the hybrid image and preimage
conditions are equivalent to injectivity of the complementary target map
and surjectivity of the remaining coordinate map. These are conditions on
the actual assembled linear map, with no rank or analytic hypothesis.
-/

namespace UniqueGamesTheorem.Inverse.KMSAnalyticHybridCoordinates

variable {R A W D B C : Type*} [Field R]
  [AddCommGroup A] [Module R A] [AddCommGroup W] [Module R W]
  [AddCommGroup D] [Module R D] [AddCommGroup B] [Module R B]
  [AddCommGroup C] [Module R C]

open UniqueGamesTheorem.Appendix

private theorem psi_split {z : B →ₗ[R] W}
    (p : Coordinates (A := A) (D := D) (C := C) z) (b : B) (c : C) :
    p.psi (b, c) = z b + p.psi (0, c) := by
  have hleft : p.psi (b, 0) = z b :=
    congrArg (fun L : B →ₗ[R] W => L b) p.psi_left
  calc
    p.psi (b, c) = p.psi ((b, 0) + (0, c)) := by simp
    _ = p.psi (b, 0) + p.psi (0, c) := p.psi.map_add _ _
    _ = z b + p.psi (0, c) := by rw [hleft]

/-- The genuine hybrid selector is exactly the two independent coordinate
conditions. In particular the full-rank coordinate condition does not
depend on the chosen injective map into the complementary target. -/
theorem hybrid_assemble_iff {z : B →ₗ[R] W}
    (p : Coordinates (A := A) (D := D) (C := C) z)
    (hz : Function.Surjective z) :
    LinearIdentities.Hybrid (assemble p)
        (LinearMap.range (LinearMap.inl R A (W × D)))
        (LinearMap.range (LinearMap.inl R B C)) ↔
      Function.Injective p.v ∧
        Function.Surjective (p.alpha.prod (p.psi.prod (LinearMap.snd R B C))) := by
  constructor
  · intro h
    have hzero : ∀ c : C, p.v c = 0 → c = 0 := by
      intro c hc
      obtain ⟨b, hb⟩ := hz (-p.psi (0, c))
      have hpsi : p.psi (b, c) = 0 := by
        rw [psi_split, hb, neg_add_cancel]
      have hmem : (b, c) ∈ LinearMap.range (LinearMap.inl R B C) := by
        apply h.2
        change assemble p (b, c) ∈ LinearMap.range (LinearMap.inl R A (W × D))
        refine ⟨p.alpha (b, c), ?_⟩
        change (p.alpha (b, c), (0, 0)) = (p.alpha (b, c), p.psi (b, c), p.v c)
        rw [hpsi, hc]
      obtain ⟨b', hb'⟩ := hmem
      exact (congrArg (fun x : B × C => x.2) hb').symm
    refine ⟨?_, ?_⟩
    · intro c d hcd
      apply sub_eq_zero.mp
      apply hzero
      rw [map_sub, hcd, sub_self]
    · rintro ⟨a, w, c⟩
      obtain ⟨b, hb⟩ := hz (w - p.psi (0, c))
      have hpsi : p.psi (b, c) = w := by
        rw [psi_split, hb, sub_add_cancel]
      have hmem : (a - p.alpha (b, c), (0, 0)) ∈ LinearMap.range (assemble p) := by
        apply h.1
        exact ⟨a - p.alpha (b, c), rfl⟩
      obtain ⟨x, hx⟩ := hmem
      have hxa : p.alpha x = a - p.alpha (b, c) :=
        congrArg (fun y : A × (W × D) => y.1) hx
      have hxw : p.psi x = 0 :=
        congrArg (fun y : A × (W × D) => y.2.1) hx
      have hxd : p.v x.2 = 0 :=
        congrArg (fun y : A × (W × D) => y.2.2) hx
      have hxc : x.2 = 0 := hzero _ hxd
      refine ⟨x + (b, c), ?_⟩
      change (p.alpha (x + (b, c)), p.psi (x + (b, c)), (x + (b, c)).2) =
        (a, w, c)
      apply Prod.ext
      · rw [map_add, hxa, sub_add_cancel]
      · apply Prod.ext
        · change p.psi (x + (b, c)) = w
          rw [map_add, hxw, zero_add, hpsi]
        · change x.2 + c = c
          rw [hxc, zero_add]
  · rintro ⟨hv, htheta⟩
    constructor
    · rintro y ⟨a, rfl⟩
      obtain ⟨x, hx⟩ := htheta (a, 0, 0)
      change (p.alpha x, p.psi x, x.2) = (a, 0, 0) at hx
      have hxa : p.alpha x = a := congrArg (fun y : A × (W × C) => y.1) hx
      have hxw : p.psi x = 0 := congrArg (fun y : A × (W × C) => y.2.1) hx
      have hxc : x.2 = 0 := congrArg (fun y : A × (W × C) => y.2.2) hx
      refine ⟨x, ?_⟩
      change (p.alpha x, p.psi x, p.v x.2) = (a, 0, 0)
      rw [hxa, hxw, hxc, map_zero]
    · intro x hx
      change assemble p x ∈ LinearMap.range (LinearMap.inl R A (W × D)) at hx
      obtain ⟨a, ha⟩ := hx
      have hxd : p.v x.2 = 0 :=
        (congrArg (fun y : A × (W × D) => y.2.2) ha).symm
      have hxc : x.2 = 0 := hv (by simpa only [map_zero] using hxd)
      exact ⟨x.1, Prod.ext rfl hxc.symm⟩

end UniqueGamesTheorem.Inverse.KMSAnalyticHybridCoordinates

end

end OAI
