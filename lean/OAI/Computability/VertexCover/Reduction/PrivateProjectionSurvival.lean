import Mathlib
import OAI.Computability.VertexCover.Reduction.PrivateProjectionGroupLower

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
namespace VertexCover.LabelCover
open VertexCover.Restriction
open EnergyForm.Projection
open scoped BigOperators

def otherEndpoint {d : ℕ} (j : Fin d) (e : PositionPair d) : Fin d :=
  if e.1.1 = j then e.1.2 else e.1.1

theorem otherEndpoint_ne {d : ℕ} (j : Fin d) (e : PositionPair d) :
    otherEndpoint j e ≠ j := by
  unfold otherEndpoint
  split_ifs with h
  · rw [← h]; exact ne_of_gt e.2
  · exact h

theorem otherEndpoint_injective {d : ℕ} (j : Fin d) (e b : PositionPair d)
    (he : e.1.1 = j ∨ e.1.2 = j) (hb : b.1.1 = j ∨ b.1.2 = j)
    (h : otherEndpoint j e = otherEndpoint j b) : e = b := by
  rcases he with he | he <;> rcases hb with hb | hb
  · simp only [otherEndpoint, ite_eq_left he, ite_eq_left hb] at h
    exact Subtype.ext (Prod.ext (he.trans hb.symm) h)
  · have hbl : b.1.1 ≠ j := by rw [← hb]; exact ne_of_lt b.2
    simp only [otherEndpoint, ite_eq_left he, ite_eq_right hbl] at h
    have := e.2; have := b.2
    omega
  · have hel : e.1.1 ≠ j := by rw [← he]; exact ne_of_lt e.2
    simp only [otherEndpoint, ite_eq_right hel, ite_eq_left hb] at h
    have := e.2; have := b.2
    omega
  · have hel : e.1.1 ≠ j := by rw [← he]; exact ne_of_lt e.2
    have hbl : b.1.1 ≠ j := by rw [← hb]; exact ne_of_lt b.2
    simp only [otherEndpoint, ite_eq_right hel, ite_eq_right hbl] at h
    exact Subtype.ext (Prod.ext h (he.trans hb.symm))

theorem incident_sum_le {d : ℕ} (J : Finset (Fin d)) (j : Fin d)
    (g : Fin d → ℝ) (hg : ∀ k, 0 ≤ g k) :
    (∑ e ∈ (internalPairs J).filter (fun e => e.1.1 = j ∨ e.1.2 = j),
      g (otherEndpoint j e)) ≤ ∑ k ∈ J.erase j, g k := by
  classical
  let T := (internalPairs J).filter (fun e => e.1.1 = j ∨ e.1.2 = j)
  have hi : Set.InjOn (otherEndpoint j) ↑T := by
    intro e he b hb h
    exact otherEndpoint_injective j e b (Finset.mem_filter.mp he).2
      (Finset.mem_filter.mp hb).2 h
  have hs : T.image (otherEndpoint j) ⊆ J.erase j := by
    intro k hk
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hk
    obtain ⟨heJ, _hei⟩ := Finset.mem_filter.mp he
    have hep : e.1.1 ∈ J ∧ e.1.2 ∈ J := (Finset.mem_filter.mp heJ).2
    refine Finset.mem_erase.mpr ⟨otherEndpoint_ne j e, ?_⟩
    unfold otherEndpoint
    split_ifs <;> tauto
  calc
    _ = ∑ k ∈ T.image (otherEndpoint j), g k := (Finset.sum_image hi).symm
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hs (fun k _ _ => hg k)

theorem privatePair_incident_charge (Φ : LabelCover) {d : ℕ}
    (J : Finset (Fin d)) (j : Fin d) (e : PositionPair d)
    (he : e ∈ internalPairs J) (hi : e.1.1 = j ∨ e.1.2 = j)
    (f : Φ.RestrictionSpace d) :
    (Φ.restrictionForm d).energy ((Φ.privatePairProjection J j e).residual f) ≤
      (Φ.restrictionForm d).energy ((Φ.starProjection (otherEndpoint j e)).residual f) := by
  rcases hi with hi | hi
  · rw [Φ.privatePairProjection_left J j e he hi]
    simp only [otherEndpoint, ite_eq_left hi]
    exact Φ.oppositeProjection_charge e.1.2 e (Or.inr rfl) f
  · have hL : e.1.1 ≠ j := by rw [← hi]; exact ne_of_lt e.2
    rw [Φ.privatePairProjection_right J j e he hi]
    simp only [otherEndpoint, ite_eq_right hL]
    exact Φ.oppositeProjection_charge e.1.1 e (Or.inl rfl) f

theorem privatePair_loss_sum (Φ : LabelCover) {d : ℕ}
    (J : Finset (Fin d)) (j : Fin d) (f : Φ.RestrictionSpace d) :
    (∑ e : PositionPair d, (Φ.restrictionForm d).energy
      ((Φ.privatePairProjection J j e).residual f)) ≤
      (∑ k ∈ J.erase j, (Φ.restrictionForm d).energy ((Φ.starProjection k).residual f)) +
      ∑ e ∈ (internalPairs J).filter (fun e => ¬ (e.1.1 = j ∨ e.1.2 = j)),
        (Φ.restrictionForm d).energy ((Φ.seedProjection e).residual f) := by
  classical
  let l := fun e : PositionPair d => (Φ.restrictionForm d).energy
    ((Φ.privatePairProjection J j e).residual f)
  have hz : (∑ e, l e) = ∑ e ∈ internalPairs J, l e := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro e _ he
    simp only [l, Φ.privatePairProjection_outside J j e he, residual_apply, ident_apply,
      sub_self, EnergyForm.energy_zero]
  change (∑ e, l e) ≤ _
  rw [hz, ← Finset.sum_filter_add_sum_filter_not (internalPairs J)
    (fun e => e.1.1 = j ∨ e.1.2 = j) l]
  apply add_le_add
  · calc
      _ ≤ ∑ e ∈ (internalPairs J).filter (fun e => e.1.1 = j ∨ e.1.2 = j),
          (Φ.restrictionForm d).energy ((Φ.starProjection (otherEndpoint j e)).residual f) := by
        apply Finset.sum_le_sum
        intro e he
        exact Φ.privatePair_incident_charge J j e (Finset.mem_filter.mp he).1
          (Finset.mem_filter.mp he).2 f
      _ ≤ _ := incident_sum_le J j
        (fun k => (Φ.restrictionForm d).energy ((Φ.starProjection k).residual f))
        (fun _ => (Φ.restrictionForm d).energy_nonneg _)
  · apply le_of_eq
    apply Finset.sum_congr rfl
    intro e he
    obtain ⟨heJ, hei⟩ := Finset.mem_filter.mp he
    obtain ⟨hL,hR⟩ := not_or.mp hei
    dsimp [l]
    rw [Φ.privatePairProjection_nonincident J j e heJ hL hR]

theorem privateProjection_survival (Φ : LabelCover) {d : ℕ}
    (J : Finset (Fin d)) (j : Fin d) (f : Φ.RestrictionSpace d) :
    (Φ.restrictionForm d).energy (Φ.weightGroup j f) ≤
      (Φ.restrictionForm d).energy (Φ.privateProjection J j f) +
      (∑ k ∈ J.erase j, ((Φ.restrictionForm d).energy
        ((Φ.weightProjection k).residual (Φ.weightGroup j f)) +
        (Φ.restrictionForm d).energy ((Φ.starProjection k).residual (Φ.weightGroup j f)))) +
      ∑ e ∈ (internalPairs J).filter (fun e => ¬ (e.1.1 = j ∨ e.1.2 = j)),
        (Φ.restrictionForm d).energy ((Φ.seedProjection e).residual (Φ.weightGroup j f)) := by
  have h := Φ.privateProjection_group_lower J j f
  have hs := Φ.privatePair_loss_sum J j (Φ.weightGroup j f)
  rw [Finset.sum_add_distrib]
  linarith

end VertexCover.LabelCover


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
