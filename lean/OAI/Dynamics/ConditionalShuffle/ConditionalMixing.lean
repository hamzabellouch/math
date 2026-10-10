import OAI.Dynamics.ConditionalShuffle.PhysicalMix

namespace OAI

noncomputable section
open Filter Topology
namespace Revealed.Instrument
lemma distance_le_changeFintype {E S G Ω : Type} (s₁ s₂ : Fintype S)
    [Fintype G] [Group G] [Fintype Ω] (I : Data E S G Ω) (e : E) (t : ℕ) {r : ℝ}
    (h : @distance E S G Ω s₁ _ _ _ I e t ≤ r) :
    @distance E S G Ω s₂ _ _ _ I e t ≤ r := by
  cases Subsingleton.elim s₁ s₂
  exact h
end Revealed.Instrument
namespace Revealed
open scoped Classical
open Thorp Thorp.Conditional Split Physical

lemma worstConditionalTV_nonneg (d t : ℕ) : 0 ≤ worstConditionalTV d t := by
  exact (expectedTV_nonneg d t (Equiv.refl _)).trans
    (Finset.le_sup' (fun g₀ => expectedTV d t g₀) (Finset.mem_univ _))

lemma worstConditionalTV_le {d t : ℕ} {r : ℝ}
    (h : ∀ g₀, expectedTV d t g₀ ≤ r) : worstConditionalTV d t ≤ r := by
  exact Finset.sup'_le Finset.univ_nonempty _ (fun g₀ _ => h g₀)

lemma expectedTV_late_bound (d t : ℕ) (hd : 1 ≤ d)
    (hR : (Thorp.Specht.permutationFamily (Position d)).reciprocalSum ≤ 3)
    (ht : 3200*(d+2+2) ≤ t) (g₀ : State (d+2+2)) :
    expectedTV (d+1+2) t g₀ ≤ fullConditionalRate d := by
  let : Fintype (Outside (Position (d+1+2)) (Position (d+1+2)) (Position (d+2+2))) := inferInstance
  let e := Split.outside (splitLayout (d+1+2) g₀)
  have h₁ := expectedTV_le_instrument (d+1+2) t g₀
  have h₂ : Instrument.distance (instrument (d+2+2)) e t ≤
      Instrument.distance (instrument (d+2+2)) e (3200*(d+2+2)) :=
    Instrument.distance_antitone (instrument (d+2+2)) e ht
  have h₃ := physical_distance_bound d hd hR e
  have h₃' : Instrument.distance (instrument (d+2+2)) e (3200*(d+2+2)) ≤ fullConditionalRate d :=
    Instrument.distance_le_changeFintype _ _ _ _ _ h₃
  exact h₁.trans (h₂.trans h₃')

theorem conditional_mixing_shift :
    Tendsto (fun d : ℕ => worstConditionalTV (d+1+2)
      (40000*(400+1)*(d+2+2))) atTop (nhds 0) := by
  apply squeeze_zero' (Eventually.of_forall (fun d => worstConditionalTV_nonneg _ _))
    _ fullConditionalRate_tendsto
  filter_upwards [Thorp.Block.reciprocal_atMost_three, eventually_ge_atTop 1] with d hR hd
  exact worstConditionalTV_le (expectedTV_late_bound d _ hd hR (by omega))

theorem conditional_mixing :
    Tendsto (fun d : ℕ => worstConditionalTV d (40000*(400+1)*(d+1)))
      atTop (nhds 0) := by
  apply (tendsto_add_atTop_iff_nat 3).mp
  simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using conditional_mixing_shift

end Revealed

end

end OAI
