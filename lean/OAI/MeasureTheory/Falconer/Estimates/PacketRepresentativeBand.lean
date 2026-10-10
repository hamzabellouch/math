import OAI.MeasureTheory.Falconer.Incidence.RegularCoarsePencils

namespace OAI

/-! A weighted image can be thinned to representatives with comparable
numbers of original witnesses, retaining both regularity and total mass. -/
namespace Falconer
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem packet_representative_band {δ ρ s K C : ℝ}
    (hρ : 0 < ρ) (hδρ : δ ≤ ρ) (hs : 0 ≤ s) (hK : 1 ≤ K) (hC : 0 ≤ C)
    (T : Finset (Space 2)) (hT : T.Nonempty) (q : Space 2 → Space 2)
    (hnear : ∀ l ∈ T, dist l (q l) ≤ C*ρ)
    (hball : NormalizedFiniteBallBound δ s K T) (D : ℕ) (hD : T.card ≤ D) :
    let J := Nat.log 2 D+1
    ∃ k : ℕ, k < J ∧ ∃ A ⊆ T.image q, A.Nonempty ∧
      NormalizedFiniteBallBound ρ s (2*(K*(C+1)^s)*(J:ℝ)) A ∧
      (T.card:ℝ) ≤ (J:ℝ)*(∑ a ∈ A, (((T.filter fun l => q l = a).card):ℝ)) ∧
      ∀ a ∈ A, 2^k ≤ (T.filter fun l => q l = a).card ∧
        (T.filter fun l => q l = a).card < 2^(k+1) := by
  let w := fun a => (T.filter fun l => q l = a).card
  have htotal : (∑ a ∈ T.image q, (w a:ℝ)) = (T.card:ℝ) := by
    exact_mod_cast Finset.sum_card_fiberwise_eq_card_filter T (T.image q) q |>.trans (by
      congr 1
      exact Finset.filter_eq_self.mpr fun l hl => Finset.mem_image_of_mem q hl)
  have hwb : ∀ a ∈ T.image q, 0 < w a ∧ w a ≤ D := by
    intro a ha
    obtain ⟨l,hl,rfl⟩ := Finset.mem_image.mp ha
    exact ⟨Finset.card_pos.mpr ⟨l,Finset.mem_filter.mpr ⟨hl,rfl⟩⟩,
      (Finset.card_filter_le _ _).trans hD⟩
  have hwr : ∀ z r, ρ ≤ r → r ≤ 1 →
      (∑ a ∈ (T.image q).filter (fun a => dist a z ≤ r), (w a:ℝ)) ≤
        (K*(C+1)^s)*r^s*(∑ a ∈ T.image q, (w a:ℝ)) := by
    have hh := coarse_pencil_weight_ball_mul hρ hδρ hs hK hC
      {0} (fun _ => T) q (fun _ _ l hl => hnear l hl) (fun _ _ => hball)
    simpa only [Finset.singleton_biUnion,coarsePencilWeight,Finset.sum_singleton] using hh
  obtain ⟨k,A,hA,hne,hweight,hband,hreg⟩ := weighted_dyadic_regular_subset hρ.le
    (by positivity : 0 ≤ K*(C+1)^s) (T.image q) w (hT.image q) D hwb hwr
  refine ⟨k,?_,A,hA,hne,hreg,?_,hband⟩
  · obtain ⟨a,ha⟩ := hne
    exact Nat.lt_succ_of_le (Nat.le_log_of_pow_le (by norm_num) ((hband a ha).1.trans (hwb a (hA ha)).2))
  · rwa [htotal] at hweight

end Falconer

end OAI
