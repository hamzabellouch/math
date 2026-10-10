import OAI.MeasureTheory.Falconer.Incidence.CoarsePencilWeights

namespace OAI

/-! Heavy coarse cells selected by their original point counts. Both the
coarse regularity and the fine mass retained in their union are quantitative. -/
namespace Falconer
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem regular_coarse_cells {δ Δ t K : ℝ}
    (hΔ : 0 < Δ) (hδΔ : δ ≤ Δ) (ht : 0 ≤ t) (hK : 1 ≤ K)
    (P : Finset (Space 2)) (hP : P.Nonempty) (q : Space 2 → Space 2)
    (hnear : ∀ x ∈ P, dist x (q x) ≤ Δ)
    (hball : NormalizedFiniteBallBound δ t K P) :
    let J := Nat.log 2 P.card+1
    ∃ k : ℕ, ∃ C ⊆ P.image q, C.Nonempty ∧
      NormalizedFiniteBallBound Δ t (2*(K*(2:ℝ)^t)*(J:ℝ)) C ∧
      (P.card:ℝ) ≤ (J:ℝ)*∑ c ∈ C, ((P.filter fun x => q x = c).card:ℝ) ∧
      ∀ c ∈ C, 2^k ≤ (P.filter fun x => q x = c).card ∧
        (P.filter fun x => q x = c).card < 2^(k+1) := by
  let w := fun c => (P.filter fun x => q x = c).card
  have hw (c : Space 2) (hc : c ∈ P.image q) : 0 < w c ∧ w c ≤ P.card := by
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hc
    exact ⟨Finset.card_pos.mpr ⟨x,Finset.mem_filter.mpr ⟨hx,rfl⟩⟩,Finset.card_filter_le _ _⟩
  have htotal : (∑ c ∈ P.image q, (w c:ℝ)) = (P.card:ℝ) := by
    exact_mod_cast (Finset.card_eq_sum_card_image q P).symm
  have hb : ∀ z r, Δ ≤ r → r ≤ 1 →
      (∑ c ∈ (P.image q).filter (fun c => dist c z ≤ r), (w c:ℝ)) ≤
        (K*(2:ℝ)^t)*r^t*(∑ c ∈ P.image q, (w c:ℝ)) := by
    have hh := coarse_pencil_weight_ball hΔ hδΔ ht hK ({0}:Finset (Space 2))
      (fun _ => P) q (fun _ _ x hx => hnear x hx) (fun _ _ => hball)
    simpa only [coarsePencilWeight,Finset.singleton_biUnion,Finset.sum_singleton] using hh
  obtain ⟨k,C,hCP,hC,hmass,hband,hreg⟩ := weighted_dyadic_regular_subset hΔ.le
    (show 0 ≤ K*(2:ℝ)^t by positivity) (P.image q) w (hP.image q) P.card hw hb
  refine ⟨k,C,hCP,hC,hreg,?_,hband⟩
  rwa [htotal] at hmass

theorem heavy_coarse_union_count (P C : Finset (Space 2)) (q : Space 2 → Space 2) :
    (P.filter fun x => q x ∈ C).card = ∑ c ∈ C, (P.filter fun x => q x = c).card :=
  (Finset.sum_card_fiberwise_eq_card_filter P C q).symm

end Falconer

end OAI
