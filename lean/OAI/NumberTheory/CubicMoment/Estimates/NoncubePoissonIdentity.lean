import OAI.NumberTheory.CubicMoment.Estimates.NoncubePoissonTotal

namespace OAI

/-! The bounded dyadic sum is the literal noncube part of the lattice
Poisson identity. No frequency terms or coprimality conditions are dropped. -/
noncomputable section
open scoped BigOperators ContDiff
open Set
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem noncubePoissonContribution_lattice (S : Finset Eisenstein)
    (hS : ∀ a ∈ S, primary a) (β : Eisenstein → ℂ) (u : ℝ)
    (V : ℝ → ℂ) (hV : HasCompactSupport V) (hV' : ContDiff ℝ ∞ V)
    {A : ℝ} (hA : 0 < A) :
    noncubePoissonContribution S β u V A =
      ∑' h : Eisenstein, if ∃ z : Eisenstein, z^3 = h then 0 else
        ∑ a ∈ S, ∑ b ∈ S, if IsCoprime a b then
          (β a*normTwist u a)*star (β b*normTwist u b)*
            (A/(9*Real.sqrt (norm (b*a))):ℝ)*gramDualTerm b a V A h else 0 := by
  let G := fun (a b h : Eisenstein) => if IsCoprime a b then
    (β a*normTwist u a)*star (β b*normTwist u b)*
      (A/(9*Real.sqrt (norm (b*a))):ℝ)*gramDualTerm b a V A h else 0
  let F := fun h : Eisenstein => ∑ a ∈ S, ∑ b ∈ S,
    if ∃ z : Eisenstein, z^3 = h then 0 else G a b h
  have hG (a b : Eisenstein) (ha : a ∈ S) (hb : b ∈ S) :
      Summable (fun h : Eisenstein => if ∃ z : Eisenstein, z^3 = h then 0 else G a b h) := by
    by_cases hab : IsCoprime a b
    · have hs := ((summable_gramDualTerm (hS b hb) (hS a ha) V hV hV' hA).mul_left
        ((β a*normTwist u a)*star (β b*normTwist u b)*(A/(9*Real.sqrt (norm (b*a))):ℝ))).indicator
          {h : Eisenstein | ¬∃ z : Eisenstein, z^3 = h}
      convert hs using 1
      funext h
      by_cases hc : ∃ z : Eisenstein, z^3 = h
      · simp only [ite_eq_left hc, Set.indicator_of_notMem (show h ∉ {h : Eisenstein | ¬∃ z : Eisenstein, z^3 = h} from fun hnot => hnot hc)]
      · simp only [ite_eq_right hc, Set.indicator_of_mem (show h ∈ {h : Eisenstein | ¬∃ z : Eisenstein, z^3 = h} from hc), G, ite_eq_left hab]
    · simp only [G,hab,ite_false,ite_self]
      exact summable_zero
  have hF : Summable F := summable_sum (fun a ha => summable_sum (fun b hb => hG a b ha hb))
  have hF0 : F 0 = 0 := by
    simp only [F, ite_eq_left (show ∃ z : Eisenstein, z^3 = 0 from ⟨0,by simp⟩), Finset.sum_const_zero]
  have hblocks := hasSum_frequencyDyad F hF hF0
  have heq (j : ℕ) : (∑ h ∈ frequencyDyad j, F h) =
      finitePoissonContribution S ((frequencyDyad j).filter (fun h => ¬∃ z : Eisenstein, z^3 = h))
        β u V A := by
    unfold finitePoissonContribution
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro h hh
    by_cases hc : ∃ z : Eisenstein, z^3 = h
    · simp only [F, ite_eq_left hc, ite_eq_right (not_not_intro hc), Finset.sum_const_zero]
    · simp only [F, ite_eq_right hc, ite_eq_left hc, G]
  simp_rw [heq] at hblocks
  change (∑' j : ℕ, finitePoissonContribution S
    ((frequencyDyad j).filter (fun h => ¬∃ z : Eisenstein, z^3 = h)) β u V A) = _
  rw [hblocks.tsum_eq]
  apply tsum_congr
  intro h
  by_cases hc : ∃ z : Eisenstein, z^3 = h
  · simp only [F, ite_eq_left hc, Finset.sum_const_zero]
  · simp only [F, ite_eq_right hc, G]

end CubicFirstMoment

end

end OAI
