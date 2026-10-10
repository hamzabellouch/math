import OAI.NumberTheory.CubicMoment.Estimates.DivisorNoncubeTotal

namespace OAI

/-! The estimated divisor dyads are exactly the noncube part of the
full lattice Poisson sum, with the cube test at d*h. -/
noncomputable section
open scoped BigOperators ContDiff
open Set
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma summable_finiteDivisorPoisson_singleton {d : Eisenstein} (hd : d ≠ 0)
    (S : Finset Eisenstein) (hS : ∀ a ∈ S, primary a)
    (β : Eisenstein → ℂ) (u : ℝ) (V : ℝ → ℂ)
    (hV : HasCompactSupport V) (hV' : ContDiff ℝ ∞ V) {A : ℝ} (hA : 0 < A) :
    Summable (fun h : Eisenstein => finiteDivisorPoissonContribution d S {h} β u V A) := by
  simp only [finiteDivisorPoissonContribution,Finset.sum_singleton]
  apply summable_sum
  intro a ha
  apply summable_sum
  intro b hb
  by_cases hab : IsCoprime a b
  · simp only [ite_eq_left hab]
    have hdN := norm_pos_of_ne_zero hd
    have hs := (summable_gramDualTerm (hS b hb) (hS a ha) V hV hV'
      (show 0 < A/(norm d)^2 by positivity)).mul_left
        ((β a*normTwist u a)*star (β b*normTwist u b)*
          ((A/(norm d)^2)/(9*Real.sqrt (norm (b*a))):ℝ)*mixedSymbol b a (d^2))
    convert hs using 1
    funext h
    ring
  · simp only [ite_eq_right hab]
    exact summable_zero

lemma tsum_divisor_noncube_dyads (d : Eisenstein) (hd : d ≠ 0)
    (F : Eisenstein → ℂ) (hF : Summable F) :
    (∑' j : ℕ, ∑ h ∈ (divisorFrequencyDyad d hd j).filter
        (fun h => ¬∃ z : Eisenstein, z^3 = d*h), F h) =
      ∑' h : Eisenstein, if ∃ z : Eisenstein, z^3 = d*h then 0 else F h := by
  let G := fun h : Eisenstein => if ∃ z : Eisenstein, z^3 = d*h then 0 else F h
  have he (h : Eisenstein) : G h = {h : Eisenstein | ¬∃ z : Eisenstein, z^3 = d*h}.indicator F h := by
    by_cases hh : ∃ z : Eisenstein, z^3 = d*h
    · simp only [G,ite_eq_left hh,Set.indicator_of_notMem (show h ∉
        {h : Eisenstein | ¬∃ z : Eisenstein, z^3 = d*h} from fun hn => hn hh)]
    · simp only [G,ite_eq_right hh,Set.indicator_of_mem (show h ∈
        {h : Eisenstein | ¬∃ z : Eisenstein, z^3 = d*h} from hh)]
  have hG : Summable G := by
    rw [show G = {h : Eisenstein | ¬∃ z : Eisenstein, z^3 = d*h}.indicator F from funext he]
    exact hF.indicator {h : Eisenstein | ¬∃ z : Eisenstein, z^3 = d*h}
  have h0 : G 0 = 0 := by
    apply ite_eq_left
    exact ⟨0,by simp⟩
  have hblocks := hasSum_divisorFrequencyDyad d hd G hG h0
  have hblock (j : ℕ) : (∑ h ∈ divisorFrequencyDyad d hd j, G h) =
      ∑ h ∈ (divisorFrequencyDyad d hd j).filter
        (fun h => ¬∃ z : Eisenstein, z^3 = d*h), F h := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro h _
    by_cases hh : ∃ z : Eisenstein, z^3 = d*h
    · simp only [G,ite_eq_left hh,ite_eq_right (not_not_intro hh)]
    · simp only [G,ite_eq_right hh,ite_eq_left hh]
  simp_rw [hblock] at hblocks
  exact hblocks.tsum_eq

theorem divisorNoncubePoissonContribution_lattice {d : Eisenstein} (hd : d ≠ 0)
    (S : Finset Eisenstein) (hS : ∀ a ∈ S, primary a)
    (β : Eisenstein → ℂ) (u : ℝ) (V : ℝ → ℂ)
    (hV : HasCompactSupport V) (hV' : ContDiff ℝ ∞ V) {A : ℝ} (hA : 0 < A) :
    divisorNoncubePoissonContribution d hd S β u V A =
      ∑' h : Eisenstein, if ∃ z : Eisenstein, z^3 = d*h then 0 else
        finiteDivisorPoissonContribution d S {h} β u V A := by
  let F := fun h : Eisenstein => finiteDivisorPoissonContribution d S {h} β u V A
  have he (H : Finset Eisenstein) : finiteDivisorPoissonContribution d S H β u V A =
      ∑ h ∈ H, F h := by
    simp only [F,finiteDivisorPoissonContribution,Finset.sum_singleton]
  calc
    _ = ∑' j : ℕ, ∑ h ∈ (divisorFrequencyDyad d hd j).filter
        (fun h => ¬∃ z : Eisenstein, z^3 = d*h), F h := by
      apply tsum_congr
      exact fun j => he _
    _ = _ := tsum_divisor_noncube_dyads d hd F
      (summable_finiteDivisorPoisson_singleton hd S hS β u V hV hV' hA)

end CubicFirstMoment

end

end OAI
