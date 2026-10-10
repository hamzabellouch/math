import OAI.NumberTheory.CubicMoment.Estimates.DivisorCoprimePoisson

namespace OAI

/-! Exact cube/noncube splitting of the coprime square-divisor component. -/
noncomputable section
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma tsum_split_effective_cubes (d : Eisenstein) (F : Eisenstein → ℂ)
    (hF : Summable F) (h0 : F 0 = 0) :
    (∑' h : Eisenstein, F h) =
      (∑' h : Eisenstein, if h ≠ 0 ∧ (∃ j : Eisenstein, j^3 = d*h) then F h else 0) +
      (∑' h : Eisenstein, if ∃ j : Eisenstein, j^3 = d*h then 0 else F h) := by
  let P := fun h : Eisenstein => h ≠ 0 ∧ (∃ j : Eisenstein, j^3 = d*h)
  let Q := fun h : Eisenstein => ¬∃ j : Eisenstein, j^3 = d*h
  have hp := hF.indicator {h | P h}
  have hq := hF.indicator {h | Q h}
  have he (h : Eisenstein) : F h = {h | P h}.indicator F h+{h | Q h}.indicator F h := by
    by_cases hz : h = 0
    · subst h
      simp only [h0,Set.indicator_apply,ite_self,zero_add]
    · by_cases hc : ∃ j : Eisenstein, j^3 = d*h
      · rw [Set.indicator_of_mem (show h ∈ {h | P h} from ⟨hz,hc⟩),
          Set.indicator_of_notMem (show h ∉ {h | Q h} from fun hn => hn hc),add_zero]
      · rw [Set.indicator_of_notMem (show h ∉ {h | P h} from fun hp => hc hp.2),
          Set.indicator_of_mem (show h ∈ {h | Q h} from hc),zero_add]
  rw [tsum_congr he,hp.tsum_add hq]
  congr 1
  · apply tsum_congr
    intro h
    by_cases hh : P h
    · rw [Set.indicator_of_mem (show h ∈ {h | P h} from hh),ite_eq_left hh]
    · rw [Set.indicator_of_notMem (show h ∉ {h | P h} from hh),ite_eq_right hh]
  · apply tsum_congr
    intro h
    by_cases hc : ∃ j : Eisenstein, j^3 = d*h
    · rw [Set.indicator_of_notMem (show h ∉ {h | Q h} from fun hn => hn hc),ite_eq_left hc]
    · rw [Set.indicator_of_mem (show h ∈ {h | Q h} from hc),ite_eq_right hc]

theorem divisorCubePoissonContribution_lattice {d : Eisenstein} (hd : d ≠ 0)
    (S : Finset Eisenstein) (hS : ∀ a ∈ S, primary a)
    (β : Eisenstein → ℂ) (u : ℝ) (V : ℝ → ℂ)
    (hV : HasCompactSupport V) (hV' : ContDiff ℝ ∞ V) {A : ℝ} (hA : 0 < A) :
    divisorCubePoissonContribution d S β u V A =
      ∑' h : Eisenstein, if h ≠ 0 ∧ (∃ j : Eisenstein, j^3 = d*h) then
        finiteDivisorPoissonContribution d S {h} β u V A else 0 := by
  let P := fun h : Eisenstein => h ≠ 0 ∧ (∃ j : Eisenstein, j^3 = d*h)
  let F := fun (a b h : Eisenstein) => if IsCoprime a b then
    (β a*normTwist u a)*star (β b*normTwist u b)*
      ((A/(norm d)^2)/(9*Real.sqrt (norm (b*a))):ℝ)*
        (mixedSymbol b a (d^2)*gramDualTerm b a V (A/(norm d)^2) h) else 0
  have hF (a b : Eisenstein) (ha : a ∈ S) (hb : b ∈ S) :
      Summable (fun h => if P h then F a b h else 0) := by
    by_cases hab : IsCoprime a b
    · have hdN := norm_pos_of_ne_zero hd
      have hs := ((summable_gramDualTerm (hS b hb) (hS a ha) V hV hV'
        (show 0 < A/(norm d)^2 by positivity)).mul_left
        ((β a*normTwist u a)*star (β b*normTwist u b)*
          ((A/(norm d)^2)/(9*Real.sqrt (norm (b*a))):ℝ)*mixedSymbol b a (d^2))).indicator {h | P h}
      convert hs using 1
      funext h
      rw [Set.indicator_apply]
      change (if P h then F a b h else 0) = if P h then _ else 0
      split_ifs
      · simp only [F,ite_eq_left hab]
        ring
      · rfl
    · simp only [F,ite_eq_right hab,ite_self]
      exact summable_zero
  have he (h : Eisenstein) : (if P h then finiteDivisorPoissonContribution d S {h} β u V A else 0) =
      ∑ a ∈ S, ∑ b ∈ S, if P h then F a b h else 0 := by
    by_cases hp : P h
    · simp only [hp,ite_true,finiteDivisorPoissonContribution,Finset.sum_singleton,F]
    · simp only [hp,ite_false,Finset.sum_const_zero]
  change _ = ∑' h : Eisenstein, if P h then _ else 0
  simp_rw [he]
  rw [Summable.tsum_finsetSum (fun a ha => summable_sum (fun b hb => hF a b ha hb))]
  unfold divisorCubePoissonContribution
  apply Finset.sum_congr rfl
  intro a ha
  rw [Summable.tsum_finsetSum (fun b hb => hF a b ha hb)]
  apply Finset.sum_congr rfl
  intro b hb
  by_cases hab : IsCoprime a b
  · simp only [ite_eq_left hab]
    rw [← tsum_mul_left]
    apply tsum_congr
    intro h
    change ((β a*normTwist u a)*star (β b*normTwist u b)*
      ((A/(norm d)^2)/(9*Real.sqrt (norm (b*a))):ℝ))*
      (if P h then mixedSymbol b a (d^2)*gramDualTerm b a V (A/(norm d)^2) h else 0) =
      if P h then F a b h else 0
    by_cases hp : P h
    · simp only [hp,ite_true,F,ite_eq_left hab]
    · simp only [hp,ite_false,mul_zero]
  · simp only [ite_eq_right hab,F,ite_self,tsum_zero]

theorem divisorCoprimeDispersionGram_split {d : Eisenstein} (hd : d ≠ 0)
    (S : Finset Eisenstein) (hS : ∀ a ∈ S, primary a ∧ Squarefree a ∧ a ≠ 1)
    (β : Eisenstein → ℂ) (u : ℝ) (V : ℝ → ℂ)
    (hV : HasCompactSupport V) (hV' : ContDiff ℝ ∞ V) {A : ℝ} (hA : 0 < A) :
    divisorCoprimeDispersionGram d S β u V A =
      divisorCubePoissonContribution d S β u V A + divisorNoncubePoissonContribution d hd S β u V A := by
  rw [divisorCoprimeDispersionGram_poisson hd S (fun a ha => ⟨(hS a ha).1,(hS a ha).2.1⟩)
    β u V hV hV' hA,
    divisorCubePoissonContribution_lattice hd S (fun a ha => (hS a ha).1) β u V hV hV' hA,
    divisorNoncubePoissonContribution_lattice hd S (fun a ha => (hS a ha).1) β u V hV hV' hA]
  exact tsum_split_effective_cubes d _
    (summable_finiteDivisorPoisson_singleton hd S (fun a ha => (hS a ha).1) β u V hV hV' hA)
    (finiteDivisorPoissonContribution_zero d S hS β u V A)

end CubicFirstMoment

end

end OAI
