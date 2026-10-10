import OAI.NumberTheory.CubicMoment.Estimates.NoncubePoissonIdentity

namespace OAI

/-! Exact cube/noncube splitting of the coprime portion of the variance.
No diagonal or shared-prime contribution is silently included here. -/
noncomputable section
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma tsum_split_nonzero_cubes (F : Eisenstein → ℂ) (hF : Summable F) (h0 : F 0 = 0) :
    (∑' h : Eisenstein, F h) =
      (∑' h : Eisenstein, if h ≠ 0 ∧ (∃ j : Eisenstein, j^3 = h) then F h else 0) +
      (∑' h : Eisenstein, if ∃ j : Eisenstein, j^3 = h then 0 else F h) := by
  let P := fun h : Eisenstein => h ≠ 0 ∧ (∃ j : Eisenstein, j^3 = h)
  let Q := fun h : Eisenstein => ¬∃ j : Eisenstein, j^3 = h
  have hp := hF.indicator {h | P h}
  have hq := hF.indicator {h | Q h}
  have he (h : Eisenstein) : F h =
      {h | P h}.indicator F h+{h | Q h}.indicator F h := by
    by_cases hz : h = 0
    · subst h
      simp only [h0,Set.indicator_apply,ite_self,zero_add]
    · by_cases hc : ∃ j : Eisenstein, j^3 = h
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
    by_cases hc : ∃ j : Eisenstein, j^3 = h
    · rw [Set.indicator_of_notMem (show h ∉ {h | Q h} from fun hn => hn hc),ite_eq_left hc]
    · rw [Set.indicator_of_mem (show h ∈ {h | Q h} from hc),ite_eq_right hc]

def coprimeDispersionGram (S : Finset Eisenstein) (β : Eisenstein → ℂ)
    (u : ℝ) (W : ℝ → ℂ) (A : ℝ) : ℂ :=
  ∑ a ∈ S, ∑ b ∈ S, if IsCoprime a b then
    dispersionAmplitude β u a*star (dispersionAmplitude β u b)*primaryCharacterGram b a W A else 0

def cubePoissonContribution (S : Finset Eisenstein) (β : Eisenstein → ℂ)
    (u : ℝ) (W : ℝ → ℂ) (A : ℝ) : ℂ :=
  ∑ a ∈ S, ∑ b ∈ S, if IsCoprime a b then
    (β a*normTwist u a)*star (β b*normTwist u b)*(A/(9*Real.sqrt (norm (b*a))):ℝ)*
      ∑' h : Eisenstein, if h ≠ 0 ∧ (∃ j : Eisenstein, j^3 = h) then
        gramDualTerm b a W A h else 0
    else 0

theorem coprimeDispersionGram_split (S : Finset Eisenstein)
    (hS : ∀ a ∈ S, primary a ∧ Squarefree a ∧ a ≠ 1)
    (β : Eisenstein → ℂ) (u : ℝ) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (hW' : ContDiff ℝ ∞ W) {A : ℝ} (hA : 0 < A) :
    coprimeDispersionGram S β u W A =
      cubePoissonContribution S β u W A+noncubePoissonContribution S β u W A := by
  rw [noncubePoissonContribution_lattice S (fun a ha => (hS a ha).1) β u W hW hW' hA]
  let F := fun (a b h : Eisenstein) => if IsCoprime a b then
    (β a*normTwist u a)*star (β b*normTwist u b)*(A/(9*Real.sqrt (norm (b*a))):ℝ)*
      (if ∃ j : Eisenstein, j^3 = h then 0 else gramDualTerm b a W A h) else 0
  have hs (a b : Eisenstein) (ha : a ∈ S) (hb : b ∈ S) : Summable (F a b) := by
    by_cases hab : IsCoprime a b
    · have hf := ((summable_gramDualTerm (hS b hb).1 (hS a ha).1 W hW hW' hA).indicator
        {h : Eisenstein | ¬∃ j : Eisenstein, j^3 = h}).mul_left
          ((β a*normTwist u a)*star (β b*normTwist u b)*(A/(9*Real.sqrt (norm (b*a))):ℝ))
      convert hf using 1
      funext h
      dsimp only [F]
      rw [ite_eq_left hab]
      congr 1
      by_cases hc : ∃ j : Eisenstein, j^3 = h
      · rw [ite_eq_left hc,Set.indicator_of_notMem
          (show h ∉ {h : Eisenstein | ¬∃ j : Eisenstein, j^3 = h} from fun hn => hn hc)]
      · rw [ite_eq_right hc,Set.indicator_of_mem
          (show h ∈ {h : Eisenstein | ¬∃ j : Eisenstein, j^3 = h} from hc)]
    · simp only [F,ite_eq_right hab]
      exact summable_zero
  have hswap : (∑' h : Eisenstein, if ∃ j : Eisenstein, j^3 = h then 0 else
      ∑ a ∈ S, ∑ b ∈ S, if IsCoprime a b then
        (β a*normTwist u a)*star (β b*normTwist u b)*(A/(9*Real.sqrt (norm (b*a))):ℝ)*
          gramDualTerm b a W A h else 0) = ∑ a ∈ S, ∑ b ∈ S, ∑' h, F a b h := by
    have he (h : Eisenstein) : (if ∃ j : Eisenstein, j^3 = h then 0 else
        ∑ a ∈ S, ∑ b ∈ S, if IsCoprime a b then
          (β a*normTwist u a)*star (β b*normTwist u b)*(A/(9*Real.sqrt (norm (b*a))):ℝ)*
            gramDualTerm b a W A h else 0) = ∑ a ∈ S, ∑ b ∈ S, F a b h := by
      by_cases hc : ∃ j : Eisenstein, j^3 = h
      · simp only [F,ite_eq_left hc,mul_zero,ite_self,Finset.sum_const_zero]
      · simp only [F,ite_eq_right hc]
    simp_rw [he]
    rw [Summable.tsum_finsetSum (fun a ha => summable_sum (fun b hb => hs a b ha hb))]
    apply Finset.sum_congr rfl
    intro a ha
    exact Summable.tsum_finsetSum (fun b hb => hs a b ha hb)
  rw [hswap]
  unfold coprimeDispersionGram cubePoissonContribution
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro b hb
  by_cases hab : IsCoprime a b
  · simp only [ite_eq_left hab,F]
    have hne : b ≠ a := by
      intro hba
      exact (hS a ha).2.2 (primary_unit_eq_one (isCoprime_self.mp (hba ▸ hab)) (hS a ha).1)
    rw [dispersion_pair_poisson (hS a ha).1 (hS b hb).1
      (hS a ha).2.1 (hS b hb).2.1 hab β u W hW hW' hA,
      tsum_split_nonzero_cubes _ (summable_gramDualTerm (hS b hb).1 (hS a ha).1 W hW hW' hA)
        (gramDualTerm_zero (hS b hb).1 (hS a ha).1 (hS b hb).2.1 (hS a ha).2.1 hab.symm hne W A),
      mul_add]
    simp only [star_mul,tsum_mul_left]
    ring
  · simp only [ite_eq_right hab,F,tsum_zero,add_zero]

end CubicFirstMoment

end

end OAI
