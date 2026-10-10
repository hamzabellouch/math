import OAI.NumberTheory.DirichletL.Detector.GramShell

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbeGramCommon
open ActualEisensteinCubic ConcreteTraceCRT
local notation "O" => ActualEisensteinCubic.O

lemma nonzero_norm_one_le (z : O) (hz : z≠0) : (1:ℝ)≤‖eisEmbedding z‖^2 := by
  rw [eisEmbedding_norm_sq_eq_absNorm_span]
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr
    (Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr hz))

theorem annular_element_count (F : Finset O) (b N : ℝ) (hb : 0≤b) (hN : 0≤N)
    (hzero : ∀z∈F,z≠0) (hbound : ∀z∈F,‖eisEmbedding z‖^2≤b*N) :
    (F.card:ℝ)≤128*b*N := by
  by_cases hF : F.Nonempty
  · obtain ⟨z,hz⟩ := hF
    have hscale : 1≤b*N := (nonzero_norm_one_le z (hzero z hz)).trans (hbound z hz)
    simpa only [mul_assoc] using DescentFiberCost.finite_element_count_real F (b*N) hscale hbound
  · rw [Finset.not_nonempty_iff_eq_empty.mp hF,Finset.card_empty,Nat.cast_zero]
    positivity

theorem annular_pair_count (F G : Finset O) (b N : ℝ) (hb : 0≤b) (hN : 0≤N)
    (hFzero : ∀z∈F,z≠0) (hGzero : ∀z∈G,z≠0)
    (hFbound : ∀z∈F,‖eisEmbedding z‖^2≤b*N)
    (hGbound : ∀z∈G,‖eisEmbedding z‖^2≤b*N) :
    ((F×ˢG).card:ℝ)≤(128*b)^2*N^2 := by
  rw [Finset.card_product,Nat.cast_mul]
  have hf := annular_element_count F b N hb hN hFzero hFbound
  have hg := annular_element_count G b N hb hN hGzero hGbound
  calc
    _ ≤ (128*b*N)*(128*b*N) := mul_le_mul hf hg (Nat.cast_nonneg _) (by positivity)
    _ = _ := by ring

end SevenEighths.ProbeGramCommon
end

end OAI
