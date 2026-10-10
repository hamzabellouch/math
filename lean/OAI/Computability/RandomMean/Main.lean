import OAI.Computability.RandomMean.Complexity

namespace OAI

section
namespace MeanPayoff.RegisterBits.Compile
open BinaryData
open scoped Classical
 theorem correct_probability {K : ℕ} (P : Program K) (G : Game) (n : ℕ)
    (hh : (tree P n (RegisterBits.initial P (input G))).All (fun c => c.control=none)) :
    (2:ℚ)^(2*bound P (input G) n)*
      (tree P n (RegisterBits.initial P (input G))).probability (fun c => BinaryInput.CorrectList G c.output)≤
    ((Finset.univ.filter (fun bits : Fin (2*bound P (input G) n)→Bool =>
      CorrectOutput G (result (machine P) G (2*bound P (input G) n) bits))).card : ℚ) := by
  classical
  have hp := machine_probability P (input G) n hh (BinaryInput.CorrectList G)
  apply hp.trans
  apply Nat.cast_le.mpr
  apply Finset.card_le_card
  intro bits hb
  simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hb ⊢
  obtain ⟨out,ho,hhalt,ht⟩ := hb
  exact correctList_packet G (machine P) _ out ho hhalt ht
 theorem correct_count {K : ℕ} (P : Program K) (G : Game) (n : ℕ)
    (hh : (tree P n (RegisterBits.initial P (input G))).All (fun c => c.control=none))
    (hp : 7/8≤(tree P n (RegisterBits.initial P (input G))).probability
      (fun c => BinaryInput.CorrectList G c.output)) :
    7*2^(2*bound P (input G) n)≤8*(Finset.univ.filter
      (fun bits : Fin (2*bound P (input G) n)→Bool =>
        CorrectOutput G (result (machine P) G (2*bound P (input G) n) bits))).card := by
  classical
  have hq := correct_probability P G n hh
  have hl : (2:ℚ)^(2*bound P (input G) n)*(7/8)≤
      ((Finset.univ.filter (fun bits : Fin (2*bound P (input G) n)→Bool =>
        CorrectOutput G (result (machine P) G (2*bound P (input G) n) bits))).card : ℚ) :=
    (mul_le_mul_of_nonneg_left hp (by positivity)).trans hq
  have hr : (7:ℚ)*2^(2*bound P (input G) n)≤8*
      ((Finset.univ.filter (fun bits : Fin (2*bound P (input G) n)→Bool =>
        CorrectOutput G (result (machine P) G (2*bound P (input G) n) bits))).card : ℚ) := by
    linarith only [hl]
  exact_mod_cast hr
 theorem halt_all {K : ℕ} (P : Program K) (G : Game) (n : ℕ)
    (hh : (tree P n (RegisterBits.initial P (input G))).All (fun c => c.control=none))
    (bits : Fin (2*bound P (input G) n)→Bool) :
    (result (machine P) G (2*bound P (input G) n) bits).control=none :=
  (machine_packet P (input G) n hh bits).1
end MeanPayoff.RegisterBits.Compile

end

section
namespace MeanPayoff

theorem main : MainClaim := by
  obtain ⟨K,e,h⟩ := Realizer.post_polynomial
  obtain ⟨C,hC,hbound⟩ := Realizer.total_quasi K e
  refine ⟨RegisterBits.Compile.machine Realizer.program,C,hC,fun G =>
    ⟨Realizer.total K e ⟨input G⟩,hbound ⟨input G⟩,?_,?_⟩⟩
  · exact RegisterBits.Compile.halt_all Realizer.program G (Realizer.limit K e ⟨input G⟩)
      (Realizer.tree_halts K e h ⟨input G⟩)
  · exact RegisterBits.Compile.correct_count Realizer.program G (Realizer.limit K e ⟨input G⟩)
      (Realizer.tree_halts K e h ⟨input G⟩) (Realizer.tree_success K e h G)
end MeanPayoff

theorem randomized_quasipolynomial_mean_payoff : MeanPayoff.MainClaim := MeanPayoff.main

end

end OAI
