import Mathlib
import OAI.Combinatorics.MatchingCount.Algorithm.AlgorithmLaw
import OAI.Combinatorics.MatchingCount.Machines.Wrapper
import OAI.Combinatorics.MatchingCount.Machines.PhysicalProgramSeal

namespace OAI

namespace MatchingFPRAS.LiteralPhysical
open Turing PhysicalPost PhysicalStream LiteralAlgorithm
open scoped Classical

def ProperTape (G : GraphInput) (T : Tape Symbol) : Prop :=
  ∃ q : ℚ,0≤q ∧ T.right₀=ListBlank.mk (encodeRat q) ∧ (Z G=0→q=0)
def AccurateTape (G : GraphInput) (ε : ℚ) (T : Tape Symbol) : Prop :=
  ∃ q : ℚ,T.right₀=ListBlank.mk (encodeRat q) ∧ (1-ε)*(Z G:ℚ)≤q ∧ q≤(1+ε)*(Z G:ℚ)
lemma properTape_of_word (G : GraphInput) (as : List Symbol) (h : Proper G as) : ProperTape G (Tape.mk₁ as) := by
  obtain ⟨q,hq,rfl,hz⟩:=h
  exact ⟨q,hq,by simp [Tape.mk₁,Tape.mk₂],hz⟩
lemma accurateTape_of_word (G : GraphInput) (ε : ℚ) (as : List Symbol) (h : AccurateWord G ε as) :
    AccurateTape G ε (Tape.mk₁ as) := by
  obtain ⟨q,rfl,hq⟩:=h
  exact ⟨q,by simp [Tape.mk₁,Tape.mk₂],hq⟩
lemma mainProgram_all (G : GraphInput) (ε δ : ℚ) (he : 0<ε) (he1 : ε<1) (hd : 0≤δ)
    (n : ℕ) (hn : wrapTime algorithmRealizer (encodeInput G ε δ)≤n) (b : Bits n) :
    (MatchingFPRAS.run mainProgram.machine (encodeInput G ε δ) b).state=none ∧
      ProperTape G (MatchingFPRAS.run mainProgram.machine (encodeInput G ε δ) b).tape := by
  apply (mainProgram_realizes G ε δ).run_all _ _ n hn b
  rw [Experiment.all_map]
  exact (algorithm_proper G ε δ he he1 hd).mono (properTape_of_word G)
lemma mainProgram_outputs (G : GraphInput) (ε δ : ℚ) (he : 0<ε) (he1 : ε<1) (hd : 0≤δ)
    (n : ℕ) (hn : wrapTime algorithmRealizer (encodeInput G ε δ)≤n) :
    (∀ b : Bits n,∃ q : ℚ,0≤q ∧ Outputs mainProgram.machine (encodeInput G ε δ) b q) ∧
    (Z G=0→∀ b : Bits n,Outputs mainProgram.machine (encodeInput G ε δ) b 0) := by
  constructor
  · intro b
    obtain ⟨hh,q,hq,ht,_⟩:=mainProgram_all G ε δ he he1 hd n hn b
    exact ⟨q,hq,hh,ht⟩
  · intro hz b
    obtain ⟨hh,q,_hq,ht,hzq⟩:=mainProgram_all G ε δ he he1 hd n hn b
    rw [hzq hz] at ht
    exact ⟨hh,ht⟩
lemma average_good (A : RandomMachine) (G : GraphInput) (ε δ : ℚ) (n : ℕ)
    (hh : ∀ b : Bits n,(MatchingFPRAS.run A (encodeInput G ε δ) b).state=none) :
    average (fun b : Bits n=>if AccurateTape G ε (MatchingFPRAS.run A (encodeInput G ε δ) b).tape then 1 else 0)=
      ((goodTapes A G ε δ n).card:ℚ)/(2:ℚ)^n := by
  have he (b : Bits n) : AccurateTape G ε (MatchingFPRAS.run A (encodeInput G ε δ) b).tape ↔
      ∃ q : ℚ,Outputs A (encodeInput G ε δ) b q ∧ (1-ε)*(Z G:ℚ)≤q ∧ q≤(1+ε)*(Z G:ℚ) := by
    constructor
    · rintro ⟨q,ht,hq⟩;exact ⟨q,⟨hh b,ht⟩,hq⟩
    · rintro ⟨q,⟨_,ht⟩,hq⟩;exact ⟨q,ht,hq⟩
  simp_rw [he]
  simp only [average,goodTapes,Finset.sum_boole]
lemma mainProgram_success (G : GraphInput) (ε δ : ℚ) (he : 0<ε) (he1 : ε<1) (hd : 0<δ)
    (n : ℕ) (hn : wrapTime algorithmRealizer (encodeInput G ε δ)≤n) :
    1-δ≤((goodTapes mainProgram.machine G ε δ n).card:ℚ)/(2:ℚ)^n := by
  have hs : 1-δ≤(algorithm (encodeInput G ε δ)).mean
      (fun as=>if AccurateTape G ε (Tape.mk₁ as) then 1 else 0) := by
    apply (algorithm_success G ε δ he he1 hd).trans (Experiment.mean_mono _ _ _ ?_)
    exact (Experiment.all_true _).mono (by
      intro as _
      by_cases h : AccurateWord G ε as
      · simp only [ite_eq_left h,ite_eq_left (accurateTape_of_word G ε as h),le_refl]
      · simp only [ite_eq_right h];split_ifs <;> norm_num)
  have hm:=(mainProgram_realizes G ε δ).run_mean (fun T=>if AccurateTape G ε T then 1 else 0) n hn
  rw [Experiment.mean_map] at hm
  rw [←hm,average_good mainProgram.machine G ε δ n
    (fun b=>(mainProgram_all G ε δ he he1 hd.le n hn b).1)] at hs
  exact hs
end MatchingFPRAS.LiteralPhysical

end OAI
