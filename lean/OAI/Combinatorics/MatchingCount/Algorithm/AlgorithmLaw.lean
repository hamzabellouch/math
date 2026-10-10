import Mathlib
import OAI.Combinatorics.MatchingCount.Algorithm.Algorithm
import OAI.Combinatorics.MatchingCount.Complexity.OnlineHistoryCost

namespace OAI

namespace MatchingFPRAS.PhysicalStream
lemma qaverage_mono {A : Type} [Fintype A] (f g : A→ℚ) (h : ∀ a,f a≤g a) : qaverage f≤qaverage g := by
  unfold qaverage
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum (fun a _=>h a)) (Nat.cast_nonneg _)
lemma qaverage_indicator {A : Type} [Fintype A] (P : A→Prop) [DecidablePred P] :
    qaverage (fun a=>if P a then 1 else 0)=((Finset.univ.filter P).card:ℚ)/Fintype.card A := by
  simp only [qaverage,Finset.sum_boole]
namespace Experiment
lemma mean_mono {A : Type} (p : Experiment A) (f g : A→ℚ) (h : p.All (fun a=>f a≤g a)) : p.mean f≤p.mean g := by
  induction p with
  | done a => exact h
  | delay n p ih => exact ih h
  | read p ih => exact div_le_div_of_nonneg_right (add_le_add (ih false h.1) (ih true h.2)) (by norm_num)
lemma mean_const {A : Type} (p : Experiment A) (q : ℚ) : p.mean (fun _=>q)=q := by
  induction p with
  | done a => rfl
  | delay n p ih => exact ih
  | read p ih => simp only [mean,ih];ring
lemma mean_indicator_eq_one {A : Type} (p : Experiment A) (P : A→Prop) [DecidablePred P]
    (h : p.All P) : p.mean (fun a=>if P a then 1 else 0)=1 := by
  induction p with
  | done value => exact ite_eq_left h
  | delay ticks experiment ih => exact ih h
  | read next ih => norm_num [mean,ih false h.1,ih true h.2]
end Experiment
end MatchingFPRAS.PhysicalStream

namespace MatchingFPRAS.LiteralAlgorithm
open scoped Classical
open TreeTyped TreeFraction PhysicalStream LiteralInput

lemma empty_source (G : GraphInput) (ε δ : ℚ) : empty (parseInput (encodeInput G ε δ))=decide (G.n=0) := by
  rw [parseInput_source];rfl
lemma invalid_source (G : GraphInput) (ε δ : ℚ) : invalid (parseInput (encodeInput G ε δ))=
    (!(decide (G.n%2=0)) || decide (2*G.edges.card<G.n)) := by
  rw [parseInput_source]
  simp only [invalid,ExecutableInput.tooSparse,edgeNumbers_length]
lemma invalid_zero (G : GraphInput) (ε δ : ℚ) (h : invalid (parseInput (encodeInput G ε δ))=true) : Z G=0 := by
  rw [invalid_source] at h
  by_cases he : Even G.n
  · have he' : G.n%2=0 := Nat.even_iff.mp he
    simp only [he',decide_true,Bool.not_true,Bool.false_or] at h
    exact zero_of_vertex_bound (of_decide_eq_true h)
  · exact zero_of_not_even he
lemma valid_even (G : GraphInput) (ε δ : ℚ) (h : invalid (parseInput (encodeInput G ε δ))=false) : Even G.n := by
  rw [invalid_source] at h
  by_contra he
  have he' : ¬G.n%2=0 := fun hm=>he (Nat.even_iff.mpr hm)
  simp only [he',decide_false,Bool.not_false,Bool.true_or,Bool.true_eq_false] at h
lemma valid_size (G : GraphInput) (ε δ : ℚ) (h : invalid (parseInput (encodeInput G ε δ))=false) :
    G.n≤2*(encodeInput G ε δ).length := by
  rw [invalid_source] at h
  have hh : ¬2*G.edges.card<G.n := by
    intro hc
    simp only [hc,decide_true,Bool.or_true,Bool.true_eq_false] at h
  exact (show G.n≤2*G.edges.card by omega).trans (Nat.mul_le_mul_left 2 (edgeCard_le_input_length G ε δ))
lemma valid_two (G : GraphInput) (ε δ : ℚ) (he : empty (parseInput (encodeInput G ε δ))=false)
    (hi : invalid (parseInput (encodeInput G ε δ))=false) : 2≤G.n := by
  have h0 := of_decide_eq_false (show decide (G.n=0)=false by rwa [empty_source] at he)
  have hev:=Nat.even_iff.mp (valid_even G ε δ hi)
  omega

def Proper (G : GraphInput) (as : List Symbol) : Prop :=
  ∃ q : ℚ,0≤q ∧ as=encodeRat q ∧ (Z G=0→q=0)
def AccurateWord (G : GraphInput) (ε : ℚ) (as : List Symbol) : Prop :=
  ∃ q : ℚ,as=encodeRat q ∧ (1-ε)*(Z G:ℚ)≤q ∧ q≤(1+ε)*(Z G:ℚ)
lemma algorithm_proper (G : GraphInput) (ε δ : ℚ) (he : 0<ε) (he1 : ε<1) (hd : 0≤δ) :
    (algorithm (encodeInput G ε δ)).All (Proper G) := by
  unfold algorithm
  rw [Experiment.all_map]
  have hen : LiteralCodec.ratWord (1,1)=encodeRat 1 := LiteralCodec.ratWord_repr 1 (by norm_num)
  have hzero : LiteralCodec.ratWord (0,1)=encodeRat 0 := LiteralCodec.ratWord_repr 0 (by norm_num)
  cases hE:empty (parseInput (encodeInput G ε δ)) with
  | true =>
    have hn : G.n=0 := of_decide_eq_true (by rwa [empty_source] at hE)
    have hz:=count_empty_graph hn
    simp only [count,hE,ite_true,Experiment.All]
    exact ⟨1,by norm_num,hen,by intro h;omega⟩
  | false =>
    cases hI:invalid (parseInput (encodeInput G ε δ)) with
    | true =>
      simp only [count,hE,hI,Bool.false_eq_true,ite_false,ite_true,Experiment.All]
      exact ⟨0,by norm_num,hzero,fun _=>rfl⟩
    | false =>
      simp only [count,hE,hI,Bool.false_eq_true,ite_false]
      have hn:=valid_two G ε δ hE hI
      have hev:=valid_even G ε δ hI
      let : Nontrivial (Fin G.n):=Fin.nontrivial_iff_two_le.mpr hn
      apply Experiment.all_of_qaverage _ (fun b=>TreeFraction.repr
        (FiniteTrial.guardedAmplifiedBitOutput (FiniteTrial.parameters G hn hev ε he he1) δ b))
      · exact compute_mean hn hev ε δ he he1 hd
      · intro b
        let p:=FiniteTrial.parameters G hn hev ε he he1
        have hq:=FiniteTrial.guardedAmplifiedBitOutput_nonneg p δ b
        exact ⟨_,hq,LiteralCodec.ratWord_repr _ hq,fun hz=>FiniteTrial.guardedAmplifiedBitOutput_zero p hz δ b⟩

lemma accurate_zero (G : GraphInput) (ε : ℚ) (hz : Z G=0) : AccurateWord G ε (encodeRat 0) := by
  refine ⟨0,rfl,?_,?_⟩ <;> simp [hz]
lemma proper_accurate_zero (G : GraphInput) (ε : ℚ) (hz : Z G=0) (as : List Symbol) (ha : Proper G as) :
    AccurateWord G ε as := by
  obtain ⟨q,_,rfl,hq⟩:=ha
  rw [hq hz]
  exact accurate_zero G ε hz

lemma algorithm_success (G : GraphInput) (ε δ : ℚ) (he : 0<ε) (he1 : ε<1) (hd : 0<δ) :
    1-δ≤(algorithm (encodeInput G ε δ)).mean (fun as=>if AccurateWord G ε as then 1 else 0) := by
  classical
  by_cases hz:Z G=0
  · rw [Experiment.mean_indicator_eq_one _ _ ((algorithm_proper G ε δ he he1 hd.le).mono
      (proper_accurate_zero G ε hz))]
    linarith
  have hZ:0<Z G:=Nat.pos_of_ne_zero hz
  cases hE:empty (parseInput (encodeInput G ε δ)) with
  | true =>
    have hn : G.n=0 := of_decide_eq_true (by rwa [empty_source] at hE)
    have hz:=count_empty_graph hn
    have hq : AccurateWord G ε (LiteralCodec.ratWord (1,1)) := by
      refine ⟨1,LiteralCodec.ratWord_repr 1 (by norm_num),?_,?_⟩ <;> rw [hz] <;> norm_num <;> linarith
    simp only [algorithm,Experiment.mean_map,count,hE,ite_true,Experiment.mean,ite_eq_left hq]
    linarith
  | false =>
    have hI:invalid (parseInput (encodeInput G ε δ))=false := by
      cases hi:invalid (parseInput (encodeInput G ε δ)) with
      | false => rfl
      | true => exact False.elim (hz (invalid_zero G ε δ hi))
    have hn:=valid_two G ε δ hE hI
    have hev:=valid_even G ε δ hI
    let : Nontrivial (Fin G.n):=Fin.nontrivial_iff_two_le.mpr hn
    let p:=FiniteTrial.parameters G hn hev ε he he1
    have hs:=FiniteTrial.guardedAmplifiedBitOutput_success p hZ δ hd
    have hb : qaverage (fun b=>if FiniteTrial.Accurate p (FiniteTrial.guardedAmplifiedBitOutput p δ b) then 1 else 0)≥1-δ := by
      rw [qaverage_indicator]
      simpa only [FiniteTrial.guardedAccurateBits,Fintype.card_fun,Fintype.card_fin,Fintype.card_bool,Nat.cast_pow,Nat.cast_ofNat] using hs
    simp only [algorithm,Experiment.mean_map,count,hE,hI,Bool.false_eq_true,ite_false]
    rw [compute_mean hn hev ε δ he he1 hd.le]
    apply hb.trans (qaverage_mono _ _ (fun b=>?_))
    split_ifs with ha hword hword
    · rfl
    · exfalso
      apply hword
      exact ⟨_,LiteralCodec.ratWord_repr _ (FiniteTrial.guardedAmplifiedBitOutput_nonneg p δ b),ha⟩
    · norm_num
    · rfl
end MatchingFPRAS.LiteralAlgorithm

end OAI
