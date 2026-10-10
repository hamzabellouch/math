import Mathlib
import OAI.Combinatorics.RamseyFive.Entropy.RevealDomains
import OAI.Combinatorics.RamseyFive.Entropy.FiniteKernels

namespace OAI

noncomputable section

namespace SharpRamseyFive.FiniteEntropy

section
open scoped Classical BigOperators
variable {B A T β κ : Type} [Fintype B] [Fintype A] [Fintype T] [Fintype β]
  [Fintype κ] [Nonempty A]
local instance uniformHistoryIndexDecEq : DecidableEq ((B × A) ⊕ T) := Classical.decEq _
local instance uniformHistorySubtypeDecEq (E : Finset ((B × A) ⊕ T)) : DecidableEq E := Classical.decEq _

theorem exists_uniform_pre_round (μ : Law κ)
    (p : κ→Law (((B×A)⊕T)→β)) (S : κ→B→Finset A)
    (n : ℕ) (hn : 0<n) (hS : ∀ c,0<μ c→∀ b,n+1≤(S c b).card) :
    ∃ i : Fin n, mean μ (fun c=>blockRoundMean blockAllInformation (p c) (S c) n i)≤
      2*mean μ (fun c=>totalCorrelation (p c))/n := by
  have hb : (∑ i : Fin n,mean μ (fun c=>blockRoundMean blockAllInformation (p c) (S c) n i))≤
      2*mean μ (fun c=>totalCorrelation (p c)) := by
    rw [←mean_sum,←mean_smul]
    exact mean_mono_pos μ (fun c hc=>block_information_telescope (p c) (S c) n (hS c hc))
  by_contra! hh
  have hs := Finset.sum_lt_sum_of_nonempty (s:=Finset.univ)
    (Finset.univ_nonempty_iff.mpr ⟨⟨0,hn⟩⟩) (fun i _=>hh i)
  have he : (∑ _i : Fin n,2*mean μ (fun c=>totalCorrelation (p c))/n)=
      2*mean μ (fun c=>totalCorrelation (p c)) := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hn0 : (n:ℝ)≠0 := Nat.cast_ne_zero.mpr hn.ne'
    field_simp
  rw [he] at hs
  exact (not_lt_of_ge hb) hs

def preRoundLaw (μ : Law κ) (p : κ→Law (((B×A)⊕T)→β))
    (S : κ→B→Finset A) (n : ℕ) : Law ((κ×BlockHistory B A T β n)×(B→A)) :=
  adaptiveLaw (adaptiveLaw μ (fun c=>historyLaw (p c) (S c) n))
    (fun z=>freshBlockLaw (historyUnused (S z.1) z.2))

lemma preRound_mean (μ : Law κ) (p : κ→Law (((B×A)⊕T)→β))
    (S : κ→B→Finset A) (n : ℕ)
    (J : Law (((B×A)⊕T)→β)→(B→Finset A)→(B→A)→ℝ) :
    mean (preRoundLaw μ p S n) (fun z=>J (historyPosterior (p z.1.1) z.1.2)
      (historyUnused (S z.1.1) z.1.2) z.2)=
      mean μ (fun c=>blockRoundMean J (p c) (S c) (n+1) (Fin.last n)) := by
  rw [preRoundLaw,mean_adaptive,mean_adaptive]
  apply mean_congr
  intro c
  exact (history_round_mean J (p c) (S c) n).symm

theorem exists_preRoundLaw_information (μ : Law κ)
    (p : κ→Law (((B×A)⊕T)→β)) (S : κ→B→Finset A)
    (n : ℕ) (hn : 0<n) (hS : ∀ c,0<μ c→∀ b,n+1≤(S c b).card) :
    ∃ i : Fin n, mean (preRoundLaw μ p S i.val)
      (fun z=>blockAllInformation (historyPosterior (p z.1.1) z.1.2)
        (historyUnused (S z.1.1) z.1.2) z.2)≤
      2*mean μ (fun c=>totalCorrelation (p c))/n := by
  obtain ⟨i,hi⟩:=exists_uniform_pre_round μ p S n hn hS
  refine ⟨i,?_⟩
  rw [preRound_mean]
  have he (c : κ) := blockRoundMean_total_irrel blockAllInformation (p c) (S c)
    (i.val+1) n (Fin.last i.val) i rfl
  simp_rw [he]
  exact hi

lemma preRoundLaw_deficit (μ : Law κ) (p : κ→Law (((B×A)⊕T)→β))
    (S : κ→B→Finset A) (J : ℝ) (D : κ→((B×A)⊕T)→Finset β)
    (hJ : ∀ c x,Real.log (D c x).card≤J) (hp : ∀ c,0<μ c→InDomains (p c) (D c))
    (hfix : ∀ c,0<μ c→FixedOutside (p c) (blockActive (S c)))
    (n : ℕ) (hS : ∀ c,0<μ c→∀ b,n+1≤(S c b).card) :
    mean (preRoundLaw μ p S n) (fun z=>blockAllDeficit J
      (historyPosterior (p z.1.1) z.1.2) (historyUnused (S z.1.1) z.1.2) z.2)≤
      mean μ (fun c=>activeDeficit (p c) (blockActive (S c)) J) := by
  rw [preRound_mean]
  exact mean_mono_pos μ (fun c hc=>block_round_deficit J (D c) (hJ c)
    (p c) (S c) (hp c hc) (hfix c hc) (n+1) (hS c hc) (Fin.last n))

omit [Fintype A] [Fintype T] [Nonempty A] in
lemma representativeSet_card (s : B→A) : (representativeSet (T:=T) s).card=Fintype.card B := by
  unfold representativeSet
  rw [Finset.card_image_of_injective]
  · exact Finset.card_univ
  · intro b c he
    exact congrArg Prod.fst (Sum.inl.inj he)

omit [Nonempty A] in
lemma blockHistory_card (n : ℕ) :
    Fintype.card (BlockHistory B A T β n)=
      (Fintype.card A^Fintype.card B * Fintype.card β^Fintype.card B)^n := by
  induction n with
  | zero => change Fintype.card Unit=_;simp
  | succ n ih =>
    change Fintype.card (Σ s : B→A,(representativeSet (T:=T) s→β)×BlockHistory B A T β n)=_
    simp only [Fintype.card_sigma,Fintype.card_prod,Fintype.card_fun,Fintype.card_coe,
      representativeSet_card,ih,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    rw [pow_succ]
    simp only [Nat.cast_id]
    ring

end

open scoped Classical BigOperators
variable {B A T β κ : Type} [Fintype B] [Fintype A] [Fintype T] [Fintype β]
  [Fintype κ] [Nonempty A]
local instance historyProducerIndexDecEq : DecidableEq ((B × A) ⊕ T) := Classical.decEq _
local instance historyProducerSubtypeDecEq (E : Finset ((B × A) ⊕ T)) : DecidableEq E := Classical.decEq _

omit [Fintype β] [Nonempty A] in
lemma history_unused_card (S : B→Finset A) (r n : ℕ)
    (hS : ∀ b,r+n≤(S b).card) (h : BlockHistory B A T β n) :
    ∀ b,r≤(historyUnused S h b).card := by
  induction n generalizing S with
  | zero => simpa only [historyUnused,Nat.add_zero] using hS
  | succ n ih =>
    apply ih (eraseBlock S h.1) _ h.2.2
    apply eraseBlock_card S h.1 (r+n)
    intro b
    have := hS b
    omega

omit [Nonempty A] in
lemma history_in_domains (p : Law (((B×A)⊕T)→β)) (D : ((B×A)⊕T)→Finset β)
    (hp : InDomains p D) (n : ℕ) (h : BlockHistory B A T β n) :
    InDomains (historyPosterior p h) D := by
  induction n generalizing p with
  | zero => exact hp
  | succ n ih => exact ih _ (hp.fiber _ _) h.2.2

lemma history_fixedOutside (p : Law (((B×A)⊕T)→β)) (S : B→Finset A)
    (hp : FixedOutside p (blockActive S)) (n : ℕ)
    (h : BlockHistory B A T β n) (hh : 0<historyLaw p S n h) :
    FixedOutside (historyPosterior p h) (blockActive (historyUnused S h)) := by
  induction n generalizing p S with
  | zero => exact hp
  | succ n ih =>
    have hpair : 0<adaptiveLaw (first (reveal p (representativeSet h.1)))
        (fun a=>historyLaw (fiber (reveal p (representativeSet h.1)) a)
          (eraseBlock S h.1) n) h.2 := by
      change 0<freshBlockLaw S h.1 * _ at hh
      exact (mul_pos_iff.mp hh).resolve_right (fun hn=>(freshBlockLaw S).nonneg h.1 |>.not_gt hn.1) |>.2
    have hc : 0<first (reveal p (representativeSet h.1)) h.2.1 ∧
        0<historyLaw (fiber (reveal p (representativeSet h.1)) h.2.1) (eraseBlock S h.1) n h.2.2 := by
      change 0<first (reveal p (representativeSet h.1)) h.2.1 * _ at hpair
      exact (mul_pos_iff.mp hpair).resolve_right (fun hn=>(first (reveal p (representativeSet h.1))).nonneg h.2.1 |>.not_gt hn.1)
    apply ih _ _ _ h.2.2 hc.2
    rw [blockActive_erase]
    exact hp.fiber _ _ hc.1

lemma mean_historyPosterior (p : Law (((B×A)⊕T)→β)) (S : B→Finset A)
    (n : ℕ) (f : (((B×A)⊕T)→β)→ℝ) :
    mean (historyLaw p S n) (fun h=>mean (historyPosterior p h) f)=mean p f := by
  change mean (historyLaw p S n) (fun h=>∑ x,historyPosterior p h x*f x)=_
  rw [mean_sum]
  unfold mean at ⊢
  apply Finset.sum_congr rfl
  intro x _
  have he := mean_smul (historyLaw p S n) (f x) (fun h=>historyPosterior p h x)
  rw [history_posterior_mean] at he
  simpa only [mean,mul_comm] using he

def preRoundTupleLaw (μ : Law κ) (p : κ→Law (((B×A)⊕T)→β))
    (S : κ→B→Finset A) (n : ℕ) :
    Law (((κ×BlockHistory B A T β n)×(B→A))×(((B×A)⊕T)→β)) :=
  adaptiveLaw (preRoundLaw μ p S n) (fun z=>historyPosterior (p z.1.1) z.1.2)

lemma preRoundTuple_context_tuple (μ : Law κ) (p : κ→Law (((B×A)⊕T)→β))
    (S : κ→B→Finset A) (n : ℕ) :
    map (preRoundTupleLaw μ p S n) (fun z=>(z.1.1.1,z.2))=adaptiveLaw μ p := by
  apply Law.ext_mean
  intro f
  rw [mean_map]
  simp only [preRoundTupleLaw,preRoundLaw,mean_adaptive]
  simp_rw [mean_const,mean_historyPosterior]

lemma preRoundTuple_fiber (μ : Law κ) (p : κ→Law (((B×A)⊕T)→β))
    (S : κ→B→Finset A) (n : ℕ) (z : (κ×BlockHistory B A T β n)×(B→A))
    (hz : 0<preRoundLaw μ p S n z) :
    fiber (preRoundTupleLaw μ p S n) z=historyPosterior (p z.1.1) z.1.2 :=
  fiber_adaptive _ _ _ hz

variable {Ω : Type} [Fintype Ω]

def historyObservationLaw (μ : Law κ) (p : κ→Law (((B×A)⊕T)→β))
    (S : κ→B→Finset A) (n : ℕ) :
    Law ((κ×(((B×A)⊕T)→β))×(BlockHistory B A T β n×(B→A))) :=
  map (preRoundTupleLaw μ p S n) (fun z=>((z.1.1.1,z.2),(z.1.1.2,z.1.2)))

lemma historyObservation_first (μ : Law κ) (p : κ→Law (((B×A)⊕T)→β))
    (S : κ→B→Finset A) (n : ℕ) :
    first (historyObservationLaw μ p S n)=adaptiveLaw μ p := by
  have hf {X Y : Type} [Fintype X] [Fintype Y] (r : Law (X×Y)) :
      first r=map r Prod.fst := by
    apply Law.ext
    funext x
    simp only [first,map,Fintype.sum_prod_type]
    rw [Finset.sum_comm]
    simp
  rw [hf,historyObservationLaw, map_comp]
  exact preRoundTuple_context_tuple μ p S n

def originalHistoryLaw (P : Law Ω) (context : Ω→κ) (tuple : Ω→((B×A)⊕T)→β)
    (S : κ→B→Finset A) (n : ℕ) : Law (Ω×(BlockHistory B A T β n×(B→A))) :=
  liftObserved P (fun ω=>(context ω,tuple ω))
    (historyObservationLaw (first (pair P context tuple)) (fiber (pair P context tuple)) S n)

lemma originalHistory_unchanged (P : Law Ω) (context : Ω→κ) (tuple : Ω→((B×A)⊕T)→β)
    (S : κ→B→Finset A) (n : ℕ) :
    map (originalHistoryLaw P context tuple S n) Prod.fst=P := liftObserved_original _ _ _

lemma originalHistory_joint (P : Law Ω) (context : Ω→κ) (tuple : Ω→((B×A)⊕T)→β)
    (S : κ→B→Finset A) (n : ℕ) :
    map (originalHistoryLaw P context tuple S n)
      (fun z=>(((context z.1,z.2.1),z.2.2),tuple z.1))=
      preRoundTupleLaw (first (pair P context tuple)) (fiber (pair P context tuple)) S n := by
  let q:=historyObservationLaw (first (pair P context tuple)) (fiber (pair P context tuple)) S n
  have hq : first q=map P (fun ω=>(context ω,tuple ω)) := by
    dsimp [q]
    rw [historyObservation_first,adaptive_reconstruct]
    rfl
  have he:=liftObserved_joint P (fun ω=>(context ω,tuple ω)) q hq
  have hm:=congrArg (fun r=>map r (fun z=>(((z.1.1,z.2.1),z.2.2),z.1.2))) he
  dsimp [q] at hm
  rw [map_comp,historyObservationLaw,map_comp] at hm
  change map (originalHistoryLaw P context tuple S n)
    (fun z=>(((context z.1,z.2.1),z.2.2),tuple z.1))=
      map (preRoundTupleLaw (first (pair P context tuple)) (fiber (pair P context tuple)) S n) id at hm
  rwa [map_id] at hm

end SharpRamseyFive.FiniteEntropy

end

end OAI
