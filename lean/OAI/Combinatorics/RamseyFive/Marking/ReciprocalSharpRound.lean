import Mathlib
import OAI.Combinatorics.RamseyFive.Iteration.CodedWindowStage
import OAI.Combinatorics.RamseyFive.Entropy.AllWindowCost
import OAI.Combinatorics.RamseyFive.Marking.WindowSmallFailure
import OAI.Combinatorics.RamseyFive.Marking.WindowCodeDomains
import OAI.Combinatorics.RamseyFive.Entropy.PreparedWindows

namespace OAI

namespace SharpRamseyFive.SelectedTuple

section
open Module ProjectiveIncidence FiniteEntropy Windows Marking
open scoped Classical BigOperators LinearAlgebra.Projectivization
noncomputable section
variable {K V Ω κ α : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype Ω] [Fintype κ] [Fintype α]
  {N w n : ℕ} [Nonempty (Fin n)] {admissible : (Fin N→α)→Prop}
local instance rprBDE : DecidableEq (Fin w×Bool) := Classical.decEq _
local instance rprTDE : DecidableEq (Fin w×Fin (2*n)) := Classical.decEq _
local instance rprIDE : DecidableEq (Slots w n) := Classical.decEq _

theorem reciprocal_prepared_round_sharp (hd : finrank K V=5)
    (S : SelectedStream (Ω:=Ω) (β:=FlagPair K V) N (w*(4*n)) admissible)
    (ctx : Ω→κ) (J B M : ℝ) (P : Prepared S ctx J B M)
    (rounds rem : ℕ) (hrounds : 0<rounds) (hrem : 0<rem) (hroom : rem+rounds≤n)
    (d s ε width : ℝ) (hdp : 0<d) (hs : 2 ≤ s) (he : 0<ε) (_hM : 0≤M)
    (u : κ→Slots w n→ℝ) (b : Fin 7)
    (hband : ∀c,0 < map S.law ctx c→∀i,BandCondition (Real.log (Nat.card K)) width (u c i) b)
    (hsmall : Real.log 32+width+3*s<Real.log (Nat.card K))
    (hwide : Real.log 32+3*s<width) :
    ∃i : Fin rounds,mean (preRoundLaw (first (pair S.law ctx (windowTuple S)))
      (fiber (pair S.law ctx (windowTuple S))) (fun _ _=>Finset.univ) i.val) (fun z=>
      ∑j∈blockActive (historyUnused (fun _=>Finset.univ) z.1.2),
        preRoundBad (first (pair S.law ctx (windowTuple S)))
          (fiber (pair S.law ctx (windowTuple S))) (fun _ _=>Finset.univ) i.val J d ε
          (historyCollision (fiber (pair S.law ctx (windowTuple S))) u s) z j)≤
      B/d+(2*B/rounds+(if b.val%2=0 then (4*(w*(4*n):ℝ)*M)/rem else 0))/ε := by
  let μ:=first (pair S.law ctx (windowTuple S))
  let p:=fiber (pair S.law ctx (windowTuple S))
  let elig:=fun _ : κ=>fun _ : Fin w×Bool=>(Finset.univ : Finset (Fin n))
  have hS : ∀c,0<μ c→∀b,rem+rounds≤(elig c b).card := by
    intro c hc b
    simpa only [elig,Finset.card_univ,Fintype.card_fin] using hroom
  have hD:=window_posterior_domains S ctx P.domain P.contains
  have hdef:=P.window_deficit S ctx J B M
  have hfix : ∀c,0<μ c→FixedOutside (p c) (blockActive (elig c)) := by
    intro c hc
    simpa only [elig,blockActive_univ] using fixedOutside_univ (p c)
  have hband' : ∀c,0<μ c→∀i,BandCondition (Real.log (Nat.card K)) width (u c i) b := by
    intro c hc i
    exact hband c (by simpa only [μ,first_pair] using hc) i
  by_cases hb : b.val%2=0
  · simp only [ite_eq_left hb]
    exact exists_closed_reciprocal_round hd μ p elig rounds rem hrounds hrem hS J d ε B s width M
      hdp he (fun c i=>P.domain c (slotEmbedding i)) (fun c i=>P.cap c (slotEmbedding i)) hD hfix hdef
      u b hs hband' hb hsmall (window_posterior_incident S ctx P.incident)
      (window_posterior_occupancy S ctx M P.occupancy)
  · obtain ⟨i,hi⟩:=exists_open_reciprocal_round hd μ p elig rounds rem hrounds hrem hS J d ε B s width
      hdp he (fun c i=>P.domain c (slotEmbedding i)) (fun c i=>P.cap c (slotEmbedding i)) hD hfix hdef
      u b hs hband' hb hwide
    refine ⟨i,?_⟩
    simpa only [ite_eq_right hb,add_zero] using hi
end
end

open Module ProjectiveIncidence FiniteEntropy Windows Marking PivotTree MessageWeights ReverseCap ScoreGeometry
open ParameterHierarchy Filter
open scoped Classical BigOperators LinearAlgebra.Projectivization Topology NNReal
noncomputable section
local instance rpsBDE (w : ℕ) : DecidableEq (Fin w×Bool) := Classical.decEq _
local instance rpsTDE (w n : ℕ) : DecidableEq (Fin w×Fin (2*n)) := Classical.decEq _
local instance rpsIDE (w n : ℕ) : DecidableEq (Slots w n) := Classical.decEq _

theorem eventually_reciprocal_coded_stage {η : ℝ} (hη : 0<η) (hη' : η<1/10)
    (Cb C₀ ρ : ℝ) (hCb : 0≤Cb) (hC : 0≤C₀) (hρ : 0<ρ) :
    ∀ᶠ σ : ℝ in atTop,∀ (D k J lo hi B M width : ℝ) (R : ℕ) (L₀ : ℝ≥0),
    ∀ (q₀ : ℕ) (K V Ω κ α : Type) [Field K] [AddCommGroup V] [Module K V]
      [Finite K] [CharP K q₀] [FiniteDimensional K V]
      [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
      [Fintype (ℙ K (Dual K (Dual K V)))] [Fintype Ω] [Fintype κ] [Fintype α],
    ∀ (_hd : finrank K V=5) (_hq3 : 3≤Nat.card K) (N w n H rounds rem l : ℕ) [Nonempty (Fin n)]
      (admissible : (Fin N→α)→Prop)
      (S : SelectedStream (Ω:=Ω) (β:=FlagPair K V) N (w*(4*n)) admissible)
      (ctx : Ω→κ) (PS : Prepared S ctx J B M)
      (u : κ→Slots w n→ℝ) (b : Fin 7)
      (_hforward : ∀c,0<FiniteEntropy.map S.law ctx c→∀i,ForwardCaps (PS.domain c (slotEmbedding i)) (u c i))
      (_hflag : ∀c,0<FiniteEntropy.map S.law ctx c→∀i,((PS.domain c (slotEmbedding i)).card:ℝ)≤C₀*(Nat.card K:ℝ)^4)
      (_hu : ∀c,0<FiniteEntropy.map S.law ctx c→∀i,lo≤u c i ∧ u c i≤hi)
      (_hband : ∀c,0<FiniteEntropy.map S.law ctx c→∀i,BandCondition (Real.log (Nat.card K)) width (u c i) b)
      (_hlohi : lo≤hi) (_hk : 0<k) (_hJ : 4*Real.log (Nat.card K)≤J)
      (_hσ : 1≤σ) (_hq : Real.exp σ=Nat.card K),
      Nat.card K=q₀ → Range η σ D R → (L₀:ℝ)=L η σ D →
      0<rounds → 0<rem → n≤2*rem → rem+rounds≤n → l<w*(2*n) →
      0≤M → 2≤D*σ^(2*beta η) →
      Real.log 32+width+3*(D*σ^(2*beta η))<Real.log (Nat.card K) →
      Real.log 32+3*(D*σ^(2*beta η))<width →
      0≤k+2*(D*σ^(2*beta η))+Real.log 4 →
      k+2*(D*σ^(2*beta η))+Real.log 4≤Cb*D*σ^(6*beta η) →
      w<2^H → (H:ℝ)≤σ^beta η →
      reciprocalBadMass (D*σ^(2*beta η)) (D*σ^beta η) C₀≤1/2 →
      2*(D*σ^beta η+Real.log 32+Real.log 33+2*(Real.log (5*Real.log (Nat.card K)+1)+1))/(D*σ^(2*beta η))+
        2*Real.exp 1*reciprocalBadMass (D*σ^(2*beta η)) (D*σ^beta η) C₀≤1/2 →
      ((4*Real.exp 1)^2*80004)*(σ^(-2000*beta η)/Real.exp σ)≤1/(4*(Nat.card K:ℝ)) →
      5*(B/(D*σ^beta η)+(2*B/rounds+(if b.val%2=0 then (4*(w*(4*n):ℝ)*M)/rem else 0))/(σ^(-2000*beta η)/Real.exp σ))+
        (2*n:ℝ)*((hi-lo+2*(w:ℝ)*(2*(D*σ^(2*beta η))+Real.log 64))/k)+(w*(2*n):ℝ)*ρ≤
        ((w*(2*n):ℝ)-l)/10 →
      Nonempty (CodedStream (K:=K) (V:=V) N l admissible ((10/9)*S.density)
        (windowCodeBudget σ (Nat.card K) (P η σ D R) (k+2*(D*σ^(2*beta η))+Real.log 4) w H+
          (w+1)*Real.log (l+1)) (4*σ+codeDomainSlack k (D*σ^(2*beta η))) M) := by
  filter_upwards [eventually_actual_reciprocal_loss hη hη' Cb C₀ ρ hCb hC hρ,
    eventually_allWindow_cost hη hη' Cb hCb] with σ hloss hcost
  intro D k J lo hi B M width R L₀ q₀ K V Ω κ α _ _ _ _ _ _ _ _ _ _ _ _ hd hq3 N w n H rounds rem l _
    admissible S ctx PS u b hforward hflag hu hband hlohi hk hJ hσ hq hcard hrange hL
    hrounds hrem hn hroom hl hM hs hsmall hwide hb0 hbhi hw hH hmass hend hε hnum
  have hD : 0<D := (Real.rpow_pos_of_pos (zero_lt_one.trans_le hσ) _).trans_le hrange.dlo
  let f:=fun C : PivotContext K V=>fourFinitePredictor hd σ C.1 C.2
    (P η σ D R) (σ^(-800*beta η)) R L₀
  let r:=fun C : PivotContext K V=>fourFinitePredictor (K:=K) (V:=Dual K V)
    (by simpa using hd) σ C.2 (C.1.map bidualPoint.toEmbedding)
      (P η σ D R) (σ^(-800*beta η)) R L₀
  obtain ⟨i,hbad⟩:=reciprocal_prepared_round_sharp hd S ctx J B M PS rounds rem hrounds hrem hroom
    (D*σ^beta η) (D*σ^(2*beta η)) (σ^(-2000*beta η)/Real.exp σ) width
    (by positivity) hs (by positivity) hM u b hband hsmall hwide
  let μ:=first (pair S.law ctx (windowTuple S))
  let p:=fiber (pair S.law ctx (windowTuple S))
  let elig:=fun _ : κ=>fun _ : Fin w×Bool=>(Finset.univ : Finset (Fin n))
  have hh : ∀c,0<μ c→0<FiniteEntropy.map S.law ctx c := by intro c hc;simpa only [μ,first_pair] using hc
  have hcaps : ∀c,0<μ c→ReciprocalCaps (p c) (u c) C₀ := by
    intro c hc
    exact ReciprocalCaps.of_domains (p c) (fun j=>PS.domain c (slotEmbedding j)) (u c) C₀
      (window_posterior_domains S ctx PS.domain PS.contains c hc)
      (window_posterior_incident S ctx PS.incident c hc) (hforward c (hh c hc)) (hflag c (hh c hc))
  have hroom' : ∀c,0<μ c→∀b,rem+i.val≤(elig c b).card := by
    intro c hc b
    simpa only [elig,Finset.card_univ,Fintype.card_fin] using
      (Nat.add_le_add_left (Nat.le_of_lt i.isLt) rem).trans hroom
  obtain ⟨W,hW⟩:=hloss D k J lo hi _ R L₀ q₀ K V κ hd hq3 w n H i.val rem μ p elig u hcaps
    (window_posterior_consistent S ctx PS.consistent) (fun c hc=>hu c (hh c hc))
    hlohi hk hJ hσ hq hcard hrange hL hb0 hbhi hw hH hmass hend hε hrem hn hroom' hbad
  let E:=actualWindowSet μ p u J (D*σ^beta η) (σ^(-2000*beta η)/Real.exp σ) (D*σ^(2*beta η)) k (steps:=i.val)
  have hdrop : ∀h,∀v∈E h,u h.1.1 (earlySlot h.2 v)-u h.1.1 (lateSlot h.2 v)≤k := by
    intro h v hv
    dsimp only [E,actualWindowSet] at hv
    split_ifs at hv with hp
    · exact (Finset.mem_filter.mp hv).2
    · exact False.elim (Finset.notMem_empty v hv)
  apply actualWindow_coded S ctx elig i.val f r (fun h=>u h.1.1) E W σ hσ hq hd.le
    (9/100000) (9/10) (σ^(-1000*beta η)) (P η σ D R) (by norm_num) hl
    (preRoundBad μ p elig i.val J (D*σ^beta η) (σ^(-2000*beta η)/Real.exp σ)
      (historyCollision p u (D*σ^(2*beta η))))
    (windowCodeBudget σ (Nat.card K) (P η σ D R) (k+2*(D*σ^(2*beta η))+Real.log 4) w H)
    (4*σ+codeDomainSlack k (D*σ^(2*beta η))) M PS.geometric
  · intro C
    exact fourFinite_weight hd σ C.1 C.2 (P η σ D R) (σ^(-800*beta η)) R L₀
  · intro C
    exact fourFinite_weight (K:=K) (V:=Dual K V) (by simpa using hd) σ C.2 (C.1.map bidualPoint.toEmbedding) (P η σ D R) (σ^(-800*beta η)) R L₀
  · intro h v t
    exact hcost D k (D*σ^(2*beta η)) R L₀ q₀ K V hd w n H (windowPosterior p h) (u h.1.1)
      h.2 (E h) (W h) hσ hq hcard hrange hL hb0 hbhi (hdrop h) hw t v
  · intro h v t j
    exact allWindow_domain_log f r (windowPosterior p h) (u h.1.1) h.2 (E h) (W h)
      σ hσ hq hd k (σ^(-1000*beta η)) (P η σ D R) hb0 (hdrop h) t v j
  · exact hW.trans hnum
end

end SharpRamseyFive.SelectedTuple

end OAI
