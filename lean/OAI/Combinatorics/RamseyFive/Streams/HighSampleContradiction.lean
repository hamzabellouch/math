import Mathlib
import OAI.Combinatorics.RamseyFive.Entropy.PreparedWindows
import OAI.Combinatorics.RamseyFive.Marking.HighDomainPreRound
import OAI.Combinatorics.RamseyFive.Iteration.HighWindowStage
import OAI.Combinatorics.RamseyFive.Entropy.HighEntropyNumerics
import OAI.Combinatorics.RamseyFive.Entropy.FlagAlphabetLogs

namespace OAI

namespace SharpRamseyFive.SelectedTuple

section
open Module ProjectiveIncidence FiniteEntropy Windows Marking HighSamples Filter ParameterHierarchy
open scoped Classical BigOperators LinearAlgebra.Projectivization
noncomputable section
local instance hscBDE : DecidableEq (Fin 1×Bool) := Classical.decEq _
local instance hscTDE (n : ℕ) : DecidableEq (Fin 1×Fin (2*n)) := Classical.decEq _
local instance hscIDE (n : ℕ) : DecidableEq (Slots 1 n) := Classical.decEq _

theorem eventually_high_sample_impossible {η : ℝ} (hη : 0<η) (c C : ℝ) (hc : 0<c) :
    ∀ᶠ σ : ℝ in atTop,∀ (K V Ω κ α : Type) [Field K] [AddCommGroup V] [Module K V]
      [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
      [Fintype (ℙ K (Dual K (Dual K V)))] [Fintype Ω] [Fintype κ] [Fintype α] [Nonempty α],
    ∀ (N n l steps r' h : ℕ) [Nonempty (Fin n)] (admissible : (Fin N→α)→Prop)
      (S : SelectedStream (Ω:=Ω) (β:=FlagPair K V) N (1*(4*n)) admissible)
      (ctx : Ω→κ) (elig : κ→Fin 1×Bool→Finset (Fin n)) (s : ℝ),
      finrank K V=5→1≤σ→Real.exp σ=Nat.card K→
      7*σ≤Real.log (Fintype.card α)→(N:ℝ)≤Real.exp (4*σ)*σ→l≤N→l<2*n→
      c*Real.exp σ*σ^(1+η)≤l→S.density≤C→(h:ℝ)≤2*Real.exp σ*σ^beta η→
      mean (adaptiveLaw (preRoundTupleLaw (first (pair S.law ctx (windowTuple S)))
        (fiber (pair S.law ctx (windowTuple S))) elig steps)
        (fun z=>highFourSampler (fiber (pair S.law ctx (windowTuple S))) r' s h z.1))
        (fun z=>((coveredPositions (fun t=>z.1.2 (Sum.inr (0,t))) (highDomain z.2))ᶜ.card:ℝ))≤
          ((2*n:ℝ)-l)/10→False := by
  filter_upwards [eventually_high_entropy_contradiction hη c ((10/9)*C) hc] with σ hnum
  intro K V Ω κ α _ _ _ _ _ _ _ _ _ _ _ _ N n l steps r' h _ admissible S ctx elig s
    hd hσ hq hα hN hlN hl hlen hC hh hloss
  obtain ⟨hE,hden,hent⟩:=highSampleStream_extract S ctx elig steps r' s h hd hl hloss
  let T:=highSampleStream S ctx elig steps r' s h
  let S':=(T.restrict _ hE).extract hl.le
    (fun z=>coveredPositions (T.tuple z) (highDomain z.2))
  have hlenpos : 0<(l:ℝ) := (by positivity : 0<c*Real.exp σ*σ^(1+η)).trans_le hlen
  have hl0 : 0<l := by exact_mod_cast hlenpos
  have hden' : S'.density≤(10/9)*C := hden.trans (mul_le_mul_of_nonneg_left hC (by norm_num))
  have hlo:=S'.flag_entropy_lower_fraction σ η c ((10/9)*C)
    (zero_lt_one.trans_le hσ) hc hden' hl0 hlN hα hN hlen
  have hhi : entropy (map S'.law S'.tuple)≤3*h*(8*σ+Real.log 4)+(l:ℝ)*(4*σ+Real.log 2) := by
    apply hent.trans
    exact add_le_add
      (mul_le_mul_of_nonneg_left (flagPair_log_card hd σ (zero_le_one.trans hσ) hq) (by positivity))
      (mul_le_mul_of_nonneg_left (point_log_card (K:=K) (V:=Dual K V)
        (by simpa using hd) σ (zero_le_one.trans hσ) hq) (by positivity))
  exact hnum (Real.exp σ) l h (entropy (map S'.law S'.tuple)) rfl hlen
    (Nat.cast_nonneg _) hh hlo hhi
end
end

open Module ProjectiveIncidence FiniteEntropy Windows Marking HighSamples
open scoped Classical BigOperators LinearAlgebra.Projectivization
noncomputable section
variable {K V Ω κ α : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))]
  [Nonempty (ℙ K V)] [Nonempty (ℙ K (Dual K V))]
  [Nonempty (ℙ K (Dual K (Dual K V)))] [Fintype Ω] [Fintype κ] [Fintype α]
  {N n : ℕ} [Nonempty (Fin n)] {admissible : (Fin N→α)→Prop}
local instance hprBDE : DecidableEq (Fin 1×Bool) := Classical.decEq _
local instance hprTDE : DecidableEq (Fin 1×Fin (2*n)) := Classical.decEq _
local instance hprIDE : DecidableEq (Slots 1 n) := Classical.decEq _

omit [Fintype (ℙ K (Dual K (Dual K V)))] [Nonempty (ℙ K V)]
  [Nonempty (ℙ K (Dual K V))] [Nonempty (ℙ K (Dual K (Dual K V)))] in
theorem high_prepared_round (hd : finrank K V=5)
    (S : SelectedStream (Ω:=Ω) (β:=FlagPair K V) N (1*(4*n)) admissible)
    (ctx : Ω→κ) (J B M : ℝ) (P : Prepared S ctx J B M)
    (r' : ℕ) (hr' : r'≤4)
    (hcap : ∀c,0 < map S.law ctx c→∀i,HighCaps (P.domain c i) 4 r')
    (rounds rem : ℕ) (hrounds : 0<rounds) (hrem : 0<rem)
    (hn : n≤2*rem) (hroom : rem+rounds≤n)
    (d s ε : ℝ) (hJ : 4*Real.log (Nat.card K)≤J) (hdp : 0<d) (hs : 0<s) (he : 0<ε)
    (hbad : highBadMass s d 153≤(1:ℝ)/4)
    (hsmall : 2*(Nat.card K:ℝ)^2*(2*Real.exp s/(Nat.card K:ℝ)^4)≤1/(20*(Nat.card K:ℝ)))
    (h : ℕ) :
    ∃i : Fin rounds,
      mean (adaptiveLaw (preRoundTupleLaw (first (pair S.law ctx (windowTuple S)))
        (fiber (pair S.law ctx (windowTuple S))) (fun _ _=>Finset.univ) i.val)
        (fun z=>highFourSampler (fiber (pair S.law ctx (windowTuple S))) r' s h z.1))
        (fun z=>((coveredPositions (fun t=>z.1.2 (Sum.inr (0,t))) (highDomain z.2))ᶜ.card:ℝ))≤
          5*(B/d+(2*B/rounds)/(ε))+(2*n:ℝ)*highFourLoss (Nat.card K) r' h s d ε := by
  let μ:=first (pair S.law ctx (windowTuple S))
  let p:=fiber (pair S.law ctx (windowTuple S))
  let elig:=fun _ : κ=>fun _ : Fin 1×Bool=>(Finset.univ : Finset (Fin n))
  have hS : ∀c,0<μ c→∀b,rem+rounds≤(elig c b).card := by
    intro c hc b
    simpa only [elig,Finset.card_univ,Fintype.card_fin] using hroom
  have hD:=window_posterior_domains S ctx P.domain P.contains
  have hbudget : mean μ (fun c=>activeDeficit (p c) (blockActive (elig c)) J)≤B := by
    dsimp only [μ,p,elig]
    rw [window_posterior_deficit]
    have h:=P.deficit
    simp only [Nat.cast_mul,Nat.cast_ofNat] at h
    have he : psFinDE (1*(4*n)) = (inferInstance : DecidableEq (Fin (1*(4*n)))) := Subsingleton.elim _ _
    rw [he] at h
    exact h
  obtain ⟨i,hi⟩:=exists_small_deletion_round μ p elig rounds rem hrounds hrem hS
    J d ε B 0 hdp he (fun c i=>P.domain c (slotEmbedding i))
    (fun c i=>P.cap c (slotEmbedding i)) hD
    (fun c _=>by simpa only [elig,blockActive_univ] using fixedOutside_univ (p c)) hbudget
    (fun _ _ _ _ _=>0) (by intros;exact le_rfl)
    (by intros;simp)
  refine ⟨i,?_⟩
  have hp:=high_domain_preRound_omissions (n:=i.val) (rem:=rem) hd μ p (fun c i=>P.domain c (slotEmbedding i))
    hD r' hr' (fun c hc i=>hcap c (by simpa only [μ,first_pair] using hc) (slotEmbedding i))
    (window_posterior_consistent S ctx P.consistent) (window_posterior_incident S ctx P.incident)
    elig hrem hn (fun c hc b=>by have:=hS c hc b;have:=i.isLt;omega)
    J d s ε hJ hs hdp.le he.le hbad hsmall
    (fun _ _ _ _=>0) (by intros;exact le_rfl) (by intros;rfl) h
  apply hp.trans
  exact add_le_add (mul_le_mul_of_nonneg_left
    (by simpa only [zero_div,add_zero] using hi) (by norm_num)) le_rfl
end

end SharpRamseyFive.SelectedTuple

end OAI
