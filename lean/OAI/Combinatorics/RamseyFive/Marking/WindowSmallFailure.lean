import Mathlib
import OAI.Combinatorics.RamseyFive.Marking.ReciprocalDomainCaps
import OAI.Combinatorics.RamseyFive.Marking.WindowTargetRetention
import OAI.Combinatorics.RamseyFive.Marking.ReciprocalNumerics

namespace OAI

namespace SharpRamseyFive.Marking

section
open Module FiniteEntropy ProjectiveIncidence Windows
open ReverseCap ScoreGeometry BinaryTree TreeCodec PivotTree Filter ParameterHierarchy
open scoped Classical BigOperators LinearAlgebra.Projectivization NNReal Topology
noncomputable section
local instance smallFailureBDE (w : ℕ) : DecidableEq (Fin w×Bool) := Classical.decEq _
local instance smallFailureIDE (w n : ℕ) : DecidableEq (Slots w n) := Classical.decEq _

theorem eventually_window_failure_small {η : ℝ} (hη : 0<η) (hη' : η<1/10)
    (Cb C₀ ρ : ℝ) (hCb : 0≤Cb) (hC : 0≤C₀) (hρ : 0<ρ) :
    ∀ᶠ σ : ℝ in atTop,∀ (D k J : ℝ) (R : ℕ) (L₀ : ℝ≥0),
    ∀ (q₀ : ℕ) (K V : Type) [Field K] [AddCommGroup V] [Module K V]
      [Finite K] [CharP K q₀] [FiniteDimensional K V]
      [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
      [Fintype (ℙ K (Dual K (Dual K V)))],
    ∀ (hd : finrank K V=5) (hq3 : 3≤Nat.card K) (w n H : ℕ) [Nonempty (Fin n)]
      (p : Law (Slots w n→FlagPair K V)) (u : Slots w n→ℝ)
      (sel : Fin w×Bool→Fin n) (E : Finset (Fin w))
      (W : ∀hE : E.Nonempty,ReciprocalWindows p u sel (survivingOriginal E hE) (D*σ^(2*beta η)))
      (hcons : ∀x,0<p x→∀i j,slotEmbedding i<slotEmbedding j→
        Incident (x i).1 (x j).2→Incident (x j).1 (x i).2)
      (hinc : ∀x,0<p x→∀i,Incident (x i).1 (x i).2)
      (hA : ∀i,((support (first (map p (fun x=>x i)))).card:ℝ)≤32*Real.exp (5*Real.log (Nat.card K)-u i))
      (hB : ∀i,((support (second (map p (fun x=>x i)))).card:ℝ)≤32*Real.exp (u i))
      (_hflag : ∀i,((support (map p (fun x=>x i))).card:ℝ)≤C₀*(Nat.card K:ℝ)^4)
      (_hJ : 4*Real.log (Nat.card K)≤J)
      (_hgood : ∀v∈E,indexBad J (D*σ^beta η) (σ^(-2000*beta η)/Real.exp σ) p
        (orderedCollision p (slotEquiv w n) u (D*σ^(2*beta η))) sel (earlySlot sel v)=0)
      (_hdrop : ∀v∈E,u (earlySlot sel v)-u (lateSlot sel v)≤k)
      (hσ : 1≤σ) (hq : Real.exp σ=Nat.card K),
      Nat.card K=q₀→Range η σ D R→(L₀:ℝ)=L η σ D→
      0≤k+2*(D*σ^(2*beta η))+Real.log 4→
      k+2*(D*σ^(2*beta η))+Real.log 4≤Cb*D*σ^(6*beta η)→
      w<2^H→(H:ℝ)≤σ^beta η→
      let f := fun C : PivotContext K V=>fourFinitePredictor hd σ C.1 C.2
        (P η σ D R) (σ^(-800*beta η)) R L₀
      let r := fun C : PivotContext K V=>fourFinitePredictor (K:=K) (V:=Dual K V)
        (by simpa using hd) σ C.2 (C.1.map bidualPoint.toEmbedding)
        (P η σ D R) (σ^(-800*beta η)) R L₀
      ∀ (v : Fin w) (_hv : v∈E) (t : Fin (2*n)),
      indexBad J (D*σ^beta η) (σ^(-2000*beta η)/Real.exp σ) p
        (orderedCollision p (slotEquiv w n) u (D*σ^(2*beta η))) sel (middleSlot v t)=0→
      allWindowFailure f r p u sel E W σ hσ hq hd.le
        (9/100000) (9/10) (σ^(-1000*beta η)) (P η σ D R) (by norm_num) v t≤ρ := by
  have hb : 0<beta η := by unfold beta;positivity
  filter_upwards [eventually_surviving_target_retention hη hη' Cb hCb,
    eventually_retention_error hb C₀ ρ hC hρ] with σ hret hnum
  intro D k J R L₀ q₀ K V _ _ _ _ _ _ _ _ _ hd hq3 w n H _ p u sel E W
    hcons hinc hA hB hflag hJ hgood hdrop hσ hq hcard hr hL hb0 hbhi hw hH
  dsimp only
  intro v hv t ht
  have hE : E.Nonempty := ⟨v,hv⟩
  have hD : σ^beta η≤D := hr.dlo
  have hDp : 0<D := (Real.rpow_pos_of_pos (zero_lt_one.trans_le hσ) _).trans_le hD
  rw [allWindowFailure_nonempty _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hE]
  have hh:=hret D k (D*σ^(2*beta η)) (D*σ^beta η) (σ^(-2000*beta η)/Real.exp σ)
    C₀ R L₀ q₀ K V hd hq3 w n p u sel E hE (W hE) hcons hinc hA hB hflag
    (fun v hv=>indexBad_of_larger_cap hJ _ _ _ _ (hgood v hv)) hdrop hσ hq hcard hr hL
    (by positivity) (by positivity) hb0 hbhi v hv t
    (indexBad_of_larger_cap hJ _ _ _ _ ht)
  have hheight0 : (finiteBalanced E.card).height≤H :=
    finiteBalanced_height H E.card (lt_of_le_of_lt (by simpa using Finset.card_le_univ E) hw)
  have hheight : ((finiteBalanced E.card).height:ℝ)≤σ^beta η := by
    have hh' : ((finiteBalanced E.card).height:ℝ)≤H := by exact_mod_cast hheight0
    exact hh'.trans hH
  have hn:=hnum D (finiteBalanced E.card).height hD (by positivity) hheight
  apply hh.trans
  simpa only [publicRetentionError,hq,add_assoc] using hn
end
end

open Module ProjectiveIncidence FiniteEntropy Windows
open ReverseCap ScoreGeometry BinaryTree TreeCodec PivotTree Filter ParameterHierarchy
open scoped Classical BigOperators LinearAlgebra.Projectivization NNReal Topology
noncomputable section
local instance arlBDE (w : ℕ) : DecidableEq (Fin w×Bool) := Classical.decEq _
local instance arlTDE (w n : ℕ) : DecidableEq (Fin w×Fin (2*n)) := Classical.decEq _
local instance arlIDE (w n : ℕ) : DecidableEq (Slots w n) := Classical.decEq _

attribute [local irreducible] actualWindows actualWindowSet

theorem eventually_actual_reciprocal_loss {η : ℝ} (hη : 0<η) (hη' : η<1/10)
    (Cb C₀ ρ : ℝ) (hCb : 0≤Cb) (hC : 0≤C₀) (hρ : 0<ρ) :
    ∀ᶠ σ : ℝ in atTop,∀ (D k J lo hi B : ℝ) (R : ℕ) (L₀ : ℝ≥0),
    ∀ (q₀ : ℕ) (K V κ : Type) [Field K] [AddCommGroup V] [Module K V]
      [Finite K] [CharP K q₀] [FiniteDimensional K V]
      [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
      [Fintype (ℙ K (Dual K (Dual K V)))] [Fintype κ],
    ∀ (hd : finrank K V=5) (hq3 : 3≤Nat.card K) (w n H steps rem : ℕ) [Nonempty (Fin n)]
      (μ : Law κ) (p : κ→Law (Slots w n→FlagPair K V))
      (elig : κ→(Fin w×Bool)→Finset (Fin n)) (u : κ→Slots w n→ℝ)
      (hcap : ∀a,0<μ a→ReciprocalCaps (p a) (u a) C₀)
      (hcons : ∀a,0<μ a→∀x,0<p a x→∀i j,slotEmbedding i<slotEmbedding j→
        Incident (x i).1 (x j).2→Incident (x j).1 (x i).2)
      (hu : ∀a,0<μ a→∀i,lo≤u a i ∧ u a i≤hi)
      (hlohi : lo≤hi) (hk : 0<k) (hJ : 4*Real.log (Nat.card K)≤J)
      (hσ : 1≤σ) (hq : Real.exp σ=Nat.card K)
      (hcard : Nat.card K=q₀) (hrange : Range η σ D R) (hL : (L₀:ℝ)=L η σ D)
      (hb0 : 0≤k+2*(D*σ^(2*beta η))+Real.log 4)
      (hbhi : k+2*(D*σ^(2*beta η))+Real.log 4≤Cb*D*σ^(6*beta η))
      (hw : w<2^H) (hH : (H:ℝ)≤σ^beta η)
      (hmass : reciprocalBadMass (D*σ^(2*beta η)) (D*σ^beta η) C₀≤1/2)
      (hsmall : 2*(D*σ^beta η+Real.log 32+Real.log 33+2*(Real.log (5*Real.log (Nat.card K)+1)+1))/(D*σ^(2*beta η))+
        2*Real.exp 1*reciprocalBadMass (D*σ^(2*beta η)) (D*σ^beta η) C₀≤1/2)
      (_hε : ((4*Real.exp 1)^2*80004)*(σ^(-2000*beta η)/Real.exp σ)≤1/(4*(Nat.card K:ℝ)))
      (_hrem : 0<rem) (_hn : n≤2*rem)
      (_hS : ∀a,0<μ a→∀b,rem+steps≤(elig a b).card)
      (_hbad : mean (preRoundLaw μ p elig steps) (fun z=>
        ∑j∈blockActive (historyUnused (elig z.1.1) z.1.2),
          preRoundBad μ p elig steps J (D*σ^beta η) (σ^(-2000*beta η)/Real.exp σ)
            (historyCollision p u (D*σ^(2*beta η))) z j)≤B),
      let s:=D*σ^(2*beta η)
      let d:=D*σ^beta η
      let ε:=σ^(-2000*beta η)/Real.exp σ
      let f := fun C : PivotContext K V=>fourFinitePredictor hd σ C.1 C.2
        (P η σ D R) (σ^(-800*beta η)) R L₀
      let r := fun C : PivotContext K V=>fourFinitePredictor (K:=K) (V:=Dual K V)
        (by simpa using hd) σ C.2 (C.1.map bidualPoint.toEmbedding)
        (P η σ D R) (σ^(-800*beta η)) R L₀
      let E:=actualWindowSet μ p u J d ε s k
      ∃ W : ∀z,∀hE : (E z).Nonempty,
        ReciprocalWindows (windowPosterior p z) (u z.1.1) z.2 (survivingOriginal (E z) hE) s,
      mean (preRoundLaw μ p elig steps) (fun h=>
        mean (allWindowExperiment f r (windowPosterior p h) (u h.1.1) h.2 (E h) (W h)) (fun z=>
          ((allWindowPositions f r (windowPosterior p h) (u h.1.1) h.2 (E h) (W h)
            σ hσ hq hd.le (9/100000) (9/10) (σ^(-1000*beta η)) (P η σ D R) (by norm_num)
            (preRoundBad μ p elig steps J d ε (historyCollision p u s) h)
            z.2.2 (z.1,z.2.1))ᶜ.card:ℝ)))≤
        5*B+(2*n:ℝ)*((hi-lo+2*(w:ℝ)*(2*s+Real.log 64))/k)+(w*(2*n):ℝ)*ρ := by
  filter_upwards [eventually_window_failure_small hη hη' Cb C₀ ρ hCb hC hρ] with σ hfail
  intro D k J lo hi B R L₀ q₀ K V κ _ _ _ _ _ _ _ _ _ _ hd hq3 w n H steps rem _
    μ p elig u hcap hcons hu hlohi hk hJ hσ hq hcard hrange hL hb0 hbhi hw hH hmass hsmall hε hrem hn hS hbad
  dsimp only
  have hD : 0<D := (Real.rpow_pos_of_pos (zero_lt_one.trans_le hσ) _).trans_le hrange.dlo
  have hs : 0<D*σ^(2*beta η) := by positivity
  let E:=actualWindowSet μ p u J (D*σ^beta η) (σ^(-2000*beta η)/Real.exp σ) (D*σ^(2*beta η)) k (steps:=steps)
  let W:=actualWindows hd μ p u J (D*σ^beta η) (σ^(-2000*beta η)/Real.exp σ)
    (D*σ^(2*beta η)) k C₀ hcap hs hJ hmass hsmall (steps:=steps)
  refine ⟨W,?_⟩
  have hdrop:=actualWindows_drop_mean (steps:=steps) hd μ p elig u J (D*σ^beta η) (σ^(-2000*beta η)/Real.exp σ)
    (D*σ^(2*beta η)) k C₀ lo hi hcap hs hJ hmass hsmall hcons hu hlohi
    (by positivity) hk hε
  apply (allHistory_window_loss _ _ μ p elig hrem hn hS (fun z=>u z.1.1)
    J (D*σ^beta η) (σ^(-2000*beta η)/Real.exp σ) (D*σ^(2*beta η)) k ρ hρ.le
    (historyCollision p u (D*σ^(2*beta η)))
    (fun z v=>u z.1.1 (earlySlot z.2 v)-u z.1.1 (lateSlot z.2 v)) E W
    (actualWindowSet_eq μ p elig u _ _ _ _ _)
    σ hσ hq hd.le (9/100000) (9/10) (σ^(-1000*beta η)) (P η σ D R) (by norm_num) ?_).trans
  · exact add_le_add (add_le_add (mul_le_mul_of_nonneg_left hbad (by norm_num))
      (mul_le_mul_of_nonneg_left hdrop (by positivity))) le_rfl
  · intro z hz v hv t ht
    have ha:=(preRound_positive μ p elig steps z hz).1
    have hcp:=(hcap z.1.1 ha).history _ _ _ steps z.1.2
    have he : E z=survivingWindowSet
        (preRoundBad μ p elig steps J (D*σ^beta η) (σ^(-2000*beta η)/Real.exp σ)
          (historyCollision p u (D*σ^(2*beta η))) z) z.2
        (fun v=>u z.1.1 (earlySlot z.2 v)-u z.1.1 (lateSlot z.2 v)) k :=
      actualWindowSet_eq μ p elig u _ _ _ _ _ z hz
    apply hfail D k J R L₀ q₀ K V hd hq3 w n H (windowPosterior p z) (u z.1.1) z.2
      (E z) (W z) (fun x hx=>hcons z.1.1 ha x (history_support (p z.1.1) steps z.1.2 x hx))
      hcp.incident hcp.first hcp.second hcp.flag hJ ?_ ?_ hσ hq hcard hrange hL hb0 hbhi hw hH v hv t ht
    · intro v hv
      rw [he] at hv
      exact (mem_goodWindowSet _ _ _).mp (Finset.mem_filter.mp hv).1 false
    · intro v hv
      rw [he] at hv
      exact (Finset.mem_filter.mp hv).2
end

end SharpRamseyFive.Marking

end OAI
