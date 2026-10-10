import Mathlib
import OAI.Combinatorics.RamseyFive.Marking.ClassifiedStream
import OAI.Combinatorics.RamseyFive.Streams.SelectedLength
import OAI.Combinatorics.RamseyFive.Marking.HighChosenRound

namespace OAI

namespace SharpRamseyFive.SelectedTuple

section
open Module ProjectiveIncidence FiniteEntropy Windows Marking HighSamples
open scoped Classical BigOperators LinearAlgebra.Projectivization
noncomputable section
variable {K V Ω κ α : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))]
  [Nonempty (ℙ K V)] [Nonempty (ℙ K (Dual K V))]
  [Nonempty (ℙ K (Dual K (Dual K V)))] [Fintype Ω] [Fintype κ] [Fintype α]
  {N n : ℕ} [Nonempty (Fin n)] {admissible : (Fin N→α)→Prop}
local instance htpBDE : DecidableEq (Fin 1×Bool) := Classical.decEq _
local instance htpTDE : DecidableEq (Fin 1×Fin (2*n)) := Classical.decEq _
local instance htpIDE : DecidableEq (Slots 1 n) := Classical.decEq _

omit [Fintype (ℙ K (Dual K (Dual K V)))] [Nonempty (ℙ K V)]
  [Nonempty (ℙ K (Dual K V))] [Nonempty (ℙ K (Dual K (Dual K V)))] in
theorem high_three_prepared_impossible (hd : finrank K V=5)
    (S : SelectedStream (Ω:=Ω) (β:=FlagPair K V) N (1*(4*n)) admissible)
    (ctx : Ω→κ) (J B M : ℝ) (P : Prepared S ctx J B M)
    (hcap : ∀c,0 < map S.law ctx c→∀i,HighCaps (P.domain c i) 3 3)
    (rounds rem : ℕ) (hrounds : 0<rounds) (hrem : 0<rem)
    (hn : n≤2*rem) (hroom : rem+rounds≤n)
    (d s ε : ℝ) (hJ : 4*Real.log (Nat.card K)≤J) (hdp : 0<d) (hs : 2 ≤ s) (he : 0<ε)
    (hlog : Real.log 32+3*s<Real.log (Nat.card K))
    (hbad : highBadMass s d 153≤(1:ℝ)/4)
    (hvar : 64*(Nat.card K:ℝ)^5*(Real.exp s/(Nat.card K:ℝ)^3)*
      (Real.exp s/(Nat.card K:ℝ)^3)≤(1:ℝ)/4)
    (hsmall : 80004*ε<1/(8*(Nat.card K:ℝ)))
    (hbudget : 5*(B/d+(2*B/rounds+(16*n*M)/rem)/ε)<2*n) : False := by
  let μ:=first (pair S.law ctx (windowTuple S))
  let p:=fiber (pair S.law ctx (windowTuple S))
  let elig:=fun _ : κ=>fun _ : Fin 1×Bool=>(Finset.univ : Finset (Fin n))
  have hS : ∀c,0<μ c→∀b,rem+rounds≤(elig c b).card := by
    intro c hc b
    simpa only [elig,Finset.card_univ,Fintype.card_fin] using hroom
  have hD:=window_posterior_domains S ctx P.domain P.contains
  have hdef : mean μ (fun c=>activeDeficit (p c) (blockActive (elig c)) J)≤B := by
    dsimp only [μ,p,elig]
    rw [window_posterior_deficit]
    have h:=P.deficit
    simp only [Nat.cast_mul,Nat.cast_ofNat] at h
    have he : psFinDE (1*(4*n)) = (inferInstance : DecidableEq (Fin (1*(4*n)))) := Subsingleton.elim _ _
    rw [he] at h
    exact h
  obtain ⟨i,hi⟩:=exists_high_three_round hd μ p elig rounds rem hrounds hrem hS J d ε B s M
    hdp he (fun c i=>P.domain c (slotEmbedding i)) (fun c i=>P.cap c (slotEmbedding i)) hD
    (fun c _=>by simpa only [elig,blockActive_univ] using fixedOutside_univ (p c)) hdef hs hlog
    (window_posterior_incident S ctx P.incident) (window_posterior_occupancy S ctx M P.occupancy)
  apply high_three_domain_preRound_impossible (n:=i.val) (rem:=rem) hd μ p
    (fun c i=>P.domain c (slotEmbedding i)) hD
    (fun c hc i=>hcap c (by simpa only [μ,first_pair] using hc) (slotEmbedding i))
    (window_posterior_consistent S ctx P.consistent) elig hrem hn
    (fun c hc b=>by have:=hS c hc b;have:=i.isLt;omega)
    J d s ε hJ (by linarith) hbad hvar hsmall
  have hh:=mul_le_mul_of_nonneg_left hi (by norm_num : (0:ℝ)≤5)
  simp only [Nat.cast_one,one_mul,mul_one] at hh ⊢
  have heq : 4*(4*(n:ℝ))*M=16*n*M := by ring
  rw [heq] at hh
  exact hh.trans_lt hbudget
end
end

open Module ProjectiveIncidence FiniteEntropy Windows Marking Filter ParameterHierarchy
open scoped Classical BigOperators LinearAlgebra.Projectivization
noncomputable section

theorem eventually_high_three_prepared_impossible {η : ℝ} (hη : 0<η) (c Cb Cm : ℝ)
    (hc : 0<c) (hCb : 0≤Cb) (hCm : 0≤Cm) :
    ∀ᶠ σ : ℝ in atTop,∀ (K V Ω κ α : Type) [Field K] [AddCommGroup V] [Module K V]
      [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
      [Fintype (ℙ K (Dual K (Dual K V)))] [Nonempty (ℙ K V)] [Nonempty (ℙ K (Dual K V))]
      [Nonempty (ℙ K (Dual K (Dual K V)))] [Fintype Ω] [Fintype κ] [Fintype α],
    ∀ (N n : ℕ) [Nonempty (Fin n)] (admissible : (Fin N→α)→Prop)
      (S : SelectedStream (Ω:=Ω) (β:=FlagPair K V) N (1*(4*n)) admissible)
      (ctx : Ω→κ) (D J B M : ℝ) (P : Prepared S ctx J B M),
      finrank K V=5→1≤σ→Real.exp σ=Nat.card K→
      c*Real.exp σ*σ^(1+η)≤n→σ^beta η≤D→D≤σ^(1-η/2)→
      B≤Cb*n*D*σ^(-beta η)→M≤Cm*σ→4*σ≤J→
      (∀a,0 < map S.law ctx a→∀i,HighCaps (P.domain a i) 3 3)→False := by
  have ha : 3000*beta η<η/2 := by unfold beta;linarith
  have ha3 : 3*beta η<η/2 := by unfold beta;linarith
  filter_upwards [eventually_deletion_budget hη Cb (16*Cm) (2/c) (1/1000) hCb (by positivity) (by positivity) (by norm_num),
    eventually_high_four_loss hη (1/1000) (by norm_num),eventually_high_geometry hη,
    eventually_stage_scale hη 3000 (c/4) ha (by positivity),
    eventually_stage_scale hη 3 (1/8) ha3 (by norm_num),
    (tendsto_rpow_atTop (beta_pos hη)).eventually_ge_atTop 2,
    eventually_ge_atTop (8*(Real.log 32+1))] with σ hdel hfour hgeom hscale hsc3 ht hlog
  intro K V Ω κ α _ _ _ _ _ _ _ _ _ _ _ _ _ _ N n _ admissible S ctx D J B M P
    hd hσ hq hlen hD hDhi hB hM hJ hcap
  have hs : 0<σ := zero_lt_one.trans_le hσ
  have hqp : 2≤Nat.card K := Nat.succ_le_of_lt (Finite.one_lt_card (α:=K))
  have hqr : (2:ℝ)≤Nat.card K := by exact_mod_cast hqp
  have hqpos : (0:ℝ)<Nat.card K := by linarith
  have hDpos : 0<D := (Real.rpow_pos_of_pos hs _).trans_le hD
  have hσeq : Real.log (Nat.card K)=σ := by rw [←hq,Real.log_exp]
  let T:=⌊(Nat.card K:ℝ)*D*σ^(3000*beta η)⌋₊
  let rem:=n-T
  let h:=⌈(Nat.card K:ℝ)*σ^beta η⌉₊
  obtain ⟨hn,hT,hrem,hnrem,hroom,hTlo,hremlo,hhlo,hhhi⟩:=
    high_integer_ranges hη hσ hqr hc hD (by nlinarith [hscale D hDhi]) n (by simpa only [hq] using hlen)
  have hfour':=hfour D (Nat.card K) 3 h hD hDhi (by omega) hq (by norm_num) hhlo hhhi
  have hgeom':=hgeom D hDhi
  rw [hq] at hgeom'
  have hcol : 16*(n:ℝ)*M≤(16*Cm)*σ*n := by nlinarith [mul_le_mul_of_nonneg_left hM (by positivity : (0:ℝ)≤16*n)]
  have hbudget:=hdel (Nat.card K) D n B T rem (16*n*M) hqpos hDpos (Nat.cast_nonneg _) hB hTlo hremlo hcol
  have hε : 0<σ^(-2000*beta η)/(Nat.card K:ℝ) := by positivity
  have hbad : highBadMass (D*σ^(3*beta η)) (D*σ^beta η) 153≤(1:ℝ)/4 :=
    (highBadMass_le_highFourLoss (Nat.card K) 3 h (by omega) _ _ _ hε.le).trans
      (hfour'.trans (by norm_num))
  have hslo : 2≤D*σ^(3*beta η) := by
    have hh : 1≤σ^(3*beta η) := Real.one_le_rpow hσ (by have:=beta_pos hη;positivity)
    have h2 := ht.trans hD
    nlinarith
  apply high_three_prepared_impossible hd S ctx J B M P hcap T rem hT hrem hnrem hroom
    (D*σ^beta η) (D*σ^(3*beta η)) (σ^(-2000*beta η)/(Nat.card K:ℝ))
    (by simpa only [hσeq] using hJ) (by positivity) hslo hε
    (by rw [hσeq];have:=hsc3 D hDhi;linarith) hbad hgeom'.2.1 hgeom'.2.2
  have hnp : (0:ℝ)<n := by exact_mod_cast hn
  linarith

theorem eventually_no_high_class {η : ℝ} (hη : 0<η) (c C Cb Cm : ℝ)
    (hc : 0<c) (hCb : 0≤Cb) (hCm : 0≤Cm) :
    ∀ᶠ σ : ℝ in atTop,∀ (K V Ω κ α : Type) [Field K] [AddCommGroup V] [Module K V]
      [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
      [Fintype (ℙ K (Dual K (Dual K V)))] [Nonempty (ℙ K V)] [Nonempty (ℙ K (Dual K V))]
      [Nonempty (ℙ K (Dual K (Dual K V)))] [Fintype Ω] [Fintype κ] [Fintype α] [Nonempty α],
    ∀ (N n : ℕ) [Nonempty (Fin n)] (admissible : (Fin N→α)→Prop)
      (S : SelectedStream (Ω:=Ω) (β:=FlagPair K V) N (1*(4*n)) admissible)
      (ctx : Ω→κ) (D J B M width : ℝ) (P : Prepared S ctx J B M) (r s : Fin 5),
      finrank K V=5→1≤σ→Real.exp σ=Nat.card K→
      7*σ≤Real.log (Fintype.card α)→(N:ℝ)≤Real.exp (4*σ)*σ→
      c*Real.exp σ*σ^(1+η)≤n→S.density≤C→
      σ^beta η≤D→D≤σ^(1-η/2)→B≤Cb*n*D*σ^(-beta η)→M≤Cm*σ→4*σ≤J→
      (∀a,0 < map S.law ctx a→∀i,DomainClass width (P.domain a i) (.inr (.inr (r,s))))→False := by
  filter_upwards [eventually_high_prepared_impossible hη c C Cb hc hCb,
    eventually_high_three_prepared_impossible hη c Cb Cm hc hCb hCm] with σ hfour hthree
  intro K V Ω κ α _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ N n _ adm S ctx D J B M width P r s
    hd hσ hq hα hN hlen hC hD hDhi hB hM hJ hcl
  have hcap : ∀a,0 < map S.law ctx a→∀i,HighCaps (P.domain a i) r.val s.val :=
    fun a ha i=>(hcl a ha i).2
  obtain ⟨a,hap⟩:=(map S.law ctx).exists_positive
  have hn : 0<n := by have:=Fintype.card_pos (α:=Fin n);simpa using this
  have hsum:= (hcl a hap ⟨0,by omega⟩).1
  by_cases hr : r.val=4
  · apply hfour K V Ω κ α N n s.val adm S ctx D J B M P hd hσ hq hα hN hlen hC hD hDhi hB hJ
      (by omega) (by omega)
    simpa only [hr] using hcap
  · by_cases hs : s.val=4
    · let : Fintype (ℙ K (Dual K (Dual K (Dual K V)))) :=
        Fintype.ofEquiv (ℙ K (Dual K V)) bidualPoint
      let : Nonempty (ℙ K (Dual K (Dual K (Dual K V)))) :=
        ⟨bidualPoint (Classical.arbitrary (ℙ K (Dual K V)))⟩
      apply hfour K (Dual K V) Ω κ α N n r.val adm
        (S.changeOrientation swapFlag swapFlag.symm swapFlag.symm_apply_apply)
        ctx D J B M P.swap (by simpa using hd) hσ hq hα hN hlen hC hD hDhi hB hJ
        (by omega) (by omega)
      intro a ha i
      have hh:=(hcap a ha i.rev).swap
      simpa only [Prepared.swap,hs] using hh
    · have hr3 : r.val=3 := by omega
      have hs3 : s.val=3 := by omega
      apply hthree K V Ω κ α N n adm S ctx D J B M P hd hσ hq hlen hD hDhi hB hM hJ
      simpa only [hr3,hs3] using hcap
end

end SharpRamseyFive.SelectedTuple

end OAI
