import Mathlib
import OAI.Combinatorics.RamseyFive.Iteration.PreparedDispatch
import OAI.Combinatorics.RamseyFive.Marking.ClassPrepared
import OAI.Combinatorics.RamseyFive.Entropy.MarkingNumerics
import OAI.Combinatorics.RamseyFive.Iteration.StageCuts
import OAI.Combinatorics.RamseyFive.Entropy.MarkingBudget

namespace OAI

namespace SharpRamseyFive.SelectedTuple
open Module ProjectiveIncidence FiniteEntropy Windows Marking Filter ParameterHierarchy
open scoped Classical BigOperators LinearAlgebra.Projectivization NNReal
noncomputable section
local instance acsFinDE (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

def markingStageConstant (c : ℝ) : ℝ:=(39*(19201+Real.log 800))/(c/200)
lemma markingStageConstant_nonneg {c : ℝ} (hc : 0<c) : 0 ≤ markingStageConstant c := by
  have hlog : 0≤Real.log 800 := Real.log_nonneg (by norm_num)
  unfold markingStageConstant
  positivity

theorem eventually_actual_compression {η : ℝ} (hη : 0<η) (hη' : η<1/10)
    (c d Cm : ℝ) (hc : 0<c) (hCm : 0≤Cm) :
    ∀ᶠ σ : ℝ in atTop,∀ (q₀ : ℕ) (K V α : Type) [Field K] [AddCommGroup V] [Module K V]
      [Finite K] [CharP K q₀] [FiniteDimensional K V]
      [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
      [Fintype (ℙ K (Dual K (Dual K V)))]
      [Nonempty (ℙ K V)] [Nonempty (ℙ K (Dual K V))] [Nonempty (ℙ K (Dual K (Dual K V)))]
      [Fintype α] [Nonempty α],
    ∀ (N n : ℕ) (adm : (Fin N→α)→Prop) (Λ Δ M k₀ D : ℝ)
      (_S : CodedStream (K:=K) (V:=V) N n adm d Λ (Real.log (153*(Nat.card K:ℝ)^4)+Δ) M),
      finrank K V=5→3≤Nat.card K→Nat.card K=q₀→1≤σ→Real.exp σ=Nat.card K→
      7*σ≤Real.log (Fintype.card α)→(N:ℝ)≤Real.exp (4*σ)*σ→
      c*(Nat.card K:ℝ)*σ^(1+η)≤n→(n:ℝ)≤k₀→k₀≤(Nat.card K:ℝ)*σ^(1+η)→
      (Nat.card K:ℝ)*σ^(1+η)≤2*k₀→0≤Λ→0≤Δ→0≤M→M≤Cm*σ→
      D=σ^beta η*(1+Λ/k₀+Δ*σ^(-η))→σ^beta η≤D→D≤σ^(1-η/2)→
      Nonempty (CodedStream (K:=K) (V:=V) N (n/20000) adm (44*d)
        (k₀*D*σ^(-η/3)) (Real.log (153*(Nat.card K:ℝ)^4)+domainSlackConstant*D*σ^(6*beta η)) M) ∨
      Nonempty (CodedStream (K:=K) (V:=Dual K V) N (n/20000) adm (44*d)
        (k₀*D*σ^(-η/3)) (Real.log (153*(Nat.card K:ℝ)^4)+domainSlackConstant*D*σ^(6*beta η)) M) := by
  filter_upwards [eventually_prepared_dispatch hη hη' (c/200) (markingStageConstant c) Cm (39*d)
      (by positivity) (markingStageConstant_nonneg hc) hCm,
    eventually_stream_cheap_entropy hη c d hc,eventually_marking_small hη c hc]
    with σ hstep hent hsmall
  intro q₀ K V α _ _ _ _ _ _ _ _ _ _ _ _ _ _ N n adm Λ Δ M k₀ D S
    hd hq3 hcard hσ hq hα hN hlen hn hk₀ hk₀lo hΛ hΔ hM hMhi hDeq hD hDhi
  have hs : 0<σ := zero_lt_one.trans_le hσ
  have hqpos : (0:ℝ)<Nat.card K := by rw [←hq];positivity
  have hkp : 0<k₀ := by have h:=mul_pos hqpos (Real.rpow_pos_of_pos hs (1+η));linarith
  have hDp : 0<D := (Real.rpow_pos_of_pos hs _).trans_le hD
  have hdpos : 0≤d := S.stream.density_nonneg.trans S.density_bound
  have hlen' : c*Real.exp σ*σ^(1+η)≤n := by rwa [hq]
  obtain ⟨hnlarge,hneglig⟩:=hsmall n hlen'
  obtain ⟨hm8,hmlo,hmhi,hlm,hlhi,hllo⟩:=stage_cuts n hnlarge
  let m:=n/100
  have hmlen : c/200*(Nat.card K:ℝ)*σ^(1+η)≤(m:ℝ) := by dsimp [m];nlinarith
  have hmle : m≤n := Nat.div_le_self _ _
  have hEmark:=expensiveBound_coarse (K:=K) (V:=V) hd σ hσ hq
  have hE : expensiveBound K V≤9600*(Nat.card K:ℝ)*σ := by rwa [hq] at hEmark
  have hsize : 39*(m:ℝ)+expensiveBound K V≤n := by dsimp [m];nlinarith
  have hJ : Real.log (153*(Nat.card K:ℝ)^4)=4*σ+Real.log 153 := by
    rw [Real.log_mul (by norm_num) (pow_pos hqpos _).ne',Real.log_pow,←hq,Real.log_exp]
    norm_num;ring
  have hcheap:=hent S.sample α (FlagPair K V) N n adm S.stream hσ hα hN hlen' S.density_bound
  rw [←hJ] at hcheap
  let B:=markingStageConstant c*(m:ℝ)*D*σ^(-beta η)
  have hB0 : 0≤B := by dsimp [B];exact mul_nonneg (mul_nonneg (mul_nonneg (markingStageConstant_nonneg hc) (Nat.cast_nonneg _)) hDp.le) (Real.rpow_nonneg hs.le _)
  have hbudget : 39*(Λ+n*Real.log 800+expensiveBound K V*Δ)≤B := by
    have hb:=marking_budget_bound hσ hqpos hkp hn hΛ hΔ hE hk₀lo hDeq
    apply hb.trans
    have hmK : (c/200)*k₀≤(m:ℝ) :=
      (mul_le_mul_of_nonneg_left hk₀ (by positivity)).trans (by nlinarith [hmlen])
    exact marking_budget_length hs.le hDp.le (by have:=Real.log_nonneg (show (1:ℝ)≤800 by norm_num);positivity)
      (by positivity) hmK (-beta η)
  obtain ⟨P⟩:=classify_coded hd (by positivity : 0≤D*σ^(3*beta η)) hΔ S hmle hsize (by convert hcheap using 1; congr 1; exact Subsingleton.elim _ _) hbudget
  have hout:=hstep q₀ K V P.sample P.context α N m (n/20000) adm P.stream P.ctx D B M k₀ P.prepared P.slotClass
    hd hq3 hcard hσ hq hα hN P.density_bound hm8 hD hDhi hmlen
    (by exact (by exact_mod_cast hmle : (m:ℝ)≤n).trans (hn.trans hk₀)) hlhi hk₀lo
    hB0 le_rfl hM hMhi P.classified
  have hden : (10/9)*P.stream.density≤44*d := by
    have hh:=P.density_bound
    linarith only [hh,hdpos]
  rcases hout with h|h
  · obtain ⟨out⟩:=h
    exact Or.inl ⟨out.mono hden le_rfl le_rfl⟩
  · obtain ⟨out⟩:=h
    exact Or.inr ⟨out.mono hden le_rfl le_rfl⟩
end
end SharpRamseyFive.SelectedTuple

end OAI
