import Mathlib
import OAI.Combinatorics.RamseyFive.Streams.SelectedLength
import OAI.Combinatorics.RamseyFive.Entropy.DescriptionClean

namespace OAI

namespace SharpRamseyFive.Marking
open Module SharpRamseyFive.ProjectiveIncidence SharpRamseyFive.FiniteEntropy
open scoped Classical LinearAlgebra.Projectivization BigOperators
noncomputable section
local instance finalMarkingDecEq (N : ℕ) : DecidableEq (Fin N) := Classical.decEq _
variable {K V κ : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))]
  [Nonempty (ℙ K V)] [Nonempty (ℙ K (Dual K V))]
  [Nonempty (ℙ K (Dual K (Dual K V)))] [Fintype κ] {N : ℕ}

theorem final_marking_entropy (hdim : finrank K V=5)
    (p : Law (κ×(Fin N→FlagPair K V)))
    (hf : ∀ c x,0<p (c,x)→TupleIncident x)
    (hc : ∀ c x,0<p (c,x)→TupleConsistent x)
    (S : κ→Fin N→Finset (FlagPair K V)) (cap L : ℝ) (hcap : 1≤cap)
    (hS : ∀ c i,((S c i).card:ℝ)≤cap)
    (hsupp : ∀ c x,0<p (c,x)→∀ i,x i∈S c i)
    (hΔ : Real.log (153*(Nat.card K:ℝ)^4)≤Real.log cap)
    (hctx : entropy (first p)≤L) :
    entropy (second p)≤(N:ℝ)*Real.log (153*(Nat.card K:ℝ)^4)+L+(N:ℝ)*Real.log 800+
      (800*(Nat.card K:ℝ)*(Real.log (1+Fintype.card (ℙ K (Dual K V)))+
        Real.log (1+Fintype.card (ℙ K V))))*
      (Real.log cap-Real.log (153*(Nat.card K:ℝ)^4)) := by
  let J:=Real.log (153*(Nat.card K:ℝ)^4)
  have hd:=marking_expected_deficit hdim p hc S cap J ((N:ℝ)*J-entropy (second p)) L
    hcap hS hsupp (sub_nonneg.mpr hΔ) le_rfl hctx
  have hn : 0 ≤ mean (first (withMessage p markingMessage))
      (fun z=>activeDeficit (fiber (withMessage p markingMessage) z) (unspecified z.2) J) := by
    have hh:=mean_mono_pos (first (withMessage p markingMessage)) (f:=fun _=>0)
      (g:=fun z=>activeDeficit (fiber (withMessage p markingMessage) z) (unspecified z.2) J)
      (fun z hz=>marking_deficit_nonneg hdim p hf hc z.1 z.2 hz)
    simpa only [mean_const] using hh
  dsimp [J] at hd hn
  linarith

theorem final_marking_entropy_on_support (hdim : finrank K V=5)
    (p : Law (κ×(Fin N→FlagPair K V)))
    (hf : ∀ c x,0<p (c,x)→TupleIncident x)
    (hc : ∀ c x,0<p (c,x)→TupleConsistent x)
    (S : κ→Fin N→Finset (FlagPair K V)) (cap L : ℝ) (hcap : 1≤cap)
    (hS : ∀ c,0<first p c→∀ i,((S c i).card:ℝ)≤cap)
    (hsupp : ∀ c x,0<p (c,x)→∀ i,x i∈S c i)
    (hΔ : Real.log (153*(Nat.card K:ℝ)^4)≤Real.log cap)
    (hctx : entropy (first p)≤L) :
    entropy (second p)≤(N:ℝ)*Real.log (153*(Nat.card K:ℝ)^4)+L+(N:ℝ)*Real.log 800+
      (800*(Nat.card K:ℝ)*(Real.log (1+Fintype.card (ℙ K (Dual K V)))+
        Real.log (1+Fintype.card (ℙ K V))))*
      (Real.log cap-Real.log (153*(Nat.card K:ℝ)^4)) := by
  let D:=fun c i=>if 0<first p c then S c i else ∅
  apply final_marking_entropy hdim p hf hc D cap L hcap
  · intro c i
    dsimp [D]
    split_ifs with hp
    · exact hS c hp i
    · simpa using (le_trans (by norm_num : (0:ℝ)≤1) hcap)
  · intro c x hx i
    have hp : 0<first p c := (lt_of_lt_of_le hx (Finset.single_le_sum
      (fun y _=>p.nonneg (c,y)) (Finset.mem_univ x)))
    simpa only [D,ite_eq_left hp] using hsupp c x hx i
  · exact hΔ
  · exact hctx
end
end SharpRamseyFive.Marking

namespace SharpRamseyFive.SelectedTuple
open Module ProjectiveIncidence FiniteEntropy Windows Marking
open scoped Classical BigOperators LinearAlgebra.Projectivization
noncomputable section
local instance cfmFinDE (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
variable {K V α : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))]
  [Nonempty (ℙ K V)] [Nonempty (ℙ K (Dual K V))] [Nonempty (ℙ K (Dual K (Dual K V)))]
  [Fintype α] {N n : ℕ} {adm : (Fin N→α)→Prop} {d Λ Δ M : ℝ}
lemma CodedStream.final_entropy_bound (hd : finrank K V=5) (hΔ : 0≤Δ)
    (S : CodedStream (K:=K) (V:=V) N n adm d Λ (Real.log (153*(Nat.card K:ℝ)^4)+Δ) M) :
    entropy (map S.stream.law S.stream.tuple)≤n*Real.log (153*(Nat.card K:ℝ)^4)+Λ+
      n*Real.log 800+expensiveBound K V*Δ := by
  have hcheap : 0≤Real.log (153*(Nat.card K:ℝ)^4) := by
    apply Real.log_nonneg
    have hq : (1:ℝ)≤Nat.card K := by exact_mod_cast (Finite.one_lt_card (α:=K)).le
    have hh:=one_le_pow₀ (n:=4) hq
    linarith
  let p:=pair S.stream.law S.description.context S.stream.tuple
  have hp : ∀c x,0<p (c,x)→∃z,0<S.stream.law z ∧
      (S.description.context z,S.stream.tuple z)=(c,x) := by
    intro c x hx
    exact map_positive S.stream.law (fun z=>(S.description.context z,S.stream.tuple z)) (c,x) hx
  have h:=final_marking_entropy hd p
    (fun c x hx=>by obtain ⟨z,hz,he⟩:=hp c x hx;cases he;exact S.geometric.incident z hz)
    (fun c x hx=>by obtain ⟨z,hz,he⟩:=hp c x hx;cases he;exact S.geometric.consistent z hz)
    S.description.cleanDomain (Real.exp (Real.log (153*(Nat.card K:ℝ)^4)+Δ)) Λ
    (Real.one_le_exp_iff.mpr (add_nonneg hcheap hΔ)) S.description.clean_cap
    (fun c x hx=>by obtain ⟨z,hz,he⟩:=hp c x hx;cases he;exact S.description.clean_contains z hz)
    (by rw [Real.log_exp];linarith)
    (by simpa only [p,first_pair] using S.description.entropy_bound)
  simpa only [p,second_pair,Real.log_exp,add_sub_cancel_left,expensiveBound] using h
end
end SharpRamseyFive.SelectedTuple

namespace SharpRamseyFive.SelectedTuple
open FiniteEntropy Filter
open scoped Classical
noncomputable section

theorem eventually_stream_entropy_gain {η : ℝ} (hη : 0<η) (c C A : ℝ) (hc : 0<c) :
    ∀ᶠ σ : ℝ in atTop,∀ (Ω α β : Type) [Fintype Ω] [Fintype α] [Fintype β] [Nonempty α],
    ∀ (N n : ℕ) (adm : (Fin N→α)→Prop) (S : SelectedStream (Ω:=Ω) (β:=β) N n adm),
      1≤σ→7*σ≤Real.log (Fintype.card α)→(N:ℝ)≤Real.exp (4*σ)*σ→
      c*Real.exp σ*σ^(1+η)≤n→S.density≤C→
      (n:ℝ)*(4*σ+Real.log 153+A)≤entropy (map S.law S.tuple) := by
  have ht : Tendsto (fun σ : ℝ=>η*Real.log σ) atTop atTop :=
    Real.tendsto_log_atTop.const_mul_atTop hη
  have he : Tendsto (fun σ : ℝ=>c*Real.exp σ) atTop atTop :=
    Real.tendsto_exp_atTop.const_mul_atTop hc
  filter_upwards [ht.eventually_ge_atTop (Real.log 153+A+2-Real.log c),
    he.eventually_ge_atTop (Real.log (2*C))] with σ ht he
  intro Ω α β _ _ _ _ N n adm S hσ hα hN hlen hC
  have hs : 0<σ := zero_lt_one.trans_le hσ
  have hn : 0<n := by
    have hh : 0<(n:ℝ) := (by positivity : 0<c*Real.exp σ*σ^(1+η)).trans_le hlen
    exact_mod_cast hh
  have hlog : Real.log (2*C)≤n := by
    have hp : 1≤σ^(1+η) := Real.one_le_rpow hσ (by linarith)
    have hh:=mul_le_mul_of_nonneg_left hp (by positivity : (0:ℝ)≤c*Real.exp σ)
    nlinarith
  have hb:=S.flag_entropy_lower_fraction σ η c C hs hc hC hn S.length_le_source hα hN hlen
  have hh:=mul_le_mul_of_nonneg_right ht (Nat.cast_nonneg n)
  nlinarith
end
end SharpRamseyFive.SelectedTuple

end OAI
