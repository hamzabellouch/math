import Mathlib
import OAI.Combinatorics.SharpRamsey.Marking.SelectedStep
import OAI.Combinatorics.SharpRamsey.Marking.StageBudget

namespace OAI

section
namespace SharpLogRamsey.Marking
open Finset Real Filter Selection Selection.Windows ActualHighRank SourceScales
open scoped Classical BigOperators Topology
noncomputable section
local instance uniformFiniteDual {K : Type} [Field K] [Fintype K] {d : ℕ} : Finite (Module.Dual K (Fin (d+1)→K)) :=
  Finite.of_injective ((↑) : Module.Dual K (Fin (d+1)→K)→((Fin (d+1)→K)→K)) DFunLike.coe_injective
local instance uniformFiniteDouble {K : Type} [Field K] [Fintype K] {d : ℕ} : Finite (Module.Dual K (Module.Dual K (Fin (d+1)→K))) :=
  Finite.of_injective ((↑) : Module.Dual K (Module.Dual K (Fin (d+1)→K))→(Module.Dual K (Fin (d+1)→K)→K)) DFunLike.coe_injective
local instance uniformProjective {K : Type} [Field K] [Fintype K] {d : ℕ} : Fintype (Projectivization K (Fin (d+1)→K)) := Fintype.ofFinite _
local instance uniformDualProjective {K : Type} [Field K] [Fintype K] {d : ℕ} : Fintype (Projectivization K (Module.Dual K (Fin (d+1)→K))) := Fintype.ofFinite _
local instance uniformDoubleProjective {K : Type} [Field K] [Fintype K] {d : ℕ} : Fintype (Projectivization K (Module.Dual K (Module.Dual K (Fin (d+1)→K)))) := Fintype.ofFinite _

theorem eventually_uniform_step (i : ℕ) (η c C A B M0 : ℝ)
    (hη : 0 < η) (hηu : η ≤ 1) (hc : 0 < c) (hC : 0 < C)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hM0 : 0 ≤ M0) :
    ∀ᶠ σ : ℝ in atTop, ∀ (q : ℕ) [Fact q.Prime], 3 ≤ q → exp σ=(q:ℝ) →
    ∀ (Ω Γ : Type) [Fintype Ω] [Fintype Γ] (N k : ℕ) (p : Law Ω) (msg : Ω→Γ)
      (F : Ω→Fin N→ProjectivePair (K:=ZMod q) (V:=Fin (i+4)→ZMod q))
      (S : Γ→Fin N→Finset (ProjectivePair (K:=ZMod q) (V:=Fin (i+4)→ZMod q)))
      (Λ Δ J : ℝ) (R : ℕ),
      0 < k → 0 ≤ Λ → 0 ≤ Δ → (k:ℝ) ≤ (q:ℝ)*σ^(1+η) →
      c*(q:ℝ)*σ^(1+η) ≤ N → (N:ℝ) ≤ C*q*σ^(1+η) →
      Admissible σ η (stageD σ η k Λ Δ) R →
      entropy (p.map msg) ≤ Λ →
      (N:ℝ)*((i+3:ℕ):ℝ)*σ-A*N ≤ entropy (p.map F) →
      J-jointJ (ZMod q) (i+3) ≤ Δ+B →
      (∀ z j,log (S z j).card ≤ J) →
      (∀ x,p.mass x≠0→∀ j,F x j∈S (msg x) j) →
      (∀ x,p.mass x≠0→∀ j,Incidence.Incident (F x j).1 (F x j).2) →
      (∀ x,p.mass x≠0→ScanConsistent ((List.ofFn (F x)).map toScan)) →
      (∀ x,p.mass x≠0→∀ W : Submodule (ZMod q) (Fin (i+4)→ZMod q),
        ((univ.filter (fun j : Fin N=>covectorTuple (F x) j∈
          orthogonalRectangle Projectivization.rep Projectivization.rep W)).card:ℝ) ≤ M0*σ) →
      ∃ m' : ℕ, (N:ℝ)/(256*classCount i) ≤ m' ∧
        Nonempty (ContextOutput p F m' (stepPrefactor (i+3)*(q:ℝ)^(i+3)*exp (16*scaleKstar σ η (stageD σ η k Λ Δ)))
          (stageD σ η k Λ Δ*σ^(-η/3)*(N:ℝ)) (4*classCount i)) := by
  let K:=classCount i
  let Ecoef:=64*(((i+1:ℕ):ℝ)+4)^3
  let A1:=log 64+2*log (3*(((i+1:ℕ):ℝ)+4))+A+B
  let B1:=(1+Ecoef)/c+A1
  let C0:=max M0 (4*(K:ℝ)^2*B1)+1
  have hK : 0 < K:=classCount_pos i
  have hKr : (0:ℝ) < K:=by exact_mod_cast hK
  have hE : 0 ≤ Ecoef:=by dsimp only [Ecoef];positivity
  have hA1 : 0 ≤ A1:=by
    have hl : (1:ℝ) ≤ 3*(((i+1:ℕ):ℝ)+4):=by
      have : (0:ℝ) ≤ (i+1:ℕ):=by positivity
      nlinarith
    dsimp only [A1]
    linarith [log_nonneg hl,log_nonneg (by norm_num : (1:ℝ) ≤ 64)]
  have hB1 : 0 ≤ B1:=by dsimp only [B1];positivity
  have hC0 : 0 < C0:=by dsimp only [C0];linarith [le_max_left M0 (4*(K:ℝ)^2*B1)]
  have hMup : M0 ≤ C0:=by dsimp only [C0];linarith [le_max_left M0 (4*(K:ℝ)^2*B1)]
  have hCostup : 4*(K:ℝ)^2*B1 ≤ C0:=by dsimp only [C0];linarith [le_max_right M0 (4*(K:ℝ)^2*B1)]
  filter_upwards [eventually_selected_step i η (c/(4*K)) C C0 hη hηu (by positivity) hC hC0,
    eventually_class_packing η c Ecoef K hη hc hE hK,
    eventually_ge_atTop (1:ℝ)] with σ hstep hpack hσ
  intro q _ hq he Ω Γ _ _ N k p msg F S Λ Δ J R hk hΛ hΔ hkup hNlo hNhi had hmsg hF hJ hSJ hS hf hcon hocc
  have hσ0 : 0 < σ:=by linarith
  have hq0 : (0:ℝ) < q:=he ▸ exp_pos _
  have hlog : log (Nat.card (ZMod q):ℝ)=σ:=by rw [Nat.card_zmod,←he,log_exp]
  have hdim : Module.finrank (ZMod q) (Fin (i+4)→ZMod q)=(i+1)+3:=by simp
  let D:=stageD σ η k Λ Δ
  let Dn:=D*σ^(-beta η)
  have hDn : 0 ≤ Dn:=by dsimp only [Dn,D,stageD];positivity
  let m:=N/(2*K)
  obtain ⟨hm,hNm,hKm,hpacking,hmlo⟩:=hpack (q:ℝ) N he hNlo
  have hmhi : (m:ℝ) ≤ C*q*σ^(1+η):=
    (show (m:ℝ) ≤ N by exact_mod_cast Nat.div_le_self N (2*K)).trans hNhi
  have hx:=excessCost_linear hdim p msg F σ Λ Δ A B J hlog hσ hΔ hB hmsg hF hJ
  rw [Nat.card_zmod] at hx
  have hxb := stage_budget_bound hσ0 hk hΛ hΔ hq0 hc hA1 hE hkup hNlo
  have hcb := class_budget_scale hK hB1 hDn hNm (hx.trans hxb)
  have hcb' : excessCost p msg F J (jointJ (ZMod q) (i+3)) ≤
      C0*(m:ℝ)*D*σ^(-beta η)/(K:ℝ) := by
    apply hcb.trans
    calc
      _ = (4*(K:ℝ)^2*B1)*((m:ℝ)*Dn/(K:ℝ)):=by ring
      _ ≤ C0*((m:ℝ)*Dn/(K:ℝ)):=mul_le_mul_of_nonneg_right hCostup (by positivity)
      _ = _:=by dsimp only [Dn];ring
  have hpacking' : ((classCount i*m:ℕ):ℝ)+
      expensiveBudget (ZMod q) (Fin (i+4)→ZMod q)+
      expensiveBudget (ZMod q) (Module.Dual (ZMod q) (Fin (i+4)→ZMod q)) ≤ N := by
    have hh:=twoExpensive_linear hdim hlog hσ
    rw [Nat.card_zmod] at hh
    dsimp only [Ecoef] at hpacking
    linarith only [hh,hpacking]
  obtain ⟨m',hmret,⟨out⟩⟩:=hstep q hq he Ω Γ N m p msg F S D J R had hmlo hmhi
    hSJ hS hf hcon hpacking' hcb' (by
      intro x hx W
      exact (hocc x hx W).trans (mul_le_mul_of_nonneg_right hMup hσ0.le))
  refine ⟨m',?_,⟨out⟩⟩
  have hn : (N:ℝ) ≤ 4*K*m:=by exact_mod_cast hNm
  apply (div_le_iff₀ (show (0:ℝ) < 256*K by positivity)).mpr
  nlinarith only [hn,hmret]
end
end SharpLogRamsey.Marking

end

end OAI
