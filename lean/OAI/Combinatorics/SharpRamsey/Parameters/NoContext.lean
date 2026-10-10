import Mathlib
import OAI.Combinatorics.SharpRamsey.Entropy.TerminalEntropy
import OAI.Combinatorics.SharpRamsey.Parameters.TerminalGain

namespace OAI

section
namespace SharpLogRamsey.Marking
open Finset Real Filter Selection Selection.Windows ActualHighRank SourceScales ActualPivot
open scoped Classical BigOperators Topology
noncomputable section
local instance noCtxFiniteDual {K : Type} [Field K] [Fintype K] {d : ℕ} : Finite (Module.Dual K (Fin (d+1)→K)) :=
  Finite.of_injective ((↑) : Module.Dual K (Fin (d+1)→K)→((Fin (d+1)→K)→K)) DFunLike.coe_injective
local instance noCtxFiniteDouble {K : Type} [Field K] [Fintype K] {d : ℕ} : Finite (Module.Dual K (Module.Dual K (Fin (d+1)→K))) :=
  Finite.of_injective ((↑) : Module.Dual K (Module.Dual K (Fin (d+1)→K))→(Module.Dual K (Fin (d+1)→K)→K)) DFunLike.coe_injective
local instance noCtxProjective {K : Type} [Field K] [Fintype K] {d : ℕ} : Fintype (Projectivization K (Fin (d+1)→K)) := Fintype.ofFinite _
local instance noCtxDualProjective {K : Type} [Field K] [Fintype K] {d : ℕ} : Fintype (Projectivization K (Module.Dual K (Fin (d+1)→K))) := Fintype.ofFinite _
local instance noCtxDoubleProjective {K : Type} [Field K] [Fintype K] {d : ℕ} : Fintype (Projectivization K (Module.Dual K (Module.Dual K (Fin (d+1)→K)))) := Fintype.ofFinite _

theorem eventually_no_small_context (i : ℕ) (η c Lstar P : ℝ)
    (hη : 0 < η) (hc : 0 < c) (hLs : 0 < Lstar) (hP : 1 ≤ P) :
    ∀ᶠ σ : ℝ in atTop, ∀ (q : ℕ) [Fact q.Prime], exp σ=(q:ℝ) →
    ∀ (Ω : Type) [Fintype Ω] (N k m : ℕ) (p : Law Ω)
      (stream : Ω→Fin N→Flag (ZMod q) (Fin (i+4)→ZMod q))
      (F : Ω→Fin k→Flag (ZMod q) (Fin (i+4)→ZMod q)),
      k ≤ N → (k:ℝ) ≤ (q:ℝ)*σ^(1+η) →
      (∀ g,(p.map stream).mass g ≤ 2/(Fintype.card (Flag (ZMod q) (Fin (i+4)→ZMod q)):ℝ)^N) →
      (∀ x,p.mass x≠0→Occurs (F x) (stream x) ∨ Occurs (reverseTuple (F x)) (stream x)) →
      (N:ℝ) ≤ (q:ℝ)^(i+3)*σ →
      (∀ x,p.mass x≠0→ScanConsistent ((List.ofFn (fun j=>flagPair (F x j))).map toScan)) →
      c*(q:ℝ)*σ^(1+η) ≤ m →
      ¬Nonempty (ContextOutput p (fun x j=>flagPair (F x j)) m
        (P*(q:ℝ)^(i+3)*exp (48*σ^(8*beta η))) k Lstar) := by
  let A:=1+|log c|+|log (2*(Lstar*2))|
  let B:=|log P|+|log 64|
  let E:=32*((i:ℝ)+5)^3
  let C:=log (3*((i:ℝ)+5))+log 64+1/c+1
  have hB : 0 ≤ B:=by dsimp [B];positivity
  have hE : 0 ≤ E:=by dsimp [E];positivity
  have hg : 1+8*beta η < 1+η:=by unfold beta;linarith
  filter_upwards [eventually_monomial_le_power (E*(48+B)) (1+8*beta η) (1+η) c hg hc,
    tendsto_log_atTop.eventually_gt_atTop ((A+C)/η),eventually_ge_atTop (1:ℝ)] with σ hsmall hlog hσ
  intro q _ he Ω _ N k m p stream F hkn hku hdom hsel hN hcons hmlo ⟨e⟩
  have hσ0 : 0 < σ:=by linarith
  have hq0 : (0:ℝ) < q:=he ▸ exp_pos _
  have hm0 : (0:ℝ) < m:=(by positivity : (0:ℝ) < c*(q:ℝ)*σ^(1+η)).trans_le hmlo
  have hgain:=flag_context_gain i q σ η c Lstar hσ hη.le hc hLs he Ω N k m p stream F
    _ k Lstar (le_refl _) hkn hdom hsel hN e hmlo
  have hu:=terminal_entropy_upper i q σ P (48*σ^(8*beta η)) k Lstar hσ hP (by positivity) he
    Ω k m p F hcons e
  have hp : 1 ≤ σ^(8*beta η):=one_le_rpow hσ (by have:=beta_pos hη;positivity)
  have hdelta : 48*σ^(8*beta η)+B ≤ (48+B)*σ^(8*beta η):=by nlinarith [mul_le_mul_of_nonneg_left hp hB]
  have herr : E*(q:ℝ)*σ*(48*σ^(8*beta η)+B) ≤ m:=by
    calc
      _ ≤ E*(q:ℝ)*σ*((48+B)*σ^(8*beta η)):=mul_le_mul_of_nonneg_left hdelta (by positivity)
      _ = (q:ℝ)*(E*(48+B)*σ^(1+8*beta η)):=by rw [rpow_add hσ0,rpow_one];ring
      _ ≤ (q:ℝ)*(c*σ^(1+η)):=mul_le_mul_of_nonneg_left hsmall hq0.le
      _ ≤ _:=by nlinarith only [hmlo]
  have hk : (k:ℝ) ≤ (m:ℝ)/c:=by apply (le_div_iff₀ hc).mpr;nlinarith only [mul_le_mul_of_nonneg_left hku hc.le,hmlo]
  have hgaineq : A+C < η*log σ:=(div_lt_iff₀ hη).mp hlog |>.trans_eq (mul_comm _ _)
  have hstrict:=mul_lt_mul_of_pos_left hgaineq hm0
  change (m:ℝ)*(((i+3:ℕ):ℝ)*σ+η*log σ)-A*m ≤ _ at hgain
  change entropy (e.μ.map (fun x j=>flagPair (F (e.source x) (e.chosen x j)))) ≤
    (k:ℝ)+(m:ℝ)*(((i+3:ℕ):ℝ)*σ+log (3*((i:ℝ)+5))+log 64)+
      E*(q:ℝ)*σ*(48*σ^(8*beta η)+B) at hu
  dsimp only [C] at hstrict
  have hk' : (k:ℝ) ≤ (m:ℝ)*(1/c):=by simpa [div_eq_mul_inv] using hk
  nlinarith only [hgain,hu,herr,hk',hstrict]
end
end SharpLogRamsey.Marking

end

end OAI
