import Mathlib
import OAI.Combinatorics.SharpRamsey.Marking.TrackedStep

namespace OAI

section
namespace SharpLogRamsey.Marking
open Finset Real Filter Selection Selection.Windows ActualHighRank SourceScales ActualPivot
open scoped Classical BigOperators Topology
noncomputable section
local instance terminalFiniteDual {K : Type} [Field K] [Fintype K] {d : ℕ} : Finite (Module.Dual K (Fin (d+1)→K)) :=
  Finite.of_injective ((↑) : Module.Dual K (Fin (d+1)→K)→((Fin (d+1)→K)→K)) DFunLike.coe_injective
local instance terminalFiniteDouble {K : Type} [Field K] [Fintype K] {d : ℕ} : Finite (Module.Dual K (Module.Dual K (Fin (d+1)→K))) :=
  Finite.of_injective ((↑) : Module.Dual K (Module.Dual K (Fin (d+1)→K))→(Module.Dual K (Fin (d+1)→K)→K)) DFunLike.coe_injective
local instance terminalProjective {K : Type} [Field K] [Fintype K] {d : ℕ} : Fintype (Projectivization K (Fin (d+1)→K)) := Fintype.ofFinite _
local instance terminalDualProjective {K : Type} [Field K] [Fintype K] {d : ℕ} : Fintype (Projectivization K (Module.Dual K (Fin (d+1)→K))) := Fintype.ofFinite _
local instance terminalDoubleProjective {K : Type} [Field K] [Fintype K] {d : ℕ} : Fintype (Projectivization K (Module.Dual K (Module.Dual K (Fin (d+1)→K)))) := Fintype.ofFinite _

lemma terminal_entropy_upper (i q : ℕ) [Fact q.Prime] (σ P Δ Λ L : ℝ)
    (hσ : 1 ≤ σ) (hP : 1 ≤ P) (hΔ : 0 ≤ Δ) (he : exp σ=(q:ℝ))
    (Ω : Type) [Fintype Ω] (k m : ℕ) (p : Law Ω)
    (F : Ω→Fin k→Flag (ZMod q) (Fin (i+4)→ZMod q))
    (hcons : ∀ x,p.mass x≠0→ScanConsistent ((List.ofFn (fun j=>flagPair (F x j))).map toScan))
    (e : ContextOutput p (fun x j=>flagPair (F x j)) m (P*(q:ℝ)^(i+3)*exp Δ) Λ L) :
    entropy (e.μ.map (fun x j=>flagPair (F (e.source x) (e.chosen x j)))) ≤
      Λ+(m:ℝ)*(((i+3:ℕ):ℝ)*σ+log (3*((i:ℝ)+5))+log 64)+
        (32*((i:ℝ)+5)^3)*(q:ℝ)*σ*(Δ+(|log P|+|log 64|)) := by
  let G:=fun x j=>flagPair (F (e.source x) (e.chosen x j))
  let B:=|log P|+|log 64|
  let J:=jointJ (ZMod q) (i+3)
  have hB : 0 ≤ B:=by dsimp [B];positivity
  have hq0 : (0:ℝ) < q:=he ▸ exp_pos _
  have hlog : log (q:ℝ)=σ:=by rw [←he,log_exp]
  have hdim : Module.finrank (ZMod q) (Fin (i+4)→ZMod q)=(i+1)+3:=by simp
  obtain ⟨hJ0,hBJ,hJgap⟩:=tracked_log_budget i q σ Δ P (zero_le_one.trans hσ) hΔ hP he
  have hprev : ∀ z j,log (e.domains z j).card ≤ J+(Δ+B):=by
    intro z j
    have hh:=e.log_size hJ0 hBJ z j
    change _ ≤ jointJ (ZMod q) (i+3)+(Δ+B)
    linarith
  have hc : ∀ x,e.μ.mass x≠0→ScanConsistent ((List.ofFn (G x)).map toScan):=by
    intro x _
    exact scanConsistent_ordered _ (hcons _ (e.supported x)) (e.chosen x)
  have HH:=actual_entropy_upper hdim e.μ e.msg G e.domains (J+(Δ+B)) hc
    (fun x _ j=>(F (e.source x) (e.chosen x j)).incident) (fun x _ j=>e.hit x j) hprev
  have HE:=expected_expensive_bound e.μ G
  have hpoints:=projective_log_card_add_one
    (show Module.finrank (ZMod q) (Fin (i+4)→ZMod q)=(i+3)+1 by simp)
    (by simpa only [Nat.card_zmod,hlog] using hσ)
  rw [Nat.card_zmod,hlog] at hpoints
  have hExp : (32*(Module.finrank (ZMod q) (Fin (i+4)→ZMod q)+1)^2*(Nat.card (ZMod q):ℝ)*
      log (Fintype.card (Points (K:=ZMod q) (V:=Fin (i+4)→ZMod q))+1:ℝ)) ≤
      (32*((i:ℝ)+5)^3)*(q:ℝ)*σ:=by
    simp only [Points] at *
    have hh:=mul_le_mul_of_nonneg_left hpoints
      (by positivity : 0 ≤ 32*((i:ℝ)+5)^2*(q:ℝ))
    simp only [Module.finrank_pi,Fintype.card_fin,Nat.card_zmod]
    push_cast at hh ⊢
    nlinarith only [hh]
  have hj : J=log 64+((i+3:ℕ):ℝ)*σ:=by
    dsimp only [J,jointJ]
    rw [Nat.card_zmod,log_mul (by norm_num) (pow_ne_zero _ hq0.ne'),log_pow,hlog]
  have heterm:=mul_le_mul_of_nonneg_right (HE.trans hExp) (add_nonneg hΔ hB)
  have hcost:=e.cost
  change _ ≤ entropy (e.μ.map e.msg)+_+(m:ℝ)*J+_*(J+(Δ+B)-J) at HH
  rw [add_sub_cancel_left,hj] at HH
  simp only [Module.finrank_pi,Fintype.card_fin] at HH
  push_cast at HH
  have hMask : log (((i:ℝ)+4+1)*3)=log (3*((i:ℝ)+5)):=by congr 1;ring
  rw [hMask] at HH
  change entropy (e.μ.map G) ≤ _
  dsimp only [B] at heterm
  push_cast
  nlinarith only [HH,heterm,hcost]
end
end SharpLogRamsey.Marking

end

end OAI
