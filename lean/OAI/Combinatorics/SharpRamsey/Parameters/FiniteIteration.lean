import Mathlib
import OAI.Combinatorics.SharpRamsey.Marking.TrackedStep
import OAI.Combinatorics.SharpRamsey.Parameters.NumericalIteration

namespace OAI

section
namespace SharpLogRamsey.Marking
open Finset Real Filter Selection Selection.Windows ActualHighRank SourceScales
open scoped Classical BigOperators Topology
noncomputable section
local instance finiteIterDual {K : Type} [Field K] [Fintype K] {d : ℕ} : Finite (Module.Dual K (Fin (d+1)→K)) :=
  Finite.of_injective ((↑) : Module.Dual K (Fin (d+1)→K)→((Fin (d+1)→K)→K)) DFunLike.coe_injective
local instance finiteIterDouble {K : Type} [Field K] [Fintype K] {d : ℕ} : Finite (Module.Dual K (Module.Dual K (Fin (d+1)→K))) :=
  Finite.of_injective ((↑) : Module.Dual K (Module.Dual K (Fin (d+1)→K))→(Module.Dual K (Fin (d+1)→K)→K)) DFunLike.coe_injective
local instance finiteIterProjective {K : Type} [Field K] [Fintype K] {d : ℕ} : Fintype (Projectivization K (Fin (d+1)→K)) := Fintype.ofFinite _
local instance finiteIterDualProjective {K : Type} [Field K] [Fintype K] {d : ℕ} : Fintype (Projectivization K (Module.Dual K (Fin (d+1)→K))) := Fintype.ofFinite _
local instance finiteIterDoubleProjective {K : Type} [Field K] [Fintype K] {d : ℕ} : Fintype (Projectivization K (Module.Dual K (Module.Dual K (Fin (d+1)→K)))) := Fintype.ofFinite _

lemma retained_length {r Q k m : ℝ} {n T : ℕ} (hr : 1 ≤ r) (hQ : 0 ≤ Q)
    (hn : n ≤ T) (hk : Q/2 ≤ k) (hm : k/r^n ≤ m) :
    ((1/2)/r^T)*Q ≤ m := by
  have hr0 : 0 < r:=by linarith
  calc
    _ = (Q/2)/r^T:=by ring
    _ ≤ (Q/2)/r^n:=div_le_div_of_nonneg_left (by positivity)
      (pow_pos hr0 _) (pow_le_pow_right₀ hr hn)
    _ ≤ k/r^n:=div_le_div_of_nonneg_right hk (by positivity)
    _ ≤ _:=hm

theorem eventually_iterated_context (i : ℕ) (η P M0 : ℝ)
    (hη : 0 < η) (hηu : η ≤ 1) (hP : 1 ≤ P)
    (hPs : stepPrefactor (i+3) ≤ P) (hM0 : 0 ≤ M0) :
    let T:=⌈8/η⌉₊+1
    let r:ℝ:=256*classCount i
    let Lstar:ℝ:=(4*classCount i)^T
    let c:ℝ:=(1/2)/r^T
    ∀ᶠ σ : ℝ in atTop, ∀ (q : ℕ) [Fact q.Prime], 3 ≤ q → exp σ=(q:ℝ) →
    ∀ (Ω : Type) [Fintype Ω] (N k : ℕ) (p : Law Ω)
      (stream : Ω→Fin N→Flag (ZMod q) (Fin (i+4)→ZMod q))
      (F : Ω→Fin k→Flag (ZMod q) (Fin (i+4)→ZMod q)),
      0 < k → k ≤ N → (k:ℝ) ≤ (q:ℝ)*σ^(1+η) → ((q:ℝ)*σ^(1+η))/2 ≤ k →
      (∀ g,(p.map stream).mass g ≤ 2/(Fintype.card (Flag (ZMod q) (Fin (i+4)→ZMod q)):ℝ)^N) →
      (∀ x,p.mass x≠0→Occurs (F x) (stream x) ∨ Occurs (reverseTuple (F x)) (stream x)) →
      (N:ℝ) ≤ (q:ℝ)^(i+3)*σ →
      (∀ x,p.mass x≠0→ScanConsistent ((List.ofFn (fun j=>flagPair (F x j))).map toScan)) →
      (∀ x,p.mass x≠0→∀ W : Submodule (ZMod q) (Fin (i+4)→ZMod q),
        ((univ.filter (fun j : Fin k=>(flagPair (F x j)).swap∈
          orthogonalRectangle Projectivization.rep Projectivization.rep W)).card:ℝ) ≤ M0*σ) →
      ContextOutput p (fun x j=>flagPair (F x j)) k
        (P*(q:ℝ)^(i+3)*exp (((i+2:ℕ):ℝ)*σ)) 0 1 →
      ∃ m : ℕ,c*(q:ℝ)*σ^(1+η) ≤ m ∧
        Nonempty (ContextOutput p (fun x j=>flagPair (F x j)) m
          (P*(q:ℝ)^(i+3)*exp (48*σ^(8*beta η))) k Lstar) := by
  intro T r Lstar c
  have hK : 0 < classCount i:=classCount_pos i
  have hr : 1 ≤ r:=by
    dsimp [r]
    have : (1:ℝ) ≤ classCount i:=by exact_mod_cast hK
    linarith
  have hr0 : 0 < r:=by linarith
  have hLone : (1:ℝ) ≤ 4*classCount i:=by
    have : (1:ℝ) ≤ classCount i:=by exact_mod_cast hK
    linarith
  have hLs : 0 < Lstar:=by dsimp [Lstar];positivity
  have hc : 0 < c:=by dsimp [c];positivity
  filter_upwards [eventually_tracked_step i η c Lstar P M0 hη hηu hc hLs hP hPs hM0,
    eventually_iteration_budgets (i+3) η hη hηu,eventually_ge_atTop (1:ℝ)] with σ hstep hbud hσ
  intro q _ hq he Ω _ N k p stream F hk hkn hku hklo hdom hselect hN hcon hocc e0
  obtain ⟨hdata,hΛlast,hΔlast⟩:=hbud k hk
  have hσ0 : 0 < σ:=by linarith
  have hq0 : (0:ℝ) < q:=he ▸ exp_pos _
  have hh : ∀ n ≤ T, ∃ m : ℕ,(k:ℝ)/r^n ≤ m ∧
      Nonempty (ContextOutput p (fun x j=>flagPair (F x j)) m
        (P*(q:ℝ)^(i+3)*exp (iterationBudgets (i+3) σ η k n).2)
        (iterationBudgets (i+3) σ η k n).1 ((4*classCount i)^n)) := by
    intro n
    induction n with
    | zero => intro _; exact ⟨k,by simp,by simpa only [iterationBudgets,pow_zero,show i+3-1=i+2 by omega] using Nonempty.intro e0⟩
    | succ n ih =>
      intro hn
      obtain ⟨m,hm,⟨e⟩⟩:=ih (by omega)
      have hml : c*(q:ℝ)*σ^(1+η) ≤ m:=by
        have hh:=retained_length hr (by positivity : 0 ≤ (q:ℝ)*σ^(1+η)) (by omega : n ≤ T) hklo hm
        simpa only [c,mul_assoc] using hh
      have hL : (0:ℝ) < (4*classCount i)^n:=by positivity
      have hLL : ((4*classCount i)^n:ℝ) ≤ Lstar:=pow_le_pow_right₀ hLone (by omega)
      obtain ⟨m',hm',⟨out⟩⟩:=hstep q hq he Ω N k m p stream F
        (iterationBudgets (i+3) σ η k n).1 (iterationBudgets (i+3) σ η k n).2
        ((4*classCount i)^n) (evenScale σ η) hk hkn hku (hdata n).1 (hdata n).2.1
        hL hLL (hdata n).2.2 hdom hselect hN hcon hocc e hml
      refine ⟨m',?_,?_⟩
      · calc
          (k:ℝ)/r^(n+1) = ((k:ℝ)/r^n)/r:=by rw [pow_succ,div_mul_eq_div_div]
          _ ≤ (m:ℝ)/r:=div_le_div_of_nonneg_right hm hr0.le
          _ ≤ _:=hm'
      · simpa only [iterationBudgets,pow_succ'] using Nonempty.intro out
  obtain ⟨m,hm,⟨e⟩⟩:=hh T le_rfl
  refine ⟨m,?_,⟨e.mono ?_ hΛlast (le_refl _)⟩⟩
  · have hh:=retained_length hr (by positivity : 0 ≤ (q:ℝ)*σ^(1+η)) (le_refl T) hklo hm
    simpa only [c,mul_assoc] using hh
  · exact mul_le_mul_of_nonneg_left (exp_le_exp.mpr hΔlast) (by positivity)
end
end SharpLogRamsey.Marking

end

end OAI
