import Mathlib
import OAI.Combinatorics.SharpRamsey.Parameters.FiniteIteration
import OAI.Combinatorics.SharpRamsey.Parameters.NoContext
import OAI.Combinatorics.SharpRamsey.Construction.InitialLaw

namespace OAI

section
namespace SharpLogRamsey.Marking
open Finset Real Filter Selection Selection.Windows ActualHighRank SourceScales
open scoped Classical BigOperators Topology
noncomputable section
local instance witnessFiniteDual {K : Type} [Field K] [Fintype K] {d : ℕ} : Finite (Module.Dual K (Fin (d+1)→K)) :=
  Finite.of_injective ((↑) : Module.Dual K (Fin (d+1)→K)→((Fin (d+1)→K)→K)) DFunLike.coe_injective
local instance witnessFiniteDouble {K : Type} [Field K] [Fintype K] {d : ℕ} : Finite (Module.Dual K (Module.Dual K (Fin (d+1)→K))) :=
  Finite.of_injective ((↑) : Module.Dual K (Module.Dual K (Fin (d+1)→K))→(Module.Dual K (Fin (d+1)→K)→K)) DFunLike.coe_injective
local instance witnessProjective {K : Type} [Field K] [Fintype K] {d : ℕ} : Fintype (Projectivization K (Fin (d+1)→K)) := Fintype.ofFinite _
local instance witnessDualProjective {K : Type} [Field K] [Fintype K] {d : ℕ} : Fintype (Projectivization K (Module.Dual K (Fin (d+1)→K))) := Fintype.ofFinite _
local instance witnessDoubleProjective {K : Type} [Field K] [Fintype K] {d : ℕ} : Fintype (Projectivization K (Module.Dual K (Module.Dual K (Fin (d+1)→K)))) := Fintype.ofFinite _

theorem eventually_graph_witness (i : ℕ) (η : ℝ) (hη : 0 < η) (hηu : η ≤ 1) :
    ∀ᶠ σ : ℝ in atTop, ∀ (q : ℕ) [Fact q.Prime], 3 ≤ q → exp σ=(q:ℝ) →
    ∀ N k : ℕ, 0 < k → k ≤ N → (k:ℝ) ≤ (q:ℝ)*σ^(1+η) →
      ((q:ℝ)*σ^(1+η))/2 ≤ k → (N:ℝ) ≤ (q:ℝ)^(i+3)*σ →
      ∃ G : SimpleGraph (Fin N),G.CliqueFree (i+4) ∧ G.indepNum < k := by
  let P:=max 4 (stepPrefactor (i+3))
  let T:=⌈8/η⌉₊+1
  let Lstar:ℝ:=(4*classCount i)^T
  let c:ℝ:=(1/2)/(256*classCount i)^T
  have hP4 : 4 ≤ P:=le_max_left _ _
  have hP1 : 1 ≤ P:=by linarith
  have hPs : stepPrefactor (i+3) ≤ P:=le_max_right _ _
  have hK : 0 < classCount i:=classCount_pos i
  have hLs : 0 < Lstar:=by dsimp [Lstar];positivity
  have hc : 0 < c:=by dsimp [c];positivity
  filter_upwards [eventually_iterated_context i η P (InitialExperiment.occupancyConstant i)
    hη hηu hP1 hPs (InitialExperiment.occupancyConstant_pos i).le,
    eventually_no_small_context i η c Lstar P hη hc hLs hP1] with σ hiter hnone
  intro q _ hq he N k hk hkn hku hklo hN
  by_contra! hbad
  have h : ∀ z : Fin N→Flag (ZMod q) (Fin (i+4)→ZMod q),
      k ≤ (flagGraph (ZMod q) (Fin (i+4)→ZMod q) z).indepNum:=by
    intro z
    exact hbad _ (prime_flagGraph_cliqueFree q (i+3) N z)
  have hlog : log (q:ℝ)=σ:=by rw [←he,log_exp]
  have hNlog : (N:ℝ) ≤ (q:ℝ)^(i+3)*log (q:ℝ):=by simpa only [hlog] using hN
  let Ω:=InitialExperiment.goodEvent i q N
  let p:=InitialExperiment.law i q N hNlog
  let stream : Ω→Fin N→Flag (ZMod q) (Fin (i+4)→ZMod q):=Subtype.val
  let F : Ω→Fin k→Flag (ZMod q) (Fin (i+4)→ZMod q):=InitialExperiment.tuple i q N k h
  have hdom : ∀ g,(p.map stream).mass g ≤ 2/(Fintype.card (Flag (ZMod q) (Fin (i+4)→ZMod q)):ℝ)^N:=
    InitialExperiment.law_dom i q N hNlog
  have hsel : ∀ x,p.mass x≠0→Occurs (F x) (stream x) ∨ Occurs (reverseTuple (F x)) (stream x):=by
    intro x _
    exact Or.inr (InitialExperiment.tuple_occurs i q N k h x)
  have hcon : ∀ x,p.mass x≠0→ScanConsistent ((List.ofFn (fun j=>flagPair (F x j))).map toScan):=by
    intro x _
    exact InitialExperiment.tuple_consistent i q N k h x
  have hocc : ∀ x,p.mass x≠0→∀ W : Submodule (ZMod q) (Fin (i+4)→ZMod q),
    ((univ.filter (fun j : Fin k=>(flagPair (F x j)).swap∈
      orthogonalRectangle Projectivization.rep Projectivization.rep W)).card:ℝ) ≤
        InitialExperiment.occupancyConstant i*σ:=by
    intro x _ W
    simpa only [hlog] using InitialExperiment.tuple_occupancy i q N k h x W
  let e0:=initial_context p F _ (InitialExperiment.alphabet_cap i q hP4 σ he)
  obtain ⟨m,hm,⟨e⟩⟩:=hiter q hq he Ω N k p stream F hk hkn hku hklo hdom hsel hN hcon hocc e0
  exact hnone q he Ω N k m p stream F hkn hku hdom hsel hN hcon hm ⟨e⟩
end
end SharpLogRamsey.Marking

end

end OAI
