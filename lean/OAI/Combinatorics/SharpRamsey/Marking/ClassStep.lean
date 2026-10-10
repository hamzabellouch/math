import Mathlib
import OAI.Combinatorics.SharpRamsey.Reciprocal.ReciprocalStep
import OAI.Combinatorics.SharpRamsey.Marking.HighRankStep

namespace OAI

section
namespace SharpLogRamsey.Marking
open Finset Real Filter Selection Selection.Windows ActualHighRank SourceScales
open scoped Classical BigOperators Topology
noncomputable section
local instance stepFiniteDual {K : Type} [Field K] [Fintype K] {d : ℕ} : Finite (Module.Dual K (Fin (d+1)→K)) :=
  Finite.of_injective ((↑) : Module.Dual K (Fin (d+1)→K)→((Fin (d+1)→K)→K)) DFunLike.coe_injective
local instance stepFiniteDouble {K : Type} [Field K] [Fintype K] {d : ℕ} : Finite (Module.Dual K (Module.Dual K (Fin (d+1)→K))) :=
  Finite.of_injective ((↑) : Module.Dual K (Module.Dual K (Fin (d+1)→K))→(Module.Dual K (Fin (d+1)→K)→K)) DFunLike.coe_injective
local instance stepProjective {K : Type} [Field K] [Fintype K] {d : ℕ} : Fintype (Projectivization K (Fin (d+1)→K)) := Fintype.ofFinite _
local instance stepDualProjective {K : Type} [Field K] [Fintype K] {d : ℕ} : Fintype (Projectivization K (Module.Dual K (Fin (d+1)→K))) := Fintype.ofFinite _
local instance stepDoubleProjective {K : Type} [Field K] [Fintype K] {d : ℕ} : Fintype (Projectivization K (Module.Dual K (Module.Dual K (Fin (d+1)→K)))) := Fintype.ofFinite _

def stepPrefactor (d : ℕ) : ℝ:=max 8000000 (highPrefactor d)

theorem eventually_class_step (i : ℕ) (η c C C0 : ℝ)
    (hη : 0 < η) (hηu : η ≤ 1) (hc : 0 < c) (hC : 0 < C) (hC0 : 0 < C0) :
    ∀ᶠ σ : ℝ in atTop, ∀ (q : ℕ) [Fact q.Prime], 3 ≤ q → exp σ=(q:ℝ) →
    ∀ (Ω Θ : Type) [Fintype Ω] [Fintype Θ] (m : ℕ) (p : Law Ω) (θ : Ω→Θ)
      (F : Ω→Fin m→ProjectivePair (K:=ZMod q) (V:=Fin (i+4)→ZMod q))
      (S : Θ→Fin m→Finset (ProjectivePair (K:=ZMod q) (V:=Fin (i+4)→ZMod q)))
      (D J M budget : ℝ) (R : ℕ) (cl : SlotClass (i+3)),
      Admissible σ η D R → c*(q:ℝ)*σ^(1+η) ≤ m → (m:ℝ) ≤ C*q*σ^(1+η) →
      ((i+3:ℕ):ℝ)*σ ≤ J → 0 ≤ M → M ≤ C0*σ →
      (∀ z j,log (S z j).card ≤ J) →
      (∀ x,p.mass x≠0→∀ j,F x j∈S (θ x) j) →
      (∀ x,p.mass x≠0→∀ j,Incidence.Incident (F x j).1 (F x j).2) →
      (∀ x,p.mass x≠0→ScanConsistent ((List.ofFn (F x)).map toScan)) →
      (∀ x,p.mass x≠0→∀ j,ValidSlotClass (i+3) (scaleKstar σ η D) (S (θ x) j) cl) →
      (∀ z j,((S z j).card:ℝ) ≤ 64*(q:ℝ)^(i+3)) →
      (∑ z,(p.map θ).mass z*((m:ℝ)*J-entropy ((p.cond θ z).map F))) ≤ budget →
      budget ≤ C0*(m:ℝ)*D*σ^(-beta η) →
      (∀ x,p.mass x≠0→∀ W : Submodule (ZMod q) (Fin (i+4)→ZMod q),
        ((univ.filter (fun j : Fin m=>covectorTuple (F x) j∈
          orthogonalRectangle Projectivization.rep Projectivization.rep W)).card:ℝ) ≤ M) →
      ∃ m' : ℕ, (m:ℝ)/64 ≤ m' ∧
        Nonempty (ContextOutput p F m' (stepPrefactor (i+3)*(q:ℝ)^(i+3)*exp (16*scaleKstar σ η D))
          (D*σ^(-η/3)*(m:ℝ)) 4) := by
  filter_upwards [eventually_reciprocal_step i η c C C0 hη hηu hc hC hC0,
    eventually_high_step η c C0 hη hc hC0 (i+3) (by omega)] with σ hrec hhigh
  intro q _ hq he Ω Θ _ _ m p θ F S D J M budget R cl had hmlo hmhi hJ hM hMup
    hSJ hS hf hcon hclass hsize hbudget hbud hocc
  cases cl with
  | inl cl =>
    obtain ⟨w,m',_,_,hm,⟨e⟩⟩:=hrec q hq he (Fin (i+4)→ZMod q)
      (by simp) Ω Θ m p θ F S D J M budget R cl.1 cl.2 had hmlo hmhi hJ hM hMup
      hSJ hS hf hcon hclass hsize hbudget hbud hocc
    refine ⟨m',by linarith [show (0:ℝ) ≤ m by positivity],⟨e.mono ?_ (le_refl _) (by norm_num)⟩⟩
    gcongr
    exact le_max_left _ _
  | inr cl =>
    obtain ⟨m',hm,⟨e⟩⟩:=hhigh q he Ω Θ m p θ F S D J budget R cl.1 cl.2 had hmlo
      hJ hSJ hS hf hcon hclass hsize hbudget hbud
    refine ⟨m',hm,⟨e.mono ?_ (le_refl _) (le_refl _)⟩⟩
    gcongr
    exact le_max_right _ _
end
end SharpLogRamsey.Marking

end

end OAI
