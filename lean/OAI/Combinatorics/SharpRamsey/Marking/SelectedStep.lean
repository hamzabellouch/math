import Mathlib
import OAI.Combinatorics.SharpRamsey.Marking.ClassStep
import OAI.Combinatorics.SharpRamsey.Marking.ExcessCost

namespace OAI

section
namespace SharpLogRamsey.Marking
open Finset Real Filter Selection Selection.Windows ActualHighRank SourceScales
open scoped Classical BigOperators Topology
noncomputable section
local instance selectFiniteDual {K : Type} [Field K] [Fintype K] {d : ℕ} : Finite (Module.Dual K (Fin (d+1)→K)) :=
  Finite.of_injective ((↑) : Module.Dual K (Fin (d+1)→K)→((Fin (d+1)→K)→K)) DFunLike.coe_injective
local instance selectFiniteDouble {K : Type} [Field K] [Fintype K] {d : ℕ} : Finite (Module.Dual K (Module.Dual K (Fin (d+1)→K))) :=
  Finite.of_injective ((↑) : Module.Dual K (Module.Dual K (Fin (d+1)→K))→(Module.Dual K (Fin (d+1)→K)→K)) DFunLike.coe_injective
local instance selectProjective {K : Type} [Field K] [Fintype K] {d : ℕ} : Fintype (Projectivization K (Fin (d+1)→K)) := Fintype.ofFinite _
local instance selectDualProjective {K : Type} [Field K] [Fintype K] {d : ℕ} : Fintype (Projectivization K (Module.Dual K (Fin (d+1)→K))) := Fintype.ofFinite _
local instance selectDoubleProjective {K : Type} [Field K] [Fintype K] {d : ℕ} : Fintype (Projectivization K (Module.Dual K (Module.Dual K (Fin (d+1)→K)))) := Fintype.ofFinite _

def classCount (i : ℕ) : ℕ:=2*(i+4)+(i+4)^2
lemma classCount_pos (i : ℕ) : 0 < classCount i:=by unfold classCount;positivity

 theorem eventually_selected_step (i : ℕ) (η c C C0 : ℝ)
    (hη : 0 < η) (hηu : η ≤ 1) (hc : 0 < c) (hC : 0 < C) (hC0 : 0 < C0) :
    ∀ᶠ σ : ℝ in atTop, ∀ (q : ℕ) [Fact q.Prime], 3 ≤ q → exp σ=(q:ℝ) →
    ∀ (Ω Γ : Type) [Fintype Ω] [Fintype Γ] (N m : ℕ) (p : Law Ω) (Cmsg : Ω→Γ)
      (F : Ω→Fin N→ProjectivePair (K:=ZMod q) (V:=Fin (i+4)→ZMod q))
      (S : Γ→Fin N→Finset (ProjectivePair (K:=ZMod q) (V:=Fin (i+4)→ZMod q)))
      (D J : ℝ) (R : ℕ), Admissible σ η D R →
      c*(q:ℝ)*σ^(1+η) ≤ m → (m:ℝ) ≤ C*q*σ^(1+η) →
      (∀ z j,log (S z j).card ≤ J) →
      (∀ x,p.mass x≠0→∀ j,F x j∈S (Cmsg x) j) →
      (∀ x,p.mass x≠0→∀ j,Incidence.Incident (F x j).1 (F x j).2) →
      (∀ x,p.mass x≠0→ScanConsistent ((List.ofFn (F x)).map toScan)) →
      ((classCount i*m:ℕ):ℝ)+expensiveBudget (ZMod q) (Fin (i+4)→ZMod q)+
        expensiveBudget (ZMod q) (Module.Dual (ZMod q) (Fin (i+4)→ZMod q)) ≤ N →
      excessCost p Cmsg F J (jointJ (ZMod q) (i+3)) ≤
        (C0*(m:ℝ)*D*σ^(-beta η))/(classCount i:ℝ) →
      (∀ x,p.mass x≠0→∀ W : Submodule (ZMod q) (Fin (i+4)→ZMod q),
        ((univ.filter (fun j : Fin N=>covectorTuple (F x) j∈
          orthogonalRectangle Projectivization.rep Projectivization.rep W)).card:ℝ) ≤ C0*σ) →
      ∃ m' : ℕ, (m:ℝ)/64 ≤ m' ∧
        Nonempty (ContextOutput p F m' (stepPrefactor (i+3)*(q:ℝ)^(i+3)*exp (16*scaleKstar σ η D))
          (D*σ^(-η/3)*(N:ℝ)) (4*classCount i)) := by
  filter_upwards [eventually_class_step i η c C C0 hη hηu hc hC hC0,
    eventually_ge_atTop (1:ℝ)] with σ hstep hσ
  intro q _ hq he Ω Γ _ _ N m p Cmsg F S D J R had hmlo hmhi hSJ hS hf hcon hpack hexc hocc
  have hσ0 : 0 < σ:=lt_of_lt_of_le zero_lt_one hσ
  have hD : 0 ≤ D:=(rpow_nonneg hσ0.le _).trans had.D_lower
  have hdim : Module.finrank (ZMod q) (Fin (i+4)→ZMod q)=(i+1)+3:=by simp
  have hgap : 0 ≤ scaleKstar σ η D:=by unfold scaleKstar;positivity
  obtain ⟨cl,E,hE,T,hmn,hprob,hcard,hgcon,hgf,hG,hdef⟩:=
    actual_ordered_class hdim hgap p Cmsg F S J hcon hf hS hSJ m hpack
  let θ:=sourceMessage Cmsg F
  let p':=p.onContextEvent θ E hE
  let e:=chosenOrder T hmn
  let G:=orderedTuple T hmn θ F
  let S':=fun z j=>cheapBoth z (e z j)
  let J':=jointJ (ZMod q) (i+3)
  let budget:=excessCost p Cmsg F J J'/(p.map θ).event E
  have hK : (0:ℝ) < classCount i:=by exact_mod_cast classCount_pos i
  have hp : 1/(classCount i:ℝ) ≤ (p.map θ).event E:=hprob
  have hcost0 : 0 ≤ C0*(m:ℝ)*D*σ^(-beta η):=by positivity
  have hbudget : budget ≤ C0*(m:ℝ)*D*σ^(-beta η) := by
    apply (div_le_iff₀ hE).mpr
    calc
      _ ≤ (C0*(m:ℝ)*D*σ^(-beta η))/(classCount i:ℝ):=hexc
      _ = (C0*(m:ℝ)*D*σ^(-beta η))*(1/(classCount i:ℝ)):=by ring
      _ ≤ _:=mul_le_mul_of_nonneg_left hp hcost0
  have hocc' : ∀ x,p'.mass x≠0→∀ W : Submodule (ZMod q) (Fin (i+4)→ZMod q),
      ((univ.filter (fun j : Fin m=>covectorTuple (G x) j∈
        orthogonalRectangle Projectivization.rep Projectivization.rep W)).card:ℝ) ≤ C0*σ := by
    intro x hx W
    have hh:=count_injective_restriction (e (θ x)).toEmbedding
      (fun j=>covectorTuple (F x) j∈orthogonalRectangle Projectivization.rep Projectivization.rep W)
    apply le_trans _ (hocc x (p.onContextEvent_support θ E hE x hx).1 W)
    have heq : ∀ j,covectorTuple (G x) j=covectorTuple (F x) (e (θ x) j) := fun _=>rfl
    simp_rw [heq]
    convert (Nat.cast_le (α:=ℝ)).mpr hh using 1
    congr!
    congr 2
    ext index
    simp only [orthogonalRectangle,mem_filter,mem_univ,true_and]
  have hJ : ((i+3:ℕ):ℝ)*σ ≤ J':=by
    have hq0 : (0:ℝ) < q:=he ▸ exp_pos _
    dsimp only [J',jointJ]
    rw [Nat.card_zmod,log_mul (by norm_num) (pow_ne_zero _ hq0.ne'),log_pow,←he,log_exp]
    linarith [log_nonneg (by norm_num : (1:ℝ) ≤ 64)]
  obtain ⟨m',hmret,⟨out⟩⟩:=hstep q hq he Ω _ m p' θ G S' D J' (C0*σ) budget R cl
    had hmlo hmhi hJ (by positivity) le_rfl
    (fun z j=>cheapBoth_log_card hdim z (e z j)) (fun x hx j=>(hG x hx j).1)
    hgf hgcon (fun x hx j=>(hG x hx j).2)
    (fun z j=>by simpa only [Nat.card_zmod] using cheapBoth_card hdim z (e z j))
    hdef hbudget hocc'
  have hdom : ∀ x,p'.mass x ≤ (classCount i:ℝ)*p.mass x:=by
    intro x
    have hh:=p.onContextEvent_domination p θ E hE 1 (by intro x;simp) x
    apply hh.trans
    apply mul_le_mul_of_nonneg_right _ (p.nonneg x)
    apply (div_le_iff₀ hE).mpr
    have hh:=(div_le_iff₀ hK).mp hp
    linarith
  have out':=out.rebase p (by norm_num) hdom
  have full:=out'.transport (Equiv.refl _) F (fun x=>e (θ x)) (fun _ _=>rfl)
  refine ⟨m',hmret,⟨full.mono (le_refl _) ?_ (le_refl _)⟩⟩
  exact mul_le_mul_of_nonneg_left (by exact_mod_cast hmn) (by positivity)
end
end SharpLogRamsey.Marking

end

end OAI
