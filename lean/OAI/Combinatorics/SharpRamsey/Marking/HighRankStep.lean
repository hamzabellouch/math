import Mathlib
import OAI.Combinatorics.SharpRamsey.Exposure.RestrictionGeometry
import OAI.Combinatorics.SharpRamsey.Execution.OutputRebase
import OAI.Combinatorics.SharpRamsey.Marking.HighRankChoices

namespace OAI

section
namespace SharpLogRamsey.Marking
open Finset Real Filter Selection Selection.Windows ActualHighRank SourceScales
open scoped Classical BigOperators Topology
noncomputable section
local instance flat_ActualHighRankStep_1 {K : Type} [Field K] [Fintype K] {d : ℕ} : Finite (Module.Dual K (Fin (d+1)→K)) :=
  Finite.of_injective ((↑) : Module.Dual K (Fin (d+1)→K)→((Fin (d+1)→K)→K)) DFunLike.coe_injective
local instance flat_ActualHighRankStep_2 {K : Type} [Field K] [Fintype K] {d : ℕ} : Finite (Module.Dual K (Module.Dual K (Fin (d+1)→K))) :=
  Finite.of_injective ((↑) : Module.Dual K (Module.Dual K (Fin (d+1)→K))→(Module.Dual K (Fin (d+1)→K)→K)) DFunLike.coe_injective
local instance flat_ActualHighRankStep_3 {K : Type} [Field K] [Fintype K] {d : ℕ} : Fintype (Projectivization K (Fin (d+1)→K)) := Fintype.ofFinite _
local instance flat_ActualHighRankStep_4 {K : Type} [Field K] [Fintype K] {d : ℕ} : Fintype (Projectivization K (Module.Dual K (Fin (d+1)→K))) := Fintype.ofFinite _
local instance flat_ActualHighRankStep_5 {K : Type} [Field K] [Fintype K] {d : ℕ} : Fintype (Projectivization K (Module.Dual K (Module.Dual K (Fin (d+1)→K)))) := Fintype.ofFinite _

theorem eventually_high_step (η c C0 : ℝ) (hη : 0 < η) (hc : 0 < c) (hC0 : 0 < C0)
    (d : ℕ) (hd : 2 ≤ d) :
    ∀ᶠ σ : ℝ in atTop, ∀ (q : ℕ) [Fact q.Prime], exp σ=(q:ℝ) →
    ∀ (Ω Θ : Type) [Fintype Ω] [Fintype Θ] (m : ℕ) (p : Law Ω) (θ : Ω→Θ)
      (F : Ω→Fin m→ProjectivePair (K:=ZMod q) (V:=Fin (d+1)→ZMod q))
      (S : Θ→Fin m→Finset (ProjectivePair (K:=ZMod q) (V:=Fin (d+1)→ZMod q)))
      (D J budget : ℝ) (R : ℕ) (r r' : Fin (d+1)),
      Admissible σ η D R → c*(q:ℝ)*σ^(1+η) ≤ m → (d:ℝ)*σ ≤ J →
      (∀ z j,log (S z j).card ≤ J) →
      (∀ x,p.mass x≠0→∀ j,F x j∈S (θ x) j) →
      (∀ x,p.mass x≠0→∀ j,Incidence.Incident (F x j).1 (F x j).2) →
      (∀ x,p.mass x≠0→ScanConsistent ((List.ofFn (F x)).map toScan)) →
      (∀ x,p.mass x≠0→∀ j,ValidSlotClass d (scaleKstar σ η D) (S (θ x) j) (.inr (r,r'))) →
      (∀ z j,((S z j).card:ℝ) ≤ 64*(q:ℝ)^d) →
      (∑ z,(p.map θ).mass z*((m:ℝ)*J-entropy ((p.cond θ z).map F))) ≤ budget →
      budget ≤ C0*(m:ℝ)*D*σ^(-beta η) →
      ∃ m' : ℕ, (m:ℝ)/64 ≤ m' ∧
        Nonempty (ContextOutput p F m' (highPrefactor d*(q:ℝ)^d*exp (16*scaleKstar σ η D))
          (D*σ^(-η/3)*(m:ℝ)) 4) := by
  filter_upwards [eventually_high_window η c hη hc,
    eventually_high_cost η c d hη hc,eventually_high_domain η d hη,
    eventually_high_ordered hη d hd (8*C0) (1/2) (by positivity) (by norm_num),
    eventually_ge_atTop (1:ℝ)] with σ hwin hcost hdom hout hσ
  intro q _ he Ω Θ _ _ m p θ F S D J budget R r r' had hmlo hJ hSJ hS hf hcon hclass hsize hbudget hb
  have hσ0 : 0 < σ:=by linarith
  have hD : 1 ≤ D:=(one_le_rpow hσ (beta_pos hη).le).trans had.D_lower
  have hqlog : log (Nat.card (ZMod q):ℝ)=σ:=by rw [Nat.card_zmod,←he,log_exp]
  let n:=m/8
  let k:=⌊(q:ℝ)*D*σ^(3000*beta η)⌋₊
  obtain ⟨hn,hk,hkn,hwm,hmup,hmret,hklow⟩:=hwin (q:ℝ) D m he had.D_lower had.D_upper hmlo
  let T : Θ→Finset (Fin m):=fun _=>prefixSet hwm
  let e:=chosenOrder T hwm
  let G:=orderedTuple T hwm θ F
  let S':=fun z j=>S z (e z j)
  have hGS : ∀ z j,log (S' z j).card ≤ J:=fun z j=>hSJ z (e z j)
  have hG : ∀ x,p.mass x≠0→∀ j,G x j∈S' (θ x) j:=fun x hx j=>hS x hx (e (θ x) j)
  have hgf : ∀ x,p.mass x≠0→∀ j,Incidence.Incident (G x j).1 (G x j).2:=
    fun x hx j=>hf x hx (e (θ x) j)
  have hgcon : ∀ x,p.mass x≠0→ScanConsistent ((List.ofFn (G x)).map toScan):=
    fun x hx=>scanConsistent_ordered (F x) (hcon x hx) (e (θ x))
  have hgclass : ∀ x,p.mass x≠0→∀ j,ValidSlotClass d (scaleKstar σ η D) (S' (θ x) j)
      (.inr (r,r')):=fun x hx j=>hclass x hx (e (θ x) j)
  have hgsize : ∀ z j,((S' z j).card:ℝ) ≤ 64*(Nat.card (ZMod q):ℝ)^d:=by
    intro z j
    simpa only [Nat.card_zmod] using hsize z (e z j)
  have hgbud : (∑ z,(p.map θ).mass z*((4*(n+k):ℕ)*J-
      entropy ((p.cond θ z).map G))) ≤ budget :=
    (prefix_budget hwm p θ F S J hS hSJ).trans hbudget
  have hbb : budget ≤ (8*C0)*(2*(n+k):ℕ)*D*σ^(-beta η) := by
    have hh:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmup hC0.le)
      (mul_nonneg (by linarith : 0 ≤ D) (rpow_nonneg hσ0.le (-beta η)))
    nlinarith only [hb,hh]
  obtain ⟨out⟩:=hout (ZMod q) Ω Θ hqlog n k hn hk hkn p θ G S' D J budget
    (scaleKstar σ η D) r r' had.D_lower had.D_upper hJ hG hGS hgf hgcon hgclass hgsize
    hgbud hbb (by simpa only [Nat.card_zmod,HighRankBudgets.beta,SourceScales.beta,k] using hklow)
  have hB : highPrefactor d*(Nat.card (ZMod q):ℝ)^d*
      exp (((d:ℝ)+1)*HighRankBudgets.scaleK σ η D) ≤
      highPrefactor d*(q:ℝ)^d*exp (16*scaleKstar σ η D) := by
    rw [Nat.card_zmod]
    apply mul_le_mul_of_nonneg_left (exp_le_exp.mpr (hdom D (by linarith)))
    exact mul_nonneg (highPrefactor_pos d).le (pow_nonneg (Nat.cast_nonneg _) _)
  have hfinalcost:=hcost (q:ℝ) D (m:ℝ) he hD hmlo
  have out':=out.toContextOutput.mono hB hfinalcost (le_refl 4)
  have final:=out'.transport (Equiv.refl _) F (fun z=>e (θ z)) (fun _ _=>rfl)
  exact ⟨(n+k)/2,hmret,⟨final⟩⟩
end
end SharpLogRamsey.Marking

end

end OAI
