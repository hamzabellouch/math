import OAI.NumberTheory.Ostmann.Characters.ShellPrior
import OAI.NumberTheory.Ostmann.Characters.SubsetTestStability
import OAI.NumberTheory.Ostmann.Characters.TypicalSelection

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters
open Construction Preliminaries Filter

theorem eventually_few_bad_shell_endpoints (d:Decomposition) (k:ℕ) (hk:4≤k) :
    ∀ᶠ X:ℕ in atTop,
      ∀ E:Finset (PrimeUpTo (collisionScale k X)), ∀ hE:0<primeShellMass E,
      ∀ L δ:ℝ, 0<L → 0<δ →
      (∀p∈E,L≤Real.log p.val) →
      (primeShellMass E*L)⁻¹*(collisionConstant k*Real.log (Real.log (X:ℝ)))<(δ/2)^2 →
      ∀ f:(p:PrimeUpTo (collisionScale k X))→ZMod p.val→ℂ,
      (∀p r,‖f p r‖≤1) →
      δ≤((primeShellPrior E hE).cmean (fun p=>
        (∑r∈d.residueSupport p.val,f p r)/((d.residueSupport p.val).card:ℂ))).re →
      ((upperWindow d.A X |>.filter (fun a=>
        ((primeShellPrior E hE).cmean (fun p=>f p (a:ZMod p.val))).re<δ/2)).card:ℝ)
        < Real.sqrt X/Real.log (X:ℝ)^k := by
  classical
  filter_upwards [eventually_subset_A_test_stability d k hk,
    eventually_collision_bound_conditions k] with X hX hcond
  intro E hE L δ hL hδ hscale hsmall f hf hmean
  have hxr : (0:ℝ)<X := by exact_mod_cast hcond.1
  have hlog : 0<Real.log (X:ℝ) := lt_of_lt_of_le (by norm_num) hcond.2.1
  have hT : 0<Real.sqrt X/Real.log (X:ℝ)^k :=
    div_pos (Real.sqrt_pos.mpr hxr) (pow_pos hlog _)
  apply few_bad_endpoints (upperWindow d.A X) (primeShellPrior E hE)
    (fun p a=>f p (a:ZMod p.val))
    (fun p=>(∑r∈d.residueSupport p.val,f p r)/((d.residueSupport p.val).card:ℂ))
    (Real.sqrt X/Real.log (X:ℝ)^k) δ
    ((primeShellMass E*L)⁻¹*(collisionConstant k*Real.log (Real.log (X:ℝ))))
    hT hδ hsmall hmean
  intro U hU hcard
  exact primeShellPrior_error_le E hE L hL hscale _ _
    (hX U hU hcard f (fun p=>probability_test_norm_le_of_norm_le_one p.val (f p) (hf p)))

attribute [local instance] Classical.propDecidable

theorem simultaneous_bad_count {ι α:Type*} [Fintype ι] [DecidableEq α]
    (S:Finset α) (P:ι→α→Prop) (T:ℝ)
    (h:∀i,((S.filter (fun a=>¬P i a)).card:ℝ)≤T) :
    ((S.filter (fun a=>¬∀i,P i a)).card:ℝ)≤(Fintype.card ι:ℝ)*T := by
  classical
  have he : S.filter (fun a=>¬∀i,P i a)=
      Finset.univ.biUnion (fun i=>S.filter (fun a=>¬P i a)) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_biUnion, Finset.mem_univ, true_and, not_forall]
    tauto
  rw [he]
  calc
    _ ≤ ∑i:ι,((S.filter (fun a=>¬P i a)).card:ℝ) := by
      exact_mod_cast Finset.card_biUnion_le (s:=Finset.univ) (t:=fun i=>S.filter (fun a=>¬P i a))
    _ ≤ ∑_i:ι,T := Finset.sum_le_sum (fun i _=>h i)
    _ = _ := by simp

end Ostmann.Characters

end

end OAI
