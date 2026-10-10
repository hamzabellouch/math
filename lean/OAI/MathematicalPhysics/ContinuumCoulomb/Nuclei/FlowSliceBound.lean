import OAI.MathematicalPhysics.ContinuumCoulomb.Nuclei.FlowHigherComposition

namespace OAI

/-! Joint derivative bounds restrict to spatial slices with no loss. -/

noncomputable section
open ContinuousLinearMap
open scoped ContDiff
namespace ContinuumCoulomb

theorem flow_slice_derivative_bound (F : ℝ × Position → Position)
    (hF : ContDiff ℝ 4 F) (n : ℕ) (hn : n ≤ 4) (t : ℝ) (x : Position) :
    ‖iteratedFDeriv ℝ n (fun y => F (t,y)) x‖ ≤
      ‖iteratedFDeriv ℝ n F (t,x)‖ := by
  let L : Position →L[ℝ] (ℝ × Position) := inr ℝ ℝ Position
  let A : ℝ × Position → Position := fun z => F ((t,0)+z)
  have hA : ContDiff ℝ 4 A := hF.comp (contDiff_const.add contDiff_id)
  have heq : (fun y => F (t,y)) = A ∘ L := by funext y; simp [A,L]
  rw [heq,L.iteratedFDeriv_comp_right hA x (by exact_mod_cast hn)]
  have hb := (iteratedFDeriv ℝ n A (L x)).norm_compContinuousLinearMap_le (fun _ => L)
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin] at hb
  have hL : ‖L‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro z
    simp [L]
  have hp : ‖L‖^n ≤ 1 := pow_le_one₀ (norm_nonneg L) hL
  apply (hb.trans (mul_le_of_le_one_right (norm_nonneg _) hp)).trans_eq
  have hd := iteratedFDeriv_comp_add_left (𝕜 := ℝ) (f := F) n (t,0) (L x)
  change ‖iteratedFDeriv ℝ n (fun z => F ((t,0)+z)) (L x)‖ = _
  rw [hd]
  simp [L]

end ContinuumCoulomb

end

end OAI
