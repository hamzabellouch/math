import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Basic.Real.Basic
import Lean.Elab.Tactic.Omega

namespace OAI

noncomputable section
namespace Zarankiewicz
open Module Submodule
variable {W W' : Type*} [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ W]
variable [AddCommGroup W'] [Module ℝ W']

theorem finrank_map_add_le (f : W →ₗ[ℝ] W') (E T : Submodule ℝ W)
    (hTE : T ≤ E) (hTk : T ≤ LinearMap.ker f) :
    finrank ℝ (E.map f) + finrank ℝ T ≤ finrank ℝ E := by
  let g := f.comp E.subtype
  have hk : T.comap E.subtype ≤ LinearMap.ker g := fun x hx => hTk hx
  have hd := Submodule.finrank_mono hk
  rw [(Submodule.comapSubtypeEquivOfLe hTE).finrank_eq] at hd
  have hr := g.finrank_range_add_finrank_ker
  have he : LinearMap.range g = E.map f := by
    dsimp only [g]
    rw [LinearMap.range_comp, Submodule.range_subtype]
  rw [he] at hr
  omega

theorem finrank_map_of_disjoint
    {W W' : Type*} [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ W]
    [AddCommGroup W'] [Module ℝ W']
    (f : W →ₗ[ℝ] W') (E : Submodule ℝ W)
    (hE : Disjoint E (LinearMap.ker f)) : finrank ℝ (E.map f) = finrank ℝ E := by
  let g := f.comp E.subtype
  have hg : Function.Injective g := by
    apply LinearMap.ker_eq_bot.mp
    apply le_antisymm _ bot_le
    intro x hx
    have hm : x.val ∈ E ⊓ LinearMap.ker f := ⟨x.property, hx⟩
    rw [hE.eq_bot] at hm
    exact (Submodule.mem_bot ℝ).mpr (Subtype.ext ((Submodule.mem_bot ℝ).mp hm))
  have hr := LinearMap.finrank_range_of_inj hg
  change finrank ℝ (LinearMap.range (f.comp E.subtype)) = finrank ℝ E at hr
  rw [LinearMap.range_comp, Submodule.range_subtype] at hr
  exact hr

end Zarankiewicz

end

end OAI
