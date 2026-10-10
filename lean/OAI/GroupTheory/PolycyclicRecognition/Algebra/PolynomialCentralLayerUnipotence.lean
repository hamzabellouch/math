import OAI.GroupTheory.PolycyclicRecognition.Algebra.UpperCentralLayerMap
import OAI.GroupTheory.PolycyclicRecognition.Algebra.IntegerConjugationUnipotent
import Mathlib.LinearAlgebra.FreeModule.PID

namespace OAI

/-! # Polynomial growth forces unipotent powers on central layers -/

noncomputable section
namespace PolycyclicRecognition
open scoped IsMulCommutative

variable {G : Type} [Group G] [DecidableEq G] (F : Subgroup G) [F.Normal]

omit [DecidableEq G] [F.Normal] in
theorem upperCentralLayerMap_surjective (i : ℕ) :
    Function.Surjective (upperCentralLayerMap F i) := by
  intro z
  obtain ⟨a, ha⟩ := QuotientGroup.mk'_surjective (Subgroup.upperCentralSeries F i) z.val
  have hm : a ∈ Subgroup.upperCentralSeries F (i + 1) := by
    change a ∈ Subgroup.upperCentralSeriesStep (Subgroup.upperCentralSeries F i)
    rw [Subgroup.upperCentralSeriesStep_eq_comap_center]
    change QuotientGroup.mk' (Subgroup.upperCentralSeries F i) a ∈ Subgroup.center _
    rw [ha]
    exact z.property
  refine ⟨⟨a, (mem_ambientUpperCentralSeries_iff F (i + 1) a).mpr hm⟩, ?_⟩
  apply Subtype.ext
  exact ha

theorem polynomial_growth_centralLayer_unipotent_power
    (S : Finset G) (hS : ∀ s ∈ S, s⁻¹ ∈ S)
    (hgen : Subgroup.closure (S : Set G) = ⊤)
    (hvol : ∃ C d : ℕ, ∀ n, (wordBall S n).card ≤ C * (1 + n) ^ d)
    (i : ℕ) [Module.Free ℤ (Additive (CentralLayer F i))]
    [Module.Finite ℤ (Additive (CentralLayer F i))] (g : G) :
    ∃ m : ℕ, 0 < m ∧ IsNilpotent ((rationalUpperCentralAction F i g).toLinearMap ^ m - 1) := by
  let A := Additive (CentralLayer F i)
  let q : ambientUpperCentralSeries F (i + 1) →* Multiplicative A :=
    { toFun := fun a => Multiplicative.ofAdd (Additive.ofMul (upperCentralLayerMap F i a))
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hq : Function.Surjective q := by
    intro z
    obtain ⟨a, ha⟩ := upperCentralLayerMap_surjective F i z.toAdd.toMul
    exact ⟨a, congrArg (fun x => Multiplicative.ofAdd (Additive.ofMul x)) ha⟩
  let T := (upperCentralLayerAut F i g).toAdditive.toIntLinearEquiv.toLinearMap
  have hT (a : ambientUpperCentralSeries F (i + 1)) :
      (q (MulAut.conjNormal g a)).toAdd = T (q a).toAdd := by
    change Additive.ofMul (upperCentralLayerMap F i (MulAut.conjNormal g a)) =
      Additive.ofMul (upperCentralLayerAut F i g (upperCentralLayerMap F i a))
    rw [upperCentralLayerMap_equivariant]
  obtain ⟨m, hm, hn⟩ := polynomial_growth_integer_conjugation_unipotent_power
    S hS hgen hvol (ambientUpperCentralSeries F (i + 1)) g q hq T hT
  refine ⟨m, hm, ?_⟩
  have hh := hn.map (Module.End.baseChangeHom ℤ ℚ A).toRingHom
  change IsNilpotent (T.baseChange ℚ ^ m - 1)
  change IsNilpotent ((T ^ m - 1).baseChange ℚ) at hh
  rw [LinearMap.baseChange_sub, LinearMap.baseChange_pow, LinearMap.baseChange_one] at hh
  exact hh

end PolycyclicRecognition

end

end OAI
