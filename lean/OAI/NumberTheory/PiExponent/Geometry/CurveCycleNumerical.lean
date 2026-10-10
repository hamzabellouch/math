import OAI.NumberTheory.PiExponent.Ampleness.AmpleCurveDegreePositive
import OAI.NumberTheory.PiExponent.Cohomology.CurveCycleEuler
import OAI.NumberTheory.PiExponent.Geometry.CurveComponentsDimension

namespace OAI

namespace PiExponent.CurveCycle
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry

theorem componentEulerDegree_eq_curveDegree {X : Scheme.{0}}
    (p : X ⟶ Spec (CommRingCat.of ℂ)) (L : LineBundle X)
    (C : irreducibleComponents X) (hd : topologicalKrullDim (reducedComponent X C) = 1) :
    componentEulerDegree p L C = NumericalAmpleness.curveDegree p L (componentIntegralCurve C hd) := rfl

theorem componentEulerDegree_nonneg_of_ample {X : Scheme.{0}} [IsNoetherian X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (hd : topologicalKrullDim X ≤ 1) (L : LineBundle X) (hL : L.IsAmple)
    (C : irreducibleComponents X) : 0 ≤ componentEulerDegree p L C := by
  rcases component_dimension_one_or_zero hd C with hC | hC
  · rw [componentEulerDegree_eq_curveDegree p L C hC]
    exact le_of_lt (NumericalAmpleness.curveDegree_pos_of_ample p L hL _)
  · rw [componentEulerDegree_zero_of_dimension_le_zero p L C hC]

theorem cycleEulerDegree_pos_of_ample {X : Scheme.{0}} [IsNoetherian X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (hd : topologicalKrullDim X = 1) (L : LineBundle X) (hL : L.IsAmple) :
    0 < cycleEulerDegree p L := by
  classical
  let : Fintype (irreducibleComponents X) :=
    NoetherianSpace.finite_irreducibleComponents.fintype
  unfold cycleEulerDegree
  apply Finset.sum_pos'
  · intro C _
    exact mul_nonneg (Int.natCast_nonneg _) (componentEulerDegree_nonneg_of_ample p hd.le L hL C)
  · obtain ⟨C,hC⟩ := exists_component_dimension_one X hd
    refine ⟨C,Finset.mem_univ _,mul_pos ?_ ?_⟩
    · exact_mod_cast componentMultiplicity_pos C
    · rw [componentEulerDegree_eq_curveDegree p L C hC]
      exact NumericalAmpleness.curveDegree_pos_of_ample p L hL _

theorem cycleEulerDegree_margin {X : Scheme.{0}} [IsNoetherian X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) (hd : topologicalKrullDim X ≤ 1)
    (L H : LineBundle X) (ε : ℝ)
    (hmargin : ∀ C : NumericalAmpleness.IntegralCurve X,
      ε * (NumericalAmpleness.curveDegree p H C : ℝ) ≤
        (NumericalAmpleness.curveDegree p L C : ℝ)) :
    ε * (cycleEulerDegree p H : ℝ) ≤ (cycleEulerDegree p L : ℝ) := by
  classical
  have hc (C : irreducibleComponents X) :
      ε * (componentEulerDegree p H C : ℝ) ≤ (componentEulerDegree p L C : ℝ) := by
    rcases component_dimension_one_or_zero hd C with hC | hC
    · exact hmargin (componentIntegralCurve C hC)
    · rw [componentEulerDegree_zero_of_dimension_le_zero p H C hC,
        componentEulerDegree_zero_of_dimension_le_zero p L C hC]
      simp
  unfold cycleEulerDegree
  simp only [Int.cast_sum,Int.cast_mul,Int.cast_natCast]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro C _
  calc
    ε * ((componentMultiplicity X C : ℝ) * (componentEulerDegree p H C : ℝ)) =
        (componentMultiplicity X C : ℝ) * (ε * (componentEulerDegree p H C : ℝ)) := by ring
    _ ≤ (componentMultiplicity X C : ℝ) * (componentEulerDegree p L C : ℝ) :=
      mul_le_mul_of_nonneg_left (hc C) (Nat.cast_nonneg _)

theorem tensor_euler_margin {X : Scheme.{0}} [IsNoetherian X] [Nonempty X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (hd : topologicalKrullDim X ≤ 1) (A : LineBundle X) (hA : A.IsAmple)
    (L H M N : LineBundle X) (ε : ℝ)
    (hmargin : ∀ C : NumericalAmpleness.IntegralCurve X,
      ε * (NumericalAmpleness.curveDegree p H C : ℝ) ≤
        (NumericalAmpleness.curveDegree p L C : ℝ)) :
    ε * ((eulerCharacteristic p 1 (H.tensor M).sheaf - eulerCharacteristic p 1 M.sheaf : ℤ) : ℝ) ≤
      ((eulerCharacteristic p 1 (L.tensor N).sheaf - eulerCharacteristic p 1 N.sheaf : ℤ) : ℝ) := by
  rw [tensor_euler_eq_cycle p hd A hA H M,tensor_euler_eq_cycle p hd A hA L N]
  exact cycleEulerDegree_margin p hd L H ε hmargin

theorem euler_degree_pos_of_ample_curve {X : Scheme.{0}} [IsNoetherian X] [Nonempty X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (hd : topologicalKrullDim X = 1) (L : LineBundle X) (hL : L.IsAmple) :
    0 < eulerCharacteristic p 1 L.sheaf - eulerCharacteristic p 1 (structureSheaf X) := by
  have h := tensor_euler_eq_cycle p hd.le L hL L (L.pow 0)
  have he := eulerCharacteristic_iso p (moduleTensorRightUnit L.sheaf) 1
  change eulerCharacteristic p 1 (L.tensor (L.pow 0)).sheaf =
    eulerCharacteristic p 1 L.sheaf at he
  rw [he] at h
  change eulerCharacteristic p 1 L.sheaf -
    eulerCharacteristic p 1 (structureSheaf X) = cycleEulerDegree p L at h
  rw [h]
  exact cycleEulerDegree_pos_of_ample p hd L hL

end
end PiExponent.CurveCycle

end OAI
