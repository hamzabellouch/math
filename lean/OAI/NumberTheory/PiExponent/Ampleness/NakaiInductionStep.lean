import OAI.NumberTheory.PiExponent.Ampleness.NakaiAmpleFromSections
import OAI.NumberTheory.PiExponent.Cohomology.EulerDifferencePolynomial
import OAI.NumberTheory.PiExponent.Cohomology.EulerPolynomialDegree
import OAI.NumberTheory.PiExponent.Geometry.CurveDegreeLaws

namespace OAI

namespace PiExponent.NumericalAmpleness
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Filter
open PiExponentSeshadri.Geometry
variable {X : Scheme.{0}}

theorem isAmple_of_lower_ampleness_of_euler_growth [IsIntegral X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (r : ℕ) (i : X ⟶ ProjectiveO1.projectiveSpace ℂ (Fin (r+1))) [IsClosedImmersion i]
    (hi : i ≫ polynomialProjectiveProjection ℂ (Fin (r+1)) = p)
    (H L : LineBundle X) (hH : H.IsAmple) (d : ℕ)
    (hdim : topologicalKrullDim X ≤ d+1)
    (hlower : ∀ I : X.IdealSheafData, topologicalKrullDim I.subscheme ≤ d →
      (L.pullback I.subschemeι).IsAmple)
    (hgrowth : Tendsto (fun n => eulerCharacteristic p (d+1) (L.pow n).sheaf) atTop atTop)
    (hpositive : ∀ C : IntegralCurve X, 0 < curveDegree p L C) : L.IsAmple := by
  obtain ⟨a,ha,k,s,hs⟩ := exists_power_section_cover_of_euler_growth
    p r i hi H L hH d hdim hlower hgrowth
  apply LineBundle.IsAmple.of_pow L ha
  apply isAmple_of_section_cover_of_curveDegree_pos p (L.pow a) (d+1) (by
    simpa only [Nat.cast_add, Nat.cast_one] using hdim) k s hs
  intro C
  rw [curveDegree_pow_of_ample p H hH L C a]
  exact mul_pos (by exact_mod_cast ha) (hpositive C)

theorem isAmple_of_lower_ampleness_of_topEuler_pos [IsIntegral X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (r : ℕ) (i : X ⟶ ProjectiveO1.projectiveSpace ℂ (Fin (r+1))) [IsClosedImmersion i]
    (hi : i ≫ polynomialProjectiveProjection ℂ (Fin (r+1)) = p)
    (H L : LineBundle X) (hH : H.IsAmple) (d : ℕ)
    (hdim : topologicalKrullDim X ≤ d+1)
    (hlower : ∀ I : X.IdealSheafData, topologicalKrullDim I.subscheme ≤ d →
      (L.pullback I.subschemeι).IsAmple)
    (htop : 0 < (fwdDiff (1 : ℕ))^[d+1]
      (fun n => eulerCharacteristic p (d+1) (L.pow n).sheaf) 0)
    (hpositive : ∀ C : IntegralCurve X, 0 < curveDegree p L C) : L.IsAmple := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  let : IsNoetherian X := {}
  have hzero := euler_power_dimension_difference_eq_zero p r i hi L (d+1) (by
    simpa only [Nat.cast_add, Nat.cast_one] using hdim)
  have hgrowth := tendsto_atTop_of_forwardDifference_eq_zero
    (fun n => eulerCharacteristic p (d+1) (L.pow n).sheaf) (d+1) (by omega) hzero htop
  exact isAmple_of_lower_ampleness_of_euler_growth p r i hi H L hH d hdim hlower hgrowth hpositive

theorem isAmple_of_lower_ampleness_of_topEuler_pos_of_margin [IsIntegral X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (r : ℕ) (i : X ⟶ ProjectiveO1.projectiveSpace ℂ (Fin (r+1))) [IsClosedImmersion i]
    (hi : i ≫ polynomialProjectiveProjection ℂ (Fin (r+1)) = p)
    (H L : LineBundle X) (hH : H.IsAmple) (d : ℕ)
    (hdim : topologicalKrullDim X ≤ d+1)
    (hlower : ∀ I : X.IdealSheafData, topologicalKrullDim I.subscheme ≤ d →
      (L.pullback I.subschemeι).IsAmple)
    (htop : 0 < (fwdDiff (1 : ℕ))^[d+1]
      (fun n => eulerCharacteristic p (d+1) (L.pow n).sheaf) 0)
    (ε : ℝ) (hε : 0 < ε)
    (hmargin : ∀ C : IntegralCurve X,
      ε * (curveDegree p H C : ℝ) ≤ (curveDegree p L C : ℝ)) : L.IsAmple :=
  isAmple_of_lower_ampleness_of_topEuler_pos p r i hi H L hH d hdim hlower htop
    (curveDegree_pos_of_uniform_margin p H L hH ε hε hmargin)

end
end PiExponent.NumericalAmpleness

end OAI
