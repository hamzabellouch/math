import OAI.NumberTheory.PiExponent.Cohomology.MixedEulerAmpleDimension
import OAI.NumberTheory.PiExponent.Cohomology.MixedEulerPolarization

namespace OAI

namespace PiExponent.NumericalAmpleness
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry
open PiExponent.SectionZeroIdeal
variable {X : Scheme.{0}}

theorem tensor_euler_difference_regular_section
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (H : LineBundle X) (hH : H.IsAmple) (d : ℕ)
    (hdim : topologicalKrullDim X ≤ d+1)
    (A M : LineBundle X) (s : GlobalSections X A.sheaf) [Mono s] :
    lineEuler p (d+1) (A.tensor M) - lineEuler p (d+1) M =
      lineEuler ((zeroIdeal A s).subschemeι ≫ p) d
        ((A.pullback (zeroIdeal A s).subschemeι).tensor
          (M.pullback (zeroIdeal A s).subschemeι)) := by
  let D := zeroIdeal A s
  let j := D.subschemeι
  have hHD := LineBundle.IsAmple.pullback_closedImmersion H hH j
  have hdimD := regular_sectionZero_dimension_le A s d hdim
  let e0 : ((A.pow 0).tensor M).sheaf ≅ M.sheaf := moduleTensorUnit M.sheaf
  let e1 : ((A.pow 1).tensor M).sheaf ≅ (A.tensor M).sheaf :=
    moduleTensorIso (moduleTensorRightUnit A.sheaf) (Iso.refl M.sheaf)
  have he := regular_mixedCartierPower_euler_difference p A M s 0 (d+1)
    (fun q _ => line_cohomology_finite_of_ample_all p H hH ((A.pow 0).tensor M) q)
    (fun q _ => line_cohomology_finite_of_ample_all p H hH ((A.pow 1).tensor M) q)
    (fun q _ => line_cohomology_finite_of_ample_all (j ≫ p) (H.pullback j) hHD
      (((A.pow 1).tensor M).pullback j) q)
    (lineBundle_cohomology_zero_of_dimension_le (d+1) p H hH ((A.pow 0).tensor M)
      (by simpa only [Nat.cast_add, Nat.cast_one] using hdim) (d+1+1) (by omega))
    (lineBundle_cohomology_zero_of_dimension_le d (j ≫ p) (H.pullback j) hHD
      (((A.pow 1).tensor M).pullback j) hdimD (d+1) (by omega))
  rw [eulerCharacteristic_iso p e0 (d+1), eulerCharacteristic_iso p e1 (d+1)] at he
  have hR := eulerCharacteristic_iso (j ≫ p)
    ((Scheme.Modules.pullback j).mapIso e1 ≪≫ PiExponentSeshadri.PullbackTensor.iso j A M) d
  simp only [Nat.add_sub_cancel, Nat.zero_add] at he
  exact he.trans hR

theorem mixedDifference_cartier_restriction
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (H : LineBundle X) (hH : H.IsAmple) (d : ℕ)
    (hdim : topologicalKrullDim X ≤ d+1)
    (A : LineBundle X) (s : GlobalSections X A.sheaf) [Mono s]
    (ls : List (LineBundle X)) (M : LineBundle X) :
    mixedDifference (A :: ls) (lineEuler p (d+1)) M =
      mixedDifference (ls.map (fun L => L.pullback (zeroIdeal A s).subschemeι))
        (lineEuler ((zeroIdeal A s).subschemeι ≫ p) d)
        ((A.pullback (zeroIdeal A s).subschemeι).tensor
          (M.pullback (zeroIdeal A s).subschemeι)) := by
  let j := (zeroIdeal A s).subschemeι
  let g := lineEuler (j ≫ p) d
  have hg := lineEuler_isoInvariant (j ≫ p) d
  have he : tensorDifference A (lineEuler p (d+1)) =
      fun N => g ((A.pullback j).tensor (N.pullback j)) := by
    funext N
    exact tensor_euler_difference_regular_section p H hH d hdim A N s
  rw [mixedDifference_cons_commute A ls _ (lineEuler_isoInvariant p (d+1)), he,
    mixedDifference_pullback ls j _ (hg.tensorShift (A.pullback j)) M,
    mixedDifference_tensorShift _ g hg (A.pullback j) (M.pullback j)]

theorem mixedTop_cartier_restriction [IsNoetherian X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (H : LineBundle X) (hH : H.IsAmple) (d : ℕ)
    (hdim : topologicalKrullDim X ≤ d+1)
    (A : LineBundle X) (s : GlobalSections X A.sheaf) [Mono s]
    (ls : List (LineBundle X)) (hlen : ls.length = d) :
    mixedTop (lineEuler p (d+1)) (A :: ls) =
      mixedTop (lineEuler ((zeroIdeal A s).subschemeι ≫ p) d)
        (ls.map (fun L => L.pullback (zeroIdeal A s).subschemeι)) := by
  let D := zeroIdeal A s
  let j := D.subschemeι
  let : IsLocallyNoetherian D.subscheme := LocallyOfFiniteType.isLocallyNoetherian j
  let : CompactSpace D.subscheme := QuasiCompact.compactSpace_of_compactSpace j
  let : IsNoetherian D.subscheme := {}
  have hHD := LineBundle.IsAmple.pullback_closedImmersion H hH j
  have hdimD := regular_sectionZero_dimension_le A s d hdim
  have hdeg : MixedDegreeLE d (lineEuler (j ≫ p) d) :=
    mixedDifference_lineEuler_of_ample (j ≫ p) (H.pullback j) hHD d hdimD
  unfold mixedTop
  rw [mixedDifference_cartier_restriction p H hH d hdim A s ls]
  exact mixedDifference_eq_structure_of_degree (lineEuler_isoInvariant (j ≫ p) d)
    hdeg _ (by simpa using hlen) _

theorem mixedTop_power_cartier_restriction [IsNoetherian X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (H : LineBundle X) (hH : H.IsAmple) (d : ℕ)
    (hdim : topologicalKrullDim X ≤ d+1)
    (A : LineBundle X) (n : ℕ) (s : GlobalSections X (A.pow n).sheaf) [Mono s]
    (ls : List (LineBundle X)) (hlen : ls.length = d) :
    (n : ℤ) * mixedTop (lineEuler p (d+1)) (A :: ls) =
      mixedTop (lineEuler ((zeroIdeal (A.pow n) s).subschemeι ≫ p) d)
        (ls.map (fun L => L.pullback (zeroIdeal (A.pow n) s).subschemeι)) := by
  have hdegree : MixedDegreeLE (d+1) (lineEuler p (d+1)) :=
    mixedDifference_lineEuler_of_ample p H hH (d+1)
      (by simpa only [Nat.cast_add, Nat.cast_one] using hdim)
  have he := congrFun (mixedDifference_pow_cons_of_degree (lineEuler_isoInvariant p (d+1))
    hdegree A n ls (by omega)) (structureLineBundle X)
  have hscale : mixedTop (lineEuler p (d+1)) (A.pow n :: ls) =
      (n : ℤ) * mixedTop (lineEuler p (d+1)) (A :: ls) := by
    simpa only [Pi.smul_apply, nsmul_eq_mul, mixedTop, Pi.mul_apply, Pi.natCast_apply] using he
  rw [← hscale]
  exact mixedTop_cartier_restriction p H hH d hdim (A.pow n) s ls hlen

end
end PiExponent.NumericalAmpleness

end OAI
