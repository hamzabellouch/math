import OAI.NumberTheory.PiExponent.Ampleness.AmpleFiniteProjectiveEmbedding
import OAI.NumberTheory.PiExponent.Ampleness.IntegralComponentAmple
import OAI.NumberTheory.PiExponent.Ampleness.ProperAmpleFiniteDimension
import OAI.NumberTheory.PiExponent.Ampleness.ZeroDimensionalAmple
import OAI.NumberTheory.PiExponent.Cohomology.NumericalEulerSlopeInputs

namespace OAI

namespace PiExponent.NumericalAmpleness
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry

theorem isAmple_of_uniform_curve_margin_dimension (d : ℕ) :
    ∀ {X : Scheme.{0}} [IsNoetherian X]
      (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
      (H L : LineBundle X), H.IsAmple → topologicalKrullDim X ≤ d →
      ∀ ε : ℝ, 0 < ε →
        (∀ C : IntegralCurve X,
          ε * (curveDegree p H C : ℝ) ≤ (curveDegree p L C : ℝ)) → L.IsAmple := by
  induction d with
  | zero =>
    intro X _ p _ H L hH hdim ε hε hmargin
    exact isAmple_of_proper_dimension_zero p (by simpa using hdim) L
  | succ d ih =>
    have hintegral : ∀ {Y : Scheme.{0}} [IsNoetherian Y] [IsIntegral Y]
        (p : Y ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
        (H L : LineBundle Y), H.IsAmple → topologicalKrullDim Y ≤ ((d+1:ℕ):WithBot ℕ∞) →
        ∀ ε : ℝ, 0 < ε →
          (∀ C : IntegralCurve Y,
            ε * (curveDegree p H C : ℝ) ≤ (curveDegree p L C : ℝ)) → L.IsAmple := by
      intro Y _ _ p _ H L hH hdim ε hε hmargin
      by_cases hsmall : topologicalKrullDim Y ≤ d
      · exact ih p H L hH hsmall ε hε hmargin
      have heq : topologicalKrullDim Y = ((d+1:ℕ):WithBot ℕ∞) := by
        apply le_antisymm hdim
        have hnot : ¬ topologicalKrullDim Y < (d:WithBot ℕ∞)+1 := by
          simpa only [ENat.WithBot.lt_add_one_iff] using hsmall
        simpa only [Nat.cast_add, Nat.cast_one] using le_of_not_gt hnot
      obtain ⟨r, i, hiClosed, hi⟩ := ample_finite_projective_embedding p H hH
      let : IsClosedImmersion i := hiClosed
      apply isAmple_of_lower_numerical_criterion p r i hi H L hH d heq _ ε hε hmargin
      intro I hI M δ hδ hM
      let : IsLocallyNoetherian I.subscheme :=
        LocallyOfFiniteType.isLocallyNoetherian I.subschemeι
      let : CompactSpace I.subscheme := QuasiCompact.compactSpace_of_compactSpace I.subschemeι
      let : IsNoetherian I.subscheme := {}
      exact ih (I.subschemeι ≫ p) (H.pullback I.subschemeι) M
        (hH.pullback_closedImmersion H I.subschemeι) hI δ hδ hM
    intro X _ p _ H L hH hdim ε hε hmargin
    apply isAmple_of_integral_closed_restrictions p L H hH
    intro Y _ j _
    let : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian j
    let : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace j
    let : IsNoetherian Y := {}
    apply hintegral (j ≫ p) (H.pullback j) (L.pullback j)
      (hH.pullback_closedImmersion H j)
      ((ProperAmpleFiniteDimension.closedImmersion_dimension_le j).trans hdim) ε hε
    exact uniform_curve_margin_restrict p L H ε hmargin j

theorem isAmple_of_uniform_curve_margin {X : Scheme.{0}}
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (H L : LineBundle X) (hH : H.IsAmple) (ε : ℝ) (hε : 0 < ε)
    (hmargin : ∀ C : IntegralCurve X,
      ε * (curveDegree p H C : ℝ) ≤ (curveDegree p L C : ℝ)) : L.IsAmple := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  let : IsNoetherian X := {}
  obtain ⟨d,hd⟩ := ProperAmpleFiniteDimension.exists_dimension_bound_of_proper_ample p H hH
  exact isAmple_of_uniform_curve_margin_dimension d p H L hH hd ε hε hmargin

end
end PiExponent.NumericalAmpleness

end OAI
