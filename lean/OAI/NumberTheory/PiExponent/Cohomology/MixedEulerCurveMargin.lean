import OAI.NumberTheory.PiExponent.Cohomology.MixedEulerPositivity
import OAI.NumberTheory.PiExponent.Geometry.CurveCycleNumerical

namespace OAI

namespace PiExponent.NumericalAmpleness
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry
open PiExponent.SectionZeroIdeal

theorem mixedTop_curve_margin_aux (d : ℕ) :
    ∀ {X : Scheme.{0}} [IsNoetherian X] [Nonempty X]
      (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
      (H L : LineBundle X), H.IsAmple →
      topologicalKrullDim X = ((d+1 : ℕ) : WithBot ℕ∞) →
      ∀ ε : ℝ, (∀ C : IntegralCurve X,
        ε * (curveDegree p H C : ℝ) ≤ (curveDegree p L C : ℝ)) →
      ∀ ls : List (LineBundle X), ls.length = d →
      (∀ A ∈ ls, A.IsAmple) →
      ε * (mixedTop (lineEuler p (d+1)) (H :: ls) : ℝ) ≤
        (mixedTop (lineEuler p (d+1)) (L :: ls) : ℝ) := by
  induction d with
  | zero =>
    intro X _ _ p _ H L hH hdim ε hmargin ls hlen hamp
    have hz : ls = [] := List.length_eq_zero_iff.mp hlen
    subst ls
    exact CurveCycle.tensor_euler_margin p hdim.le H hH L H
      (structureLineBundle X) (structureLineBundle X) ε hmargin
  | succ d ih =>
    intro X _ _ p _ H L hH hdim ε hmargin ls hlen hamp
    cases ls with
    | nil => simp at hlen
    | cons A ls =>
      have hlen' : ls.length = d := by simpa using hlen
      have hA : A.IsAmple := hamp A (by simp)
      obtain ⟨n, hn, s, hs⟩ := exists_positive_power_regular_section p A hA
      let := hs
      let D := zeroIdeal (A.pow n) s
      let j := D.subschemeι
      have hd := regular_ample_sectionZero_dimension p (A.pow n) (hA.pow n hn) s (d+1) hdim
      let : Nonempty D.subscheme := hd.1
      let : IsLocallyNoetherian D.subscheme := LocallyOfFiniteType.isLocallyNoetherian j
      let : CompactSpace D.subscheme := QuasiCompact.compactSpace_of_compactSpace j
      let : IsNoetherian D.subscheme := {}
      have hHD := LineBundle.IsAmple.pullback_closedImmersion H hH j
      have hm := ih (j ≫ p) (H.pullback j) (L.pullback j) hHD hd.2 ε
        (uniform_curve_margin_restrict p L H ε hmargin j)
        (ls.map (fun B => B.pullback j)) (by simpa using hlen') (by
          intro B hB
          obtain ⟨C, hC, rfl⟩ := List.mem_map.mp hB
          exact LineBundle.IsAmple.pullback_closedImmersion C (hamp C (by simp [hC])) j)
      have hrestrict (B : LineBundle X) :
          (n : ℤ) * mixedTop (lineEuler p (d+1+1)) (B :: A :: ls) =
            mixedTop (lineEuler (j ≫ p) (d+1))
              (B.pullback j :: ls.map (fun C => C.pullback j)) := by
        have he := mixedTop_power_cartier_restriction p H hH (d+1)
          (by simpa only [Nat.cast_add, Nat.cast_one] using hdim.le)
          A n s (B :: ls) (by simp [hlen'])
        have hswap := congrFun
          (mixedDifference_perm (List.Perm.swap B A ls) (lineEuler p (d+1+1))
            (lineEuler_isoInvariant p (d+1+1))) (structureLineBundle X)
        change mixedTop (lineEuler p (d+1+1)) (A :: B :: ls) =
          mixedTop (lineEuler p (d+1+1)) (B :: A :: ls) at hswap
        rw [hswap] at he
        exact he
      rw [← hrestrict H, ← hrestrict L] at hm
      push_cast at hm
      have hnR : (0 : ℝ) < n := by exact_mod_cast hn
      apply (mul_le_mul_iff_right₀ hnR).mp
      nlinarith [hm]

theorem mixedTop_curve_margin {X : Scheme.{0}} [IsNoetherian X] [Nonempty X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (H L : LineBundle X) (hH : H.IsAmple) (d : ℕ)
    (hdim : topologicalKrullDim X = ((d+1 : ℕ) : WithBot ℕ∞))
    (ε : ℝ) (hmargin : ∀ C : IntegralCurve X,
      ε * (curveDegree p H C : ℝ) ≤ (curveDegree p L C : ℝ))
    (ls : List (LineBundle X)) (hlen : ls.length = d) (hamp : ∀ A ∈ ls, A.IsAmple) :
    ε * (mixedTop (lineEuler p (d+1)) (H :: ls) : ℝ) ≤
      (mixedTop (lineEuler p (d+1)) (L :: ls) : ℝ) :=
  mixedTop_curve_margin_aux d p H L hH hdim ε hmargin ls hlen hamp

end
end PiExponent.NumericalAmpleness

end OAI
