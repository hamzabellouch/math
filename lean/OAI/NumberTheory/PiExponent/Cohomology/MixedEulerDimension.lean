import OAI.NumberTheory.PiExponent.Cohomology.MixedEulerAlgebra
import OAI.NumberTheory.PiExponent.Cohomology.MixedEulerCartier

namespace OAI

namespace PiExponent.NumericalAmpleness
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry PiExponentSeshadri.Projective
open PiExponent.SectionZeroIdeal PiExponent.ProjectiveO1

def lineEuler {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of ℂ)) (r : ℕ)
    (M : LineBundle X) : ℤ := eulerCharacteristic p r M.sheaf

theorem lineEuler_isoInvariant {X : Scheme.{0}}
    (p : X ⟶ Spec (CommRingCat.of ℂ)) (r : ℕ) :
    LineIsoInvariant (lineEuler p r) := by
  intro L M e
  exact eulerCharacteristic_iso p e r

theorem mixedDifference_pullback_tensorShift_zero {X Y : Scheme.{0}}
    (ls : List (LineBundle X)) (i : Y ⟶ X) (g : LineBundle Y → ℤ)
    (hg : LineIsoInvariant g) (B : LineBundle Y)
    (hz : mixedDifference (ls.map (fun L => L.pullback i)) g = 0) :
    mixedDifference ls (fun M => g (B.tensor (M.pullback i))) = 0 := by
  funext M
  rw [mixedDifference_pullback ls i (fun N => g (B.tensor N)) (hg.tensorShift B) M,
    mixedDifference_tensorShift _ g hg B (M.pullback i), hz]
  rfl

theorem mixedDifference_lineEuler_aux (d : ℕ) :
    ∀ {X : Scheme.{0}} [IsNoetherian X]
      (p : X ⟶ Spec (CommRingCat.of ℂ)) (r : ℕ)
      (i : X ⟶ projectiveSpace ℂ (Fin (r+1))) [IsClosedImmersion i]
      (_hi : i ≫ polynomialProjectiveProjection ℂ (Fin (r+1)) = p)
      (H : LineBundle X), H.IsAmple →
      topologicalKrullDim X ≤ d → ∀ ls : List (LineBundle X), ls.length = d+1 →
      mixedDifference ls (lineEuler p r) = 0 := by
  induction d with
  | zero =>
    intro X _ p r i _ hi H hH hdim ls hlen
    cases ls with
    | nil => simp at hlen
    | cons L ls =>
      have hz : ls = [] := List.length_eq_zero_iff.mp (by simpa using hlen)
      subst ls
      funext M
      obtain ⟨e⟩ := lineBundle_trivial_of_dim_le_zero hdim L
      have he := eulerCharacteristic_iso p
        (moduleTensorIso e (Iso.refl M.sheaf) ≪≫ moduleTensorUnit M.sheaf) r
      change eulerCharacteristic p r (L.tensor M).sheaf - eulerCharacteristic p r M.sheaf = 0
      exact sub_eq_zero.mpr he
  | succ d ih =>
    intro X _ p r i _ hi H hH hdim ls hlen
    cases ls with
    | nil => simp at hlen
    | cons L ls =>
      have hlen' : ls.length = d+1 := by simpa using hlen
      obtain ⟨B, s, t, hs, ht⟩ := exists_regular_twist_pair p H L hH
      let := hs
      let := ht
      let A := L.tensor B
      let D := zeroIdeal A s
      let E := zeroIdeal B t
      let jD := D.subschemeι
      let jE := E.subschemeι
      let : IsLocallyNoetherian D.subscheme := LocallyOfFiniteType.isLocallyNoetherian jD
      let : CompactSpace D.subscheme := QuasiCompact.compactSpace_of_compactSpace jD
      let : IsNoetherian D.subscheme := {}
      let : IsLocallyNoetherian E.subscheme := LocallyOfFiniteType.isLocallyNoetherian jE
      let : CompactSpace E.subscheme := QuasiCompact.compactSpace_of_compactSpace jE
      let : IsNoetherian E.subscheme := {}
      have hdD : topologicalKrullDim D.subscheme ≤ d :=
        regular_sectionZero_dimension_le A s d (by
          simpa only [Nat.cast_add, Nat.cast_one] using hdim)
      have hdE : topologicalKrullDim E.subscheme ≤ d :=
        regular_sectionZero_dimension_le B t d (by
          simpa only [Nat.cast_add, Nat.cast_one] using hdim)
      have hiD : (jD ≫ i) ≫ polynomialProjectiveProjection ℂ (Fin (r+1)) = jD ≫ p := by
        rw [Category.assoc, hi]
      have hiE : (jE ≫ i) ≫ polynomialProjectiveProjection ℂ (Fin (r+1)) = jE ≫ p := by
        rw [Category.assoc, hi]
      let g := lineEuler (jD ≫ p) r
      let h := lineEuler (jE ≫ p) r
      let g' (M : LineBundle D.subscheme) := g ((A.pullback jD).tensor M)
      let h' (M : LineBundle E.subscheme) := h (((B.tensor L).pullback jE).tensor M)
      have hg := lineEuler_isoInvariant (jD ≫ p) r
      have hh := lineEuler_isoInvariant (jE ≫ p) r
      have hDz : mixedDifference (ls.map (fun L => L.pullback jD)) g = 0 :=
        ih (jD ≫ p) r (jD ≫ i) hiD (H.pullback jD)
          (LineBundle.IsAmple.pullback_closedImmersion H hH jD) hdD _
          (by simpa using hlen')
      have hEz : mixedDifference (ls.map (fun L => L.pullback jE)) h = 0 :=
        ih (jE ≫ p) r (jE ≫ i) hiE (H.pullback jE)
          (LineBundle.IsAmple.pullback_closedImmersion H hH jE) hdE _
          (by simpa using hlen')
      have heq : tensorDifference L (lineEuler p r) =
          (fun M => g' (M.pullback jD)) - fun M => h' (M.pullback jE) := by
        funext M
        exact tensor_euler_difference_cartier_pair p r i hi L B M s t
      have hDzero := mixedDifference_pullback_tensorShift_zero ls jD g hg (A.pullback jD) hDz
      have hEzero := mixedDifference_pullback_tensorShift_zero ls jE h hh
        ((B.tensor L).pullback jE) hEz
      rw [mixedDifference_cons_commute L ls _ (lineEuler_isoInvariant p r),
        heq, mixedDifference_sub, hDzero, hEzero, sub_self]

end
end PiExponent.NumericalAmpleness

end OAI
