import OAI.NumberTheory.PiExponent.Ampleness.AmpleDivisorDimension
import OAI.NumberTheory.PiExponent.Cohomology.MixedEulerRestriction

namespace OAI

namespace PiExponent.NumericalAmpleness
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry
open PiExponent.SectionZeroIdeal

theorem exists_positive_power_regular_section {X : Scheme.{0}} [IsNoetherian X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) (A : LineBundle X) (hA : A.IsAmple) :
    ∃ n : ℕ, 0 < n ∧ ∃ s : GlobalSections X (A.pow n).sheaf, Mono s := by
  obtain ⟨N, hN⟩ := GeneratorsSectionCover.ample_eventual_fin_section_cover A hA
  obtain ⟨k, s, hs⟩ := hN (N+1) (by omega)
  obtain ⟨t, ht⟩ := exists_mono_section_of_finite_cover p (A.pow (N+1)) s hs
  exact ⟨N+1, by omega, t, ht⟩

theorem mixedTop_pos_of_ample_aux (d : ℕ) :
    ∀ {X : Scheme.{0}} [IsNoetherian X] [Nonempty X]
      (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
      (H : LineBundle X), H.IsAmple → topologicalKrullDim X = d →
      ∀ ls : List (LineBundle X), ls.length = d →
      (∀ L ∈ ls, L.IsAmple) → 0 < mixedTop (lineEuler p d) ls := by
  induction d with
  | zero =>
    intro X _ _ p _ H hH hdim ls hlen hamp
    have hz : ls = [] := List.length_eq_zero_iff.mp hlen
    subst ls
    let : Finite X := finite_of_dim_le_zero hdim.le
    exact CurveDegree.finite_nonempty_euler_pos p 0
  | succ d ih =>
    intro X _ _ p _ H hH hdim ls hlen hamp
    cases ls with
    | nil => simp at hlen
    | cons A ls =>
      have hlen' : ls.length = d := by simpa using hlen
      have hA : A.IsAmple := hamp A (by simp)
      obtain ⟨n, hn, s, hs⟩ := exists_positive_power_regular_section p A hA
      let := hs
      have hAn : (A.pow n).IsAmple := hA.pow n hn
      let D := zeroIdeal (A.pow n) s
      let j := D.subschemeι
      have hd := regular_ample_sectionZero_dimension p (A.pow n) hAn s d hdim
      let : Nonempty D.subscheme := hd.1
      let : IsLocallyNoetherian D.subscheme := LocallyOfFiniteType.isLocallyNoetherian j
      let : CompactSpace D.subscheme := QuasiCompact.compactSpace_of_compactSpace j
      let : IsNoetherian D.subscheme := {}
      have hHD := LineBundle.IsAmple.pullback_closedImmersion H hH j
      have hpos := ih (j ≫ p) (H.pullback j) hHD hd.2
        (ls.map (fun L => L.pullback j)) (by simpa using hlen') (by
          intro L hL
          obtain ⟨M, hM, rfl⟩ := List.mem_map.mp hL
          exact LineBundle.IsAmple.pullback_closedImmersion M (hamp M (by simp [hM])) j)
      have hrestrict := mixedTop_cartier_restriction p H hH d
        (by simpa only [Nat.cast_add, Nat.cast_one] using hdim.le)
        (A.pow n) s ls hlen'
      have hdeg : MixedDegreeLE (d+1) (lineEuler p (d+1)) :=
        mixedDifference_lineEuler_of_ample p H hH (d+1) hdim.le
      have hscale := congrFun (mixedDifference_pow_cons_of_degree
        (lineEuler_isoInvariant p (d+1)) hdeg A n ls (by omega)) (structureLineBundle X)
      have he : mixedTop (lineEuler p (d+1)) (A.pow n :: ls) =
          (n : ℤ) * mixedTop (lineEuler p (d+1)) (A :: ls) := by
        simpa only [Pi.smul_apply, nsmul_eq_mul, mixedTop, Pi.mul_apply, Pi.natCast_apply] using hscale
      have hmul : 0 < (n : ℤ) * mixedTop (lineEuler p (d+1)) (A :: ls) := by
        rw [← he, hrestrict]
        exact hpos
      exact (mul_pos_iff_of_pos_left (by exact_mod_cast hn : (0 : ℤ) < n)).mp hmul

theorem mixedTop_pos_of_ample {X : Scheme.{0}} [IsNoetherian X] [Nonempty X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (H : LineBundle X) (hH : H.IsAmple) (d : ℕ)
    (hdim : topologicalKrullDim X = d)
    (ls : List (LineBundle X)) (hlen : ls.length = d) (hamp : ∀ L ∈ ls, L.IsAmple) :
    0 < mixedTop (lineEuler p d) ls :=
  mixedTop_pos_of_ample_aux d p H hH hdim ls hlen hamp

theorem topEuler_pos_of_ample {X : Scheme.{0}} [IsNoetherian X] [Nonempty X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (A : LineBundle X) (hA : A.IsAmple) (d : ℕ)
    (hdim : topologicalKrullDim X = d) :
    0 < (fwdDiff (1 : ℕ))^[d] (fun n => eulerCharacteristic p d (A.pow n).sheaf) 0 := by
  have h := mixedTop_pos_of_ample p A hA d hdim (List.replicate d A) (by simp)
    (by intro L hL; obtain ⟨_, rfl⟩ := List.mem_replicate.mp hL; exact hA)
  rwa [mixedTop_replicate A _ (lineEuler_isoInvariant p d) d] at h

end
end PiExponent.NumericalAmpleness

end OAI
