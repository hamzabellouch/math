import OAI.NumberTheory.PiExponent.Ampleness.ClosedAmpleRestriction
import OAI.NumberTheory.PiExponent.Ampleness.LineAmpleOperations
import OAI.NumberTheory.PiExponent.Ampleness.ZeroDimensionalAmple
import OAI.NumberTheory.PiExponent.Approximation.GeneratorsSectionCover
import OAI.NumberTheory.PiExponent.Approximation.RegularSectionChoice
import OAI.NumberTheory.PiExponent.Cohomology.CartierMixedEuler
import OAI.NumberTheory.PiExponent.Cohomology.EulerSupportDimension
import OAI.NumberTheory.PiExponent.Cohomology.EulerZeroDimensional
import OAI.NumberTheory.PiExponent.Cohomology.NoetherianAmpleSerreVanishing

namespace OAI

namespace PiExponent.NumericalAmpleness
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open PiExponentSeshadri.Geometry
open PiExponent.SectionZeroIdeal

theorem lineBundle_cohomology_zero_of_dimension_le (d : ℕ) :
    ∀ {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
      (H : LineBundle X), H.IsAmple → ∀ (M : LineBundle X),
      topologicalKrullDim X ≤ d → ∀ q : ℕ, d < q →
      ∀ z : cohomology M.sheaf q, z = 0 := by
  induction d with
  | zero =>
    intro X p hp H hH M hdim q hq
    let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
    let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
    let : IsNoetherian X := {}
    let : Finite X := finite_of_dim_le_zero hdim
    let : IsAffine X := proper_finite_scheme_isAffine p
    let := PiExponent.GeometrySupport.LineBundleCoherent.lineBundle_isFinitePresentation M
    let : M.sheaf.IsQuasicoherent :=
      (SheafOfModules.IsFinitePresentation.exists_quasicoherentData M.sheaf).choose.isQuasicoherent
    obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hq)
    exact PiExponentSeshadri.AffineSchemeCohomology.affine_ext_zero X M.sheaf k
  | succ d ih =>
    intro X p hp H hH M hdim q hq
    let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
    let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
    let : IsNoetherian X := {}
    obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : q ≠ 0)
    have hk : d < k := by omega
    obtain ⟨N,hN⟩ := GeneratorsSectionCover.ample_eventual_fin_section_cover H hH
    let a := N+1
    obtain ⟨l,t,ht⟩ := hN a (by omega)
    let A := H.pow a
    have hA : A.IsAmple := hH.pow a (by omega)
    obtain ⟨s,hs⟩ := exists_mono_section_of_finite_cover p A t ht
    let : Mono s := hs
    let i := (zeroIdeal A s).subschemeι
    have hdimD : topologicalKrullDim (zeroIdeal A s).subscheme ≤ d :=
      regular_sectionZero_dimension_le A s d (by simpa only [Nat.cast_add,Nat.cast_one] using hdim)
    let F : ℕ → X.Modules := fun n => ((A.pow n).tensor M).sheaf
    let Q : ℕ → X.Modules := fun n => (Scheme.Modules.pushforward i).obj
      ((Scheme.Modules.pullback i).obj ((A.pow (n+1)).tensor M).sheaf)
    have hQ (n j : ℕ) (hj : d < j) : ∀ z : cohomology (Q n) j, z = 0 := by
      have hD := ih (i ≫ p) (H.pullback i) (hH.pullback_closedImmersion H i)
        ((((A.pow (n+1)).tensor M).pullback i)) hdimD j hj
      let e := ClosedImmersionSerreTransfer.cohomologyLinearEquiv i p
        ((Scheme.Modules.pullback i).obj ((A.pow (n+1)).tensor M).sheaf) j
      intro z
      obtain ⟨w,rfl⟩ := e.surjective z
      exact (congrArg e (hD w)).trans e.map_zero
    have hstep (n : ℕ) : Function.Bijective
        (cohomologyMap p (mixedCartierPowerMultiply A M s n) (k+1)) := by
      obtain ⟨hz,hS⟩ := regular_mixedCartierPower_restriction_shortExact p A M s n
      exact cohomologyMap_bijective_of_quotient_vanishing p _ hS k
        (hQ n k hk) (hQ n (k+1) (by omega))
    let := PiExponent.GeometrySupport.LineBundleCoherent.lineBundle_isFinitePresentation M
    obtain ⟨K,hK⟩ := GeometrySupport.NoetherianAmpleSerreVanishing.ample_serre_tensor_vanishing
      p A hA M.sheaf
    have hzeroK : ∀ z : cohomology (F K) (k+1), z = 0 :=
      GeometrySupport.SerrePowerDescent.ext_zero_of_iso
        (moduleTensorComm M.sheaf (A.pow K).sheaf) (k+1) (hK K le_rfl (k+1) (by omega))
    have hback : ∀ n : ℕ, (∀ z : cohomology (F n) (k+1), z = 0) →
        ∀ z : cohomology (F 0) (k+1), z = 0 := by
      intro n
      induction n with
      | zero => exact fun h => h
      | succ n ihn =>
        intro hn
        apply ihn
        intro z
        apply (hstep n).injective
        rw [map_zero]
        exact hn _
    exact GeometrySupport.SerrePowerDescent.ext_zero_of_iso (moduleTensorUnit M.sheaf)
      (k+1) (hback K hzeroK)

end
end PiExponent.NumericalAmpleness

end OAI
