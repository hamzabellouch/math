import OAI.NumberTheory.PiExponent.Cohomology.CartierEulerPair
import OAI.NumberTheory.PiExponent.Cohomology.EulerTwistTransport
import OAI.NumberTheory.PiExponent.Cohomology.NakaiEulerGrowth
import OAI.NumberTheory.PiExponent.Cohomology.NoetherianAmpleSerreVanishing

namespace OAI

namespace PiExponent.NumericalAmpleness
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Filter
open PiExponentSeshadri.Geometry
open PiExponent.SectionZeroIdeal
variable {X Y : Scheme.{0}}
attribute [local irreducible] CartierEulerPair.middleIso lineTensorAssoc moduleTensorComm
  pullbackCartierMiddleIso

theorem eventual_closed_cartierMiddle_cohomology_zero
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (f : Y ⟶ X) [IsClosedImmersion f] (A L M : LineBundle X)
    (hL : (L.pullback f).IsAmple) :
    ∃ N, ∀ n, N ≤ n → ∀ q, 0 < q → ∀ z : cohomology
      ((Scheme.Modules.pushforward f).obj
        ((Scheme.Modules.pullback f).obj (A.tensor ((L.pow n).tensor M)).sheaf)) q, z = 0 := by
  let T := (A.pullback f).tensor (M.pullback f)
  let := PiExponent.GeometrySupport.LineBundleCoherent.lineBundle_isFinitePresentation T
  obtain ⟨N,hN⟩ := GeometrySupport.NoetherianAmpleSerreVanishing.ample_serre_tensor_vanishing
    (f ≫ p) (L.pullback f) hL T.sheaf
  refine ⟨N,fun n hn q hq => ?_⟩
  apply (ClosedImmersionSerreTransfer.ext_zero_iff f
    ((Scheme.Modules.pullback f).obj (A.tensor ((L.pow n).tensor M)).sheaf) q).mp
  let e := pullbackCartierMiddleIso f A L M n ≪≫
    moduleTensorComm ((L.pullback f).pow n).sheaf T.sheaf
  exact GeometrySupport.SerrePowerDescent.ext_zero_of_iso e.symm q (hN n hn q hq)

theorem eventual_mixedPower_cohomology_stationary
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (L B M : LineBundle X)
    (s : GlobalSections X (L.tensor B).sheaf) (t : GlobalSections X B.sheaf)
    [Mono s] [Mono t]
    (hD : (L.pullback (zeroIdeal (L.tensor B) s).subschemeι).IsAmple)
    (hE : (L.pullback (zeroIdeal B t).subschemeι).IsAmple)
    (q : ℕ) (hq : 0 < q) :
    ∃ N, ∀ n, N ≤ n →
      cohomologyDimension p ((L.pow n).tensor M).sheaf (q+1) =
        cohomologyDimension p ((L.pow N).tensor M).sheaf (q+1) := by
  obtain ⟨D,hDN⟩ := eventual_closed_cartierMiddle_cohomology_zero p
    (zeroIdeal (L.tensor B) s).subschemeι (L.tensor B) L M hD
  obtain ⟨E,hEN⟩ := eventual_closed_cartierMiddle_cohomology_zero p
    (zeroIdeal B t).subschemeι B L M hE
  let N := max D E
  have hstep (n : ℕ) (hn : N ≤ n) :
      cohomologyDimension p ((L.pow n).tensor M).sheaf (q+1) =
        cohomologyDimension p ((L.pow (n+1)).tensor M).sheaf (q+1) := by
    have hnD : D ≤ n := (le_max_left D E).trans hn
    have hnE : E ≤ n+1 := (le_max_right D E).trans (hn.trans (Nat.le_succ n))
    have hleft := cohomologyDimension_eq_of_quotient_vanishing p
      (CartierEulerPair.leftComplex p L B M s n)
      (CartierEulerPair.left_shortExact p L B M s n) q
      (hDN n hnD q hq) (hDN n hnD (q+1) (by omega))
    have hright := cohomologyDimension_eq_of_quotient_vanishing p
      (CartierEulerPair.rightComplex p L B M t n)
      (CartierEulerPair.right_shortExact p L B M t n) q
      (hEN (n+1) hnE q hq) (hEN (n+1) hnE (q+1) (by omega))
    exact hleft.trans hright.symm
  refine ⟨N,fun n hn => ?_⟩
  obtain ⟨j,rfl⟩ := Nat.exists_eq_add_of_le hn
  induction j with
  | zero => simp
  | succ j ih =>
    exact (hstep (N+j) (by omega)).symm.trans (ih (by omega))

theorem eventually_nonzero_mixedPower_sections_of_growth
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (L B M : LineBundle X)
    (s : GlobalSections X (L.tensor B).sheaf) (t : GlobalSections X B.sheaf)
    [Mono s] [Mono t]
    (hD : (L.pullback (zeroIdeal (L.tensor B) s).subschemeι).IsAmple)
    (hE : (L.pullback (zeroIdeal B t).subschemeι).IsAmple)
    (d : ℕ) (hd : 1 ≤ d)
    (hgrowth : Tendsto (fun n => eulerCharacteristic p d ((L.pow n).tensor M).sheaf) atTop atTop) :
    ∀ᶠ n in atTop, ∃ s : GlobalSections X ((L.pow n).tensor M).sheaf, s ≠ 0 := by
  apply eventually_nonzero_globalSection_of_eventually_stationary p
    (fun n => ((L.pow n).tensor M).sheaf) d hd hgrowth
  intro j hj hjd
  obtain ⟨q,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
  exact eventual_mixedPower_cohomology_stationary p L B M s t hD hE q (by omega)

end
end PiExponent.NumericalAmpleness

end OAI
