import OAI.NumberTheory.PiExponent.Approximation.LinePowerLaws
import OAI.NumberTheory.PiExponent.Cohomology.CartierMixedEuler

namespace OAI

namespace PiExponent.NumericalAmpleness
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
open PiExponent.SectionZeroIdeal PiExponent.CartierPowerFrames
variable {X : Scheme.{0}}

theorem regular_tensorSection_restriction_shortExact
    (p : X ⟶ Spec (CommRingCat.of ℂ)) (A F : LineBundle X)
    (s : GlobalSections X A.sheaf) [Mono s] :
    ∃ hz : sectionMultiplyLeft A.sheaf F.sheaf s ≫
        PiExponentSeshadri.LineClosedUnit.map (zeroIdeal A s).subschemeι (A.tensor F) = 0,
      (ShortComplex.mk (sectionMultiplyLeft A.sheaf F.sheaf s)
        (PiExponentSeshadri.LineClosedUnit.map (zeroIdeal A s).subschemeι (A.tensor F)) hz).ShortExact := by
  let : Mono (moduleTensorMap s (𝟙 F.sheaf)) := moduleTensorMap_mono s F
  have hm : Mono (sectionMultiplyLeft A.sheaf F.sheaf s) := mono_comp _ _
  refine @PiExponentSeshadri.CartierSequence.exact X p F (A.tensor F)
    (sectionMultiplyLeft A.sheaf F.sheaf s) hm (zeroIdeal A s) ?_
  intro x
  obtain ⟨U, hx, ⟨a⟩, ⟨f⟩⟩ := common_affine_frames A F x
  refine ⟨U, hx, f, tensorFrame A.sheaf F.sheaf U.1 a f, ?_⟩
  exact (zeroIdeal_on_frame A s U a).trans
    (tensor_multiply_ideal A.sheaf F.sheaf s U a f).symm

def tensorSectionComplex (p : X ⟶ Spec (CommRingCat.of ℂ)) (A F : LineBundle X)
    (s : GlobalSections X A.sheaf) [Mono s] : ShortComplex X.Modules :=
  ShortComplex.mk (sectionMultiplyLeft A.sheaf F.sheaf s)
    (PiExponentSeshadri.LineClosedUnit.map (zeroIdeal A s).subschemeι (A.tensor F))
    (regular_tensorSection_restriction_shortExact p A F s).choose

theorem tensorSectionComplex_shortExact (p : X ⟶ Spec (CommRingCat.of ℂ))
    (A F : LineBundle X) (s : GlobalSections X A.sheaf) [Mono s] :
    (tensorSectionComplex p A F s).ShortExact :=
  (regular_tensorSection_restriction_shortExact p A F s).choose_spec

namespace CartierEulerPair

def source (L M : LineBundle X) (n : ℕ) : LineBundle X := (L.pow n).tensor M

def middle (L B M : LineBundle X) (n : ℕ) : LineBundle X :=
  (L.tensor B).tensor (source L M n)

def middleIso (L B M : LineBundle X) (n : ℕ) :
    (middle L B M n).sheaf ≅ (B.tensor (source L M (n+1))).sheaf :=
  moduleTensorIso (moduleTensorComm L.sheaf B.sheaf) (Iso.refl (source L M n).sheaf) ≪≫
    lineTensorAssoc B L (source L M n) ≪≫
    moduleTensorIso (Iso.refl B.sheaf) (lineTensorAssoc L (L.pow n) M).symm

def leftComplex (p : X ⟶ Spec (CommRingCat.of ℂ)) (L B M : LineBundle X)
    (s : GlobalSections X (L.tensor B).sheaf) [Mono s] (n : ℕ) : ShortComplex X.Modules :=
  tensorSectionComplex p (L.tensor B) (source L M n) s

def rightComplex (p : X ⟶ Spec (CommRingCat.of ℂ)) (L B M : LineBundle X)
    (t : GlobalSections X B.sheaf) [Mono t] (n : ℕ) : ShortComplex X.Modules :=
  let T := tensorSectionComplex p B (source L M (n+1)) t
  ShortComplex.mk (T.f ≫ (middleIso L B M n).inv)
    ((middleIso L B M n).hom ≫ T.g) (by
      exact (Category.assoc T.f (middleIso L B M n).inv
        ((middleIso L B M n).hom ≫ T.g)).trans
        ((congrArg (fun q => T.f ≫ q) ((middleIso L B M n).inv_hom_id_assoc T.g)).trans
          T.zero))

private lemma iso_middle_comm {C : Type*} [Category C] {A B D : C}
    (f : A ⟶ B) (e : D ≅ B) : 𝟙 A ≫ f = (f ≫ e.inv) ≫ e.hom := by
  simp

def rightComplexIso (p : X ⟶ Spec (CommRingCat.of ℂ)) (L B M : LineBundle X)
    (t : GlobalSections X B.sheaf) [Mono t] (n : ℕ) :
    rightComplex p L B M t n ≅ tensorSectionComplex p B (source L M (n+1)) t :=
  ShortComplex.isoMk (Iso.refl _) (middleIso L B M n) (Iso.refl _)
    (by simpa only [rightComplex] using!
      iso_middle_comm (tensorSectionComplex p B (source L M (n+1)) t).f (middleIso L B M n))
    (by simpa only [rightComplex] using!
      (Category.comp_id ((middleIso L B M n).hom ≫
        (tensorSectionComplex p B (source L M (n+1)) t).g)).symm)

theorem left_shortExact (p : X ⟶ Spec (CommRingCat.of ℂ)) (L B M : LineBundle X)
    (s : GlobalSections X (L.tensor B).sheaf) [Mono s] (n : ℕ) :
    (leftComplex p L B M s n).ShortExact :=
  tensorSectionComplex_shortExact p (L.tensor B) (source L M n) s

theorem right_shortExact (p : X ⟶ Spec (CommRingCat.of ℂ)) (L B M : LineBundle X)
    (t : GlobalSections X B.sheaf) [Mono t] (n : ℕ) :
    (rightComplex p L B M t n).ShortExact :=
  ShortComplex.shortExact_of_iso (rightComplexIso p L B M t n).symm
    (tensorSectionComplex_shortExact p B (source L M (n+1)) t)

abbrev FiniteThrough (p : X ⟶ Spec (CommRingCat.of ℂ)) (N : X.Modules) (d : ℕ) : Prop :=
  ∀ q ≤ d, letI := Module.compHom (cohomology N q) (baseScalars p)
    FiniteDimensional ℂ (cohomology N q)

theorem finiteThrough_closedPushforward {Y : Scheme.{0}} (f : Y ⟶ X)
    [IsClosedImmersion f] (p : X ⟶ Spec (CommRingCat.of ℂ)) (N : Y.Modules) (d : ℕ)
    (hfinite : FiniteThrough (f ≫ p) N d) :
    FiniteThrough p ((Scheme.Modules.pushforward f).obj N) d := by
  intro q hq
  let := Module.compHom (cohomology N q) (baseScalars (f ≫ p))
  let := Module.compHom
    (cohomology ((Scheme.Modules.pushforward f).obj N) q) (baseScalars p)
  let := hfinite q hq
  let e := PiExponent.ClosedImmersionSerreTransfer.cohomologyLinearEquiv f p N q
  exact FiniteDimensional.of_surjective e.toLinearMap e.surjective

theorem euler_difference (p : X ⟶ Spec (CommRingCat.of ℂ)) (L B M : LineBundle X)
    (s : GlobalSections X (L.tensor B).sheaf) (t : GlobalSections X B.sheaf)
    [Mono s] [Mono t] (n d : ℕ)
    (hfinitePrev : FiniteThrough p (source L M n).sheaf d)
    (hfiniteNext : FiniteThrough p (source L M (n+1)).sheaf d)
    (hfiniteMiddle : FiniteThrough p (middle L B M n).sheaf d)
    (hfiniteD : FiniteThrough ((zeroIdeal (L.tensor B) s).subschemeι ≫ p)
      ((Scheme.Modules.pullback (zeroIdeal (L.tensor B) s).subschemeι).obj
        (middle L B M n).sheaf) d)
    (hfiniteE : FiniteThrough ((zeroIdeal B t).subschemeι ≫ p)
      ((Scheme.Modules.pullback (zeroIdeal B t).subschemeι).obj
        (B.tensor (source L M (n+1))).sheaf) d)
    (hzeroPrev : ∀ z : cohomology (source L M n).sheaf (d+1), z = 0)
    (hzeroNext : ∀ z : cohomology (source L M (n+1)).sheaf (d+1), z = 0) :
    eulerCharacteristic p d (source L M (n+1)).sheaf -
        eulerCharacteristic p d (source L M n).sheaf =
      eulerCharacteristic ((zeroIdeal (L.tensor B) s).subschemeι ≫ p) d
        ((Scheme.Modules.pullback (zeroIdeal (L.tensor B) s).subschemeι).obj
          (middle L B M n).sheaf) -
      eulerCharacteristic ((zeroIdeal B t).subschemeι ≫ p) d
        ((Scheme.Modules.pullback (zeroIdeal B t).subschemeι).obj
          (B.tensor (source L M (n+1))).sheaf) := by
  let D := zeroIdeal (L.tensor B) s
  let E := zeroIdeal B t
  let Q := (Scheme.Modules.pullback D.subschemeι).obj (middle L B M n).sheaf
  let R := (Scheme.Modules.pullback E.subschemeι).obj (B.tensor (source L M (n+1))).sheaf
  let : Subsingleton (cohomology (leftComplex p L B M s n).X₁ (d+1)) :=
    ⟨fun a b => (hzeroPrev a).trans (hzeroPrev b).symm⟩
  let : Subsingleton (cohomology (rightComplex p L B M t n).X₁ (d+1)) :=
    ⟨fun a b => (hzeroNext a).trans (hzeroNext b).symm⟩
  have hleft := eulerCharacteristic_add p (left_shortExact p L B M s n) d
    hfinitePrev hfiniteMiddle (finiteThrough_closedPushforward D.subschemeι p Q d hfiniteD)
  have hright := eulerCharacteristic_add p (right_shortExact p L B M t n) d
    hfiniteNext hfiniteMiddle (finiteThrough_closedPushforward E.subschemeι p R d hfiniteE)
  change eulerCharacteristic p d (middle L B M n).sheaf =
    eulerCharacteristic p d (source L M n).sheaf +
      eulerCharacteristic p d ((Scheme.Modules.pushforward D.subschemeι).obj Q) at hleft
  change eulerCharacteristic p d (middle L B M n).sheaf =
    eulerCharacteristic p d (source L M (n+1)).sheaf +
      eulerCharacteristic p d ((Scheme.Modules.pushforward E.subschemeι).obj R) at hright
  rw [PiExponent.ClosedImmersionSerreTransfer.euler_pushforward] at hleft hright
  change eulerCharacteristic p d (source L M (n+1)).sheaf -
    eulerCharacteristic p d (source L M n).sheaf =
      eulerCharacteristic (D.subschemeι ≫ p) d Q - eulerCharacteristic (E.subschemeι ≫ p) d R
  omega

end CartierEulerPair
end
end PiExponent.NumericalAmpleness

end OAI
