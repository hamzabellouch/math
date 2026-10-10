import OAI.NumberTheory.PiExponent.Geometry.LineBundleProduct
import OAI.NumberTheory.PiExponent.Geometry.SectionCartierRegular

namespace OAI

namespace PiExponent.NumericalAmpleness
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
open PiExponent.SectionZeroIdeal PiExponent.CartierPowerFrames
variable {X : Scheme.{0}}

private lemma framed_map {C : Type*} [Category C] {A B P Q T O : C}
    (r : A ≅ P) (r' : B ≅ Q) (e : P ≅ T) (e' : Q ≅ T) (u : T ≅ O)
    (m : A ⟶ B) (p : P ⟶ Q) (b : T ⟶ T) (a : O ⟶ O)
    (hn : m ≫ r'.hom = r.hom ≫ p) (ht : p ≫ e'.hom = e.hom ≫ b)
    (hs : b ≫ u.hom = u.hom ≫ a) :
    (r ≪≫ e ≪≫ u).inv ≫ m ≫ (r' ≪≫ e' ≪≫ u).hom = a := by
  simp only [Iso.trans_hom, Iso.trans_inv, Category.assoc]
  rw [← Category.assoc m r'.hom, hn]
  simp only [Category.assoc]
  rw [← Category.assoc p e'.hom, ht]
  simp only [Category.assoc]
  rw [hs]
  simp

lemma tensorMap_framed (A B M : X.Modules) (φ : A ⟶ B) (U : X.Opens)
    (e : A.restrict U.ι ≅ O U.toScheme)
    (e' : B.restrict U.ι ≅ O U.toScheme)
    (f : M.restrict U.ι ≅ O U.toScheme) :
    (tensorFrame A M U e f).inv ≫
      (Scheme.Modules.restrictFunctor U.ι).map (moduleTensorMap φ (𝟙 M)) ≫
        (tensorFrame B M U e' f).hom =
      e.inv ≫ (Scheme.Modules.restrictFunctor U.ι).map φ ≫ e'.hom := by
  let F := Scheme.Modules.restrictFunctor U.ι
  let R := moduleTensorRestrict U A M
  let R' := moduleTensorRestrict U B M
  let E := moduleTensorIso e f
  let E' := moduleTensorIso e' f
  let T := moduleTensorUnit (O U.toScheme)
  let c := e.inv ≫ F.map φ ≫ e'.hom
  let p := moduleTensorMap (F.map φ) (𝟙 (M.restrict U.ι))
  have he : F.map φ ≫ e'.hom = e.hom ≫ c := by
    simp [c]
  have hn : F.map (moduleTensorMap φ (𝟙 M)) ≫ R'.hom = R.hom ≫ p :=
    (moduleTensorRestrict_natural U φ (𝟙 M)).trans
      (congrArg (fun q => R.hom ≫ moduleTensorMap (F.map φ) q) (F.map_id M))
  have h₁ := (moduleTensorMap_comp (F.map φ) e'.hom (𝟙 (M.restrict U.ι)) f.hom).symm.trans
    (congrArg (moduleTensorMap (F.map φ ≫ e'.hom)) (Category.id_comp f.hom))
  have h₂ := (moduleTensorMap_comp e.hom c f.hom (𝟙 (O U.toScheme))).symm.trans
    (congrArg (moduleTensorMap (e.hom ≫ c)) (Category.comp_id f.hom))
  have ht : p ≫ E'.hom = E.hom ≫ moduleTensorMap c (𝟙 (O U.toScheme)) :=
    h₁.trans ((congrArg (fun q : F.obj A ⟶ O U.toScheme => moduleTensorMap q f.hom)
      he).trans h₂.symm)
  have hs : moduleTensorMap c (𝟙 (O U.toScheme)) ≫ T.hom = T.hom ≫ c :=
    (moduleTensorUnit_scalar (X := U.toScheme) c (𝟙 (O U.toScheme))).trans
      (congrArg (fun q => T.hom ≫ q) (Category.comp_id c))
  simpa only [tensorFrame] using!
    framed_map R R' E E' T (F.map (moduleTensorMap φ (𝟙 M))) p _ c hn ht hs

def mixedCartierPowerMultiply (L M : LineBundle X)
    (s : GlobalSections X L.sheaf) (n : ℕ) :
    ((L.pow n).tensor M).sheaf ⟶ ((L.pow (n+1)).tensor M).sheaf :=
  moduleTensorMap (cartierPowerMultiply L s n) (𝟙 M.sheaf)

theorem mixedCartierPowerMultiply_mono (L M : LineBundle X)
    (s : GlobalSections X L.sheaf) [Mono s] (n : ℕ) :
    Mono (mixedCartierPowerMultiply L M s n) := by
  let := cartierPowerMultiply_mono_of_mono L s n
  exact moduleTensorMap_mono (cartierPowerMultiply L s n) M

theorem mixedCartierPower_zeroIdeal_frames (L M : LineBundle X)
    (s : GlobalSections X L.sheaf) (n : ℕ) :
    ∀ x : X, ∃ U : X.affineOpens, x ∈ U.1 ∧
      ∃ e : ((L.pow n).tensor M).sheaf.restrict U.1.ι ≅ O U.1.toScheme,
      ∃ e' : ((L.pow (n+1)).tensor M).sheaf.restrict U.1.ι ≅ O U.1.toScheme,
        (zeroIdeal L s).ideal U = Ideal.span {U.1.topIso.hom
          (endValue (e.inv ≫ (Scheme.Modules.restrictFunctor U.1.ι).map
            (mixedCartierPowerMultiply L M s n) ≫ e'.hom))} := by
  intro x
  obtain ⟨U, hx, ⟨e⟩, ⟨f⟩⟩ := common_affine_frames L M x
  refine ⟨U, hx,
    tensorFrame (L.pow n).sheaf M.sheaf U.1 (modulePowFrame U.1 e n) f,
    tensorFrame (L.pow (n+1)).sheaf M.sheaf U.1 (modulePowFrame U.1 e (n+1)) f, ?_⟩
  simp only [mixedCartierPowerMultiply]
  have hframe := tensorMap_framed (L.pow n).sheaf (L.pow (n+1)).sheaf M.sheaf
    (cartierPowerMultiply L s n) U.1 (modulePowFrame U.1 e n)
    (modulePowFrame U.1 e (n+1)) f
  exact ((zeroIdeal_on_frame L s U e).trans (cartierPowerMultiply_ideal L s n U e).symm).trans
    (congrArg (fun g : O U.1.toScheme ⟶ O U.1.toScheme =>
      Ideal.span {U.1.topIso.hom (endValue g)}) hframe.symm)

theorem regular_mixedCartierPower_restriction_shortExact
    (p : X ⟶ Spec (CommRingCat.of ℂ)) (L M : LineBundle X)
    (s : GlobalSections X L.sheaf) [Mono s] (n : ℕ) :
    ∃ hz : mixedCartierPowerMultiply L M s n ≫
        PiExponentSeshadri.LineClosedUnit.map (zeroIdeal L s).subschemeι ((L.pow (n+1)).tensor M) = 0,
      (ShortComplex.mk (mixedCartierPowerMultiply L M s n)
        (PiExponentSeshadri.LineClosedUnit.map (zeroIdeal L s).subschemeι
          ((L.pow (n+1)).tensor M)) hz).ShortExact := by
  let := mixedCartierPowerMultiply_mono L M s n
  exact PiExponentSeshadri.CartierSequence.exact p ((L.pow n).tensor M) ((L.pow (n+1)).tensor M)
    (mixedCartierPowerMultiply L M s n) (zeroIdeal L s)
    (mixedCartierPower_zeroIdeal_frames L M s n)

theorem regular_mixedCartierPower_euler_difference_same_truncation
    (p : X ⟶ Spec (CommRingCat.of ℂ)) (L M : LineBundle X)
    (s : GlobalSections X L.sheaf) [Mono s] (n d : ℕ)
    (hfiniteSource : ∀ q ≤ d,
      letI := Module.compHom (cohomology ((L.pow n).tensor M).sheaf q) (baseScalars p)
      FiniteDimensional ℂ (cohomology ((L.pow n).tensor M).sheaf q))
    (hfiniteTarget : ∀ q ≤ d,
      letI := Module.compHom (cohomology ((L.pow (n+1)).tensor M).sheaf q) (baseScalars p)
      FiniteDimensional ℂ (cohomology ((L.pow (n+1)).tensor M).sheaf q))
    (hfiniteRestricted : ∀ q ≤ d,
      letI := Module.compHom
        (cohomology ((Scheme.Modules.pullback (zeroIdeal L s).subschemeι).obj
          ((L.pow (n+1)).tensor M).sheaf) q)
        (baseScalars ((zeroIdeal L s).subschemeι ≫ p))
      FiniteDimensional ℂ
        (cohomology ((Scheme.Modules.pullback (zeroIdeal L s).subschemeι).obj
          ((L.pow (n+1)).tensor M).sheaf) q))
    (hzeroSource : ∀ z : cohomology ((L.pow n).tensor M).sheaf (d+1), z = 0) :
    eulerCharacteristic p d ((L.pow (n+1)).tensor M).sheaf -
        eulerCharacteristic p d ((L.pow n).tensor M).sheaf =
      eulerCharacteristic ((zeroIdeal L s).subschemeι ≫ p) d
        ((Scheme.Modules.pullback (zeroIdeal L s).subschemeι).obj
          ((L.pow (n+1)).tensor M).sheaf) := by
  obtain ⟨hz, hS⟩ := regular_mixedCartierPower_restriction_shortExact p L M s n
  let I := zeroIdeal L s
  let N := ((L.pow (n+1)).tensor M).sheaf
  let R := (Scheme.Modules.pullback I.subschemeι).obj N
  let : Subsingleton (cohomology ((L.pow n).tensor M).sheaf (d+1)) :=
    ⟨fun a b => (hzeroSource a).trans (hzeroSource b).symm⟩
  have hfinitePushforward (q : ℕ) (hq : q ≤ d) :
      letI := Module.compHom
        (cohomology ((Scheme.Modules.pushforward I.subschemeι).obj R) q) (baseScalars p)
      FiniteDimensional ℂ
        (cohomology ((Scheme.Modules.pushforward I.subschemeι).obj R) q) := by
    let := Module.compHom (cohomology R q) (baseScalars (I.subschemeι ≫ p))
    let := Module.compHom
      (cohomology ((Scheme.Modules.pushforward I.subschemeι).obj R) q) (baseScalars p)
    let := hfiniteRestricted q hq
    let e := PiExponent.ClosedImmersionSerreTransfer.cohomologyLinearEquiv I.subschemeι p R q
    exact FiniteDimensional.of_surjective e.toLinearMap e.surjective
  have hEuler := eulerCharacteristic_add p hS d hfiniteSource hfiniteTarget hfinitePushforward
  change eulerCharacteristic p d N =
    eulerCharacteristic p d ((L.pow n).tensor M).sheaf +
      eulerCharacteristic p d ((Scheme.Modules.pushforward I.subschemeι).obj R) at hEuler
  rw [PiExponent.ClosedImmersionSerreTransfer.euler_pushforward] at hEuler
  exact sub_eq_iff_eq_add.mpr (by simpa only [add_comm] using hEuler)

theorem regular_mixedCartierPower_euler_difference
    (p : X ⟶ Spec (CommRingCat.of ℂ)) (L M : LineBundle X)
    (s : GlobalSections X L.sheaf) [Mono s] (n d : ℕ)
    (hfiniteSource : ∀ q ≤ d,
      letI := Module.compHom (cohomology ((L.pow n).tensor M).sheaf q) (baseScalars p)
      FiniteDimensional ℂ (cohomology ((L.pow n).tensor M).sheaf q))
    (hfiniteTarget : ∀ q ≤ d,
      letI := Module.compHom (cohomology ((L.pow (n+1)).tensor M).sheaf q) (baseScalars p)
      FiniteDimensional ℂ (cohomology ((L.pow (n+1)).tensor M).sheaf q))
    (hfiniteRestricted : ∀ q ≤ d,
      letI := Module.compHom
        (cohomology ((Scheme.Modules.pullback (zeroIdeal L s).subschemeι).obj
          ((L.pow (n+1)).tensor M).sheaf) q)
        (baseScalars ((zeroIdeal L s).subschemeι ≫ p))
      FiniteDimensional ℂ
        (cohomology ((Scheme.Modules.pullback (zeroIdeal L s).subschemeι).obj
          ((L.pow (n+1)).tensor M).sheaf) q))
    (hzeroSource : ∀ z : cohomology ((L.pow n).tensor M).sheaf (d+1), z = 0)
    (hzeroRestricted : ∀ z :
      cohomology ((Scheme.Modules.pullback (zeroIdeal L s).subschemeι).obj
        ((L.pow (n+1)).tensor M).sheaf) d, z = 0) :
    eulerCharacteristic p d ((L.pow (n+1)).tensor M).sheaf -
        eulerCharacteristic p d ((L.pow n).tensor M).sheaf =
      eulerCharacteristic ((zeroIdeal L s).subschemeι ≫ p) (d-1)
        ((Scheme.Modules.pullback (zeroIdeal L s).subschemeι).obj
          ((L.pow (n+1)).tensor M).sheaf) := by
  let := mixedCartierPowerMultiply_mono L M s n
  exact cartier_euler_difference p ((L.pow n).tensor M) ((L.pow (n+1)).tensor M)
    (mixedCartierPowerMultiply L M s n) (zeroIdeal L s)
    (mixedCartierPower_zeroIdeal_frames L M s n) d hfiniteSource hfiniteTarget
    hfiniteRestricted hzeroSource hzeroRestricted

end
end PiExponent.NumericalAmpleness

end OAI
