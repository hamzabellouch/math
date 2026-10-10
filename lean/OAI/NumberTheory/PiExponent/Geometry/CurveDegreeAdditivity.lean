import OAI.NumberTheory.PiExponent.Ampleness.ClosedAmpleRestriction
import OAI.NumberTheory.PiExponent.Approximation.NumericalMarginRestriction
import OAI.NumberTheory.PiExponent.Geometry.CartierDegreeLength
import OAI.NumberTheory.PiExponent.Geometry.CartierPowerFrames
import OAI.NumberTheory.PiExponent.Geometry.CurveEffectiveTwist
import OAI.NumberTheory.PiExponent.LocalAlgebra.SectionZeroIdeal

namespace OAI

namespace PiExponent.CurveDegree
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
open PiExponent.SectionZeroIdeal PiExponent.CartierPowerFrames
variable {X : Scheme.{0}}

def FiniteLineCohomology (p : X ⟶ Spec (CommRingCat.of ℂ)) : Prop :=
  ∀ L : LineBundle X, ∀ n ≤ 1,
    let := Module.compHom (cohomology L.sheaf n) (baseScalars p)
    FiniteDimensional ℂ (cohomology L.sheaf n)

def LineCohomologyTwoZero (X : Scheme.{0}) : Prop :=
  ∀ L : LineBundle X, Subsingleton (cohomology L.sheaf 2)

theorem section_tensor_euler_add [IsIntegral X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (hd : topologicalKrullDim X ≤ 1)
    (hfinite : FiniteLineCohomology p) (hH2 : LineCohomologyTwoZero X)
    (L M : LineBundle X) (s : GlobalSections X L.sheaf) (hs : s ≠ 0) :
    eulerCharacteristic p 1 (L.tensor M).sheaf - eulerCharacteristic p 1 M.sheaf =
      eulerCharacteristic p 1 L.sheaf - eulerCharacteristic p 1 (structureSheaf X) := by
  let hsMono : Mono s := L.mono_section s hs
  let I := zeroIdeal L s
  have hI : I ≠ ⊥ := zeroIdeal_ne_bot L s hs
  let φ := sectionMultiplyLeft L.sheaf M.sheaf s
  let : Mono (moduleTensorMap s (𝟙 M.sheaf)) := moduleTensorMap_mono s M
  let hφMono : Mono φ := mono_comp _ _
  have heqTensor : ∀ x : X, ∃ U : X.affineOpens, x ∈ U.1 ∧
      ∃ f : M.sheaf.restrict U.1.ι ≅ O U.1.toScheme,
      ∃ e : (L.tensor M).sheaf.restrict U.1.ι ≅ O U.1.toScheme,
        I.ideal U = Ideal.span {U.1.topIso.hom
          (endValue (f.inv ≫ (Scheme.Modules.restrictFunctor U.1.ι).map φ ≫ e.hom))} := by
    intro x
    obtain ⟨U, hx, ⟨e⟩, ⟨f⟩⟩ := common_affine_frames L M x
    refine ⟨U, hx, f, tensorFrame L.sheaf M.sheaf U.1 e f, ?_⟩
    exact (zeroIdeal_on_frame L s U e).trans
      (tensor_multiply_ideal L.sheaf M.sheaf s U e f).symm
  have heqSection : ∀ x : X, ∃ U : X.affineOpens, x ∈ U.1 ∧
      ∃ f : (L.pow 0).sheaf.restrict U.1.ι ≅ O U.1.toScheme,
      ∃ e : L.sheaf.restrict U.1.ι ≅ O U.1.toScheme,
        I.ideal U = Ideal.span {U.1.topIso.hom
          (endValue (f.inv ≫ (Scheme.Modules.restrictFunctor U.1.ι).map s ≫ e.hom))} := by
    intro x
    obtain ⟨U, hx, ⟨e⟩, ⟨f⟩⟩ := common_affine_frames L M x
    refine ⟨U, hx, Scheme.Modules.restrictUnitIso U.1.ι, e, ?_⟩
    simpa only [coefficient, restrictSection, Category.assoc] using! zeroIdeal_on_frame L s U e
  let : Subsingleton (cohomology M.sheaf 2) := hH2 M
  let : Subsingleton (cohomology (L.pow 0).sheaf 2) := hH2 (L.pow 0)
  have hTensor := @CartierDegreeLength.cartier_euler_difference_eq_sum_local_lengths
    X inferInstance p inferInstance hd M (L.tensor M) φ hφMono I hI heqTensor (hfinite M) (hfinite (L.tensor M))
  have hSection := @CartierDegreeLength.cartier_euler_difference_eq_sum_local_lengths
    X inferInstance p inferInstance hd (L.pow 0) L s hsMono I hI heqSection (hfinite (L.pow 0)) (hfinite L)
  exact hTensor.trans hSection.symm

theorem tensor_euler_add [IsIntegral X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (hd : topologicalKrullDim X ≤ 1) (H : LineBundle X) (hH : H.IsAmple)
    (hfinite : FiniteLineCohomology p) (hH2 : LineCohomologyTwoZero X)
    (L M : LineBundle X) :
    eulerCharacteristic p 1 (L.tensor M).sheaf - eulerCharacteristic p 1 M.sheaf =
      eulerCharacteristic p 1 L.sheaf - eulerCharacteristic p 1 (structureSheaf X) := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  let : IsNoetherian X := ⟨⟩
  obtain ⟨A, ⟨t, ht⟩, ⟨u, hu⟩⟩ := exists_effective_twist H hH L
  have h₀ := section_tensor_euler_add p hd hfinite hH2 A L t ht
  have h₁ := section_tensor_euler_add p hd hfinite hH2 (A.tensor L) M u hu
  have h₂ := section_tensor_euler_add p hd hfinite hH2 A (L.tensor M) t ht
  have he := eulerCharacteristic_iso p (lineTensorAssoc A L M) 1
  change eulerCharacteristic p 1 ((A.tensor L).tensor M).sheaf =
    eulerCharacteristic p 1 (A.tensor (L.tensor M)).sheaf at he
  omega

theorem power_euler [IsIntegral X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (hd : topologicalKrullDim X ≤ 1) (H : LineBundle X) (hH : H.IsAmple)
    (hfinite : FiniteLineCohomology p) (hH2 : LineCohomologyTwoZero X)
    (L : LineBundle X) (n : ℕ) :
    eulerCharacteristic p 1 (L.pow n).sheaf - eulerCharacteristic p 1 (structureSheaf X) =
      (n : ℤ) * (eulerCharacteristic p 1 L.sheaf - eulerCharacteristic p 1 (structureSheaf X)) := by
  induction n with
  | zero => simp [LineBundle.pow, modulePow, structureSheaf]
  | succ n ih =>
    have he := tensor_euler_add p hd H hH hfinite hH2 L (L.pow n)
    change eulerCharacteristic p 1 (L.pow (n+1)).sheaf -
      eulerCharacteristic p 1 (L.pow n).sheaf = _ at he
    push_cast
    nlinarith

theorem inverse_euler [IsIntegral X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (hd : topologicalKrullDim X ≤ 1) (H : LineBundle X) (hH : H.IsAmple)
    (hfinite : FiniteLineCohomology p) (hH2 : LineCohomologyTwoZero X)
    (L : LineBundle X) :
    eulerCharacteristic p 1 L.inverse.sheaf - eulerCharacteristic p 1 (structureSheaf X) =
      -(eulerCharacteristic p 1 L.sheaf - eulerCharacteristic p 1 (structureSheaf X)) := by
  have h := tensor_euler_add p hd H hH hfinite hH2 L L.inverse
  have he := eulerCharacteristic_iso p (lineTensorInverseIso L) 1
  change eulerCharacteristic p 1 (L.tensor L.inverse).sheaf =
    eulerCharacteristic p 1 (structureSheaf X) at he
  omega

end
end PiExponent.CurveDegree

namespace PiExponent.NumericalAmpleness
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry
variable {X : Scheme.{0}}

theorem curveDegree_tensor (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (H : LineBundle X) (hH : H.IsAmple) (L M : LineBundle X) (C : IntegralCurve X)
    (hfinite : CurveDegree.FiniteLineCohomology (C.embedding ≫ p))
    (hH2 : CurveDegree.LineCohomologyTwoZero C.scheme) :
    curveDegree p (L.tensor M) C = curveDegree p L C + curveDegree p M C := by
  have he := CurveDegree.tensor_euler_add (C.embedding ≫ p) C.dimension.le
    (H.pullback C.embedding) (LineBundle.IsAmple.pullback_closedImmersion H hH C.embedding)
    hfinite hH2 (L.pullback C.embedding) (M.pullback C.embedding)
  have hi := eulerCharacteristic_iso (C.embedding ≫ p)
    (PiExponentSeshadri.PullbackTensor.iso C.embedding L M) 1
  unfold curveDegree
  rw [hi]
  change _ - _ = (_ - _) + (_ - _)
  dsimp only [LineBundle.pullback, LineBundle.tensor] at he ⊢
  omega

theorem curveDegree_pow (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (H : LineBundle X) (hH : H.IsAmple) (L : LineBundle X) (C : IntegralCurve X)
    (hfinite : CurveDegree.FiniteLineCohomology (C.embedding ≫ p))
    (hH2 : CurveDegree.LineCohomologyTwoZero C.scheme) (n : ℕ) :
    curveDegree p (L.pow n) C = (n : ℤ) * curveDegree p L C := by
  have hi := eulerCharacteristic_iso (C.embedding ≫ p)
    (PiExponentSeshadri.PullbackTensor.powIso C.embedding L n) 1
  unfold curveDegree
  rw [hi]
  exact CurveDegree.power_euler (C.embedding ≫ p) C.dimension.le
    (H.pullback C.embedding) (LineBundle.IsAmple.pullback_closedImmersion H hH C.embedding)
    hfinite hH2 (L.pullback C.embedding) n

theorem curveDegree_iso (p : X ⟶ Spec (CommRingCat.of ℂ))
    (L M : LineBundle X) (C : IntegralCurve X) (e : L.sheaf ≅ M.sheaf) :
    curveDegree p L C = curveDegree p M C := by
  unfold curveDegree
  rw [eulerCharacteristic_iso (C.embedding ≫ p)
    ((Scheme.Modules.pullback C.embedding).mapIso e) 1]

theorem curveDegree_inverse (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (H : LineBundle X) (hH : H.IsAmple) (L : LineBundle X) (C : IntegralCurve X)
    (hfinite : CurveDegree.FiniteLineCohomology (C.embedding ≫ p))
    (hH2 : CurveDegree.LineCohomologyTwoZero C.scheme) :
    curveDegree p L.inverse C = -curveDegree p L C := by
  have h := curveDegree_tensor p H hH L L.inverse C hfinite hH2
  have hi := eulerCharacteristic_iso (C.embedding ≫ p)
    (((Scheme.Modules.pullback C.embedding).mapIso (lineTensorInverseIso L)) ≪≫
      PiExponentSeshadri.Geometry.pullbackUnitIso C.embedding) 1
  change eulerCharacteristic (C.embedding ≫ p) 1
    ((Scheme.Modules.pullback C.embedding).obj (L.tensor L.inverse).sheaf) =
      eulerCharacteristic (C.embedding ≫ p) 1 (structureSheaf C.scheme) at hi
  have hz : curveDegree p (L.tensor L.inverse) C = 0 := by
    unfold curveDegree
    rw [hi]
    exact sub_self _
  omega

theorem curveDegree_eq_rat_of_power_iso
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (H : LineBundle X) (hH : H.IsAmple) (L A B : LineBundle X) (C : IntegralCurve X)
    (hfinite : CurveDegree.FiniteLineCohomology (C.embedding ≫ p))
    (hH2 : CurveDegree.LineCohomologyTwoZero C.scheme)
    (n a b : ℕ) (hn : 0 < n)
    (e : (L.pow n).sheaf ≅ ((A.pow a).tensor (B.inverse.pow b)).sheaf) :
    (curveDegree p L C : ℚ) =
      ((a : ℚ) / n) * (curveDegree p A C : ℚ) -
        ((b : ℚ) / n) * (curveDegree p B C : ℚ) := by
  have hd := curveDegree_iso p (L.pow n) ((A.pow a).tensor (B.inverse.pow b)) C e
  rw [curveDegree_pow p H hH L C hfinite hH2 n,
    curveDegree_tensor p H hH (A.pow a) (B.inverse.pow b) C hfinite hH2,
    curveDegree_pow p H hH A C hfinite hH2 a,
    curveDegree_pow p H hH B.inverse C hfinite hH2 b,
    curveDegree_inverse p H hH B C hfinite hH2] at hd
  have hq := congrArg (fun z : ℤ => (z : ℚ)) hd
  push_cast at hq
  have hnq : (n : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  calc
    (curveDegree p L C : ℚ) =
        ((a : ℚ) * (curveDegree p A C : ℚ) - (b : ℚ) * (curveDegree p B C : ℚ)) / n :=
      (eq_div_iff hnq).mpr (by nlinarith [hq])
    _ = _ := by ring

end
end PiExponent.NumericalAmpleness

end OAI
