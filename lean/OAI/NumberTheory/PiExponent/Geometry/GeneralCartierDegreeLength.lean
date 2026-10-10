import Mathlib
import OAI.NumberTheory.PiExponent.Approximation.LinePullback
import OAI.NumberTheory.PiExponent.Cohomology.EulerExact
import OAI.NumberTheory.PiExponent.Cohomology.EulerSupportDimension
import OAI.NumberTheory.PiExponent.Cohomology.EulerZeroDimensional
import OAI.NumberTheory.PiExponent.Cohomology.FiniteLineEuler
import OAI.NumberTheory.PiExponent.Geometry.CartierPowerFrames
import OAI.NumberTheory.PiExponent.Geometry.CartierSequence
import OAI.NumberTheory.PiExponent.Geometry.LineBundleProduct

namespace OAI

noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames

namespace PiExponent.GeneralCartierDegreeLength


theorem cartier_euler_difference_eq_sum_local_lengths
    {X : Scheme.{0}}
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (M N : LineBundle X) (φ : M.sheaf ⟶ N.sheaf) [Mono φ]
    (I : X.IdealSheafData) [Finite I.subscheme]
    (heq : ∀ x : X, ∃ U : X.affineOpens, x ∈ U.1 ∧
      ∃ e : M.sheaf.restrict U.1.ι ≅ O U.1.toScheme,
      ∃ d : N.sheaf.restrict U.1.ι ≅ O U.1.toScheme,
        I.ideal U = Ideal.span {U.1.topIso.hom
          (endValue (e.inv ≫ (Scheme.Modules.restrictFunctor U.1.ι).map φ ≫ d.hom))})
    (hfiniteM : ∀ n ≤ 1, letI := Module.compHom (cohomology M.sheaf n) (baseScalars p)
      FiniteDimensional ℂ (cohomology M.sheaf n))
    (hfiniteN : ∀ n ≤ 1, letI := Module.compHom (cohomology N.sheaf n) (baseScalars p)
      FiniteDimensional ℂ (cohomology N.sheaf n))
    [Subsingleton (cohomology M.sheaf 2)] :
    letI : Fintype I.subscheme := Fintype.ofFinite _
    eulerCharacteristic p 1 N.sheaf - eulerCharacteristic p 1 M.sheaf =
      ∑ x : I.subscheme,
        ((Module.length (I.subscheme.presheaf.stalk x)
          (I.subscheme.presheaf.stalk x)).toNat : ℤ) := by
  let : Fintype I.subscheme := Fintype.ofFinite _
  obtain ⟨hz, hseq⟩ := PiExponentSeshadri.CartierSequence.exact p M N φ I heq
  have hfiniteZ (n : ℕ) (_hn : n ≤ 1) :=
    PiExponentSeshadri.FiniteSupport.finite_line_pushforward_finiteDimensional
      I.subschemeι p (N.pullback I.subschemeι) n
  have h := eulerCharacteristic_add p hseq 1 hfiniteM hfiniteN hfiniteZ
  have hdiff : eulerCharacteristic p 1 N.sheaf - eulerCharacteristic p 1 M.sheaf =
      eulerCharacteristic p 1
        ((Scheme.Modules.pushforward I.subschemeι).obj
          ((Scheme.Modules.pullback I.subschemeι).obj N.sheaf)) := by
    exact sub_eq_iff_eq_add.mpr (by simpa [add_comm] using h)
  exact hdiff.trans
    (PiExponentSeshadri.FiniteSupport.finite_line_euler_eq_sum_stalk_lengths
      I.subschemeι p (N.pullback I.subschemeι) 1)

theorem finite_zeroIdeal_of_mono {X : Scheme.{0}}
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (hd : topologicalKrullDim X ≤ 1)
    (L : LineBundle X) (s : GlobalSections X L.sheaf) [Mono s] :
    Finite (PiExponent.SectionZeroIdeal.zeroIdeal L s).subscheme := by
  let I := PiExponent.SectionZeroIdeal.zeroIdeal L s
  let q := I.subschemeι ≫ p
  let : IsLocallyNoetherian I.subscheme := LocallyOfFiniteType.isLocallyNoetherian q
  let : CompactSpace I.subscheme := QuasiCompact.compactSpace_of_compactSpace q
  let : IsNoetherian I.subscheme := {}
  exact PiExponent.NumericalAmpleness.finite_of_dim_le_zero
    (PiExponent.NumericalAmpleness.regular_sectionZero_dimension_le L s 0 (by simpa using hd))

theorem regular_section_tensor_euler_eq_sum_local_lengths {X : Scheme.{0}}
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (hd : topologicalKrullDim X ≤ 1)
    (L M : LineBundle X) (s : GlobalSections X L.sheaf) [Mono s]
    (hfiniteM : ∀ n ≤ 1, letI := Module.compHom (cohomology M.sheaf n) (baseScalars p)
      FiniteDimensional ℂ (cohomology M.sheaf n))
    (hfiniteLM : ∀ n ≤ 1, letI := Module.compHom (cohomology (L.tensor M).sheaf n) (baseScalars p)
      FiniteDimensional ℂ (cohomology (L.tensor M).sheaf n))
    [Subsingleton (cohomology M.sheaf 2)] :
    letI : Finite (PiExponent.SectionZeroIdeal.zeroIdeal L s).subscheme :=
      finite_zeroIdeal_of_mono p hd L s
    letI : Fintype (PiExponent.SectionZeroIdeal.zeroIdeal L s).subscheme := Fintype.ofFinite _
    eulerCharacteristic p 1 (L.tensor M).sheaf - eulerCharacteristic p 1 M.sheaf =
      ∑ x : (PiExponent.SectionZeroIdeal.zeroIdeal L s).subscheme,
        ((Module.length
          ((PiExponent.SectionZeroIdeal.zeroIdeal L s).subscheme.presheaf.stalk x)
          ((PiExponent.SectionZeroIdeal.zeroIdeal L s).subscheme.presheaf.stalk x)).toNat : ℤ) := by
  let I := PiExponent.SectionZeroIdeal.zeroIdeal L s
  let : Finite I.subscheme := finite_zeroIdeal_of_mono p hd L s
  let : Fintype I.subscheme := Fintype.ofFinite _
  let φ := PiExponent.CartierPowerFrames.sectionMultiplyLeft L.sheaf M.sheaf s
  let : Mono (moduleTensorMap s (𝟙 M.sheaf)) := moduleTensorMap_mono s M
  have hmono : Mono φ := mono_comp _ _
  refine @cartier_euler_difference_eq_sum_local_lengths X p inferInstance M (L.tensor M)
    φ hmono I inferInstance ?_ hfiniteM hfiniteLM inferInstance
  intro x
  obtain ⟨U,hx,⟨e⟩,⟨f⟩⟩ := common_affine_frames L M x
  refine ⟨U,hx,f,PiExponent.CartierPowerFrames.tensorFrame L.sheaf M.sheaf U.1 e f,?_⟩
  exact (PiExponent.SectionZeroIdeal.zeroIdeal_on_frame L s U e).trans
    (PiExponent.CartierPowerFrames.tensor_multiply_ideal L.sheaf M.sheaf s U e f).symm

end PiExponent.GeneralCartierDegreeLength

end

end OAI
