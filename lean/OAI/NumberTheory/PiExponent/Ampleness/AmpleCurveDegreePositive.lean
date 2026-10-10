import OAI.NumberTheory.PiExponent.Approximation.SectionZeroSupport
import OAI.NumberTheory.PiExponent.Cohomology.AmpleCohomologyFinite
import OAI.NumberTheory.PiExponent.Cohomology.LineCohomologyDimension
import OAI.NumberTheory.PiExponent.Geometry.CurveDegreeAdditivity
import OAI.NumberTheory.PiExponent.Geometry.CurveMorphismFinite

namespace OAI

noncomputable section
namespace PiExponent.CurveDegree
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
open PiExponent.SectionZeroIdeal
variable {X : Scheme.{0}}

theorem exists_ample_section_with_zero [IsIntegral X]
    (hdim : topologicalKrullDim X = 1) (L : LineBundle X) (hL : L.IsAmple) :
    ∃ n : ℕ, 0 < n ∧ ∃ s : GlobalSections X (L.pow n).sheaf,
      s ≠ 0 ∧ ∃ y : X, y ∉ sectionOpen X s := by
  classical
  have : Nontrivial X := by
    by_contra h
    have : Subsingleton X := not_nontrivial_iff_subsingleton.mp h
    have hz := topologicalKrullDim_zero_of_discreteTopology X
    rw [hdim] at hz
    norm_num at hz
  obtain ⟨y, hy⟩ := exists_ne (genericPoint X)
  have hclosed := CurveMorphismFinite.isClosed_singleton_of_ne_genericPoint X hdim.le y hy
  let U : X.Opens := ⟨({y} : Set X)ᶜ, hclosed.isOpen_compl⟩
  have hη : genericPoint X ∈ U := by
    change genericPoint X ≠ y
    exact Ne.symm hy
  obtain ⟨n, hn, s, hsη, hsub, -⟩ := hL (genericPoint X) U hη
  refine ⟨n, hn, s, section_ne_zero_of_mem_isoOpen (L.pow n) s (genericPoint X) hsη,
    y, ?_⟩
  intro hys
  exact hsub hys rfl

theorem finite_nonempty_euler_pos [Finite X] [Nonempty X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p] (d : ℕ) :
    0 < eulerCharacteristic p d (structureSheaf X) := by
  classical
  let : Algebra ℂ Γ(X, ⊤) := (baseScalars p).toAlgebra
  have : FiniteDimensional ℂ Γ(X, ⊤) := proper_finite_functions p
  obtain ⟨x⟩ : Nonempty X := inferInstance
  have : Nontrivial Γ(X, ⊤) := (X.presheaf.germ ⊤ x trivial).hom.domain_nontrivial
  rw [proper_finite_euler]
  change (0 : ℤ) < (Module.finrank ℂ Γ(X, ⊤) : ℤ)
  exact_mod_cast (Module.finrank_pos (R := ℂ) (M := Γ(X, ⊤)))

theorem section_euler_degree_pos [IsIntegral X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (hdim : topologicalKrullDim X ≤ 1)
    (L : LineBundle X) (s : GlobalSections X L.sheaf) (hs : s ≠ 0)
    (hzero : ∃ y : X, y ∉ sectionOpen X s)
    (hfiniteO : ∀ n ≤ 1,
      letI := Module.compHom (cohomology (structureSheaf X) n) (baseScalars p)
      FiniteDimensional ℂ (cohomology (structureSheaf X) n))
    (hfiniteL : ∀ n ≤ 1,
      letI := Module.compHom (cohomology L.sheaf n) (baseScalars p)
      FiniteDimensional ℂ (cohomology L.sheaf n))
    [Subsingleton (cohomology (structureSheaf X) 2)] :
    0 < eulerCharacteristic p 1 L.sheaf -
      eulerCharacteristic p 1 (structureSheaf X) := by
  classical
  have hsMono : Mono s := L.mono_section s hs
  let I := zeroIdeal L s
  have hI : I ≠ ⊥ := zeroIdeal_ne_bot L s hs
  let : Finite I.subscheme := finite_subscheme_of_curve p hdim I hI
  let : Fintype I.subscheme := Fintype.ofFinite _
  obtain ⟨y, hy⟩ := hzero
  have hyI : y ∈ I.support := by
    change y ∈ ((zeroIdeal L s).support : Set X)
    rw [zeroIdeal_support]
    exact hy
  have hyrange : y ∈ Set.range I.subschemeι := by
    rw [Scheme.IdealSheafData.range_subschemeι]
    exact hyI
  obtain ⟨z, -⟩ := hyrange
  have : Nonempty I.subscheme := ⟨z⟩
  have heq : ∀ x : X, ∃ U : X.affineOpens, x ∈ U.1 ∧
      ∃ f : (L.pow 0).sheaf.restrict U.1.ι ≅ O U.1.toScheme,
      ∃ e : L.sheaf.restrict U.1.ι ≅ O U.1.toScheme,
        I.ideal U = Ideal.span {U.1.topIso.hom
          (endValue (f.inv ≫ (Scheme.Modules.restrictFunctor U.1.ι).map s ≫ e.hom))} := by
    intro x
    obtain ⟨U, hx, ⟨e⟩, -⟩ := common_affine_frames L L x
    refine ⟨U, hx, Scheme.Modules.restrictUnitIso U.1.ι, e, ?_⟩
    simpa only [coefficient, restrictSection, Category.assoc] using! zeroIdeal_on_frame L s U e
  have : Subsingleton (cohomology (L.pow 0).sheaf 2) := by
    change Subsingleton (cohomology (structureSheaf X) 2)
    infer_instance
  have hdegree := @CartierDegreeLength.cartier_euler_difference_eq_sum_local_lengths
    X inferInstance p inferInstance hdim (L.pow 0) L s hsMono I hI heq hfiniteO hfiniteL inferInstance
  change eulerCharacteristic p 1 L.sheaf -
    eulerCharacteristic p 1 (structureSheaf X) = _ at hdegree
  have hsum := proper_finite_euler_eq_sum_stalk_lengths (I.subschemeι ≫ p) 1
  have hpos := finite_nonempty_euler_pos (I.subschemeι ≫ p) 1
  rw [hdegree]
  rwa [hsum] at hpos

theorem ample_euler_degree_pos [IsIntegral X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (hdim : topologicalKrullDim X = 1)
    (L : LineBundle X) (hL : L.IsAmple)
    (hfinite : FiniteLineCohomology p) :
    0 < eulerCharacteristic p 1 L.sheaf -
      eulerCharacteristic p 1 (structureSheaf X) := by
  have hH2 : LineCohomologyTwoZero X := by
    intro M
    exact ⟨fun a b =>
      (NumericalAmpleness.lineBundle_cohomology_zero_of_dimension_le 1 p L hL M
        hdim.le 2 (by omega) a).trans
      (NumericalAmpleness.lineBundle_cohomology_zero_of_dimension_le 1 p L hL M
        hdim.le 2 (by omega) b).symm⟩
  obtain ⟨n, hn, s, hs, hzero⟩ := exists_ample_section_with_zero hdim L hL
  have : Subsingleton (cohomology (structureSheaf X) 2) := hH2 (L.pow 0)
  have hpos := section_euler_degree_pos p hdim.le (L.pow n) s hs hzero
    (hfinite (L.pow 0)) (hfinite (L.pow n))
  rw [power_euler p hdim.le L hL hfinite hH2 L n] at hpos
  have hnz : (0 : ℤ) < n := by exact_mod_cast hn
  exact (mul_pos_iff_of_pos_left hnz).mp hpos

theorem finite_line_cohomology_of_ample [IsIntegral X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (H : LineBundle X) (hH : H.IsAmple) : FiniteLineCohomology p := by
  intro M q _
  let := GeometrySupport.LineBundleCoherent.lineBundle_isFinitePresentation M
  exact AmpleCohomologyFinite.cohomology_finite_of_ample p H hH M.sheaf q

theorem euler_degree_pos_of_ample [IsIntegral X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (hdim : topologicalKrullDim X = 1) (L : LineBundle X) (hL : L.IsAmple) :
    0 < eulerCharacteristic p 1 L.sheaf -
      eulerCharacteristic p 1 (structureSheaf X) :=
  ample_euler_degree_pos p hdim L hL (finite_line_cohomology_of_ample p L hL)

end PiExponent.CurveDegree

namespace PiExponent.NumericalAmpleness
open AlgebraicGeometry CategoryTheory
open PiExponentSeshadri.Geometry

theorem curveDegree_pos_of_ample
    {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (L : LineBundle X) (hL : L.IsAmple) (C : IntegralCurve X) :
    0 < curveDegree p L C := by
  exact CurveDegree.euler_degree_pos_of_ample (C.embedding ≫ p) C.dimension
    (L.pullback C.embedding) (LineBundle.IsAmple.pullback_closedImmersion L hL C.embedding)

end PiExponent.NumericalAmpleness

end

end OAI
