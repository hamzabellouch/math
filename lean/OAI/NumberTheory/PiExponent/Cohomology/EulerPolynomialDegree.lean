import OAI.NumberTheory.PiExponent.Ampleness.ClosedAmpleRestriction
import OAI.NumberTheory.PiExponent.Ampleness.ProjectiveO1Ample
import OAI.NumberTheory.PiExponent.Cohomology.CartierEulerPair
import OAI.NumberTheory.PiExponent.Cohomology.EulerCutoff
import OAI.NumberTheory.PiExponent.Cohomology.EulerPolynomialInterpolation
import OAI.NumberTheory.PiExponent.Cohomology.EulerRegularSections
import OAI.NumberTheory.PiExponent.Cohomology.EulerSupportDimension
import OAI.NumberTheory.PiExponent.Cohomology.EulerTwistTransport
import OAI.NumberTheory.PiExponent.Cohomology.ProjectiveEmbeddingCohomologyBound
import OAI.NumberTheory.PiExponent.Geometry.ProjectiveSpaceFinite

namespace OAI

namespace PiExponent.NumericalAmpleness
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry PiExponentSeshadri.Projective
open PiExponent.SectionZeroIdeal PiExponent.ProjectiveO1

lemma iterate_fwdDiff_sub {G : Type*} [AddCommGroup G] (f g : ℕ → G) (k : ℕ) :
    (fwdDiff (1 : ℕ))^[k] (f-g) = (fwdDiff (1 : ℕ))^[k] f - (fwdDiff (1 : ℕ))^[k] g := by
  simpa only [fwdDiff_aux.coe_fwdDiffₗ_pow] using
    map_sub (fwdDiff_aux.fwdDiffₗ ℕ G (1 : ℕ) ^ k) f g

private lemma difference_step {G : Type*} [AddCommGroup G] (f g h : ℕ → G) (k : ℕ)
    (hd : fwdDiff (1 : ℕ) f = g - fun n => h (n+1))
    (hg : (fwdDiff (1 : ℕ))^[k] g=0) (hh : (fwdDiff (1 : ℕ))^[k] h=0) :
    (fwdDiff (1 : ℕ))^[k+1] f=0 := by
  rw [Function.iterate_succ_apply, hd, iterate_fwdDiff_sub, hg]
  have hz : (fwdDiff (1 : ℕ))^[k] (fun n => h (n+1))=0 := by
    funext n
    rw [fwdDiff_iter_comp_add, hh]
    rfl
  rw [hz, sub_self]

theorem projective_line_cohomology_finite {X : Scheme.{0}}
    (p : X ⟶ Spec (CommRingCat.of ℂ)) (r : ℕ)
    (i : X ⟶ projectiveSpace ℂ (Fin (r+1))) [IsClosedImmersion i]
    (hi : i ≫ polynomialProjectiveProjection ℂ (Fin (r+1)) = p)
    (L : LineBundle X) (q : ℕ) :
    letI := Module.compHom (cohomology L.sheaf q) (baseScalars p)
    FiniteDimensional ℂ (cohomology L.sheaf q) := by
  let : L.sheaf.IsFinitePresentation :=
    PiExponent.GeometrySupport.LineBundleCoherent.lineBundle_isFinitePresentation L
  exact PiExponent.ProjectiveSpaceFinite.projectiveOver_cohomology_finite p r i hi L.sheaf q

theorem euler_tensor_power_difference_aux (d : ℕ) :
    ∀ {X : Scheme.{0}} [IsNoetherian X]
      (p : X ⟶ Spec (CommRingCat.of ℂ)) (r : ℕ)
      (i : X ⟶ projectiveSpace ℂ (Fin (r+1))) [IsClosedImmersion i]
      (_hi : i ≫ polynomialProjectiveProjection ℂ (Fin (r+1)) = p)
      (H : LineBundle X), H.IsAmple → ∀ (L M : LineBundle X),
      topologicalKrullDim X ≤ d →
      (fwdDiff (1 : ℕ))^[d+1]
        (fun n => eulerCharacteristic p r ((L.pow n).tensor M).sheaf) = 0 := by
  induction d with
  | zero =>
    intro X _ p r i _ hi H hH L M hdim
    simpa only [Nat.zero_add, Function.iterate_one] using
      fwdDiff_eulerCharacteristic_left_pow_eq_zero p L M r hdim
  | succ d ih =>
    intro X _ p r i _ hi H hH L M hdim
    obtain ⟨B, s, t, hs, ht⟩ := exists_regular_twist_pair p H L hH
    let : Mono s := hs
    let : Mono t := ht
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
    let f (n : ℕ) := eulerCharacteristic p r ((L.pow n).tensor M).sheaf
    let g (n : ℕ) := eulerCharacteristic (jD ≫ p) r
      (((L.pullback jD).pow n).tensor ((A.pullback jD).tensor (M.pullback jD))).sheaf
    let h (n : ℕ) := eulerCharacteristic (jE ≫ p) r
      (((L.pullback jE).pow n).tensor ((B.pullback jE).tensor (M.pullback jE))).sheaf
    have hg : (fwdDiff (1 : ℕ))^[d+1] g = 0 :=
      ih (jD ≫ p) r (jD ≫ i) hiD (H.pullback jD)
        (LineBundle.IsAmple.pullback_closedImmersion H hH jD)
        (L.pullback jD) ((A.pullback jD).tensor (M.pullback jD)) hdD
    have hh : (fwdDiff (1 : ℕ))^[d+1] h = 0 :=
      ih (jE ≫ p) r (jE ≫ i) hiE (H.pullback jE)
        (LineBundle.IsAmple.pullback_closedImmersion H hH jE)
        (L.pullback jE) ((B.pullback jE).tensor (M.pullback jE)) hdE
    have hd : fwdDiff (1 : ℕ) f = g - fun n => h (n+1) := by
      funext n
      have hv := CartierEulerPair.euler_difference p L B M s t n r
        (fun q _ => projective_line_cohomology_finite p r i hi ((L.pow n).tensor M) q)
        (fun q _ => projective_line_cohomology_finite p r i hi ((L.pow (n+1)).tensor M) q)
        (fun q _ => projective_line_cohomology_finite p r i hi
          (A.tensor ((L.pow n).tensor M)) q)
        (fun q _ => projective_line_cohomology_finite (jD ≫ p) r (jD ≫ i) hiD
          ((A.tensor ((L.pow n).tensor M)).pullback jD) q)
        (fun q _ => projective_line_cohomology_finite (jE ≫ p) r (jE ≫ i) hiE
          ((B.tensor ((L.pow (n+1)).tensor M)).pullback jE) q)
        (lineBundle_cohomology_eq_zero_of_projective_embedding r i
          ((L.pow n).tensor M) (r+1) le_rfl)
        (lineBundle_cohomology_eq_zero_of_projective_embedding r i
          ((L.pow (n+1)).tensor M) (r+1) le_rfl)
      dsimp only [CartierEulerPair.source, CartierEulerPair.middle] at hv
      rw [eulerCharacteristic_pullback_cartierMiddle,
        eulerCharacteristic_pullback_cartierMiddle] at hv
      exact hv
    exact difference_step f g h (d+1) hd hg hh

theorem euler_tensor_power_difference_eq_zero {X : Scheme.{0}} [IsNoetherian X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) (r : ℕ)
    (i : X ⟶ projectiveSpace ℂ (Fin (r+1))) [IsClosedImmersion i]
    (hi : i ≫ polynomialProjectiveProjection ℂ (Fin (r+1)) = p)
    (L M : LineBundle X) (d : ℕ) (hdim : topologicalKrullDim X ≤ d) :
    (fwdDiff (1 : ℕ))^[d+1]
      (fun n => eulerCharacteristic p r ((L.pow n).tensor M).sheaf) = 0 := by
  let H := (PiExponent.ProjectiveO1.lineBundle (R := ℂ) (σ := Fin (r+1))).pullback i
  have hH : H.IsAmple := LineBundle.IsAmple.pullback_closedImmersion _
    PiExponent.ProjectiveO1.lineBundle_ample i
  exact euler_tensor_power_difference_aux d p r i hi H hH L M hdim

theorem euler_power_difference_eq_zero {X : Scheme.{0}} [IsNoetherian X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) (r : ℕ)
    (i : X ⟶ projectiveSpace ℂ (Fin (r+1))) [IsClosedImmersion i]
    (hi : i ≫ polynomialProjectiveProjection ℂ (Fin (r+1)) = p)
    (L : LineBundle X) (d : ℕ) (hdim : topologicalKrullDim X ≤ d) :
    (fwdDiff (1 : ℕ))^[d+1]
      (fun n => eulerCharacteristic p r (L.pow n).sheaf) = 0 := by
  have h := euler_tensor_power_difference_eq_zero p r i hi L (L.pow 0) d hdim
  have he : (fun n => eulerCharacteristic p r ((L.pow n).tensor (L.pow 0)).sheaf) =
      (fun n => eulerCharacteristic p r (L.pow n).sheaf) := by
    funext n
    exact eulerCharacteristic_iso p (moduleTensorRightUnit (L.pow n).sheaf) r
  rwa [he] at h

theorem euler_tensor_power_dimension_difference_eq_zero
    {X : Scheme.{0}} [IsNoetherian X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) (r : ℕ)
    (i : X ⟶ projectiveSpace ℂ (Fin (r+1))) [IsClosedImmersion i]
    (hi : i ≫ polynomialProjectiveProjection ℂ (Fin (r+1)) = p)
    (L M : LineBundle X) (d : ℕ) (hdim : topologicalKrullDim X ≤ d) :
    (fwdDiff (1 : ℕ))^[d+1]
      (fun n => eulerCharacteristic p d ((L.pow n).tensor M).sheaf) = 0 := by
  let H := (PiExponent.ProjectiveO1.lineBundle (R := ℂ) (σ := Fin (r+1))).pullback i
  have hH : H.IsAmple := LineBundle.IsAmple.pullback_closedImmersion _
    PiExponent.ProjectiveO1.lineBundle_ample i
  have he : (fun n => eulerCharacteristic p r ((L.pow n).tensor M).sheaf) =
      (fun n => eulerCharacteristic p d ((L.pow n).tensor M).sheaf) := by
    funext n
    exact eulerCharacteristic_projective_eq_dimension p r i hi H hH
      ((L.pow n).tensor M) d hdim
  have h := euler_tensor_power_difference_eq_zero p r i hi L M d hdim
  rwa [he] at h

theorem euler_power_dimension_difference_eq_zero
    {X : Scheme.{0}} [IsNoetherian X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) (r : ℕ)
    (i : X ⟶ projectiveSpace ℂ (Fin (r+1))) [IsClosedImmersion i]
    (hi : i ≫ polynomialProjectiveProjection ℂ (Fin (r+1)) = p)
    (L : LineBundle X) (d : ℕ) (hdim : topologicalKrullDim X ≤ d) :
    (fwdDiff (1 : ℕ))^[d+1]
      (fun n => eulerCharacteristic p d (L.pow n).sheaf) = 0 := by
  have h := euler_tensor_power_dimension_difference_eq_zero p r i hi L (L.pow 0) d hdim
  have he : (fun n => eulerCharacteristic p d ((L.pow n).tensor (L.pow 0)).sheaf) =
      (fun n => eulerCharacteristic p d (L.pow n).sheaf) := by
    funext n
    exact eulerCharacteristic_iso p (moduleTensorRightUnit (L.pow n).sheaf) d
  rwa [he] at h

theorem exists_euler_tensor_polynomial {X : Scheme.{0}} [IsNoetherian X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) (r : ℕ)
    (i : X ⟶ projectiveSpace ℂ (Fin (r+1))) [IsClosedImmersion i]
    (hi : i ≫ polynomialProjectiveProjection ℂ (Fin (r+1)) = p)
    (L M : LineBundle X) (d : ℕ) (hdim : topologicalKrullDim X ≤ d) :
    ∃ P : Polynomial ℚ, P.natDegree ≤ d ∧ ∀ n : ℕ,
      P.eval (n : ℚ) = (eulerCharacteristic p d ((L.pow n).tensor M).sheaf : ℚ) := by
  let f (n : ℕ) := eulerCharacteristic p d ((L.pow n).tensor M).sheaf
  refine ⟨newtonPolynomial f d, newtonPolynomial_natDegree_le f d, ?_⟩
  exact newtonPolynomial_eval f d
    (euler_tensor_power_dimension_difference_eq_zero p r i hi L M d hdim)

theorem exists_euler_polynomial {X : Scheme.{0}} [IsNoetherian X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) (r : ℕ)
    (i : X ⟶ projectiveSpace ℂ (Fin (r+1))) [IsClosedImmersion i]
    (hi : i ≫ polynomialProjectiveProjection ℂ (Fin (r+1)) = p)
    (L : LineBundle X) (d : ℕ) (hdim : topologicalKrullDim X ≤ d) :
    ∃ P : Polynomial ℚ, P.natDegree ≤ d ∧ ∀ n : ℕ,
      P.eval (n : ℚ) = (eulerCharacteristic p d (L.pow n).sheaf : ℚ) := by
  let f (n : ℕ) := eulerCharacteristic p d (L.pow n).sheaf
  refine ⟨newtonPolynomial f d, newtonPolynomial_natDegree_le f d, ?_⟩
  exact newtonPolynomial_eval f d
    (euler_power_dimension_difference_eq_zero p r i hi L d hdim)

end
end PiExponent.NumericalAmpleness

end OAI
