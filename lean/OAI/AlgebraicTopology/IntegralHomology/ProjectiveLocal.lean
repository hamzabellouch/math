import OAI.AlgebraicTopology.IntegralHomology.ProjectivePuncture
import OAI.AlgebraicTopology.IntegralHomology.Sphere

namespace OAI

noncomputable section

namespace Kaplansky

/-! Nonzero local classes and local homology of projective spaces and products. -/

section
open Set
namespace ComplexGrassmann

instance grassmannZero_subsingleton : Subsingleton (Grassmann 1 0) := by
  constructor
  intro P Q
  apply Subtype.ext
  have hp : P.val = ⊤ := Submodule.eq_top_of_finrank_eq (by simpa using P.property)
  have hq : Q.val = ⊤ := Submodule.eq_top_of_finrank_eq (by simpa using Q.property)
  exact hp.trans hq.symm

variable {ι : Type} [Fintype ι] (K : ι → ℕ)

/-- If the dimensions sum to one, there is exactly one nontrivial factor. -/
theorem projectiveProduct_sum_one_factor (hK : ∑ i, K i = 1) :
    ∃ i, K i = 1 ∧ ∀ j, j ≠ i → K j = 0 := by
  classical
  obtain ⟨i, _, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero (by omega : ∑ i, K i ≠ 0)
  have hi1 : K i = 1 := by
    have := Finset.single_le_sum (fun j _ => Nat.zero_le (K j)) (Finset.mem_univ i)
    omega
  refine ⟨i, hi1, ?_⟩
  intro j hji
  have hsum := Finset.sum_erase_add (Finset.univ : Finset ι) K (Finset.mem_univ i)
  have hj := Finset.single_le_sum (fun k _ => Nat.zero_le (K k))
    (Finset.mem_erase.mpr ⟨hji, Finset.mem_univ j⟩)
  omega

/-- Projection onto the unique positive-dimensional factor is a homeomorphism;
all other actual Grassmann factors have one point. -/
def projectiveProductOneFactorHomeomorph (i : ι) (hrest : ∀ j, j ≠ i → K j = 0) :
    ProjectiveProduct K ≃ₜ Grassmann 1 (K i) := by
  classical
  let f : ProjectiveProduct K → Grassmann 1 (K i) := fun P => P i
  have hinj : Function.Injective f := by
    intro P Q h
    funext j
    by_cases hj : j = i
    · subst j; exact h
    · have hs : Subsingleton (Grassmann 1 (K j)) := by rw [hrest j hj]; infer_instance
      exact hs.elim _ _
  have hsurj : Function.Surjective f := by
    intro P
    let Q : ProjectiveProduct K := fun j => slopePoint (standardLineGraphFrame (K j)) 0
    exact ⟨Function.update Q i P, by simp [f]⟩
  exact Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective f ⟨hinj, hsurj⟩) (continuous_apply i)

/-- The punctured actual product of total complex dimension one is contractible,
including products with any number of zero-dimensional factors. -/
theorem projectiveProductPuncture_contractible_of_sum_one (hK : ∑ i, K i = 1)
    (P : ProjectiveProduct K) : ContractibleSpace ({P}ᶜ : Set (ProjectiveProduct K)) := by
  obtain ⟨i, hi, hrest⟩ := projectiveProduct_sum_one_factor K hK
  let e := projectiveProductOneFactorHomeomorph K i hrest
  let e' : ({P}ᶜ : Set (ProjectiveProduct K)) ≃ₜ
      ({e P}ᶜ : Set (Grassmann 1 (K i))) := e.subtype (fun x => show x ≠ P ↔ e x ≠ e P from (not_congr e.injective.eq_iff).symm)
  have hc : ∀ Q : Grassmann 1 (K i), ContractibleSpace ({Q}ᶜ : Set (Grassmann 1 (K i))) := by
    rw [hi]
    exact projectiveLinePuncture_contractible
  let := hc (e P)
  exact e'.contractibleSpace

end ComplexGrassmann

end

section
open CategoryTheory
open ComplexGrassmann
variable {ι : Type} [Fintype ι] (K : ι → ℕ)

/-- Real dimension of the actual complex graph-coordinate space. -/
theorem canonicalCoordinateSpace_real_finrank :
    Module.finrank ℝ ((Σ i, Fin (K i)) → ℂ) = 2 * (∑ i, K i) := by
  rw [finrank_real_of_complex]
  simp [Fintype.card_sigma, Nat.mul_comm]

/-- Nonzero integral top sphere class in the exact normed coordinate space
used by the canonical section of the actual hyperplane product bundle. -/
theorem canonicalCoordinateSphere_topHomology_nonzero (hp : 0 < (∑ i, K i)) :
    ∃ z : (integralSingularHomology (2 * (∑ i, K i) - 1)).obj
      (TopCat.of (Metric.sphere (0 : ((Σ i, Fin (K i)) → ℂ)) 1)), z ≠ 0 := by
  have hd : Module.finrank ℝ ((Σ i, Fin (K i)) → ℂ) = (2 * (∑ i, K i) - 2) + 2 := by
    rw [canonicalCoordinateSpace_real_finrank]
    omega
  have h := finiteDimensionalSphere_topHomology_nonzero ((Σ i, Fin (K i)) → ℂ)
    (2 * (∑ i, K i) - 2) hd
  have hn : (2 * (∑ i, K i) - 2) + 1 = 2 * (∑ i, K i) - 1 := by omega
  rw [hn] at h
  exact h

/-- A nonzero local relative class in the actual chart at the canonical zero. -/
theorem canonicalChart_localRelative_nonzero (hp : 0 < (∑ i, K i)) :
    ∃ z : relativeSingularHomology (subspaceInclusion
      ({⟨firstCoordinateProduct K, canonicalProduct_zero_in_chart K⟩}ᶜ :
        Set (canonicalProductGraphChart K).source)) (2 * (∑ i, K i)), z ≠ 0 := by
  have hn : 2 * (∑ i, K i) - 1 ≠ 0 := by omega
  have he : (2 * (∑ i, K i) - 1) + 1 = 2 * (∑ i, K i) := by omega
  have h := nonzero_class_of_iso (canonicalChartSphereHomologyIso K _ hn)
    (canonicalCoordinateSphere_topHomology_nonzero K hp)
  rw [he] at h
  exact h

theorem canonicalProduct_localRelative_nonzero (hp : 0 < (∑ i, K i)) :
    ∃ z : relativeSingularHomology (subspaceInclusion
      ({firstCoordinateProduct K}ᶜ : Set (ProjectiveProduct K))) (2 * (∑ i, K i)), z ≠ 0 :=
  nonzero_class_of_iso (canonicalChartExcisionIso K (2 * (∑ i, K i))).symm
    (canonicalChart_localRelative_nonzero K hp)

end

section
open CategoryTheory Metric
open ComplexGrassmann

/-- Top integral sphere homology for any finite-dimensional real normed space,
using a chosen linear coordinate system and the recursive sphere normalization. -/
def finiteDimensionalSphereTopHomologyIso (E : Type)
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (n : ℕ) (hd : Module.finrank ℝ E = n+2) :
    (integralSingularHomology (n+1)).obj (TopCat.of (sphere (0 : E) 1)) ≅ ModuleCat.of ℤ ℤ :=
  integralHomologyHomotopyIso
    (continuousLinearEquivSphereHomotopyEquiv
      (ContinuousLinearEquiv.ofFinrankEq (by simpa using hd) :
        E ≃L[ℝ] EuclideanSpace ℝ (Fin (n+2)))) (n+1) ≪≫
    euclideanSphereTopHomologyIso n

variable {ι : Type} [Fintype ι] (K : ι → ℕ)

/-- Local relative integral homology at the canonical point of the full
projective product is ℤ in its real dimension. -/
def canonicalProductLocalHomologyIso (hp : 0 < ∑ i, K i) :
    relativeSingularHomology (subspaceInclusion
      ({firstCoordinateProduct K}ᶜ : Set (ProjectiveProduct K))) (2 * (∑ i, K i)) ≅
        ModuleCat.of ℤ ℤ := by
  let p := ∑ i, K i
  have hdim : Module.finrank ℝ ((Σ i, Fin (K i)) → ℂ) = (2*p-2)+2 := by
    rw [canonicalCoordinateSpace_real_finrank]
    dsimp [p]
    omega
  let e := (canonicalChartExcisionIso K ((2*p-2)+2)).symm ≪≫
    canonicalChartSphereHomologyIso K ((2*p-2)+1) (by dsimp [p]; omega) ≪≫
      finiteDimensionalSphereTopHomologyIso ((Σ i, Fin (K i)) → ℂ) (2*p-2) hdim
  have he : (2*p-2)+2 = 2*p := by dsimp [p]; omega
  rw [he] at e
  exact e

/-- A specific primitive integral local class, obtained from 1 under the
proved local homology isomorphism. Its orientation is the chosen recursive
coordinate orientation; comparison with the standard complex orientation is separate. -/
def canonicalProductLocalGenerator (hp : 0 < ∑ i, K i) :
    relativeSingularHomology (subspaceInclusion
      ({firstCoordinateProduct K}ᶜ : Set (ProjectiveProduct K))) (2 * (∑ i, K i)) :=
  (canonicalProductLocalHomologyIso K hp).inv (1 : ℤ)

theorem canonicalProductLocalGenerator_coordinate (hp : 0 < ∑ i, K i) :
    (canonicalProductLocalHomologyIso K hp).hom (canonicalProductLocalGenerator K hp) = (1 : ℤ) :=
  ConcreteCategory.congr_hom (canonicalProductLocalHomologyIso K hp).inv_hom_id 1

theorem canonicalProductLocalGenerator_ne_zero (hp : 0 < ∑ i, K i) :
    canonicalProductLocalGenerator K hp ≠ 0 := by
  intro h
  have hc := canonicalProductLocalGenerator_coordinate K hp
  rw [h, map_zero] at hc
  norm_num at hc

/-- Every local relative class is the unique integral multiple of this generator. -/
theorem canonicalProductLocalGenerator_spans (hp : 0 < ∑ i, K i)
    (z : relativeSingularHomology (subspaceInclusion
      ({firstCoordinateProduct K}ᶜ : Set (ProjectiveProduct K))) (2 * (∑ i, K i))) :
    ((canonicalProductLocalHomologyIso K hp).hom z : ℤ) • canonicalProductLocalGenerator K hp = z := by
  apply (ModuleCat.mono_iff_injective (canonicalProductLocalHomologyIso K hp).hom).mp inferInstance
  have hsm := map_zsmul (canonicalProductLocalHomologyIso K hp).hom.hom.toAddMonoidHom
    ((canonicalProductLocalHomologyIso K hp).hom z : ℤ) (canonicalProductLocalGenerator K hp)
  calc
    _ = ((canonicalProductLocalHomologyIso K hp).hom z : ℤ) •
        (canonicalProductLocalHomologyIso K hp).hom (canonicalProductLocalGenerator K hp) := hsm
    _ = _ := by rw [canonicalProductLocalGenerator_coordinate]; exact mul_one _

end

section
open CategoryTheory Limits

section

/-- Punctured finite-dimensional real coordinate spaces of dimension at least
two are path connected, with their actual norm topology. -/
theorem puncturedVector_pathConnected_of_finrank (E : Type)
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (hd : 2 ≤ Module.finrank ℝ E) : PathConnectedSpace ({0}ᶜ : Set E) := by
  apply isPathConnected_iff_pathConnectedSpace.mp
  apply isPathConnected_compl_singleton_of_one_lt_rank
  rw [← Module.finrank_eq_rank]
  exact_mod_cast (show 1 < Module.finrank ℝ E by omega)

/-- Actual local relative homology of a real vector space vanishes in every
non-top degree, including the low degrees zero and one. -/
theorem localVectorHomology_isZero (E : Type)
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (hd : 2 ≤ Module.finrank ℝ E) (n : ℕ) (hn : n ≠ Module.finrank ℝ E) :
    IsZero (relativeSingularHomology (subspaceInclusion ({0}ᶜ : Set E)) n) := by
  let := puncturedVector_pathConnected_of_finrank E hd
  cases n with
  | zero => exact relativeHomologyZero_isZero _
  | succ n =>
      cases n with
      | zero => exact relativeHomologyOne_isZero _
      | succ n =>
          exact (finiteDimensionalSphereHomology_isZero E (Module.finrank ℝ E-1) (n+1)
            (by omega) (by omega) (by omega)).of_iso
              (localVectorSphereHomologyIso E (n+1) (by omega))

open ComplexGrassmann
variable {ι : Type} [Fintype ι] (K : ι → ℕ)

/-- Local integral homology of the actual projective product at its canonical
point is concentrated in its real dimension. Combined with the preserved local
ℤ isomorphism, this supplies the complete local group calculation. -/
theorem canonicalProductLocalHomology_isZero (hp : 0 < ∑ i, K i)
    (n : ℕ) (hn : n ≠ 2*(∑ i, K i)) :
    IsZero (relativeSingularHomology (subspaceInclusion
      ({firstCoordinateProduct K}ᶜ : Set (ProjectiveProduct K))) n) := by
  have hd : 2 ≤ Module.finrank ℝ ((Σ i, Fin (K i)) → ℂ) := by
    rw [canonicalCoordinateSpace_real_finrank]
    omega
  have hne : n ≠ Module.finrank ℝ ((Σ i, Fin (K i)) → ℂ) := by
    rwa [canonicalCoordinateSpace_real_finrank]
  exact (localVectorHomology_isZero ((Σ i, Fin (K i)) → ℂ) hd n hne).of_iso
    ((canonicalChartExcisionIso K n).symm ≪≫ canonicalLocalRelativeHomologyIso K n)

end

open ComplexGrassmann
variable {ι : Type} [Fintype ι] (K : ι → ℕ)

/-- An actual full product graph chart containing any specified projective point. -/
def projectivePointChart (P : ProjectiveProduct K) :
    OpenPartialHomeomorph (ProjectiveProduct K) (ProjectiveProductModel K) :=
  OpenPartialHomeomorph.pi (fun i =>
    grassmannChart (Classical.choose (grassmann_atlas_covers (P i))))

theorem projectivePointChart_mem (P : ProjectiveProduct K) :
    P ∈ (projectivePointChart K P).source :=
  fun i _ => Classical.choose_spec (grassmann_atlas_covers (P i))

theorem projectivePointChart_target (P : ProjectiveProduct K) :
    (projectivePointChart K P).target = Set.univ := by
  ext A
  simp [projectivePointChart]

def projectivePointChartHomeomorph (P : ProjectiveProduct K) :
    (projectivePointChart K P).source ≃ₜ ProjectiveProductModel K :=
  (projectivePointChart K P).toHomeomorphSourceTarget.trans
    ((Homeomorph.setCongr (projectivePointChart_target K P)).trans (Homeomorph.Set.univ _))

/-- Local homology at every point of the actual projective product, rather
than only at the canonical section zero, has the genuine coordinate comparison. -/
def projectivePointLocalCoordinateIso (P : ProjectiveProduct K) (n : ℕ) :
    relativeSingularHomology (subspaceInclusion ({P}ᶜ : Set (ProjectiveProduct K))) n ≅
      relativeSingularHomology (subspaceInclusion ({0}ᶜ : Set (ProjectiveProductModel K))) n :=
  openChartCoordinateLocalHomologyIso _ (projectivePointChart K P).open_source P
    (projectivePointChart_mem K P) (projectivePointChartHomeomorph K P) n

/-- Every actual projective point has local integral homology concentrated
in the real dimension of the product. -/
theorem projectivePointLocalHomology_isZero (hp : 0 < ∑ i, K i)
    (P : ProjectiveProduct K) (n : ℕ) (hn : n ≠ 2*(∑ i, K i)) :
    IsZero (relativeSingularHomology
      (subspaceInclusion ({P}ᶜ : Set (ProjectiveProduct K))) n) := by
  have hd : 2 ≤ Module.finrank ℝ (ProjectiveProductModel K) := by
    rw [projectiveProduct_real_finrank]
    omega
  have hne : n ≠ Module.finrank ℝ (ProjectiveProductModel K) := by
    rwa [projectiveProduct_real_finrank]
  exact (localVectorHomology_isZero (ProjectiveProductModel K) hd n hne).of_iso
    (projectivePointLocalCoordinateIso K P n)

/-- At every projective point the top local integral group is ℤ. Choices of
charts and bases give separate generators; their orientation coherence is not asserted. -/
def projectivePointLocalTopHomologyIso (hp : 0 < ∑ i, K i) (P : ProjectiveProduct K) :
    relativeSingularHomology (subspaceInclusion ({P}ᶜ : Set (ProjectiveProduct K)))
      (2*(∑ i, K i)) ≅ ModuleCat.of ℤ ℤ := by
  let p := ∑ i, K i
  have hd : Module.finrank ℝ (ProjectiveProductModel K) = (2*p-2)+2 := by
    rw [projectiveProduct_real_finrank]
    dsimp [p]
    omega
  let e := projectivePointLocalCoordinateIso K P ((2*p-2)+2) ≪≫
    localVectorSphereHomologyIso (ProjectiveProductModel K) ((2*p-2)+1) (by omega) ≪≫
      finiteDimensionalSphereTopHomologyIso (ProjectiveProductModel K) (2*p-2) hd
  have he : (2*p-2)+2 = 2*p := by dsimp [p]; omega
  rw [he] at e
  exact e

/-- A primitive local class at every point, with no claim of a coherent
orientation or a global lift when the total complex dimension exceeds one. -/
def projectivePointLocalGenerator (hp : 0 < ∑ i, K i) (P : ProjectiveProduct K) :
    relativeSingularHomology (subspaceInclusion ({P}ᶜ : Set (ProjectiveProduct K)))
      (2*(∑ i, K i)) :=
  (projectivePointLocalTopHomologyIso K hp P).inv (1 : ℤ)

theorem projectivePointLocalGenerator_coordinate (hp : 0 < ∑ i, K i)
    (P : ProjectiveProduct K) :
    (projectivePointLocalTopHomologyIso K hp P).hom (projectivePointLocalGenerator K hp P) = (1 : ℤ) :=
  ConcreteCategory.congr_hom (projectivePointLocalTopHomologyIso K hp P).inv_hom_id 1

theorem projectivePointLocalGenerator_ne_zero (hp : 0 < ∑ i, K i)
    (P : ProjectiveProduct K) : projectivePointLocalGenerator K hp P ≠ 0 := by
  intro hz
  have h := projectivePointLocalGenerator_coordinate K hp P
  rw [hz, map_zero] at h
  norm_num at h

end

open CategoryTheory Limits
section
open ComplexGrassmann

/-- Local homology of a single projective space in actual graph coordinates. -/
def projectiveSpaceLocalCoordinateIso {k : ℕ} (P : Grassmann 1 k) (n : ℕ) :
    relativeSingularHomology (subspaceInclusion ({P}ᶜ : Set (Grassmann 1 k))) n ≅
      relativeSingularHomology (subspaceInclusion ({0}ᶜ : Set (GraphSlope 1 k))) n := by
  let F := (grassmann_atlas_covers P).choose
  have hF := (grassmann_atlas_covers P).choose_spec
  let e := (grassmannChart F).toHomeomorphSourceTarget.trans
    ((Homeomorph.setCongr (grassmannChart_target F)).trans (Homeomorph.Set.univ _))
  exact openChartCoordinateLocalHomologyIso _ (grassmannChart F).open_source P hF e n

theorem projectiveSpaceLocalHomology_isZero {k : ℕ} (hk : 0 < k)
    (P : Grassmann 1 k) (n : ℕ) (hn : n ≠ 2*k) :
    IsZero (relativeSingularHomology (subspaceInclusion ({P}ᶜ : Set (Grassmann 1 k))) n) := by
  have hd : 2 ≤ Module.finrank ℝ (GraphSlope 1 k) := by
    rw [graph_slope_real_finrank]; omega
  have hne : n ≠ Module.finrank ℝ (GraphSlope 1 k) := by
    rw [graph_slope_real_finrank]; omega
  exact (localVectorHomology_isZero (GraphSlope 1 k) hd n hne).of_iso
    (projectiveSpaceLocalCoordinateIso P n)

/-- The actual punctured-space homology reduces to the lower projective space. -/
def projectiveSpacePunctureHomologyIso {k : ℕ} (P : Grassmann 1 (k+1)) (n : ℕ) :
    (integralSingularHomology n).obj (TopCat.of ({P}ᶜ : Set (Grassmann 1 (k+1)))) ≅
      (integralSingularHomology n).obj (TopCat.of (Grassmann 1 k)) :=
  integralHomologyHomotopyIso (projectivePointPunctureLowerHomotopyEquiv P) n

end

end Kaplansky

end

end OAI
