import OAI.Analysis.KadisonKastler.MatrixAveraging
import OAI.Analysis.KadisonKastler.PublishedDixmier
import Mathlib.Analysis.Convex.Combination

namespace OAI

/-! # Scalar averaging inside a full finite matrix algebra -/

namespace KadisonKastler

open Generator
open scoped BigOperators

noncomputable section

variable {G V : Type*} [Fintype G] [Nonempty G]
  [NormedAddCommGroup V] [NormedSpace ℂ V]

/-- Uniform finite averages belong to the real convex hull of their values. -/
theorem finiteAverage_mem_convexHull (f : G → V) :
    finiteAverage f ∈ convexHull ℝ (Set.range f) := by
  have h := (Finset.univ : Finset G).centerMass_mem_convexHull
    (w := fun _ => (1 : ℝ)) (z := f) (s := Set.range f) (by intros; norm_num)
    (by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
        exact_mod_cast Fintype.card_pos (α := G))
    (fun i _ => Set.mem_range_self i)
  have hr : ((Fintype.card G : ℝ)⁻¹) • (∑ i, f i) ∈
      convexHull ℝ (Set.range f) := by
    simpa only [Finset.centerMass, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      mul_one, one_smul] using h
  change ((Fintype.card G : ℂ)⁻¹) • (∑ i, f i) ∈ convexHull ℝ (Set.range f)
  have he : ((Fintype.card G : ℂ)⁻¹) = (((Fintype.card G : ℝ)⁻¹ : ℝ) : ℂ) := by simp
  have hs := RCLike.real_smul_eq_coe_smul (K := ℂ) ((Fintype.card G : ℝ)⁻¹) (∑ i, f i)
  rw [hs] at hr
  rw [he]
  exact hr


variable {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [Nontrivial H] [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- The center of a concrete full matrix algebra consists of scalars. -/
theorem matrixUnits_scalar_of_mem_of_commutes
    (E : MatrixUnitSystem ι (H →L[ℂ] H))
    (x : H →L[ℂ] H) (hx : x ∈ E.algebra)
    (hc : ∀ i j, Commute (E.entry i j) x) :
    ∃ z : ℂ, x = z • (1 : H →L[ℂ] H) := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨z, hz⟩ := Matrix.mem_range_scalar_of_commute_single (M := a) (by
    intro i j _
    apply E.injective
    simp only [map_mul, E.hom_single, one_smul]
    exact (hc i j).eq)
  refine ⟨z, ?_⟩
  have he : Matrix.scalar ι z = z • (1 : Matrix ι ι ℂ) := by
    ext i j
    simp [Matrix.scalar_apply, Matrix.diagonal, Matrix.one_apply, smul_eq_mul]
  change E.hom a = z • (1 : H →L[ℂ] H)
  rw [← hz, he, map_smul, map_one]

/-- Averaging over the finite signed group sends its whole matrix algebra
into the ambient scalar operators. -/
theorem matrixUnitAverage_scalar (E : MatrixUnitSystem ι (H →L[ℂ] H))
    (x : H →L[ℂ] H) (hx : x ∈ E.algebra) :
    ∃ z : ℂ, matrixUnitAverage E x = z • (1 : H →L[ℂ] H) := by
  have hm : matrixUnitAverage E x ∈ E.algebra := by
    apply E.algebra.smul_mem
    apply E.algebra.sum_mem
    intro g _
    exact E.algebra.mul_mem
      (E.algebra.mul_mem (matrixUnitSignedRepresentation_mem E g) hx)
      (star_mem (s := E.algebra) (matrixUnitSignedRepresentation_mem E g))
  exact matrixUnits_scalar_of_mem_of_commutes E _ hm
    (fun i j => matrixUnitAverage_commutes E x _ (E.entry_mem i j))

omit [Nontrivial H] [Nonempty ι] in
/-- The same average lies in the actual ambient unitary orbit hull. -/
theorem matrixUnitAverage_mem_orbitHull (E : MatrixUnitSystem ι (H →L[ℂ] H))
    (M : VonNeumannAlgebra H) (hE : E.algebra ≤ M.toStarSubalgebra)
    (x : H →L[ℂ] H) :
    matrixUnitAverage E x ∈ convexHull ℝ (innerUnitaryOrbit M x) := by
  apply (convexHull_mono (s := Set.range (fun g =>
      unitaryConj (matrixUnitSignedRepresentation E g) x)) ?_)
    (finiteAverage_mem_convexHull _)
  rintro _ ⟨g, rfl⟩
  let u := algebraUnitaryOfMem (matrixUnitSignedRepresentation E g)
    (hE (matrixUnitSignedRepresentation_mem E g))
  exact ⟨u, rfl⟩

end

end KadisonKastler

end OAI
