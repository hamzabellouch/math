import Mathlib.Analysis.InnerProductSpace.NormDet
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace OAI

open scoped RealInnerProductSpace

namespace ProjectionCounterexample

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]

abbrev perpendicularTo (v : V) : Submodule ℝ V := (ℝ ∙ v)ᗮ

/-- Restrict the actual orthogonal projection to the source tangent hyperplane. -/
def hyperplaneProjection (n u : V) : perpendicularTo n →ₗ[ℝ] V :=
  (perpendicularTo u).starProjection.toLinearMap.comp (perpendicularTo n).subtype

theorem perpendicularTo_finrank {n : V} (hn : ‖n‖ = 1) :
    Module.finrank ℝ (perpendicularTo n) = Module.finrank ℝ V - 1 := by
  have hn0 : n ≠ 0 := by
    intro h
    rw [h, norm_zero] at hn
    exact zero_ne_one hn
  have h := (ℝ ∙ n).finrank_add_finrank_orthogonal
  have h' := congrArg (fun k : ℕ => k - 1) h
  simpa only [finrank_span_singleton hn0, Nat.add_sub_cancel_left] using h'

omit [FiniteDimensional ℝ V] in
theorem perpendicularTo_projection_apply {u : V} (hu : ‖u‖ = 1) (x : V) :
    (perpendicularTo u).starProjection x = x - ⟪u, x⟫ • u := by
  rw [Submodule.starProjection_orthogonal_val,
    Submodule.starProjection_unit_singleton ℝ hu]

omit [FiniteDimensional ℝ V] in
theorem inner_perpendicularTo_projection {u : V} (hu : ‖u‖ = 1) (x y : V) :
    ⟪(perpendicularTo u).starProjection x, (perpendicularTo u).starProjection y⟫ =
      ⟪x, y⟫ - ⟪u, x⟫ * ⟪u, y⟫ := by
  rw [perpendicularTo_projection_apply hu, perpendicularTo_projection_apply hu]
  simp only [inner_sub_left, inner_sub_right, real_inner_smul_left,
    real_inner_smul_right, real_inner_self_eq_norm_sq, hu, one_pow, mul_one]
  rw [real_inner_comm x u]
  ring

/-- The projected facet's area factor is the absolute inner product of unit normals. -/
theorem hyperplaneProjection_normDet {n u : V} (hn : ‖n‖ = 1) (hu : ‖u‖ = 1) :
    (hyperplaneProjection n u).normDet = |⟪n, u⟫| := by
  classical
  let b := stdOrthonormalBasis ℝ (perpendicularTo n)
  let a : Fin (Module.finrank ℝ (perpendicularTo n)) → ℝ :=
    fun i => ⟪u, (b i : V)⟫
  let f := hyperplaneProjection n u
  have hGram : Matrix.gram ℝ (fun i => f (b i)) =
      1 + Matrix.replicateCol Unit (-a) * Matrix.replicateRow Unit a := by
    ext i j
    rw [Matrix.gram_apply]
    change ⟪(perpendicularTo u).starProjection (b i : V),
      (perpendicularTo u).starProjection (b j : V)⟫ = _
    rw [inner_perpendicularTo_projection hu]
    have hbij : ⟪(b i : V), (b j : V)⟫ = if i = j then 1 else 0 :=
      b.inner_eq_ite i j
    rw [hbij]
    simp [Matrix.add_apply, Matrix.one_apply, Matrix.mul_apply,
      Matrix.replicateCol_apply, Matrix.replicateRow_apply, a, sub_eq_add_neg]
  have hparseval : ∑ i, (a i) ^ 2 =
      ‖(perpendicularTo n).orthogonalProjectionOnto u‖ ^ 2 := by
    calc
      ∑ i, (a i) ^ 2 =
          ∑ i, ⟪b i, (perpendicularTo n).orthogonalProjectionOnto u⟫ ^ 2 := by
        apply Finset.sum_congr rfl
        intro i _
        congr 1
        rw [Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left]
        exact real_inner_comm _ _
      _ = ‖(perpendicularTo n).orthogonalProjectionOnto u‖ ^ 2 :=
        b.sum_sq_inner_right _
  have hnormal : ‖(ℝ ∙ n).starProjection u‖ ^ 2 = ⟪n, u⟫ ^ 2 := by
    rw [Submodule.starProjection_unit_singleton ℝ hn]
    simp [norm_smul, hn, Real.norm_eq_abs, sq_abs]
  have hsum : ∑ i, (a i) ^ 2 = 1 - ⟪n, u⟫ ^ 2 := by
    have hp := Submodule.norm_sq_eq_add_norm_sq_starProjection u (ℝ ∙ n)
    rw [hu, one_pow, hnormal] at hp
    change 1 = ⟪n, u⟫ ^ 2 + ‖(perpendicularTo n).orthogonalProjectionOnto u‖ ^ 2 at hp
    rw [← hparseval] at hp
    linarith
  have hsquare : f.normDet ^ 2 = ⟪n, u⟫ ^ 2 := by
    calc
      f.normDet ^ 2 = (Matrix.gram ℝ (fun i => f (b i))).det :=
        f.normDet_sq_eq_det_gram b
      _ = 1 + a ⬝ᵥ (-a) := by
        rw [hGram, Matrix.det_one_add_replicateCol_mul_replicateRow]
      _ = 1 - ∑ i, (a i) ^ 2 := by
        simp [dotProduct, pow_two, Finset.sum_neg_distrib, sub_eq_add_neg]
      _ = ⟪n, u⟫ ^ 2 := by rw [hsum]; ring
  apply (sq_eq_sq₀ f.normDet_nonneg (abs_nonneg _)).mp
  simpa using hsquare

/-- The same area factor for any linear chart into the source tangent hyperplane.
The chart may be singular; the norm determinant identity handles that case as well. -/
theorem normDet_project_comp {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
    [FiniteDimensional ℝ U] (L : U →ₗ[ℝ] V) {n u : V}
    (hn : ‖n‖ = 1) (hu : ‖u‖ = 1)
    (hmem : ∀ x, ⟪n, L x⟫ = 0)
    (hrank : Module.finrank ℝ U = Module.finrank ℝ V - 1) :
    ((perpendicularTo u).starProjection.toLinearMap.comp L).normDet =
      |⟪n, u⟫| * L.normDet := by
  let L' : U →ₗ[ℝ] perpendicularTo n := L.codRestrict (perpendicularTo n)
    (fun x => Submodule.mem_orthogonal_singleton_iff_inner_right.mpr (hmem x))
  have hdim : Module.finrank ℝ U = Module.finrank ℝ (perpendicularTo n) :=
    hrank.trans (perpendicularTo_finrank hn).symm
  have hL : L'.normDet = L.normDet := by
    dsimp only [L']
    exact LinearMap.normDet_codRestrict
      (fun x => Submodule.mem_orthogonal_singleton_iff_inner_right.mpr (hmem x))
  calc
    ((perpendicularTo u).starProjection.toLinearMap.comp L).normDet =
        ((hyperplaneProjection n u).comp L').normDet := rfl
    _ = (hyperplaneProjection n u).normDet * L'.normDet :=
      LinearMap.normDet_comp_of_finrank_eq L' (hyperplaneProjection n u) hdim
    _ = |⟪n, u⟫| * L.normDet := by rw [hyperplaneProjection_normDet hn hu, hL]

open MeasureTheory Measure in
theorem hyperplaneProjection_measure_image [MeasurableSpace V] [BorelSpace V]
    {n u : V} (hn : ‖n‖ = 1) (hu : ‖u‖ = 1) (s : Set (perpendicularTo n)) :
    μHE[Module.finrank ℝ (perpendicularTo n)] (hyperplaneProjection n u '' s) =
      ENNReal.ofReal |⟪n, u⟫| * volume s := by
  rw [(hyperplaneProjection n u).euclideanHausdorffMeasure_image_eq_normDet_mul_volume,
    hyperplaneProjection_normDet hn hu]

open MeasureTheory Measure in
theorem hyperplaneProjection_measure_translated [MeasurableSpace V] [BorelSpace V]
    {n u : V} (hn : ‖n‖ = 1) (hu : ‖u‖ = 1) (c : V)
    (s : Set (perpendicularTo n)) :
    μHE[Module.finrank ℝ (perpendicularTo n)]
        ((perpendicularTo u).starProjection '' ((fun x : perpendicularTo n => c + (x : V)) '' s)) =
      ENNReal.ofReal |⟪n, u⟫| *
        μHE[Module.finrank ℝ (perpendicularTo n)] ((fun x : perpendicularTo n => c + (x : V)) '' s) := by
  have hshift : Isometry (fun x : perpendicularTo n => c + (x : V)) :=
    (isometry_add_left c).comp isometry_subtype_coe
  have himage :
      (perpendicularTo u).starProjection '' ((fun x : perpendicularTo n => c + (x : V)) '' s) =
        (fun y : V => (perpendicularTo u).starProjection c + y) ''
          (hyperplaneProjection n u '' s) := by
    rw [Set.image_image, Set.image_image]
    congr 1
    funext x
    exact map_add (perpendicularTo u).starProjection c (x : V)
  rw [himage, (isometry_add_left _).euclideanHausdorffMeasure_image,
    hyperplaneProjection_measure_image hn hu, hshift.euclideanHausdorffMeasure_image,
    InnerProductSpace.euclideanHausdorffMeasure_eq_volume]

end

end ProjectionCounterexample

end OAI
