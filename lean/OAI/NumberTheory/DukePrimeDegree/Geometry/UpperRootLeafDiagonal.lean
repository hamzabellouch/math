import OAI.NumberTheory.DukePrimeDegree.Geometry.UpperRootDiagonalCharts

namespace OAI

/-! # Diagonal covariance of actual full upper-root conditional leaves -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal BigOperators

namespace DukePrimeDegree
open PrimeDegreePackets
namespace UpperRootBox
variable {n : ℕ} {g : G n}

lemma base_ae_of_ae (A B : UpperRootBox n g) (hAB : A.time ⊆ B.time)
    (μ : Measure (X n)) [IsFiniteMeasure μ] {p : UpperRootTransverse n → Prop}
    (hp : ∀ᵐ s ∂(B.coordinateMeasure μ).fst, p s) :
    ∀ᵐ s ∂(A.coordinateMeasure μ).fst, s ∈ B.transverse → p s := by
  let U := A.transverse ∩ B.transverse
  have hU : IsOpen U := A.transverse_open.inter B.transverse_open
  have H := (B.shrink_marginal_absolutelyContinuous U A.time hU A.time_open
    inter_subset_right hAB μ).ae_le (ae_restrict_of_ae hp)
  have hE : B.shrink U A.time hU A.time_open inter_subset_right hAB =
      A.shrink U A.time hU A.time_open inter_subset_left subset_rfl := rfl
  rw [hE,A.shrink_full_time_marginal] at H
  have H' := (ae_restrict_iff' hU.measurableSet).mp H
  filter_upwards [H',A.coordinateMeasure_fst_ae_transverse μ] with s hs hsA
  exact fun hsB => hs ⟨hsA,hsB⟩

theorem ae_leafMeasure_diagonal (A : UpperRootBox n g) (R S : ℝ)
    (hAR : A.time ⊆ upperRootWindow n R 0)
    (ell : Fin n → ℝ) (hell : ∑ i, ell i = 0) (t : ℝ)
    (hAS : (A.diagonal ell hell t).time ⊆ upperRootWindow n S 0)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v ∈ positiveRootGeneratedGroup (allPositiveRoots n),
      rightAction x v = x → v = 1)
    (hinv : μ.map (fun x => rightAction x (diagonalOneParameter ell hell t)) = μ) :
    ∀ᵐ s ∂(A.coordinateMeasure μ).fst,
      (A.diagonal ell hell t).leafMeasure S μ (upperRootTransverseDiagonal ell hell t s) =
        (A.leafMeasure R μ s).map ((completeRootChain n).rootDilation ell (-t)) := by
  let C := upperRootLongBoxFamily n g R
  let (m : ℕ) : Countable (C m) := (upperRootLongBoxFamily_countable n g R m).to_subtype
  let e := upperRootTransverseDiagonalHomeomorph ell hell t
  let f := (completeRootChain n).rootDilation ell (-t)
  let AD := A.diagonal ell hell t
  have hT (m : ℕ) (B : C m) : B.val.time = upperRootWindow n R m :=
    upperRootLongBoxFamily_time n g R m B.val B.prop
  have hinc (m : ℕ) (B : C m) : A.time ⊆ B.val.time := by
    rw [hT m B]
    exact hAR.trans (upperRootWindow_mono n R (Nat.zero_le m))
  have hincD (m : ℕ) (B : C m) : AD.time ⊆ (B.val.diagonal ell hell t).time :=
    image_mono (hinc m B)
  have hcov : ∀ᵐ s ∂(A.coordinateMeasure μ).fst, ∀ (m : ℕ) (B : C m),
      s ∈ B.val.transverse →
      (B.val.diagonal ell hell t).conditionalKernel μ (e s) =
        (B.val.conditionalKernel μ s).map f := by
    apply ae_all_iff.mpr
    intro m
    apply ae_all_iff.mpr
    intro B
    exact base_ae_of_ae A B.val (hinc m B) μ
      (B.val.diagonal_conditionalKernel ell hell t μ hinv)
  have hD : ∀ᵐ s ∂(A.coordinateMeasure μ).fst, ∀ (m : ℕ) (B : C m),
      s ∈ B.val.transverse →
      (AD.leafMeasure S μ (e s)).restrict (f '' B.val.time) =
        (anchorNormalize ((B.val.diagonal ell hell t).conditionalKernel μ (e s))
          (f '' A.time)).restrict (f '' B.val.time) := by
    apply ae_all_iff.mpr
    intro m
    apply ae_all_iff.mpr
    intro B
    have H := AD.ae_leafMeasure_restrict S hAS μ hfree
      (B.val.diagonal ell hell t) (hincD m B)
    rw [A.diagonal_marginal ell hell t μ hinv] at H
    have H' := e.toMeasurableEquiv.measurableEmbedding.ae_map_iff.mp H
    filter_upwards [H'] with s hs
    intro hsB
    exact (hs (mem_image_of_mem e hsB)).2
  filter_upwards [A.ae_leafMeasure_spec R hAR μ hfree,
    A.ae_injective_upperRoot_slice_of_ae_free μ hfree,hcov,hD] with s hs hi hc hd
  apply measure_eq_of_restrictionChain (fun m => f '' upperRootWindow n R m)
    (fun a b hab => image_mono (upperRootWindow_mono n R hab))
    (by rw [←image_iUnion,upperRootWindow_cover,image_univ,f.surjective.range_eq])
  intro m
  obtain ⟨B,hBC,hsB⟩ := upperRootLongBoxFamily_covers n g R m s hi
  let B' : C m := ⟨B,hBC⟩
  have H := hd m B' hsB
  rw [hc m B' hsB] at H
  have ha : anchorNormalize ((B.conditionalKernel μ s).map f) (f '' A.time) =
      (anchorNormalize (B.conditionalKernel μ s) A.time).map f :=
    anchorNormalize_map_equiv (B.conditionalKernel μ s) f.toMeasurableEquiv A.time
  change (AD.leafMeasure S μ (e s)).restrict (f '' B.time) =
    (anchorNormalize ((B.conditionalKernel μ s).map f) (f '' A.time)).restrict (f '' B.time) at H
  rw [ha] at H
  change (AD.leafMeasure S μ (e s)).restrict (f '' upperRootWindow n R m) =
    ((A.leafMeasure R μ s).map f).restrict (f '' upperRootWindow n R m)
  have hmap (ν : Measure (UpperRootTime n)) (J : Set (UpperRootTime n)) :
      (ν.map f).restrict (f '' J) = (ν.restrict J).map f := by
    exact (f.toMeasurableEquiv.restrict_map ν (f '' J)).trans
      (congrArg (fun T : Set (UpperRootTime n) => (ν.restrict T).map f) (f.injective.preimage_image J))
  rw [hmap,hs.2.2.2 m B hBC hsB]
  rw [hmap] at H
  simpa only [upperRootLongBoxFamily_time n g R m B hBC] using H

lemma diagonal_time_bound (A : UpperRootBox n g) (R : ℝ)
    (hAR : A.time ⊆ upperRootWindow n R 0)
    (ell : Fin n → ℝ) (hell : ∑ i, ell i = 0) (t : ℝ) :
    ∃ S : ℝ, (A.diagonal ell hell t).time ⊆ upperRootWindow n S 0 := by
  let f := (completeRootChain n).rootDilation ell (-t)
  have hc := ((completeRootChain n).closedCube_compact R).image f.continuous
  obtain ⟨m, hm⟩ := hc.elim_directed_cover (upperRootWindow n 0)
    (upperRootWindow_open n 0) (by rw [upperRootWindow_cover]; exact subset_univ _)
    (fun a b => ⟨max a b, upperRootWindow_mono n 0 (le_max_left _ _),
      upperRootWindow_mono n 0 (le_max_right _ _)⟩)
  refine ⟨m, ?_⟩
  have hA : A.time ⊆ (completeRootChain n).closedCube R := by
    exact hAR.trans (by simpa only [upperRootWindow, Nat.cast_zero, add_zero] using
      (completeRootChain n).cube_subset_closedCube R)
  have H := (image_mono hA).trans hm
  change f '' A.time ⊆ upperRootWindow n (m : ℝ) 0
  simpa only [upperRootWindow, Nat.cast_zero, zero_add, add_zero] using H

theorem ae_basedLeaf_diagonal (A : UpperRootBox n g) (R S : ℝ)
    (hAR : A.time ⊆ upperRootWindow n R 0)
    (ell : Fin n → ℝ) (hell : ∑ i, ell i = 0) (t : ℝ)
    (hAS : (A.diagonal ell hell t).time ⊆ upperRootWindow n S 0)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v ∈ positiveRootGeneratedGroup (allPositiveRoots n),
      rightAction x v = x → v = 1)
    (hinv : μ.map (fun x => rightAction x (diagonalOneParameter ell hell t)) = μ) :
    ∀ᵐ z ∂A.coordinateMeasure μ,
      (A.diagonal ell hell t).basedLeaf S μ (upperRootDiagonalCoordinates ell hell t z) =
        anchorNormalize ((A.basedLeaf R μ z).map
          ((completeRootChain n).rootDilation ell (-t))) ((completeRootChain n).cube 1) := by
  have H := ae_of_ae_map measurable_fst.aemeasurable
    (A.ae_leafMeasure_diagonal R S hAR ell hell t hAS μ hfree hinv)
  have Hlf := ae_of_ae_map measurable_fst.aemeasurable
    ((A.ae_leafMeasure_spec R hAR μ hfree).mono fun s hs => hs.1)
  filter_upwards [H,Hlf,A.ae_mem_leafMeasure_support R hAR μ hfree] with z hz hlf ht
  let : IsLocallyFiniteMeasure (A.leafMeasure R μ z.1) := hlf
  change basedUpperRootMeasure n
    ((A.diagonal ell hell t).leafMeasure S μ (upperRootTransverseDiagonal ell hell t z.1))
    ((completeRootChain n).rootDilation ell (-t) z.2) = _
  rw [hz]
  exact basedUpperRootMeasure_dilation n _ ell hell (-t) _ ht

end UpperRootBox
end DukePrimeDegree

end

end OAI
