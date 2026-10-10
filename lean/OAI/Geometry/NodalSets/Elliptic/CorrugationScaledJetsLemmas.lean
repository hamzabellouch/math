import OAI.Geometry.NodalSets.Elliptic.LocalizedCorrugation

namespace OAI

noncomputable section

namespace Yau.Geometry

section

open Yau.Jets
open scoped ContDiff

lemma scalar_const_mul_second (c : ℝ) (f : Coord → ℝ) (hf : ContDiff ℝ ∞ f)
    (x u v : Coord) :
    fderiv ℝ (fderiv ℝ (fun z ↦ c*f z)) x u v = c*fderiv ℝ (fderiv ℝ f) x u v := by
  simpa using scalar_product_second (fun _ ↦ c) f contDiff_const hf x u v

lemma localizedCorrugation_first (χ : Coord → ℝ) (f : (ℝ × ℝ) → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hf : ContDiff ℝ ∞ f)
    (s J R : ℝ) (a b : Coord →L[ℝ] ℝ) (y x v : Coord) :
    fderiv ℝ (localizedCorrugation χ f s J R a b y) x v =
      (s/J) * (fderiv ℝ χ (corrugationSlowMap R (x-y)) (corrugationSlowMap R v) *
        f (corrugationFastMap J a b (x-y)) +
        χ (corrugationSlowMap R (x-y)) *
          fderiv ℝ f (corrugationFastMap J a b (x-y)) (corrugationFastMap J a b v)) := by
  let A := corrugationSlowMap R
  let B := corrugationFastMap J a b
  have hA : ContDiff ℝ ∞ (fun z ↦ χ (A (z-y))) :=
    hχ.comp (A.contDiff.comp (contDiff_id.sub contDiff_const))
  have hB : ContDiff ℝ ∞ (fun z ↦ f (B (z-y))) :=
    hf.comp (B.contDiff.comp (contDiff_id.sub contDiff_const))
  have he : localizedCorrugation χ f s J R a b y =
      (fun z ↦ (s/J)*(χ (A (z-y))*f (B (z-y)))) := by
    funext z; dsimp [localizedCorrugation,A,B]; ring
  rw [he]
  have hd := ((hA.differentiable (by simp) x).hasFDerivAt.mul
    (hB.differentiable (by simp) x).hasFDerivAt).const_mul (s/J)
  change HasFDerivAt (fun z ↦ (s/J)*(χ (A (z-y))*f (B (z-y)))) _ x at hd
  rw [hd.fderiv]
  simp only [smul_apply,add_apply,smul_eq_mul]
  rw [affine_scalar_first χ hχ,affine_scalar_first f hf]
  dsimp [A,B]
  ring

lemma localizedCorrugation_second (χ : Coord → ℝ) (f : (ℝ × ℝ) → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hf : ContDiff ℝ ∞ f)
    (s J R : ℝ) (a b : Coord →L[ℝ] ℝ) (y x u v : Coord) :
    fderiv ℝ (fderiv ℝ (localizedCorrugation χ f s J R a b y)) x u v =
      (s/J) * (
        fderiv ℝ (fderiv ℝ χ) (corrugationSlowMap R (x-y))
          (corrugationSlowMap R u) (corrugationSlowMap R v) * f (corrugationFastMap J a b (x-y)) +
        fderiv ℝ χ (corrugationSlowMap R (x-y)) (corrugationSlowMap R v) *
          fderiv ℝ f (corrugationFastMap J a b (x-y)) (corrugationFastMap J a b u) +
        fderiv ℝ χ (corrugationSlowMap R (x-y)) (corrugationSlowMap R u) *
          fderiv ℝ f (corrugationFastMap J a b (x-y)) (corrugationFastMap J a b v) +
        χ (corrugationSlowMap R (x-y)) *
          fderiv ℝ (fderiv ℝ f) (corrugationFastMap J a b (x-y))
            (corrugationFastMap J a b u) (corrugationFastMap J a b v)) := by
  let A := corrugationSlowMap R
  let B := corrugationFastMap J a b
  have hA : ContDiff ℝ ∞ (fun z ↦ χ (A (z-y))) :=
    hχ.comp (A.contDiff.comp (contDiff_id.sub contDiff_const))
  have hB : ContDiff ℝ ∞ (fun z ↦ f (B (z-y))) :=
    hf.comp (B.contDiff.comp (contDiff_id.sub contDiff_const))
  have he : localizedCorrugation χ f s J R a b y =
      (fun z ↦ (s/J)*(χ (A (z-y))*f (B (z-y)))) := by
    funext z; dsimp [localizedCorrugation,A,B]; ring
  rw [he,scalar_const_mul_second _ _ (hA.mul hB),scalar_product_second _ _ hA hB]
  simp only [affine_scalar_first χ hχ,affine_scalar_first f hf,
    affine_scalar_second χ hχ,affine_scalar_second f hf]
  rfl

end

open Yau.Jets Set Filter
open scoped ContDiff Topology
variable {ι : Type*}

lemma finite_sum_compact_support (I : Finset ι) (w : ι → Coord → ℝ)
    (hw : ∀ i ∈ I, HasCompactSupport (w i)) :
    HasCompactSupport (fun x ↦ ∑ i ∈ I, w i x) := by
  classical
  induction I using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    change HasCompactSupport (0 : Coord → ℝ)
    exact HasCompactSupport.zero
  | @insert i I hi ih =>
    simp only [Finset.sum_insert hi]
    change HasCompactSupport (w i + fun x ↦ ∑ j ∈ I, w j x)
    exact (hw i (Finset.mem_insert_self i I)).add (ih (fun j hj ↦ hw j (Finset.mem_insert_of_mem hj)))

lemma finite_sum_support_subset (I : Finset ι) (w : ι → Coord → ℝ) (U : Set Coord)
    (hw : ∀ i ∈ I, tsupport (w i) ⊆ U) :
    tsupport (fun x ↦ ∑ i ∈ I, w i x) ⊆ U := by
  classical
  induction I using Finset.induction_on with
  | empty => simp
  | @insert i I hi ih =>
    simp only [Finset.sum_insert hi]
    exact (tsupport_add _ _).trans (union_subset
      (hw i (Finset.mem_insert_self i I)) (ih (fun j hj ↦ hw j (Finset.mem_insert_of_mem hj))))

lemma finite_disjoint_sum_eventually (I : Finset ι) (w : ι → Coord → ℝ)
    (hd : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (tsupport (w i)) (tsupport (w j)))
    {i : ι} (hi : i ∈ I) {x : Coord} (hx : x ∈ tsupport (w i)) :
    (fun z ↦ ∑ j ∈ I, w j z) =ᶠ[𝓝 x] w i := by
  classical
  have hz : ∀ j ∈ I, j ≠ i → w j =ᶠ[𝓝 x] 0 := by
    intro j hj hji
    apply notMem_tsupport_iff_eventuallyEq.mp
    exact fun hjx ↦ Set.disjoint_left.mp (hd i hi j hj hji.symm) hx hjx
  have he : ∀ᶠ z in 𝓝 x, ∀ j ∈ I, j ≠ i → w j z = 0 := by
    apply (eventually_all_finite I.finite_toSet).mpr
    intro j hj
    by_cases hji : j=i
    · simp [hji]
    · filter_upwards [hz j hj hji] with z hz
      exact fun _ ↦ hz
  filter_upwards [he] with z hz
  exact Finset.sum_eq_single i hz (fun h ↦ (h hi).elim)

lemma finite_disjoint_sum_jets (I : Finset ι) (w : ι → Coord → ℝ)
    (hd : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (tsupport (w i)) (tsupport (w j)))
    {i : ι} (hi : i ∈ I) {x : Coord} (hx : x ∈ tsupport (w i)) :
    fderiv ℝ (fun z ↦ ∑ j ∈ I, w j z) x = fderiv ℝ (w i) x ∧
    fderiv ℝ (fderiv ℝ (fun z ↦ ∑ j ∈ I, w j z)) x = fderiv ℝ (fderiv ℝ (w i)) x := by
  have h := finite_disjoint_sum_eventually I w hd hi hx
  exact ⟨h.fderiv_eq,h.fderiv.fderiv_eq⟩

lemma finite_disjoint_sum_bound (I : Finset ι) (w : ι → Coord → ℝ)
    (hd : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (tsupport (w i)) (tsupport (w j)))
    {B : ℝ} (hB : 0 ≤ B) (hw : ∀ i ∈ I, ∀ x, |w i x| ≤ B) (x : Coord) :
    |∑ i ∈ I, w i x| ≤ B := by
  classical
  by_cases hx : ∃ i ∈ I, x ∈ tsupport (w i)
  · obtain ⟨i,hi,hxi⟩ := hx
    rw [(finite_disjoint_sum_eventually I w hd hi hxi).eq_of_nhds]
    exact hw i hi x
  · have hz : ∀ i ∈ I, w i x = 0 := by
      intro i hi
      by_contra h
      exact hx ⟨i,hi,subset_tsupport _ h⟩
    rw [Finset.sum_eq_zero hz,abs_zero]
    exact hB

end Yau.Geometry

end

end OAI
