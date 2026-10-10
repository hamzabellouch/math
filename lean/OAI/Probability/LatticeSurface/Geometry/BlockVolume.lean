import Mathlib
import OAI.Probability.LatticeSurface.Geometry.TriangularCover
import OAI.Probability.LatticeSurface.Geometry.TriangularGeometry

namespace OAI

open MeasureTheory

open scoped ENNReal

noncomputable section

namespace TriangularLipschitz

@[simp] lemma mem_interior {L : ℕ} {x : Vertex} :
    x ∈ interior L ↔ (1 ≤ x.1 ∧ x.1 ≤ (L : ℤ) - 1) ∧
      (1 ≤ x.2 ∧ x.2 ≤ (L : ℤ) - 1) := by
  simp [interior]

lemma interior_subset_box (L : ℕ) : interior L ⊆ box L := by
  intro x hx
  simp only [mem_interior, mem_box] at hx ⊢
  omega

@[simp] lemma origin_not_interior (L : ℕ) : (0,0) ∉ interior L := by
  simp [mem_interior]

@[simp] lemma filledHeight_free (L : ℕ) (s : Vertex → ℝ) (a : Filling L)
    (x : {x : Vertex // x ∈ interior L}) : filledHeight L s a x = a x :=
  dite_eq_left x.property

@[simp] lemma filledHeight_fixed (L : ℕ) (s : Vertex → ℝ) (a : Filling L)
    {x : Vertex} (hx : x ∉ interior L) : filledHeight L s a x = s x :=
  dite_eq_right hx

lemma continuous_filledHeight (L : ℕ) (s : Vertex → ℝ) (x : Vertex) :
    Continuous (fun a : Filling L => filledHeight L s a x) := by
  unfold filledHeight
  split_ifs with hx
  · exact continuous_apply (⟨x,hx⟩ : {x : Vertex // x ∈ interior L})
  · exact continuous_const

lemma isClosed_fillingPolytope (L : ℕ) (s : Vertex → ℝ) :
    IsClosed (fillingPolytope L s) := by
  simp only [fillingPolytope, Set.ofPred_forall]
  exact isClosed_iInter fun x => isClosed_iInter fun _ =>
    isClosed_iInter fun y => isClosed_iInter fun _ => isClosed_iInter fun _ =>
      isClosed_le ((continuous_filledHeight L s x).sub
        (continuous_filledHeight L s y)).abs continuous_const

lemma measurableSet_fillingPolytope (L : ℕ) (s : Vertex → ℝ) :
    MeasurableSet (fillingPolytope L s) := (isClosed_fillingPolytope L s).measurableSet

def filledHeightAffine (L : ℕ) (s : Vertex → ℝ) (x : Vertex) :
    Filling L →ᵃ[ℝ] ℝ :=
  if hx : x ∈ interior L then (LinearMap.proj ⟨x,hx⟩).toAffineMap
  else AffineMap.const ℝ _ (s x)

@[simp] lemma filledHeightAffine_apply (L : ℕ) (s : Vertex → ℝ) (x : Vertex)
    (a : Filling L) : filledHeightAffine L s x a = filledHeight L s a x := by
  unfold filledHeightAffine filledHeight
  split_ifs <;> rfl

lemma convex_fillingPolytope (L : ℕ) (s : Vertex → ℝ) :
    Convex ℝ (fillingPolytope L s) := by
  intro a ha b hb α β hα hβ hsum x hx y hy hxy
  let φ := filledHeightAffine L s x - filledHeightAffine L s y
  have hφ : ∀ c, φ c = filledHeight L s c x - filledHeight L s c y := by
    intro c
    simp only [φ, AffineMap.coe_sub, Pi.sub_apply, filledHeightAffine_apply]
  have h := ((convex_Icc (-1 : ℝ) 1).affine_preimage φ)
    (show φ a ∈ Set.Icc (-1) 1 by rw [hφ]; exact abs_le.mp (ha x hx y hy hxy))
    (show φ b ∈ Set.Icc (-1) 1 by rw [hφ]; exact abs_le.mp (hb x hx y hy hxy))
    hα hβ hsum
  rw [Set.mem_preimage, hφ] at h
  exact abs_le.mpr h

lemma latticeDist_origin_le {L : ℕ} {x : Vertex} (hx : x ∈ box L) :
    latticeDist x (0,0) ≤ 2 * (L : ℝ) := by
  obtain ⟨⟨hx0,hxL⟩,⟨hy0,hyL⟩⟩ := mem_box.mp hx
  have hx0' : (0 : ℝ) ≤ x.1 := by exact_mod_cast hx0
  have hy0' : (0 : ℝ) ≤ x.2 := by exact_mod_cast hy0
  have hxL' : (x.1 : ℝ) ≤ L := by exact_mod_cast hxL
  have hyL' : (x.2 : ℝ) ≤ L := by exact_mod_cast hyL
  simp only [latticeDist, Int.cast_zero, sub_zero, abs_of_nonneg hx0',
    abs_of_nonneg hy0', abs_of_nonneg (add_nonneg hx0' hy0'), max_le_iff]
  constructor
  · constructor <;> linarith
  · linarith

lemma fillingPolytope_subset_closedBall (L : ℕ) (s : Vertex → ℝ) :
    fillingPolytope L s ⊆ Metric.closedBall (fun _ => s (0,0) : Filling L) (2*L) := by
  intro a ha
  rw [Metric.mem_closedBall, dist_pi_le_iff (by positivity : (0 : ℝ) ≤ 2*L)]
  intro x
  have h := near_global_bound ha (interior_subset_box L x.property)
    (show (0,0) ∈ box L by simp)
  rw [filledHeight_free, filledHeight_fixed _ _ _ (origin_not_interior L), one_mul] at h
  exact h.trans (latticeDist_origin_le (interior_subset_box L x.property))

lemma fillingVolume_lt_top (L : ℕ) (s : Vertex → ℝ) : fillingVolume L s < ⊤ :=
  (measure_mono (fillingPolytope_subset_closedBall L s)).trans_lt measure_closedBall_lt_top

lemma isCompact_fillingPolytope (L : ℕ) (s : Vertex → ℝ) :
    IsCompact (fillingPolytope L s) :=
  (isCompact_closedBall _ _).of_isClosed_subset (isClosed_fillingPolytope L s)
    (fillingPolytope_subset_closedBall L s)

lemma filledHeight_center (L : ℕ) (h : Vertex → ℝ) (x : Vertex) :
    filledHeight L h (fun x => h x) x = h x := by
  unfold filledHeight
  split_ifs <;> rfl

lemma filledHeight_perturbation (L : ℕ) (h : Vertex → ℝ) (a : Filling L) (x : Vertex) :
    |filledHeight L h a x - h x| ≤ ‖a - (fun x => h x : Filling L)‖ := by
  by_cases hx : x ∈ interior L
  · rw [filledHeight, dite_eq_left hx]
    exact norm_le_pi_norm (a - (fun x => h x : Filling L)) ⟨x,hx⟩
  · rw [filledHeight_fixed _ _ _ hx, sub_self, abs_zero]
    exact norm_nonneg _

lemma ball_subset_fillingPolytope {L : ℕ} {h : Vertex → ℝ} {δ : ℝ}
    (hne : ∀ x ∈ box L, ∀ y ∈ box L, Adj x y → |h x-h y| ≤ 1-δ) :
    Metric.ball (fun x => h x : Filling L) (δ/4) ⊆ fillingPolytope L h := by
  intro a ha x hx y hy hxy
  have hnorm : ‖a - (fun x => h x : Filling L)‖ < δ/4 := by
    simpa only [Metric.mem_ball, dist_eq_norm] using ha
  have hxerr := filledHeight_perturbation L h a x
  have hyerr := filledHeight_perturbation L h a y
  have hed := hne x hx y hy hxy
  have htri : |filledHeight L h a x-filledHeight L h a y| ≤
      |filledHeight L h a x-h x| + |h x-h y| + |filledHeight L h a y-h y| := by
    calc
      _ ≤ |filledHeight L h a x-h x| + |h x-filledHeight L h a y| := abs_sub_le _ _ _
      _ ≤ _ := by
        have ht := abs_sub_le (h x) (h y) (filledHeight L h a y)
        rw [abs_sub_comm (h y)] at ht
        linarith
  have hn := norm_nonneg (a - (fun x => h x : Filling L))
  linarith

lemma fillingVolume_pos_of_strict {L : ℕ} {h : Vertex → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hne : ∀ x ∈ box L, ∀ y ∈ box L, Adj x y → |h x-h y| ≤ 1-δ) :
    0 < fillingVolume L h :=
  (Metric.measure_ball_pos volume _ (by positivity : 0 < δ/4)).trans_le
    (measure_mono (ball_subset_fillingPolytope hne))

end TriangularLipschitz

end

end OAI
