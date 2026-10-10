import OAI.MeasureTheory.Falconer.Estimates.PlanarQuarter
import OAI.MeasureTheory.Falconer.Geometry.GridProjectionTransfer

namespace OAI

/-! Bounded actual projection coordinates, with exact finite cell-count
comparison to the original planar projections. -/
namespace Falconer

noncomputable def boundedProjectionCoordinates (a b : ℝ) (p : Space 2) : Space 2 :=
  planarQuarter (planarProjectionCoordinates a b p)

 theorem boundedProjectionCoordinates_zero (a b : ℝ) (p : Space 2) :
    boundedProjectionCoordinates a b p 0 = lineParameterProjection a p / 4 := by
  rw [boundedProjectionCoordinates,planarQuarter_apply]
  rfl

 theorem boundedProjectionCoordinates_one (a b : ℝ) (p : Space 2) :
    boundedProjectionCoordinates a b p 1 = lineParameterProjection b p / 4 := by
  rw [boundedProjectionCoordinates,planarQuarter_apply]
  rfl

 theorem boundedProjectionCoordinates_injective {a b : ℝ} (hab : b ≠ a) :
    Function.Injective (boundedProjectionCoordinates a b) :=
  planarQuarter_injective.comp (planarProjectionCoordinates_injective hab)

 theorem boundedProjectionCoordinates_image (a b : ℝ) (G : Finset (Space 2)) :
    G.image (boundedProjectionCoordinates a b) =
      (G.image (planarProjectionCoordinates a b)).image planarQuarter := by
  rw [Finset.image_image]
  rfl

 theorem boundedProjectionCoordinates_separated {δ a b : ℝ} (hδ : 0 < δ)
    (hab : b ≠ a) (ha : |a| ≤ 1) (hb : |b| ≤ 1)
    (G : Finset (Space 2)) (hsep : FiniteSeparatedAt δ G) :
    FiniteSeparatedAt ((δ/(4/|b-a|))/4) (G.image (boundedProjectionCoordinates a b)) := by
  rw [boundedProjectionCoordinates_image]
  exact planarQuarter_separated _ (planarProjectionCoordinates_separated hδ hab ha hb G hsep)

 theorem boundedProjectionCoordinates_regular {δ t K a b : ℝ} (hδ : 0 < δ)
    (hab : b ≠ a) (ha : |a| ≤ 1) (hb : |b| ≤ 1) (ht : 0 ≤ t) (hK : 1 ≤ K)
    (G : Finset (Space 2)) (hreg : NormalizedFiniteBallBound δ t K G) :
    NormalizedFiniteBallBound ((δ/(4/|b-a|))/4) t (K*(4/|b-a|)^t*4^t)
      (G.image (boundedProjectionCoordinates a b)) := by
  have hba : |b-a| ≤ 2 := (abs_sub b a).trans (by linarith)
  have hd : 0 < |b-a| := abs_pos.mpr (sub_ne_zero.mpr hab)
  have hL : 1 ≤ 4/|b-a| := (le_div_iff₀ hd).2 (by linarith)
  have hpow : 1 ≤ (4/|b-a|)^t := Real.one_le_rpow hL ht
  have hKK : 1 ≤ K*(4/|b-a|)^t := by nlinarith
  rw [boundedProjectionCoordinates_image]
  exact planarQuarter_regular (by positivity) ht hKK _
    (planarProjectionCoordinates_regular hδ hab ha hb ht hK G hreg)

 theorem boundedProjectionCoordinates_bound {a b : ℝ} (ha : |a| ≤ 1) (hb : |b| ≤ 1)
    (p : Space 2) (hp : ∀ i, |p i| ≤ 1) (i : Fin 2) :
    |boundedProjectionCoordinates a b p i| ≤ 1/2 := by
  have hproj (y : ℝ) (hy : |y| ≤ 1) : |lineParameterProjection y p| ≤ 2 := by
    have hh := abs_add_le (y*p 0) (p 1)
    rw [abs_mul] at hh
    have hm := mul_le_mul hy (hp 0) (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 1)
    change |y*p 0+p 1| ≤ 2
    linarith [hp 1]
  fin_cases i
  · change |boundedProjectionCoordinates a b p 0| ≤ 1/2
    rw [boundedProjectionCoordinates_zero,abs_div]
    norm_num
    linarith [hproj a ha]
  · change |boundedProjectionCoordinates a b p 1| ≤ 1/2
    rw [boundedProjectionCoordinates_one,abs_div]
    norm_num
    linarith [hproj b hb]

 theorem boundedProjectionCoordinates_coordinate_cells {σ δ a b : ℝ} (hσ : 0 < σ)
    (hδ : 0 < δ) (G : Finset (Space 2)) (m : ℕ) (hm : δ ≤ (m:ℝ)*σ)
    (i : Fin 2) :
    (scalarCells σ ((G.image (boundedProjectionCoordinates a b)).image (fun p => p i))).card ≤
      5*(2*m+3)*(projectionCells δ (if i = 0 then a else b) G).card := by
  have he : (G.image (boundedProjectionCoordinates a b)).image (fun p => p i) =
      (G.image (lineParameterProjection (if i = 0 then a else b))).image (fun v => (1/4:ℝ)*v) := by
    simp only [Finset.image_image,Function.comp_def]
    apply Finset.image_congr
    intro p _
    fin_cases i
    · change boundedProjectionCoordinates a b p 0 = (1/4:ℝ)*lineParameterProjection a p
      rw [boundedProjectionCoordinates_zero]
      ring
    · change boundedProjectionCoordinates a b p 1 = (1/4:ℝ)*lineParameterProjection b p
      rw [boundedProjectionCoordinates_one]
      ring
  rw [he]
  have hd := scalar_dilation_cells (c := (1/4:ℝ)) hσ
    (G.image (lineParameterProjection (if i = 0 then a else b))) 1 (by norm_num)
  have hr := scalar_cells_resolution hσ hδ m hm
    (G.image (lineParameterProjection (if i = 0 then a else b)))
  have hc : scalarCells δ (G.image (lineParameterProjection (if i = 0 then a else b))) =
      projectionCells δ (if i = 0 then a else b) G := by
    simp only [scalarCells,projectionCells,Finset.image_image,Function.comp_def]
  rw [hc] at hr
  exact hd.trans ((Nat.mul_le_mul_left 5 hr).trans_eq (by ring))

 theorem boundedProjectionCoordinates_projection_image {a b y : ℝ} (hab : b ≠ a)
    (hy : y ≠ b) (G : Finset (Space 2)) :
    (G.image (boundedProjectionCoordinates a b)).image (cartesianProjection ((y-a)/(b-y))) =
      (G.image (lineParameterProjection y)).image (fun v => (((b-a)/(b-y))/4)*v) := by
  simp only [Finset.image_image,Function.comp_def]
  apply Finset.image_congr
  intro p _
  have hh := planar_projection_normalized hab hy p
  change (boundedProjectionCoordinates a b p 0)+((y-a)/(b-y))*(boundedProjectionCoordinates a b p 1) = _
  rw [boundedProjectionCoordinates_zero,boundedProjectionCoordinates_one]
  nlinarith

end Falconer

end OAI
