import OAI.MeasureTheory.Falconer.Geometry.BoundedProjectionCoordinates
import OAI.MeasureTheory.Falconer.Geometry.PlanarGridRegularity
import OAI.MeasureTheory.Falconer.Graphs.CoordinateGraph

namespace OAI

/-! The finite coordinate graph used in the planar projection application:
actual points, a fixed contraction, and an injective fine-grid rounding. -/
namespace Falconer

noncomputable def roundedProjectionCoordinates (σ a b : ℝ) (p : Space 2) : Space 2 :=
  planarGridFloor σ (boundedProjectionCoordinates a b p)

 theorem roundedProjectionCoordinates_image (σ a b : ℝ) (G : Finset (Space 2)) :
    G.image (roundedProjectionCoordinates σ a b) =
      (G.image (boundedProjectionCoordinates a b)).image (planarGridFloor σ) := by
  rw [Finset.image_image]
  rfl

 theorem roundedProjectionCoordinates_injOn {δ σ a b : ℝ} (hδ : 0 < δ) (hσ : 0 < σ)
    (hab : b ≠ a) (ha : |a| ≤ 1) (hb : |b| ≤ 1)
    (hsmall : 4*σ < (δ/(4/|b-a|))/4)
    (G : Finset (Space 2)) (hsep : FiniteSeparatedAt δ G) :
    Set.InjOn (roundedProjectionCoordinates σ a b) (G:Set (Space 2)) := by
  have hi := planarGridFloor_injOn hσ hsmall _
    (boundedProjectionCoordinates_separated hδ hab ha hb G hsep)
  intro x hx y hy he
  exact boundedProjectionCoordinates_injective hab (hi
    (Finset.mem_image_of_mem _ hx) (Finset.mem_image_of_mem _ hy) he)

 theorem roundedProjectionCoordinates_card {δ σ a b : ℝ} (hδ : 0 < δ) (hσ : 0 < σ)
    (hab : b ≠ a) (ha : |a| ≤ 1) (hb : |b| ≤ 1)
    (hsmall : 4*σ < (δ/(4/|b-a|))/4)
    (G : Finset (Space 2)) (hsep : FiniteSeparatedAt δ G) :
    (G.image (roundedProjectionCoordinates σ a b)).card = G.card :=
  Finset.card_image_of_injOn (roundedProjectionCoordinates_injOn hδ hσ hab ha hb hsmall G hsep)

 theorem roundedProjectionCoordinates_coordinate_separated {σ a b : ℝ} (hσ : 0 < σ)
    (G : Finset (Space 2)) (i : Fin 2) :
    ∀ x ∈ (G.image (roundedProjectionCoordinates σ a b)).image (fun p => p i),
      ∀ y ∈ (G.image (roundedProjectionCoordinates σ a b)).image (fun p => p i),
        x ≠ y → σ ≤ |x-y| := by
  rw [roundedProjectionCoordinates_image]
  exact planarGridFloor_coordinate_separated hσ _ i

 theorem roundedProjectionCoordinates_bound {σ a b : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1/2)
    (ha : |a| ≤ 1) (hb : |b| ≤ 1) (p : Space 2) (hp : ∀ i, |p i| ≤ 1) (i : Fin 2) :
    |roundedProjectionCoordinates σ a b p i| ≤ 1 := by
  have herr := scalarGridFloor_error hσ (boundedProjectionCoordinates a b p i)
  have hbound := boundedProjectionCoordinates_bound ha hb p hp i
  have ht := abs_add_le (boundedProjectionCoordinates a b p i)
    (scalarGridFloor σ (boundedProjectionCoordinates a b p i)-boundedProjectionCoordinates a b p i)
  rw [abs_sub_comm] at ht
  have he : boundedProjectionCoordinates a b p i+
      (scalarGridFloor σ (boundedProjectionCoordinates a b p i)-boundedProjectionCoordinates a b p i) =
      scalarGridFloor σ (boundedProjectionCoordinates a b p i) := by ring
  rw [he] at ht
  change |planarGridFloor σ (boundedProjectionCoordinates a b p) i| ≤ 1
  rw [planarGridFloor_apply]
  linarith

 theorem roundedProjectionCoordinates_coordinate_card {σ δ a b : ℝ} (hσ : 0 < σ)
    (hδ : 0 < δ) (G : Finset (Space 2)) (m : ℕ) (hm : δ ≤ (m:ℝ)*σ) (i : Fin 2) :
    ((G.image (roundedProjectionCoordinates σ a b)).image (fun p => p i)).card ≤
      5*(2*m+3)*(projectionCells δ (if i = 0 then a else b) G).card := by
  rw [roundedProjectionCoordinates_image,planarGridFloor_coordinate_card hσ]
  exact boundedProjectionCoordinates_coordinate_cells hσ hδ G m hm i

 theorem roundedProjectionCoordinates_regular {δ σ α C t K a b : ℝ}
    (hδ : 0 < δ) (hσ : 0 < σ) (hα : 0 < α) (hC : 1 ≤ C)
    (hab : b ≠ a) (ha : |a| ≤ 1) (hb : |b| ≤ 1)
    (hscale : (δ/(4/|b-a|))/4 ≤ C*α) (herror : 2*σ ≤ (C-1)*α)
    (hsmall : 4*σ < (δ/(4/|b-a|))/4)
    (ht : 0 ≤ t) (hK : 1 ≤ K) (G : Finset (Space 2))
    (hsep : FiniteSeparatedAt δ G) (hreg : NormalizedFiniteBallBound δ t K G) :
    NormalizedFiniteBallBound α t ((K*(4/|b-a|)^t*4^t)*C^t)
      (G.image (roundedProjectionCoordinates σ a b)) := by
  have hd : 0 < |b-a| := abs_pos.mpr (sub_ne_zero.mpr hab)
  have hba : |b-a| ≤ 2 := (abs_sub b a).trans (by linarith)
  have hL : 1 ≤ 4/|b-a| := (le_div_iff₀ hd).2 (by linarith)
  have hp : 1 ≤ (4/|b-a|)^t := Real.one_le_rpow hL ht
  have hp4 : 1 ≤ (4:ℝ)^t := Real.one_le_rpow (by norm_num) ht
  have hKK0 : 1 ≤ K*(4/|b-a|)^t := by nlinarith
  have hKK : 1 ≤ K*(4/|b-a|)^t*4^t := by nlinarith
  rw [roundedProjectionCoordinates_image]
  exact planarGridFloor_regular hσ hα hC hscale herror ht hKK _
    (boundedProjectionCoordinates_regular hδ hab ha hb ht hK G hreg)
    (planarGridFloor_injOn hσ hsmall _
      (boundedProjectionCoordinates_separated hδ hab ha hb G hsep))

end Falconer

end OAI
