import OAI.MeasureTheory.Falconer.Estimates.FiniteNearbyImages
import OAI.MeasureTheory.Falconer.Estimates.PlanarQuarter

namespace OAI

/-! Turn the width-three incidences produced by a coarse packet into exact
mesh-scale incidences. The output slope and intercept lie on the mesh, and
every output line remains within nine mesh lengths of its original line. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

noncomputable def rowAdjustedRaw (δ : ℝ) (p l : Space 2) : Space 2 :=
  rowPoint (l 0) (p 1-scalarGridFloor δ (l 0)*p 0)

noncomputable def rowAdjustedLine (δ : ℝ) (p l : Space 2) : Space 2 :=
  planarGridFloor δ (rowAdjustedRaw δ p l)

@[simp] theorem rowAdjustedLine_zero (δ : ℝ) (p l : Space 2) :
    rowAdjustedLine δ p l 0 = scalarGridFloor δ (l 0) := rfl

@[simp] theorem rowAdjustedLine_one (δ : ℝ) (p l : Space 2) :
    rowAdjustedLine δ p l 1 = scalarGridFloor δ (p 1-scalarGridFloor δ (l 0)*p 0) := rfl

theorem rowAdjustedLine_residual {δ : ℝ} (hδ : 0 < δ) (p l : Space 2) :
    |p 1-rowAdjustedLine δ p l 0*p 0-rowAdjustedLine δ p l 1| ≤ δ := by
  simpa only [rowAdjustedLine_zero,rowAdjustedLine_one] using
    scalarGridFloor_error hδ (p 1-scalarGridFloor δ (l 0)*p 0)

theorem rowAdjustedLine_incident {δ : ℝ} (hδ : 0 < δ) (p l : Space 2) :
    TubeIncident δ p (rowAdjustedLine δ p l) := by
  have hd : 1 ≤ Real.sqrt (1+(rowAdjustedLine δ p l 0)^2) := by
    apply (Real.le_sqrt (by norm_num) (by positivity)).2
    nlinarith only [sq_nonneg (rowAdjustedLine δ p l 0)]
  apply (div_le_iff₀ (zero_lt_one.trans_le hd)).2
  exact (rowAdjustedLine_residual hδ p l).trans (le_mul_of_one_le_right hδ.le hd)

theorem rowAdjustedLine_coordinate_error {δ : ℝ} (hδ : 0 < δ) (p l : Space 2)
    (hp : |p 0| ≤ 1) (hl : |l 0| ≤ 1) (hi : TubeIncident (3*δ) p l) :
    |l 0-rowAdjustedLine δ p l 0| ≤ δ ∧ |l 1-rowAdjustedLine δ p l 1| ≤ 8*δ := by
  have ha := scalarGridFloor_error hδ (l 0)
  have hb := scalarGridFloor_error hδ (p 1-scalarGridFloor δ (l 0)*p 0)
  have hres : |p 1-l 0*p 0-l 1| ≤ 6*δ := by
    have hh := tube_residual_le (show 0 ≤ 3*δ by positivity) hl hi
    linarith only [hh]
  have hmul : |(l 0-scalarGridFloor δ (l 0))*p 0| ≤ δ := by
    rw [abs_mul]
    exact (mul_le_mul ha hp (abs_nonneg _) hδ.le).trans_eq (mul_one δ)
  have hu : |p 1-scalarGridFloor δ (l 0)*p 0-l 1| ≤ 7*δ := by
    have he : p 1-scalarGridFloor δ (l 0)*p 0-l 1 =
        (p 1-l 0*p 0-l 1)+(l 0-scalarGridFloor δ (l 0))*p 0 := by ring
    rw [he]
    exact (abs_add_le _ _).trans (by linarith only [hres,hmul])
  refine ⟨ha,?_⟩
  rw [rowAdjustedLine_one]
  have hh := abs_sub_le (l 1) (p 1-scalarGridFloor δ (l 0)*p 0)
    (scalarGridFloor δ (p 1-scalarGridFloor δ (l 0)*p 0))
  rw [abs_sub_comm (l 1) (p 1-scalarGridFloor δ (l 0)*p 0)] at hh
  exact hh.trans (by linarith only [hb,hu])

theorem rowAdjustedLine_near {δ : ℝ} (hδ : 0 < δ) (p l : Space 2)
    (hp : |p 0| ≤ 1) (hl : |l 0| ≤ 1) (hi : TubeIncident (3*δ) p l) :
    dist l (rowAdjustedLine δ p l) ≤ 9*δ := by
  obtain ⟨h0,h1⟩ := rowAdjustedLine_coordinate_error hδ p l hp hl hi
  exact (planar_dist_le_coordinate_sum _ _).trans (by linarith only [h0,h1])

theorem rowAdjustedLine_family_separated {δ : ℝ} (hδ : 0 < δ)
    (P : Finset (Space 2)) (T : Space 2 → Finset (Space 2)) :
    FiniteSeparatedAt δ (P.biUnion fun p => (T p).image (rowAdjustedLine δ p)) := by
  let U := P.biUnion fun p => (T p).image (rowAdjustedRaw δ p)
  have he : P.biUnion (fun p => (T p).image (rowAdjustedLine δ p)) =
      U.image (planarGridFloor δ) := by
    simp only [U,Finset.biUnion_image,Finset.image_image,Function.comp_def]
    rfl
  rw [he]
  exact planarGridFloor_separated hδ U

theorem rowAdjustedLine_family_card {δ : ℝ} (hδ : 0 < δ)
    (P : Finset (Space 2)) (T : Space 2 → Finset (Space 2))
    (hp : ∀ p ∈ P, |p 0| ≤ 1)
    (hT : ∀ p ∈ P, ∀ l ∈ T p, |l 0| ≤ 1 ∧ TubeIncident (3*δ) p l) :
    ((P.biUnion fun p => (T p).image (rowAdjustedLine δ p)).card:ℝ) ≤
      361*((P.biUnion T).card:ℝ) := by
  apply separated_near_cover_card hδ _ _ (rowAdjustedLine_family_separated hδ P T)
  intro q hq
  obtain ⟨p,hpP,hq⟩ := Finset.mem_biUnion.mp hq
  obtain ⟨l,hl,rfl⟩ := Finset.mem_image.mp hq
  refine ⟨l,Finset.mem_biUnion.mpr ⟨p,hpP,hl⟩,?_⟩
  rw [dist_comm]
  exact rowAdjustedLine_near hδ p l (hp p hpP) (hT p hpP l hl).1 (hT p hpP l hl).2

theorem rowAdjustedLine_pencil_card {δ : ℝ} (hδ : 0 < δ)
    (p : Space 2) (T : Finset (Space 2)) (hp : |p 0| ≤ 1)
    (hsep : FiniteSeparatedAt δ T)
    (hT : ∀ l ∈ T, |l 0| ≤ 1 ∧ TubeIncident (3*δ) p l) :
    (T.card:ℝ) ≤ 361*((T.image (rowAdjustedLine δ p)).card:ℝ) :=
  nearby_image_card hδ T _ hsep
    (fun l hl => rowAdjustedLine_near hδ p l hp (hT l hl).1 (hT l hl).2)

theorem rowAdjustedLine_pencil_regular {δ s K : ℝ} (hδ : 0 < δ)
    (hs : 0 ≤ s) (hK : 1 ≤ K) (p : Space 2) (T : Finset (Space 2))
    (hp : |p 0| ≤ 1) (hsep : FiniteSeparatedAt δ T)
    (hT : ∀ l ∈ T, |l 0| ≤ 1 ∧ TubeIncident (3*δ) p l)
    (hreg : NormalizedFiniteBallBound δ s K T) :
    NormalizedFiniteBallBound δ s (361*K*(10:ℝ)^s) (T.image (rowAdjustedLine δ p)) :=
  nearby_image_regular hδ hs hK T _ hsep
    (fun l hl => rowAdjustedLine_near hδ p l hp (hT l hl).1 (hT l hl).2) hreg

end Falconer

end OAI
