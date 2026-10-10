import OAI.MeasureTheory.Falconer.Angular.AngularGrid
import OAI.MeasureTheory.Falconer.Graphs.GraphBallCover
import OAI.MeasureTheory.Falconer.Geometry.TubeFiberCoordinates

namespace OAI

/-! A common coarse grid inside the original chart and the resulting
point-line incidence error. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

noncomputable def coarsePlanarRound (Δ : ℝ) (p : Space 2) : Space 2 :=
  rowPoint (lineGridRound Δ (p 0)) (lineGridRound Δ (p 1))

@[simp] theorem coarsePlanarRound_zero (Δ : ℝ) (p : Space 2) :
    coarsePlanarRound Δ p 0 = lineGridRound Δ (p 0) := rfl

@[simp] theorem coarsePlanarRound_one (Δ : ℝ) (p : Space 2) :
    coarsePlanarRound Δ p 1 = lineGridRound Δ (p 1) := rfl

theorem coarsePlanarRound_near {Δ : ℝ} (hΔ : 0 < Δ) (p : Space 2) :
    dist p (coarsePlanarRound Δ p) ≤ Δ := by
  have hh := planar_dist_le_coordinate_sum p (coarsePlanarRound Δ p)
  simp only [coarsePlanarRound_zero,coarsePlanarRound_one] at hh
  linarith only [hh,lineGridRound_error hΔ (p 0),lineGridRound_error hΔ (p 1)]

theorem coarsePlanarRound_separated {Δ : ℝ} (hΔ : 0 < Δ) (P : Finset (Space 2)) :
    FiniteSeparatedAt Δ (P.image (coarsePlanarRound Δ)) := by
  intro x hx y hy hxy
  obtain ⟨p,_,rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨q,_,rfl⟩ := Finset.mem_image.mp hy
  apply gridLine_dist_ge hΔ
    (p := (round (p 0/Δ),round (p 1/Δ)))
    (q := (round (q 0/Δ),round (q 1/Δ)))
  intro he
  exact hxy (congrArg (gridLine Δ) he)

theorem lineGridRound_bounded {Δ : ℝ} (hΔ : 0 < Δ) (M : ℕ)
    (hmesh : Δ*(M:ℝ) = 1) {a : ℝ} (ha : |a| ≤ 1) :
    |lineGridRound Δ a| ≤ 1 := by
  have hal := (abs_le.mp ha).1
  have hau := (abs_le.mp ha).2
  have hlo : -(M:ℝ) ≤ a/Δ := (le_div_iff₀ hΔ).2 (by nlinarith only [hal,hmesh])
  have hhi : a/Δ ≤ (M:ℝ) := (div_le_iff₀ hΔ).2 (by nlinarith only [hau,hmesh])
  have hrl : -(M:ℝ)-1 < (round (a/Δ):ℝ) := by
    have hh := sub_half_lt_round (a/Δ)
    linarith only [hlo,hh]
  have hru : (round (a/Δ):ℝ) < (M:ℝ)+1 := by
    have hh := round_le_add_half (a/Δ)
    linarith only [hhi,hh]
  have hrl' : -(M:ℤ)-1 < round (a/Δ) := by exact_mod_cast hrl
  have hru' : round (a/Δ) < (M:ℤ)+1 := by exact_mod_cast hru
  have hir : -(M:ℤ) ≤ round (a/Δ) ∧ round (a/Δ) ≤ (M:ℤ) := by omega
  have hreal : -(M:ℝ) ≤ (round (a/Δ):ℝ) ∧ (round (a/Δ):ℝ) ≤ (M:ℝ) := by exact_mod_cast hir
  unfold lineGridRound
  rw [abs_le]
  constructor
  · have hh := mul_le_mul_of_nonneg_left hreal.1 hΔ.le
    nlinarith only [hh,hmesh]
  · have hh := mul_le_mul_of_nonneg_left hreal.2 hΔ.le
    nlinarith only [hh,hmesh]

theorem dyadic_coarse_round_chart (N : ℕ) (P : Finset (Space 2))
    (hP : InBoundedLineChart P) :
    InBoundedLineChart (P.image (coarsePlanarRound (1/(2:ℝ)^N))) := by
  have hΔ : 0 < 1/(2:ℝ)^N := by positivity
  have hmesh : (1/(2:ℝ)^N)*((2^N:ℕ):ℝ) = 1 := by push_cast; field_simp
  intro p hp
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hp
  exact ⟨lineGridRound_bounded hΔ (2^N) hmesh (hP x hx).1,
    lineGridRound_bounded hΔ (2^N) hmesh (hP x hx).2⟩

theorem coarse_round_incident {δ Δ : ℝ} (hδ : 0 ≤ δ) (hΔ : 0 < Δ) (hδΔ : δ ≤ Δ)
    (p c l : Space 2) (hc : dist p c ≤ Δ) (hc0 : |c 0| ≤ 1) (hl0 : |l 0| ≤ 1)
    (hi : TubeIncident δ p l) : TubeIncident (5*Δ) c (coarsePlanarRound Δ l) := by
  let q := coarsePlanarRound Δ l
  have hres := tube_residual_le hδ hl0 hi
  have h0 : |p 0-c 0| ≤ Δ := (show |p 0-c 0| ≤ dist p c by
    simpa only [Real.dist_eq] using PiLp.dist_apply_le p c 0).trans hc
  have h1 : |c 1-p 1| ≤ Δ := by
    rw [abs_sub_comm]
    exact (show |p 1-c 1| ≤ dist p c by simpa only [Real.dist_eq] using PiLp.dist_apply_le p c 1).trans hc
  have h2 : |l 0*(p 0-c 0)| ≤ Δ := by
    rw [abs_mul]
    exact (mul_le_mul hl0 h0 (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 1)).trans_eq (one_mul _)
  have h3 : |(l 0-q 0)*c 0| ≤ Δ/2 := by
    rw [abs_mul]
    exact (mul_le_mul (lineGridRound_error hΔ (l 0)) hc0 (abs_nonneg _) (by positivity)).trans_eq (mul_one _)
  have h4 : |l 1-q 1| ≤ Δ/2 := lineGridRound_error hΔ (l 1)
  have he : c 1-q 0*c 0-q 1 = (p 1-l 0*p 0-l 1)+(c 1-p 1)+
      l 0*(p 0-c 0)+(l 0-q 0)*c 0+(l 1-q 1) := by ring
  have habs : |c 1-q 0*c 0-q 1| ≤ 5*Δ := by
    rw [abs_le]
    obtain ⟨hrl,hru⟩ := abs_le.mp hres
    obtain ⟨h1l,h1u⟩ := abs_le.mp h1
    obtain ⟨h2l,h2u⟩ := abs_le.mp h2
    obtain ⟨h3l,h3u⟩ := abs_le.mp h3
    obtain ⟨h4l,h4u⟩ := abs_le.mp h4
    constructor <;> linarith only [he,hrl,hru,h1l,h1u,h2l,h2u,h3l,h3u,h4l,h4u,hδΔ]
  have hsqrt : 1 ≤ Real.sqrt (1+(q 0)^2) := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]
    nlinarith only [sq_nonneg (q 0)]
  exact (div_le_self (abs_nonneg _) hsqrt).trans habs

end Falconer

end OAI
