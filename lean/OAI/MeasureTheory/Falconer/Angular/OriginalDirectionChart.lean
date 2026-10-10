import OAI.MeasureTheory.Falconer.Angular.CapNet
import Mathlib.MeasureTheory.Measure.Prod

namespace OAI

/-! # Selecting a small direction chart on the original incidence labels -/

namespace Falconer
open Set Metric MeasureTheory
open scoped ENNReal
variable {d : ℕ}

theorem sphere_chart_pair_inner_nonnegative (w v c : Sphere d)
    (hw : dist w c ≤ 1/2) (hv : dist v c ≤ 1/2) :
    0 ≤ inner ℝ (w:Space d) (v:Space d) := by
  have hd : dist w v ≤ 1 := (dist_triangle w c v).trans (by rw [dist_comm c v]; linarith)
  have hn : ‖(w:Space d)-(v:Space d)‖ ≤ 1 := by simpa only [Subtype.dist_eq,dist_eq_norm] using hd
  have hsq := norm_sub_sq_real (w:Space d) (v:Space d)
  rw [sphere_norm,sphere_norm] at hsq
  nlinarith [norm_nonneg ((w:Space d)-(v:Space d))]

theorem direction_chart_pair_ae (ν : Measure (Sphere d)) [SFinite ν] (c : Sphere d)
    {ρ : ℝ} (hρ : ρ ≤ 1/2) :
    ∀ᵐ z : Sphere d × Sphere d ∂(ν.restrict (closedBall c ρ)).prod (ν.restrict (closedBall c ρ)),
      0 ≤ inner ℝ (z.1:Space d) (z.2:Space d) := by
  have ha : ∀ᵐ w ∂ν.restrict (closedBall c ρ), w ∈ closedBall c ρ := ae_restrict_mem measurableSet_closedBall
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae ha,Measure.quasiMeasurePreserving_snd.ae ha]
    with z hz₁ hz₂
  exact sphere_chart_pair_inner_nonnegative z.1 z.2 c (hz₁.trans hρ) (hz₂.trans hρ)

theorem original_direction_chart_selection
    (μ : Measure (Space d)) (ν : Measure (Sphere d)) [SFinite μ] [SFinite ν]
    (E : Set (Space d × Sphere d)) (hE : MeasurableSet E)
    {ρ : ℝ} (hρ : 0 < ρ) {a : ℝ≥0∞}
    (hmean : ENNReal.ofReal ((2/ρ+1)^d)*a < (μ.prod ν) E) :
    ∃ c : Sphere d, a < (μ.prod (ν.restrict (closedBall c ρ))) E := by
  classical
  obtain ⟨S,_,hcover,hcard,_⟩ := finite_separated_cap_net d (show 0 < 2*ρ by positivity)
  have hcover' (w : Sphere d) : ∃ c ∈ S, dist w c ≤ ρ := by
    have hr : (2*ρ)/2 = ρ := by ring
    simpa only [hr] using hcover w
  let F : Sphere d → Set (Space d × Sphere d) := fun c => E ∩ (univ ×ˢ closedBall c ρ)
  have hsub : E ⊆ ⋃ c ∈ S, F c := by
    intro z hz
    obtain ⟨c,hc,hd⟩ := hcover' z.2
    exact mem_iUnion.mpr ⟨c,mem_iUnion.mpr ⟨hc,hz,mem_univ _,hd⟩⟩
  have hmass : (μ.prod ν) E ≤ ∑ c ∈ S, (μ.prod ν) (F c) :=
    (measure_mono hsub).trans (measure_biUnion_finset_le S F)
  have he (c : Sphere d) : (μ.prod ν) (F c) = (μ.prod (ν.restrict (closedBall c ρ))) E := by
    have hprod : μ.prod (ν.restrict (closedBall c ρ)) =
        (μ.prod ν).restrict (univ ×ˢ closedBall c ρ) := by
      simpa only [Measure.restrict_univ] using
        Measure.prod_restrict (μ := μ) (ν := ν) univ (closedBall c ρ)
    rw [hprod,Measure.restrict_apply hE]
  by_contra! hn
  have hsum : (μ.prod ν) E ≤ (S.card:ℝ≥0∞)*a := hmass.trans (by
    calc
      _ ≤ ∑ _c ∈ S, a := Finset.sum_le_sum (fun c _ => by rw [he]; exact hn c)
      _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul])
  have hcard' : (S.card:ℝ≥0∞) ≤ ENNReal.ofReal ((2/ρ+1)^d) := by
    have hh : (S.card:ℝ) ≤ (2/ρ+1)^d := by
      have hr : 4/(2*ρ)+1 = 2/ρ+1 := by field_simp; ring
      simpa only [hr] using hcard
    simpa only [ENNReal.ofReal_natCast] using ENNReal.ofReal_le_ofReal hh
  exact (not_le_of_gt hmean) (hsum.trans (mul_le_mul' hcard' le_rfl))

end Falconer

end OAI
