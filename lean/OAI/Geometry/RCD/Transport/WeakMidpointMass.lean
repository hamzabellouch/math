import OAI.Geometry.RCD.Metric.ProbabilityClosedMass

namespace OAI

/-! # Passing a mass contraction through weak probability convergence

The source is open and the target is closed. This avoids assuming null
boundaries before the limiting measure has been identified.
-/

open Set Metric Filter MeasureTheory
open scoped Topology
noncomputable section
namespace RegularPointCoordinates

theorem probability_open_closed_contraction {n : ℕ}
    {P : ℕ → ProbabilityMeasure (Euclidean n)} {Q : ProbabilityMeasure (Euclidean n)}
    (hlim : Tendsto P atTop (𝓝 Q)) {A B : Set (Euclidean n)}
    (hA : IsOpen A) (hB : IsClosed B) {c : ℝ} (hc : 0 < c)
    {cs : ℕ → ℝ} (hcs : Tendsto cs atTop (𝓝 c))
    (hbound : ∀ᶠ k in atTop,
      cs k*(P k : Measure (Euclidean n)).real A ≤ (P k : Measure (Euclidean n)).real B) :
    c*(Q : Measure (Euclidean n)).real A ≤ (Q : Measure (Euclidean n)).real B := by
  let a := (Q : Measure (Euclidean n)).real A
  let b := (Q : Measure (Euclidean n)).real B
  have ha : 0 ≤ a := measureReal_nonneg
  by_contra hnot
  have hgap : 0 < c*a-b := by dsimp only [a,b]; linarith
  let δ := min (c/2) ((c*a-b)/(2*(c+a+3)))
  have hδ : 0 < δ := lt_min (by positivity) (div_pos hgap (by positivity))
  have hδc : δ ≤ c/2 := min_le_left _ _
  have hδgap : δ*(c+a+3) ≤ (c*a-b)/2 := by
    have hh := (le_div_iff₀ (by positivity : 0 < 2*(c+a+3))).mp
      (min_le_right (c/2) ((c*a-b)/(2*(c+a+3))))
    nlinarith
  have hlo := probability_open_eventual_lower hlim hA
    (show a-δ < (Q : Measure (Euclidean n)).real A by dsimp only [a]; linarith)
  have hfinite : Tendsto (fun k => (P k).toFiniteMeasure) atTop (𝓝 Q.toFiniteMeasure) :=
    (ProbabilityMeasure.toFiniteMeasure_continuous.tendsto Q).comp hlim
  have hhi := finite_measure_closed_eventual_bound hfinite hB hδ
  have hcoef := hcs.eventually (Ioi_mem_nhds (show c-δ<c by linarith))
  obtain ⟨k,hklo,hkhi,hkc,hkb⟩ := (hlo.and (hhi.and (hcoef.and hbound))).exists
  have hmul : (c-δ)*(a-δ) ≤ cs k*(P k : Measure (Euclidean n)).real A := by
    calc
      _ ≤ (c-δ)*(P k : Measure (Euclidean n)).real A :=
        mul_le_mul_of_nonneg_left hklo (by linarith)
      _ ≤ _ := mul_le_mul_of_nonneg_right hkc.le measureReal_nonneg
  have hfinal := hmul.trans (hkb.trans hkhi)
  change (c-δ)*(a-δ) ≤ b+δ at hfinal
  nlinarith [sq_nonneg δ]

end RegularPointCoordinates

end

end OAI
