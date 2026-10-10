import OAI.Geometry.RCD.Transport.WeakMidpointMass

namespace OAI

/-! # Passing both source masses through weak probability convergence -/

open Set Metric Filter MeasureTheory
open scoped Topology
noncomputable section
namespace RegularPointCoordinates

theorem probability_open_closed_min_contraction {n : ℕ}
    {P : ℕ → ProbabilityMeasure (Euclidean n)} {Q : ProbabilityMeasure (Euclidean n)}
    (hlim : Tendsto P atTop (𝓝 Q)) {A B C : Set (Euclidean n)}
    (hA : IsOpen A) (hB : IsOpen B) (hC : IsClosed C) {c : ℝ} (hc : 0 < c)
    {cs : ℕ → ℝ} (hcs : Tendsto cs atTop (𝓝 c))
    (hbound : ∀ᶠ k in atTop,
      cs k*min ((P k : Measure (Euclidean n)).real A) ((P k : Measure (Euclidean n)).real B) ≤
        (P k : Measure (Euclidean n)).real C) :
    c*min ((Q : Measure (Euclidean n)).real A) ((Q : Measure (Euclidean n)).real B) ≤
      (Q : Measure (Euclidean n)).real C := by
  let a := min ((Q : Measure (Euclidean n)).real A) ((Q : Measure (Euclidean n)).real B)
  let b := (Q : Measure (Euclidean n)).real C
  have ha : 0 ≤ a := le_min measureReal_nonneg measureReal_nonneg
  by_contra hnot
  have hgap : 0 < c*a-b := by dsimp only [a,b]; linarith only [hnot]
  let δ := min (c/2) ((c*a-b)/(2*(c+a+3)))
  have hδ : 0 < δ := lt_min (by positivity) (div_pos hgap (by positivity))
  have hδc : δ ≤ c/2 := min_le_left _ _
  have hδgap : δ*(c+a+3) ≤ (c*a-b)/2 := by
    have hh := (le_div_iff₀ (by positivity : 0 < 2*(c+a+3))).mp (min_le_right (c/2) ((c*a-b)/(2*(c+a+3))))
    change δ*(2*(c+a+3)) ≤ c*a-b at hh
    linarith only [hh]
  have hloA := probability_open_eventual_lower hlim hA
    (show a-δ < (Q : Measure (Euclidean n)).real A from
      (sub_lt_self _ hδ).trans_le (min_le_left _ _))
  have hloB := probability_open_eventual_lower hlim hB
    (show a-δ < (Q : Measure (Euclidean n)).real B from
      (sub_lt_self _ hδ).trans_le (min_le_right _ _))
  have hfinite : Tendsto (fun k => (P k).toFiniteMeasure) atTop (𝓝 Q.toFiniteMeasure) :=
    (ProbabilityMeasure.toFiniteMeasure_continuous.tendsto Q).comp hlim
  have hhi := finite_measure_closed_eventual_bound hfinite hC hδ
  have hcoef := hcs.eventually (Ioi_mem_nhds (show c-δ<c by linarith only [hδ]))
  obtain ⟨k,hkA,hkB,hkhi,hkc,hkb⟩ := (hloA.and (hloB.and (hhi.and (hcoef.and hbound)))).exists
  have hmul : (c-δ)*(a-δ) ≤ cs k*
      min ((P k : Measure (Euclidean n)).real A) ((P k : Measure (Euclidean n)).real B) := by
    calc
      _ ≤ (c-δ)*min ((P k : Measure (Euclidean n)).real A)
          ((P k : Measure (Euclidean n)).real B) :=
        mul_le_mul_of_nonneg_left (le_min hkA hkB) (by linarith only [hδc,hc])
      _ ≤ _ := mul_le_mul_of_nonneg_right hkc.le (le_min measureReal_nonneg measureReal_nonneg)
  have hfinal := hmul.trans (hkb.trans hkhi)
  change (c-δ)*(a-δ) ≤ b+δ at hfinal
  nlinarith only [hfinal,hδgap,hδ,ha,hc,sq_nonneg δ]

end RegularPointCoordinates

end

end OAI
