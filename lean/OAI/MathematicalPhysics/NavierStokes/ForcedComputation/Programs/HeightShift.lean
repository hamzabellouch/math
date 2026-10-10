import OAI.MathematicalPhysics.NavierStokes.ShearFlows.Model

namespace OAI

/-! Moving the coding sheet does not change the finite planar program. This
supplies the different fixed particle heights in the assigned applications. -/

namespace ShearFlows

def Input.shiftHeight (d : Input) (c : ℚ) : Input :=
  letI := neZeroThree
  { d with
    chart := ⟨fun j => d.chart.lower j + if j = 2 then c else 0,
      fun j => d.chart.upper j + if j = 2 then c else 0⟩
    codingHeight := d.codingHeight + c }

theorem ValidInput.shiftHeight {d : Input} (hd : ValidInput d) (c : ℚ) :
    ValidInput (d.shiftHeight c) := by
  refine ⟨hd.period_pos, ?_, ?_, hd.h_pos, hd.centers_nonempty, ?_, ?_,
    hd.source_positive, hd.target_positive, ?_, ?_, hd.factor_pos, hd.image_eq,
    hd.source_separation, hd.target_separation, hd.halfWidths,
    hd.source_centers, hd.target_centers⟩
  · intro j
    have hj := hd.chart_positive j
    change d.chart.lower j + (if j = 2 then c else 0) <
      d.chart.upper j + (if j = 2 then c else 0)
    linarith
  · intro j
    have hj := hd.chart_length j
    change (d.chart.upper j + (if j = 2 then c else 0)) -
      (d.chart.lower j + (if j = 2 then c else 0)) < d.period
    simpa only [add_sub_add_right_eq_sub] using hj
  · intro j
    fin_cases j
    · simpa [Input.shiftHeight] using hd.chartMargin 0
    · simpa [Input.shiftHeight] using hd.chartMargin 1
  · simpa [Input.shiftHeight, Rat.cast_add] using hd.height_inside
  · intro b hb x hx j
    fin_cases j
    · simpa [Input.shiftHeight, Input.inPlanarChart] using hd.source_in_chart b hb hx 0
    · simpa [Input.shiftHeight, Input.inPlanarChart] using hd.source_in_chart b hb hx 1
  · intro b hb x hx j
    fin_cases j
    · simpa [Input.shiftHeight, Input.inPlanarChart] using hd.target_in_chart b hb hx 0
    · simpa [Input.shiftHeight, Input.inPlanarChart] using hd.target_in_chart b hb hx 1

@[simp] theorem Input.shiftHeight_period (d : Input) (c : ℚ) :
    (d.shiftHeight c).period = d.period := rfl

@[simp] theorem Input.shiftHeight_instructions (d : Input) (c : ℚ) :
    (d.shiftHeight c).instructions = d.instructions := rfl

@[simp] theorem Input.shiftHeight_codingHeight (d : Input) (c : ℚ) :
    (d.shiftHeight c).codingHeight = d.codingHeight + c := rfl

end ShearFlows

end OAI
