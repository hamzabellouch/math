import OAI.Analysis.Laughlin.Operators.Certificate

namespace OAI

namespace Laughlin.Certificate

theorem threeBody_2 : e 2 < limitBound 2 := by decide +kernel

theorem threeBody_4 : e 4 < limitBound 4 := by decide +kernel

theorem threeBody_5 : e 5 < limitBound 5 := by decide +kernel

theorem threeBody_6 : e 6 < limitBound 6 := by decide +kernel

theorem threeBody_7 : e 7 < limitBound 7 := by decide +kernel

theorem threeBody_8 : e 8 < limitBound 8 := by decide +kernel

theorem threeBody_9 : e 9 < limitBound 9 := by decide +kernel

theorem threeBody_10 : e 10 < limitBound 10 := by decide +kernel

theorem threeBody_11 : e 11 < limitBound 11 := by decide +kernel

theorem threeBody_12 : e 12 < limitBound 12 := by decide +kernel

theorem threeBody_13 : e 13 < limitBound 13 := by decide +kernel

theorem threeBody_14 : e 14 < limitBound 14 := by decide +kernel

theorem threeBody_15 : e 15 < limitBound 15 := by decide +kernel

theorem threeBody_certificate (z : ℕ)
    (hz : z ∈ [2, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]) : e z < limitBound z := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact threeBody_2
  · exact threeBody_4
  · exact threeBody_5
  · exact threeBody_6
  · exact threeBody_7
  · exact threeBody_8
  · exact threeBody_9
  · exact threeBody_10
  · exact threeBody_11
  · exact threeBody_12
  · exact threeBody_13
  · exact threeBody_14
  · exact threeBody_15

end Laughlin.Certificate

end OAI
