import OAI.GroupTheory.Hyperbolic.Hyperbolicity

namespace OAI

namespace Release075

theorem main : ∃ (G : Type) (_ : Group G),
    TorsionFree G ∧ WordHyperbolic G ∧ ¬ Group.ResiduallyFinite G := by
  obtain ⟨q,r,hq,hr,hrq,hrb,⟨d⟩⟩ := exists_markedLineData
  let : Fact q.Prime := ⟨hq⟩
  have hq200 : 200 ≤ q := by
    have hb : 200 ≤ 100*100^20 := by norm_num
    omega
  exact ⟨(d.presentation hr).GroupType, inferInstance,
    d.presentation_torsionFree hr, d.presentation_wordHyperbolic hr,
    d.actual_presentation_not_residuallyFinite hr hrq hq200⟩

end Release075

end OAI
