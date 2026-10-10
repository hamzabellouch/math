import OAI.Probability.SLE.Geometry.DiskUpperStraightening

namespace OAI

/-! Reflection gives the second prescribed boundary extension. -/
noncomputable section
open Set Complex
open scoped ComplexConjugate

namespace SLEExactGauge

def diskLowerArc (s : ℝ) : ℂ := conj (diskUpperArc s)

theorem disk_crosscut_lower_straightening
    (p : ℝ → ℂ) (hc : ContinuousOn p (Icc 0 1)) (hi : InjOn p (Icc 0 1))
    (h0 : p 0=-1) (h1 : p 1=1) (hp : ∀ s ∈ Ioo 0 1, ‖p s‖ < 1) :
    ∃ H : ℂ ≃ₜ ℂ,
      (∀ s ∈ Icc 0 1, H (p s)=diskDiameter s) ∧
      ∀ z ∈ diskLowerArc '' Icc 0 1, H z=z := by
  let q (s : ℝ) := conj (p s)
  have hqc : ContinuousOn q (Icc 0 1) := Complex.continuous_conj.comp_continuousOn hc
  have hqi : InjOn q (Icc 0 1) := by
    intro s hs t ht he
    exact hi hs ht (Complex.conjCLE.injective he)
  have hq0 : q 0=-1 := by simp [q,h0]
  have hq1 : q 1=1 := by simp [q,h1]
  have hqp (s : ℝ) (hs : s ∈ Ioo 0 1) : ‖q s‖ < 1 := by simpa [q] using hp s hs
  obtain ⟨H,hHp,hHa⟩ := disk_crosscut_upper_straightening q hqc hqi hq0 hq1 hqp
  let C : ℂ ≃ₜ ℂ := Complex.conjCLE.toHomeomorph
  refine ⟨(C.trans H).trans C,?_,?_⟩
  · intro s hs
    change conj (H (q s))=diskDiameter s
    rw [hHp s hs]
    exact Complex.conj_ofReal _
  · rintro z ⟨s,hs,rfl⟩
    change conj (H (conj (diskLowerArc s)))=diskLowerArc s
    simp only [diskLowerArc,Complex.conj_conj]
    rw [hHa _ (mem_image_of_mem diskUpperArc hs)]

end SLEExactGauge

end

end OAI
