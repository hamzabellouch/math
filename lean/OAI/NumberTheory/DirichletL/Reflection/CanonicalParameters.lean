import OAI.NumberTheory.DirichletL.Reflection.CanonicalCaps

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open InverseMoment InverseTerminalWidths
noncomputable section

theorem canonical_reflection_parameters (L c η : ℝ)
    (hL : 0≤L) (hc : 0<c) (hη : 0<η) (hη1 : η≤1) (hηc : η≤c/100000) :
    ∃ ε ρ κ δ π : ℝ,0<ε ∧ 0<ρ ∧ 0<κ ∧ 0<δ ∧
      0≤δ+(7*L+1) ∧ η≤c/1000 ∧ δ+η≤c/1000 ∧ π≤c/1000 ∧
      ε*(L+L+2*(δ+(7*L+1)+η))+η/2≤π ∧ κ+ρ*L≤c/16 := by
  let ε := c/(100000*(L+1))
  let ρ := c/(64*(L+1))
  let κ := c/64
  refine ⟨ε,ρ,κ,η,c/1000,div_pos hc (by positivity),div_pos hc (by positivity),
    div_pos hc (by norm_num),hη,by positivity,by linarith,by linarith,le_refl _,?_,?_⟩
  · have hep : 0≤ε := (div_pos hc (by positivity : 0<100000*(L+1))).le
    have hed : ε*(L+1)=c/100000 := by dsimp [ε];field_simp
    have hb : L+L+2*(η+(7*L+1)+η)≤22*(L+1) := by linarith
    have hh := mul_le_mul_of_nonneg_left hb hep
    have he22 : ε*(22*(L+1))=22*(c/100000) := by calc
      _ = 22*(ε*(L+1)) := by ring
      _ = _ := by rw [hed]
    rw [he22] at hh
    linarith
  · have hrp : 0≤ρ := (div_pos hc (by positivity : 0<64*(L+1))).le
    have hrd : ρ*(L+1)=c/64 := by dsimp [ρ];field_simp
    have hb := mul_le_mul_of_nonneg_left (show L≤L+1 by linarith) hrp
    dsimp only [κ]
    rw [hrd] at hb
    linarith

lemma canonical_reflected_target_positive (F M Q z margin c O : ℝ)
    (h : CanonicalMargins F M Q z margin) (hM : 0≤M) (hQ : 0≤Q) (hz : 0≤z)
    (hc : 0<c) (hm : c/2≤margin) (hO : O≤M) :
    0<F-3*c/16-O/2 := by
  obtain ⟨hfirst,hsecond⟩ := h
  linarith
end
end SevenEighths.InverseReflectedPhase

end OAI
