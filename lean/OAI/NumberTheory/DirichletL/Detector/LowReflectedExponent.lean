import OAI.NumberTheory.DirichletL.Inversion.TerminalWidths

namespace OAI

namespace SevenEighths.ProbeLowReflected
open InverseTerminalWidths

lemma hybrid_half_with_error {v za ε : ℝ} (hv : -ε≤v) (hε : 0≤ε)
    (hu : hybridSaving v za≠za) : v/2-ε/2≤hybridSaving v za := by
  unfold hybridSaving at *
  rcases le_total v (min za ((v+za)/3)) with h|h
  · rw [min_eq_left h]
    linarith
  · rw [min_eq_right h] at *
    rcases le_total za ((v+za)/3) with hz|hz
    · exact (hu (min_eq_left hz)).elim
    · rw [min_eq_right hz]
      have hzv := min_le_left za ((v+za)/3)
      rw [min_eq_right hz] at hzv
      linarith

lemma retained_kernel_quarter (Td y : ℝ) : Td/4≤y/4+max 0 (Td-y)/2 := by
  have h0 := le_max_left 0 (Td-y)
  have h1 := le_max_right 0 (Td-y)
  linarith

theorem compensated_reflected_exponent (d O₀ H A₀ N₀ S₀ B₀ za v ell el θ ε : ℝ)
    (hd : 0≤d) (_hd1 : d≤1/6) (hε : 0≤ε)
    (hO : -ε≤O₀) (hH : H≤(5/6-2*d)-O₀+ε)
    (hA : 2*A₀≤O₀+ε) (hN : 0≤N₀) (hNA : N₀≤A₀)
    (hS : 0≤S₀) (hB : 0≤B₀) (hz : za≤1/6-d)
    (hv : -ε≤v) (hl : -ε≤ell) (he : -ε≤el) (hθ : |θ|≤ε)
    (hret : v+3*ell+el≤2*H+2*A₀+2*za-1-(1/6-d)-θ-N₀-3*B₀+ε) :
    reflectedExponent O₀ H S₀ B₀ za v ell el
      (2*H+2*A₀+2*za-1-(1/6-d)-θ-N₀-3*B₀)≤5/6-2*d+20*ε := by
  let Td := 2*H+2*A₀+2*za-1-(1/6-d)-θ-N₀-3*B₀
  have hθlo : -ε≤θ := (abs_le.mp hθ).1
  have hθhi : θ≤ε := (abs_le.mp hθ).2
  have hTd : Td≤H-3*d+3*ε := by dsimp [Td];linarith
  have hcol : v+ell≤H+7*ε := by dsimp [Td] at hTd;linarith
  have hmax : max H (v+ell)≤H+7*ε := max_le (by linarith) hcol
  have hk := le_max_left 0 (Td-v-3*ell-el)
  by_cases hu : hybridSaving v za=za
  · unfold reflectedExponent
    rw [hu]
    change O₀/2+max H (v+ell)-S₀-B₀+za-za-ell-2*el/3-max 0 (Td-v-3*ell-el)/2≤_
    linarith
  · have hhalf := hybrid_half_with_error hv hε hu
    have hquarter := retained_kernel_quarter Td (v+3*ell+el)
    have hcharge : Td/4-17*ε/12≤
        hybridSaving v za+ell+2*el/3+max 0 (Td-v-3*ell-el)/2 := by
      have heq : Td-(v+3*ell+el)=Td-v-3*ell-el := by ring
      rw [heq] at hquarter
      linarith
    have hbound : reflectedExponent O₀ H S₀ B₀ za v ell el Td≤
        O₀/2+H-S₀-B₀+za-Td/4+(7+17/12)*ε := by
      unfold reflectedExponent
      linarith
    change reflectedExponent O₀ H S₀ B₀ za v ell el Td≤_
    apply hbound.trans
    dsimp [Td]
    linarith

end SevenEighths.ProbeLowReflected

end OAI
