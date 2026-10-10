import Mathlib
import OAI.Analysis.BiholderTransport.Coordinates.FiniteLogScaleAvoidance

namespace OAI

section
section
noncomputable section
open Set

namespace WeakMTWTransport

lemma uniform_finite_radial_scale {N : ℕ} {D η L : ℝ}
    (hD : 0 < D) (hη : 0<η) (hL : 0 < L) :
    ∃ c : ℝ, 0 < c ∧ ∀ (S : Finset ℝ), S.card ≤ N → ∀ s₀ s₁ : ℝ,
      0 < s₁ → s₁ ≤ D → s₀ < c*s₁ →
      ∃ δ : ℝ, 0<δ ∧ δ ≤ η ∧ Real.exp L*s₀ ≤ δ ∧ δ*Real.exp L ≤ s₁ ∧
        ∀ s∈S, Real.exp L*s ≤ δ ∨ δ*Real.exp L ≤ s := by
  classical
  let T := min (η/D) (Real.exp (-L))
  let W := ((N:ℝ)+3)*(2*L+1)
  have hT : 0 < T := lt_min (div_pos hη hD) (Real.exp_pos _)
  have hTe : T ≤ Real.exp (-L) := min_le_right _ _
  have hTη : T*D ≤ η := by
    have HH := min_le_left (η/D) (Real.exp (-L))
    change T ≤ η/D at HH
    exact (le_div_iff₀ hD).mp HH
  refine ⟨T*Real.exp (-W-L),mul_pos hT (Real.exp_pos _),?_⟩
  intro S hNS s₀ s₁ hs₁ hsD hs₀
  let Q := (S.filter (fun s => 0 < s)).image Real.log
  have hQc : Q.card ≤ N := (Finset.card_image_le.trans (Finset.card_filter_le _ _)).trans hNS
  have hlog : Real.exp (Real.log (s₁*T))=s₁*T := Real.exp_log (mul_pos hs₁ hT)
  have hwide : (Real.log (s₁*T)-W)+((Q.card:ℝ)+2)*(2*L+1) < Real.log (s₁*T) := by
    have hc : (Q.card:ℝ) ≤ N := by exact_mod_cast hQc
    dsimp [W]
    have HH := mul_nonneg (show 0 ≤ (N:ℝ)-Q.card by linarith) (show 0 ≤ 2*L+1 by linarith)
    nlinarith only [HH,hL]
  obtain ⟨u,hu,hsep⟩ := finite_log_scale_avoidance Q hL.le hwide
  let δ := Real.exp u
  have hδhi : δ ≤ s₁*T := by
    have HH := (Real.exp_lt_exp.mpr hu.2).le
    simpa only [hlog] using HH
  have hδlo : s₁*T*Real.exp (-W) ≤ δ := by
    have HH := (Real.exp_lt_exp.mpr hu.1).le
    rw [sub_eq_add_neg,Real.exp_add,hlog] at HH
    exact HH
  have hexp : Real.exp (-L)*Real.exp L=1 := by rw [←Real.exp_add]; simp
  have hexpW : Real.exp (-W-L)*Real.exp L=Real.exp (-W) := by
    rw [←Real.exp_add]
    congr 1
    ring
  refine ⟨δ,Real.exp_pos _,?_,?_,?_,?_⟩
  · have HH := mul_le_mul_of_nonneg_right hsD hT.le
    exact hδhi.trans (HH.trans (by simpa only [mul_comm T] using hTη))
  · have HH := mul_lt_mul_of_pos_right hs₀ (Real.exp_pos L)
    have he : T*Real.exp (-W-L)*s₁*Real.exp L=s₁*T*Real.exp (-W) := by
      calc
        _ = (s₁*T)*(Real.exp (-W-L)*Real.exp L) := by ring
        _ = _ := by rw [hexpW]
    rw [he] at HH
    have Hcenter : Real.exp L*s₀ ≤ s₁*T*Real.exp (-W) := by
      simpa only [mul_comm (Real.exp L) s₀] using HH.le
    exact Hcenter.trans hδlo
  · have HH := mul_le_mul_of_nonneg_right hδhi (Real.exp_pos L).le
    have H2 := mul_le_mul_of_nonneg_left hTe hs₁.le
    have H3 := mul_le_mul_of_nonneg_right H2 (Real.exp_pos L).le
    have he : s₁*Real.exp (-L)*Real.exp L=s₁ := by rw [mul_assoc,hexp,mul_one]
    rw [he] at H3
    exact HH.trans H3
  · intro s hs
    by_cases hspos : 0 < s
    · have hlogs : Real.log s∈Q := Finset.mem_image.mpr
        ⟨s,Finset.mem_filter.mpr ⟨hs,hspos⟩,rfl⟩
      rcases lt_abs.mp (hsep (Real.log s) hlogs) with HH|HH
      · left
        have Hexp := (Real.exp_lt_exp.mpr (show Real.log s+L < u by linarith)).le
        rw [Real.exp_add,Real.exp_log hspos] at Hexp
        simpa only [mul_comm s] using Hexp
      · right
        have Hexp := (Real.exp_lt_exp.mpr (show u+L < Real.log s by linarith)).le
        rw [Real.exp_add,Real.exp_log hspos] at Hexp
        exact Hexp
    · exact Or.inl ((mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos L).le (le_of_not_gt hspos)).trans
        (Real.exp_pos u).le)
end WeakMTWTransport

end

end

section

noncomputable section
namespace WeakMTWTransport

lemma radial_profile_small {s δ l b f R ε : ℝ}
    (hs : 0 ≤ s) (hd : 0 < δ) (hl : 0 ≤ l) (hR : 1 ≤ R)
    (hsmall : R*s ≤ δ) (hbg : b*δ ≤ ε)
    (hf : l*δ/(s+δ)-b*δ ≤ f) : l/2-ε ≤ f := by
  have hsδ : s ≤ δ := by nlinarith [mul_nonneg hs (sub_nonneg.mpr hR)]
  have HH : l/2 ≤ l*δ/(s+δ) := by
    rw [le_div_iff₀ (add_pos_of_nonneg_of_pos hs hd)]
    nlinarith [mul_nonneg hl (sub_nonneg.mpr hsδ)]
  linarith

lemma radial_profile_large {s δ u b f R ε : ℝ}
    (hs : 0 ≤ s) (hd : 0 < δ) (hu : 0 ≤ u) (hR : 0 < R)
    (hlarge : δ*R ≤ s) (hbg : b*δ ≤ ε)
    (hf : f ≤ u*δ/(s+δ)+b*δ) : f ≤ u/R+ε := by
  have HH : u*δ/(s+δ) ≤ u/R := by
    rw [div_le_div_iff₀ (add_pos_of_nonneg_of_pos hs hd) hR]
    nlinarith [mul_nonneg hu (show 0 ≤ s+δ-δ*R by linarith)]
  linarith
end WeakMTWTransport

end

end

end

end OAI
