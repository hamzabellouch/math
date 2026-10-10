import Mathlib

namespace OAI
noncomputable section
open Set Filter
namespace ParametrixUniqueness

lemma nonneg_energy_eq_zero {E : ℝ → ℝ} {T L : ℝ} (hT : 0<T)
    (hc : ContinuousOn E (Icc 0 T)) (h0 : E 0=0)
    (hpos : ∀ t ∈ Icc 0 T, 0≤E t)
    (hd : ∀ t ∈ Ioo 0 T, ∃ d : ℝ, HasDerivAt E d t ∧ d≤L*E t) :
    ∀ t ∈ Icc 0 T, E t=0 := by
  let F : ℝ → ℝ := fun t => Real.exp (-L*t)*E t
  have hcF : ContinuousOn F (Icc 0 T) :=
    ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn).mul hc
  have hFd (t : ℝ) (ht : t ∈ Ioo 0 T) : ∃ d : ℝ, HasDerivAt F d t ∧ d≤0 := by
    obtain ⟨e,he,heL⟩ := hd t ht
    have hex := ((hasDerivAt_id t).const_mul (-L)).exp
    refine ⟨_,hex.mul he,?_⟩
    have hh := mul_le_mul_of_nonneg_left heL (Real.exp_pos (-L*t)).le
    dsimp
    nlinarith
  have hant : AntitoneOn F (Icc 0 T) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 T) hcF
    · intro t ht
      rw [interior_Icc] at ht
      obtain ⟨d,hd,_⟩ := hFd t ht
      exact hd.differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      obtain ⟨d,hd,hb⟩ := hFd t ht
      rwa [hd.deriv]
  intro t ht
  have hh := hant ⟨le_rfl,hT.le⟩ ht ht.1
  have hf0 : F 0=0 := by simp [F,h0]
  rw [hf0] at hh
  change Real.exp (-L*t)*E t≤0 at hh
  have hev : E t≤0 := by nlinarith [Real.exp_pos (-L*t)]
  exact le_antisymm hev (hpos t ht)
end ParametrixUniqueness

end

end OAI
