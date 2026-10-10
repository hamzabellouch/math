import OAI.MeasureTheory.Falconer.Recursion.ProfileTelescoping

namespace OAI

/-! # Fixed block and density losses below the weak radial exponent -/

namespace Falconer

theorem weak_radial_cap_parameters (d : ℕ) {β ℓ : ℝ}
    (hβ : 0 < β) (hℓ : ℓ < β*((d:ℝ)-1)) :
    ∃ J : ℕ, 0 < J ∧ ∃ e f L : ℝ, 0 < e ∧ 0 < f ∧ 0 < L ∧
      (J:ℝ)*(e+f)-β*((d:ℝ)-1-2*(d:ℝ)/((J:ℝ)+2)-L) < -ℓ := by
  let gap := β*((d:ℝ)-1)-ℓ
  have hg : 0 < gap := sub_pos.mpr hℓ
  obtain ⟨J,hJ⟩ := exists_nat_gt (max 1 (8*β*(d:ℝ)/gap))
  have hJ1 : (1:ℝ) < J := (le_max_left _ _).trans_lt hJ
  have hJpos : 0 < J := by exact_mod_cast (zero_lt_one.trans hJ1)
  have hJden : (0:ℝ) < (J:ℝ)+2 := by positivity
  have hJB : 8*β*(d:ℝ)/gap < (J:ℝ)+2 := by
    have hh := (le_max_right _ _).trans_lt hJ
    linarith
  have hignored : β*(2*(d:ℝ)/((J:ℝ)+2)) < gap/4 := by
    have hh := (div_lt_iff₀ hg).mp hJB
    apply (lt_div_iff₀ (by norm_num : (0:ℝ) < 4)).mpr
    rw [show β*(2*(d:ℝ)/((J:ℝ)+2))*4 = (8*β*(d:ℝ))/((J:ℝ)+2) by ring]
    apply (div_lt_iff₀ hJden).mpr
    nlinarith
  let e := gap/(16*((J:ℝ)+1))
  let f := e
  let L := gap/(4*β)
  have he : 0 < e := by dsimp [e]; positivity
  have hf : 0 < f := he
  have hL : 0 < L := by dsimp [L]; positivity
  have hef : ((J:ℝ)+1)*(e+f) = gap/8 := by
    dsimp [e,f]
    field_simp
    ring
  have hsum : (J:ℝ)*(e+f) ≤ gap/4 := by nlinarith
  have hloss : β*L = gap/4 := by dsimp [L]; field_simp
  refine ⟨J,hJpos,e,f,L,he,hf,hL,?_⟩
  dsimp [gap] at hg hignored hsum hloss
  nlinarith

end Falconer

end OAI
