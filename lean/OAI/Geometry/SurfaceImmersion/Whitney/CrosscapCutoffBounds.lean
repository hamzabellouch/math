import OAI.Geometry.SurfaceImmersion.Correction.CompactSmoothCutoffs

namespace OAI

/-! A smooth compact cutoff with the derivative bound needed to remove a
polynomial pair of crosscaps on a fixed rectangle. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing

theorem exists_crosscap_cutoff :
    ∃ (χ : ℝ → ℝ) (C : ℝ), ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧ 0 ≤ C ∧
      (∀ t, |t| ≤ 1 → χ t = 1 ∧ deriv χ t = 0) ∧
      ∀ t, |χ t+t*deriv χ t| ≤ C := by
  obtain ⟨χ,hχ,hcompact,_hvalues,_hsupp,hone⟩ := CollarVelocity.compact_cutoff
    (K := Icc (-2 : ℝ) 2) (U := Ioo (-3 : ℝ) 3) isCompact_Icc isOpen_Ioo
    (fun x hx => ⟨by linarith [hx.1],by linarith [hx.2]⟩)
  have hcont : Continuous (fun t => χ t+t*deriv χ t) :=
    hχ.continuous.add (continuous_id.mul (hχ.continuous_deriv (by simp)))
  obtain ⟨D,hD⟩ := hcompact.exists_bound_of_continuousOn hcont.continuousOn
  refine ⟨χ,1+|D|,hχ,hcompact,by positivity,?_,?_⟩
  · intro t ht
    have hI : t ∈ Ioo (-2 : ℝ) 2 := by
      obtain ⟨hl,hr⟩ := abs_le.mp ht
      exact ⟨by linarith,by linarith⟩
    have he : χ =ᶠ[𝓝 t] fun _ => (1 : ℝ) := by
      filter_upwards [isOpen_Ioo.mem_nhds hI] with y hy
      exact hone y ⟨hy.1.le,hy.2.le⟩
    exact ⟨he.self_of_nhds,by rw [he.deriv_eq]; simp⟩
  · intro t
    by_cases ht : t ∈ tsupport χ
    · exact (hD t ht).trans (by linarith [le_abs_self D])
    · rw [image_eq_zero_of_notMem_tsupport ht,deriv_of_notMem_tsupport ht]
      simp only [mul_zero, add_zero, abs_zero]
      positivity

theorem exists_crosscap_cutoff_scale :
    ∃ (χ : ℝ → ℝ) (R : ℝ), ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧ 0 < R ∧
      χ 0 = 1 ∧ ∀ y : ℝ,
        0 < 3*y^2-3+4*(χ (y/R)+(y/R)*deriv χ (y/R)) := by
  obtain ⟨χ,C,hχ,hcompact,hC,hone,hbound⟩ := exists_crosscap_cutoff
  let R := C+2
  have hR : 0 < R := by dsimp [R]; linarith
  refine ⟨χ,R,hχ,hcompact,hR,(hone 0 (by norm_num)).1,?_⟩
  intro y
  by_cases hy : |y/R| ≤ 1
  · obtain ⟨hχy,hdy⟩ := hone (y/R) hy
    rw [hχy,hdy]
    nlinarith [sq_nonneg y]
  · have hRy : R < |y| := by
      have hh : 1 < |y| / R := by simpa only [abs_div,abs_of_pos hR] using lt_of_not_ge hy
      simpa only [one_mul] using (lt_div_iff₀ hR).mp hh
    have hsq : R^2 ≤ y^2 := by
      have hh := mul_self_le_mul_self hR.le hRy.le
      simpa only [← pow_two,sq_abs] using hh
    have hl := (abs_le.mp (hbound (y/R))).1
    have hmargin : 0 < 3*R^2-3-4*C := by
      dsimp [R]
      nlinarith [sq_nonneg C]
    nlinarith

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
