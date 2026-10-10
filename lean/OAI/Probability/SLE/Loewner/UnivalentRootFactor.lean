import OAI.Probability.SLE.Loewner.UnivalentOddRoot

namespace OAI

/-! The normalized odd-root construction with its analytic factor kept
explicit for coefficient extraction. -/
noncomputable section
open Set Filter Metric Function
open scoped Topology

namespace SLEExactGauge

lemma univalent_root_factor {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (ball 0 1)) (hi : InjOn f (ball 0 1))
    (hf0 : f 0=0) (hd0 : deriv f 0=1) :
    ∃ q : ℂ → ℂ, DifferentiableOn ℂ q (ball 0 1) ∧ q 0=1 ∧
      (∀ z∈ball (0:ℂ) 1, q z^2=dslope f 0 z) ∧
      (∀ z∈ball (0:ℂ) 1, q z≠0) ∧
      InjOn (fun z : ℂ => z*q (z^2)) (ball 0 1) := by
  have hzero : (0:ℂ)∈ball 0 1 := mem_ball_self zero_lt_one
  let g := dslope f 0
  have hg : DifferentiableOn ℂ g (ball 0 1) :=
    (Complex.differentiableOn_dslope (ball_mem_nhds (0:ℂ) zero_lt_one)).mpr hf
  have hg0 : g 0=1 := by simpa [g] using hd0
  have hgne (z : ℂ) (hz : z∈ball (0:ℂ) 1) : g z≠0 := by
    by_cases hz0 : z=0
    · simpa only [hz0,hg0] using one_ne_zero
    · dsimp only [g]
      rw [dslope_of_ne _ hz0,slope_def_field,hf0,sub_zero,sub_zero]
      exact div_ne_zero (fun h => hz0 (hi hz hzero (h.trans hf0.symm))) hz0
  obtain ⟨q,hq,hq0,hq2⟩ := exists_normalized_analytic_square_root hg hgne hg0
  have hqne (z : ℂ) (hz : z∈ball (0:ℂ) 1) : q z≠0 := by
    intro he
    apply hgne z hz
    rw [←hq2 z hz,he,zero_pow (by norm_num : (2:ℕ)≠0)]
  refine ⟨q,hq,hq0,hq2,hqne,?_⟩
  let h (z : ℂ) := z*q (z^2)
  have hs (z : ℂ) (hz : z∈ball (0:ℂ) 1) : z^2∈ball (0:ℂ) 1 := by
    rw [mem_ball_zero_iff,norm_pow]
    exact pow_lt_one₀ (norm_nonneg _) (mem_ball_zero_iff.mp hz) (by norm_num)
  have hh2 (z : ℂ) (hz : z∈ball (0:ℂ) 1) : h z^2=f (z^2) := by
    dsimp only [h]
    rw [mul_pow,hq2 _ (hs z hz)]
    have he := sub_smul_dslope f 0 (z^2)
    simpa only [sub_zero,hf0,smul_eq_mul] using he
  have hodd (z : ℂ) : h (-z)= -h z := by simp [h]
  intro z hz w hw he
  change h z=h w at he
  have he2 : z^2=w^2 := hi (hs z hz) (hs w hw)
    ((hh2 z hz).symm.trans ((congrArg (fun v : ℂ => v^2) he).trans (hh2 w hw)))
  rcases (sq_eq_sq_iff_eq_or_eq_neg).mp he2 with hzw | hzw
  · exact hzw
  · have hhz : h z=0 := by
      have he' : h z= -h z := he.trans (by rw [show w= -z by rw [hzw,neg_neg],hodd])
      linear_combination (1/2:ℂ)*he'
    have hz2 : z^2=0 := hi (hs z hz) hzero (by rw [←hh2 z hz,hhz,hf0]; simp)
    have hz0 : z=0 := (pow_eq_zero_iff (by norm_num : (2:ℕ)≠0)).mp hz2
    rw [hz0] at hzw
    rw [hz0]
    simpa [eq_comm] using hzw

end SLEExactGauge

end

end OAI
