import OAI.Analysis.Mahler.RescaledHolomorphic

namespace OAI

namespace MahlerRescaling
open Set Metric Filter
open scoped Topology

theorem uniform_of_linear_error {X H : Type*} [NormedAddCommGroup H]
    {F : ℝ → X → H} {g : X → H} {K : Set X} {C δ : ℝ}
    (hC : 0 < C) (hδ : 0 < δ)
    (hbound : ∀ ε : ℝ, 0 < ε → ε < δ → ∀ x ∈ K, ‖F ε x-g x‖ ≤ C*ε) :
    TendstoUniformlyOn F g (𝓝[>] 0) K := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro η hη
  have hsmall : ∀ᶠ ε : ℝ in 𝓝[>] 0, ε < min δ (η/C) :=
    (eventually_lt_nhds (lt_min hδ (div_pos hη hC))).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin,hsmall] with ε hε hsmall'
  intro x hx
  have hεpos : 0 < ε := hε
  have hb := hbound ε hεpos (lt_min_iff.mp hsmall').1 x hx
  rw [dist_eq_norm']
  exact hb.trans_lt (by
    have h := (lt_div_iff₀ hC).mp (lt_min_iff.mp hsmall').2
    nlinarith)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]

/-- Differentiating the actual first derivative on an open set preserves
subtraction through order two; holomorphicity supplies the required smoothness. -/
lemma second_fderiv_sub_of_open {f g : E → ℂ} {U : Set E} {x : E}
    (hU : IsOpen U) (hx : x ∈ U)
    (hf : DifferentiableOn ℂ f U) (hg : DifferentiableOn ℂ g U) :
    fderiv ℂ (fderiv ℂ (fun y => f y-g y)) x =
      fderiv ℂ (fderiv ℂ f) x - fderiv ℂ (fderiv ℂ g) x := by
  have he : fderiv ℂ (fun y => f y-g y) =ᶠ[𝓝 x]
      fun y => fderiv ℂ f y - fderiv ℂ g y := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact fderiv_fun_sub ((hf y hy).differentiableAt (hU.mem_nhds hy))
      ((hg y hy).differentiableAt (hU.mem_nhds hy))
  rw [he.fderiv_eq]
  have hfc : ContDiffOn ℂ 1 (fderiv ℂ f) U :=
    (Mahler.contDiffOn_nat_of_differentiableOn_open hU 2 hf).fderiv_of_isOpen hU (by norm_num)
  have hgc : ContDiffOn ℂ 1 (fderiv ℂ g) U :=
    (Mahler.contDiffOn_nat_of_differentiableOn_open hU 2 hg).fderiv_of_isOpen hU (by norm_num)
  exact fderiv_fun_sub ((hfc.differentiableOn (by norm_num) x hx).differentiableAt (hU.mem_nhds hx))
    ((hgc.differentiableOn (by norm_num) x hx).differentiableAt (hU.mem_nhds hx))

end MahlerRescaling

end OAI
