import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialExteriorFiniteLimit

namespace OAI

/-! Removal of the finite-interval cutoff around the actual nonzero free profile. -/

open Set Filter
namespace DefocusingNLS

theorem exists_radialExterior_finite_limit (ν : ℕ → ℂ) (μ : ℂ)
    (hν : Tendsto ν atTop (nhds μ)) (g : ℝ → ℂ × ℂ) (hg : Continuous g)
    (δ ρ u T : ℝ) (hδ : 0 < δ) (hT : 0 ≤ T) (hρ1 : ρ < 1)
    (hb : ∀ t ∈ Icc (u-T) u, ‖(g t).1‖+2*δ ≤ ρ)
    (hlow : ∀ t ∈ Icc (u-T) u, δ < ‖(g t).1‖)
    (hgd : ∀ t ∈ Icc (u-T) u, HasDerivAt g
      ((0,-Complex.I*(Real.exp (2*t)/2 : ℝ)*(g t).2)+radialExteriorErrorMatrix μ (g t)) t)
    (x : ℕ → ℂ × ℂ) (hx : Tendsto x atTop (nhds (g u))) :
    ∃ Z : ℕ → ℝ → ℂ × ℂ,
      (∀ n, Continuous (Z n) ∧ Z n u=x n) ∧
      TendstoUniformlyOn Z g atTop (Icc (u-T) u) ∧
      ∀ᶠ n in atTop, ∀ t ∈ Icc (u-T) u, (Z n t).1 ≠ 0 ∧
        HasDerivAt (Z n)
          ((Z n t).2,-(2*ν n+10+Complex.I*(Real.exp (2*t)/2 : ℝ))*(Z n t).2-
            ν n*(ν n+10)*(Z n t).1+oddPowerNonlinearity n (Z n t).1) t := by
  obtain ⟨Z,hZ,hconv⟩ := exists_radialExterior_clipped_limit ν μ hν g hg
    δ ρ u T hδ.le hT hρ1 hb hgd x hx
  refine ⟨Z,fun n => ⟨(hZ n).1,(hZ n).2.1⟩,hconv,?_⟩
  filter_upwards [(Metric.tendstoUniformlyOn_iff.mp hconv) δ hδ] with n hn t ht
  have hdist := hn t ht
  rw [dist_comm,dist_eq_norm] at hdist
  have hc : ‖(Z n t).1-(g t).1‖ < δ :=
    (norm_fst_le (Z n t-g t)).trans_lt hdist
  have hne : (Z n t).1 ≠ 0 := by
    intro he
    rw [he,zero_sub,norm_neg] at hc
    exact ((hlow t ht).trans hc).false
  refine ⟨hne,?_⟩
  have hd := (hZ n).2.2 t ht
  rwa [radialExteriorFiniteField_eq (ν n) n (fun r => (g r).1) δ t (Z n t) hc.le] at hd

end DefocusingNLS

end OAI
