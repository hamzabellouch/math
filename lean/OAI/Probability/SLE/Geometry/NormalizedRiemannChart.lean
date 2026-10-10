import OAI.Probability.SLE.Loewner.ReflectedSlitRiemann

namespace OAI

/-! Normalization of the Riemann chart at the inversion origin. The
phase is fixed by requiring a positive real first derivative. -/
noncomputable section
open Set Complex Metric Function

namespace SLEExactGauge

theorem exists_zero_normalized_riemann_chart {D : Set ℂ}
    (ho : IsOpen D) (hs : IsSimplyConnected D) (hne : D ≠ univ) (h0 : (0:ℂ) ∈ D) :
    ∃ f : ℂ → ℂ, BijOn f D (ball 0 1) ∧ DifferentiableOn ℂ f D ∧ f 0=0 ∧
      ∃ a : ℝ, 0 < a ∧ deriv f 0=(a:ℂ) := by
  have hroots := hs.hasHolomorphicSquareRoots ho
  obtain ⟨f,hf,hmax⟩ := TauCeti.exists_isMaxOn_norm_deriv_of_hasHolomorphicSquareRoots
    hroots ho hs.isPathConnected.isConnected.isPreconnected hne h0
  have hsurj := TauCeti.surjOn_ball_of_isMaxOn ho hroots h0 hf hmax
  have hd : deriv f 0 ≠ 0 := hf.deriv_ne_zero ho h0
  let c : ℂ := (‖deriv f 0‖:ℂ)/deriv f 0
  have hdn : 0 < ‖deriv f 0‖ := norm_pos_iff.mpr hd
  have hc : c ≠ 0 := div_ne_zero (by exact_mod_cast hdn.ne') hd
  have hcn : ‖c‖=1 := by
    simp only [c,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hdn]
    exact div_self hdn.ne'
  let g : ℂ → ℂ := fun z => c*f z
  have hgm : MapsTo g D (ball 0 1) := by
    intro z hz
    have hh := hf.mapsTo hz
    simpa only [g,mem_ball,dist_zero_right,norm_mul,hcn,one_mul] using hh
  have hgi : InjOn g D := by
    intro z hz w hw he
    apply hf.injOn hz hw
    exact mul_left_cancel₀ hc he
  have hgs : SurjOn g D (ball 0 1) := by
    intro w hw
    have hcInv : ‖c⁻¹‖=1 := by rw [norm_inv,hcn,inv_one]
    have hw' : c⁻¹*w ∈ ball (0:ℂ) 1 := by
      simpa only [mem_ball,dist_zero_right,norm_mul,hcInv,one_mul] using hw
    obtain ⟨z,hz,hfz⟩ := hsurj hw'
    refine ⟨z,hz,?_⟩
    change c*f z=w
    rw [hfz,← mul_assoc,mul_inv_cancel₀ hc,one_mul]
  refine ⟨g,⟨hgm,hgi,hgs⟩,hf.differentiableOn.const_mul c,?_,‖deriv f 0‖,hdn,?_⟩
  · simp only [g,hf.map_base,mul_zero]
  · have hh := ((hf.differentiableOn.differentiableAt (ho.mem_nhds h0)).hasDerivAt.const_mul c).deriv
    change deriv g 0=(‖deriv f 0‖:ℂ)
    rw [hh]
    dsimp only [c]
    exact div_mul_cancel₀ _ hd

end SLEExactGauge

end

end OAI
