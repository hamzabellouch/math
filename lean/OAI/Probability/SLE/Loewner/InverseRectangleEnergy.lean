import OAI.Probability.SLE.Loewner.InverseVerticalDifferentiation

namespace OAI

/-! Fubini transfers the common inverse-chart Dirichlet bound to
vertical sections over a bounded real interval. -/
noncomputable section
open Set Filter Function Complex Metric MeasureTheory
open scoped Topology ENNReal

namespace SLEExactGauge

theorem initialInverse_rectangle_energy (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t≠0 → p t∈upperHalfPlane)
    {R : ℝ} (hR : 0<R) (hp : ∀ t : unitInterval, ‖p t‖<R)
    (s : unitInterval) (a b L : ℝ) {h : ℝ} (_hh : 0<h) (hh1 : h≤1)
    (hx : ∀ x∈Ioo a b, |x|≤L) :
    (∫ x in Ioo a b, ∫ y in Ioc 0 h,
      ‖deriv (initialInverseChart p hi h0 hH s) ((x:ℂ)+(y:ℂ)*Complex.I)‖^2)≤
        (volume (closedBall (0:ℂ) (L+2+3*R))).toReal ∧
    IntegrableOn (fun x : ℝ => ∫ y in Ioc 0 h,
      ‖deriv (initialInverseChart p hi h0 hH s) ((x:ℂ)+(y:ℂ)*Complex.I)‖^2)
      (Ioo a b) ∧
    ∀ᵐ x : ℝ ∂volume.restrict (Ioo a b),
      MemLp (fun y : ℝ => deriv (initialInverseChart p hi h0 hH s)
        ((x:ℂ)+(y:ℂ)*Complex.I)) 2 (volume.restrict (Ioc 0 h)) := by
  let F := initialInverseChart p hi h0 hH s
  let J := Ioo a b
  let K := Ioc 0 h
  let S := upperHalfPlane ∩ ball (0:ℂ) (L+2)
  let T := {z : ℂ | z.re∈J ∧ z.im∈K}
  let e := Complex.measurableEquivRealProd.symm
  have he : MeasurePreserving e volume volume := Complex.volume_preserving_equiv_real_prod.symm _
  have hpre : e ⁻¹' T=J ×ˢ K := by ext z; simp [e,T,J,K]
  have hTS : T⊆S := by
    intro z hz
    refine ⟨hz.2.1,mem_ball_zero_iff.mpr ?_⟩
    have hb := norm_le_abs_re_add_abs_im z
    rw [abs_of_pos hz.2.1] at hb
    have hx' := hx z.re hz.1
    have hy' : z.im≤1 := hz.2.2.trans hh1
    linarith
  have hiS : IntegrableOn (fun z => ‖deriv F z‖^2) S :=
    initialInverse_energy_integrable p hi h0 hH hR hp s (L+2)
  have hiT := hiS.mono_set hTS
  have hip : Integrable (fun z : ℝ × ℝ => ‖deriv F (e z)‖^2)
      ((volume.restrict J).prod (volume.restrict K)) := by
    rw [Measure.prod_restrict]
    exact hpre ▸ (he.integrableOn_comp_preimage e.measurableEmbedding).mpr hiT
  have heq : (∫ x in J, ∫ y in K, ‖deriv F (e (x,y))‖^2)=
      ∫ z in T, ‖deriv F z‖^2 := by
    rw [← integral_prod _ hip,Measure.prod_restrict,←hpre]
    simpa only [Measure.volume_eq_prod] using
      he.setIntegral_preimage_emb e.measurableEmbedding (fun z => ‖deriv F z‖^2) T
  have hbound : (∫ x in J, ∫ y in K, ‖deriv F (e (x,y))‖^2)≤
      (volume (closedBall (0:ℂ) (L+2+3*R))).toReal := by
    rw [heq]
    exact (setIntegral_mono_set hiS (ae_of_all _ (fun z => sq_nonneg _)) hTS.eventuallySubset).trans
      (initialInverse_energy_integral_le p hi h0 hH hR hp s (L+2))
  have hsections : ∀ᵐ x : ℝ ∂volume.restrict J,
      MemLp (fun y : ℝ => deriv F (e (x,y))) 2 (volume.restrict K) := by
    filter_upwards [hip.prod_right_ae] with x hxi
    have hm : AEStronglyMeasurable (fun y : ℝ => deriv F (e (x,y))) (volume.restrict K) :=
      ((measurable_deriv F).comp (e.measurable.comp measurable_prodMk_left)).aestronglyMeasurable
    exact (memLp_two_iff_integrable_sq_norm hm).mpr hxi
  have heval (x y : ℝ) : e (x,y)=(x:ℂ)+(y:ℂ)*Complex.I := by
    apply Complex.ext <;> simp [e]
  constructor
  · simpa only [heval] using hbound
  · constructor
    · simpa only [heval,F,J,K,IntegrableOn] using hip.integral_prod_left
    · simpa only [heval] using hsections

end SLEExactGauge

end

end OAI
