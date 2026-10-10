import OAI.Probability.SLE.Loewner.PositiveSlitCapacity

namespace OAI

/-! The explicit normalized chart of an upper half disk. Comparing with
this chart bounds the capacity of a small slit. -/
noncomputable section
open Set Filter Complex Function Metric
open scoped Topology

namespace SLEExactGauge

def exteriorUpperRadius (R : ℝ) : Set ℂ := {z | R<‖z‖ ∧ z ∈ upperHalfPlane}

def radiusHullMap (R : ℝ) (z : ℂ) : ℂ := (R:ℂ)*exteriorJoukowski (z/(R:ℂ))

lemma divide_radius_bijOn {R : ℝ} (hR : 0<R) :
    BijOn (fun z : ℂ => z/(R:ℂ)) (exteriorUpperRadius R) exteriorUpperDisk := by
  have hR0 : (R:ℂ) ≠ 0 := ofReal_ne_zero.mpr hR.ne'
  have hnorm : ‖(R:ℂ)‖=R := by simp only [Complex.norm_real,Real.norm_eq_abs,abs_of_pos hR]
  refine ⟨?_,?_,?_⟩
  · intro z hz
    refine ⟨?_,?_⟩
    · rw [norm_div,hnorm,lt_div_iff₀ hR,one_mul]
      exact hz.1
    · change 0 < (z/(R:ℂ)).im
      rw [div_ofReal_im]
      exact div_pos hz.2 hR
  · intro z _ w _ he
    exact (div_left_inj' hR0).mp he
  · intro z hz
    refine ⟨(R:ℂ)*z,⟨?_,?_⟩,?_⟩
    · rw [norm_mul,hnorm]
      nlinarith [hz.1]
    · change 0 < ((R:ℂ)*z).im
      simpa only [mul_im,ofReal_re,ofReal_im,zero_mul,add_zero] using mul_pos hR hz.2
    · field_simp

lemma radiusHullMap_bijOn {R : ℝ} (hR : 0<R) :
    BijOn (radiusHullMap R) (exteriorUpperRadius R) upperHalfPlane := by
  have hh := (positive_real_affine_halfPlane hR 0).comp
    (exteriorJoukowski_bijOn.comp (divide_radius_bijOn hR))
  apply hh.congr
  intro z _
  simp only [radiusHullMap,Function.comp_apply,ofReal_zero,sub_zero]

lemma radiusHullMap_formula {R : ℝ} (hR : 0<R) (z : ℂ) :
    radiusHullMap R z=z+(R:ℂ)^2/z := by
  by_cases hz : z=0
  · simp [radiusHullMap,exteriorJoukowski,hz]
  · dsimp only [radiusHullMap,exteriorJoukowski]
    field_simp [ofReal_ne_zero.mpr hR.ne',hz]

lemma radiusHullMap_differentiableOn {R : ℝ} (hR : 0<R) :
    DifferentiableOn ℂ (radiusHullMap R) (exteriorUpperRadius R) := by
  have hd : DifferentiableOn ℂ (fun z : ℂ => z/(R:ℂ)) (exteriorUpperRadius R) :=
    differentiableOn_id.div_const _
  exact (exteriorJoukowski_differentiableOn.comp hd (divide_radius_bijOn hR).mapsTo).const_mul _

lemma radiusHullMap_coefficient {R : ℝ} (hR : 0<R) :
    Tendsto (fun z : ℂ => z*(radiusHullMap R z-z)) (cocompact ℂ) (𝓝 ((R:ℂ)^2)) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [(isCompact_singleton (x := (0:ℂ))).compl_mem_cocompact] with z hz
  rw [radiusHullMap_formula hR,add_sub_cancel_left]
  have hz0 : z ≠ 0 := hz
  field_simp [hz0]

end SLEExactGauge

end

end OAI
