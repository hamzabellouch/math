import OAI.Analysis.CircleDomains.Topology.RegularJordanParametrization

namespace OAI

/-! The actual positively sized round disk and its once-traversed regular
boundary, used to specialize the published Green identity to a disk. -/
open Set Function Filter Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 def roundDiskChart (R : ℝ) (hR : 0 < R) : ℂ ≃ₜ ℂ :=
  Homeomorph.mulLeft₀ (R : ℂ) (by exact_mod_cast hR.ne')

 theorem roundDiskChart_interior (R : ℝ) (hR : 0 < R) :
    jordanInterior (roundDiskChart R hR) = ball (0 : ℂ) R := by
  have hn : ‖(R : ℂ)‖ = R := by simp [abs_of_pos hR]
  have hRc : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    rw [mem_ball, dist_zero_right]
    change ‖(R : ℂ)*w‖ < R
    rw [norm_mul, hn]
    have hw' : ‖w‖ < 1 := by simpa only [mem_ball, dist_zero_right] using hw
    nlinarith
  · intro hz
    have hz' : ‖z‖ < R := by simpa only [mem_ball, dist_zero_right] using hz
    refine ⟨z/(R : ℂ), ?_, ?_⟩
    · rw [mem_ball, dist_zero_right]
      change ‖z/(R : ℂ)‖ < 1
      rw [norm_div, hn]
      exact (div_lt_one hR).mpr hz'
    · change (R : ℂ)*(z/(R : ℂ)) = z
      exact mul_div_cancel₀ z hRc

 theorem unitCircleParam_hasDerivAt (R t : ℝ) :
    HasDerivAt (unitCircleParam 0 R)
      (circleMap 0 R (2*Real.pi*t) * Complex.I * (2*Real.pi)) t := by
  change HasDerivAt (fun s : ℝ => circleMap 0 R (2*Real.pi*s)) _ t
  convert (hasDerivAt_circleMap 0 R (2*Real.pi*t)).scomp t
    ((hasDerivAt_id t).const_mul (2*Real.pi)) using 1 <;>
    simp only [Function.comp_def, Complex.real_smul, Complex.ofReal_mul,
      Complex.ofReal_ofNat, mul_one]
  ring


 theorem unitCircleParam_regular (R : ℝ) (hR : 0 < R) :
    RegularJordanParametrization (roundDiskChart R hR) (unitCircleParam 0 R) := by
  have hp : 0 < 2*Real.pi := mul_pos (by norm_num) Real.pi_pos
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact (contDiff_circleMap 0 R).comp (contDiff_const.mul contDiff_id)
  · intro t
    change circleMap 0 R (2*Real.pi*(t+1)) = circleMap 0 R (2*Real.pi*t)
    rw [show 2*Real.pi*(t+1) = 2*Real.pi*t + 2*Real.pi by ring]
    exact periodic_circleMap 0 R _
  · intro a ha b hb heq
    apply (mul_left_cancel₀ hp.ne')
    apply injOn_circleMap_of_abs_sub_le' hR.ne' (a := 0) (b := 2*Real.pi) (by simp)
    · exact ⟨mul_nonneg hp.le ha.1, by nlinarith [ha.2]⟩
    · exact ⟨mul_nonneg hp.le hb.1, by nlinarith [hb.2]⟩
    · exact heq
  · intro t
    rw [(unitCircleParam_hasDerivAt R t).deriv]
    exact mul_ne_zero (mul_ne_zero (circleMap_ne_center hR.ne') Complex.I_ne_zero)
      (by exact_mod_cast hp.ne')
  · rw [roundDiskChart_interior, frontier_ball (0 : ℂ) hR.ne']
    apply Subset.antisymm
    · rintro z ⟨t, ht, rfl⟩
      have hm : unitCircleParam 0 R t ∈ range (circleMap 0 R) := ⟨2*Real.pi*t, rfl⟩
      simpa only [range_circleMap, abs_of_pos hR] using hm
    · intro z hz
      have hz' : z ∈ circleMap 0 R '' Ioc 0 (2*Real.pi) := by
        simpa only [image_circleMap_Ioc, abs_of_pos hR] using hz
      obtain ⟨t, ht, rfl⟩ := hz'
      refine ⟨t/(2*Real.pi), ⟨le_of_lt (div_pos ht.1 hp), (div_le_one hp).mpr ht.2⟩, ?_⟩
      change circleMap 0 R (2*Real.pi*(t/(2*Real.pi))) = circleMap 0 R t
      rw [mul_div_cancel₀ t hp.ne']

end CircleDomainRigidity

end

end OAI
