import OAI.Analysis.CircleDomains.Sobolev.SobolevJacobianLocality

namespace OAI

/-! Compact Sobolev perturbations contribute zero total first derivative.
The support and integrability of the actual weak derivative are proved,
so the boundary-flux replacement does not assume an unproved trace fact. -/
open Set Filter Function MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem compact_weakGradient_zero_off {u : EuclideanPlane → ℝ}
    (hu : DeGiorgi.MemW1pWitness 2 u univ) (i : Fin 2) :
    ∀ᵐ x ∂volume, x ∉ tsupport u → hu.weakGrad x i = 0 := by
  have heq : EqOn u (fun x => (0 : ℝ) * u x) (tsupport u)ᶜ := by
    intro x hx
    simp only [zero_mul]
    exact image_eq_zero_of_notMem_tsupport hx
  have hh := weakGradient_eq_on_open hu (hu.smul 0) isClosed_closure.isOpen_compl heq i
  have hh' := (ae_restrict_iff' isClosed_closure.measurableSet.compl).mp hh
  filter_upwards [hh'] with x hx hxU
  simpa only [DeGiorgi.MemW1pWitness.smul, zero_smul, PiLp.zero_apply] using hx hxU

 theorem compact_weakGradient_integrable {u : EuclideanPlane → ℝ}
    (hu : DeGiorgi.MemW1pWitness 2 u univ) (hs : HasCompactSupport u) (i : Fin 2) :
    Integrable (fun x => hu.weakGrad x i) := by
  let : IsFiniteMeasure (volume.restrict (tsupport u)) :=
    isFiniteMeasure_restrict.mpr hs.isCompact.measure_lt_top.ne
  have hG : MemLp (fun x => hu.weakGrad x i) 2 volume := by
    simpa only [Measure.restrict_univ] using hu.weakGrad_component_memLp i
  have hi : IntegrableOn (fun x => hu.weakGrad x i) (tsupport u) :=
    (hG.restrict _).integrable (by norm_num)
  exact hi.integrable_of_ae_notMem_eq_zero (compact_weakGradient_zero_off hu i)

 theorem integral_compact_weakGradient_eq_zero {u : EuclideanPlane → ℝ}
    (hu : DeGiorgi.MemW1pWitness 2 u univ) (hs : HasCompactSupport u) (i : Fin 2) :
    (∫ x, hu.weakGrad x i) = 0 := by
  obtain ⟨η, V, hη, hsη, _hunit, _hsub, hV, hKV, hone⟩ :=
    exists_smooth_compact_cutoff_one_near hs.isCompact isOpen_univ (subset_univ _)
  have hd (x : EuclideanPlane) (hx : x ∈ tsupport u) : fderiv ℝ η x = 0 := by
    have hh : η =ᶠ[𝓝 x] fun _ => (1 : ℝ) :=
      Filter.mem_of_superset (hV.mem_nhds (hKV hx)) (fun y hy => hone y hy)
    rw [hh.fderiv_eq]
    exact fderiv_const_apply (1 : ℝ)
  have hleft : (∫ x, u x * fderiv ℝ η x (EuclideanSpace.single i 1)) = 0 := by
    apply integral_eq_zero_of_ae
    apply Eventually.of_forall
    intro x
    change u x * fderiv ℝ η x (EuclideanSpace.single i 1) = 0
    by_cases hx : x ∈ tsupport u
    · rw [hd x hx, _root_.zero_apply, mul_zero]
    · rw [image_eq_zero_of_notMem_tsupport hx, zero_mul]
  have hright : (∫ x, hu.weakGrad x i * η x) = ∫ x, hu.weakGrad x i := by
    apply integral_congr_ae
    filter_upwards [compact_weakGradient_zero_off hu i] with x hx
    by_cases hxU : x ∈ tsupport u
    · rw [hone x (hKV hxU), mul_one]
    · rw [hx hxU, zero_mul]
  have hw := hu.isWeakGrad i η hη hsη (subset_univ _)
  simp only [Measure.restrict_univ] at hw
  rw [hleft, hright] at hw
  linarith

end CircleDomainRigidity

end

end OAI
