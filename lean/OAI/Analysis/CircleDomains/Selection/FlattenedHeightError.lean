import OAI.Analysis.CircleDomains.Selection.LocalHeightFlattening

namespace OAI

/-! Quantitative energy of the flattened height relative to the physical
vertical coordinate. The bound tends to zero with the actual height
error and the chosen flattening energy. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem norm_add_sq_le_twice {E : Type*} [SeminormedAddCommGroup E] (a b : E) :
    ‖a+b‖^2 ≤ 2*‖a‖^2+2*‖b‖^2 := by
  have h := (sq_le_sq₀ (norm_nonneg (a+b))
    (add_nonneg (norm_nonneg a) (norm_nonneg b))).mpr (norm_add_le a b)
  nlinarith [sq_nonneg (‖a‖-‖b‖)]

 theorem heightLimitGradient_vertical_error (g₀ g₁ : Lp ℝ 2 (volume : Measure EuclideanPlane))
    (x : EuclideanPlane) :
    ‖heightLimitGradient g₀ g₁ x-EuclideanSpace.single (1 : Fin 2) 1‖^2 =
      g₀ x^2+g₁ x^2 := by
  simp [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two, heightLimitGradient]

 theorem ControlledHeight.flattened_energy_error {R d : ℝ} (H : ControlledHeight R d)
    (A : ℝ) {v : EuclideanPlane → ℝ}
    (W : DeGiorgi.MemW1pWitness 2 v (ball 0 A)) {ε : ℝ} (hε : 0 < ε)
    (he : (∫⁻ x in ball 0 A,
      ENNReal.ofReal (‖W.weakGrad x-heightLimitGradient H.error₀ H.error₁ x‖^2)) < ENNReal.ofReal ε) :
    (∫ x in ball 0 A, ‖W.weakGrad x-EuclideanSpace.single (1 : Fin 2) 1‖^2) <
      2*ε+4*Real.pi*d := by
  let Y : EuclideanPlane := EuclideanSpace.single (1 : Fin 2) 1
  let V := heightLimitGradient H.error₀ H.error₁
  let W₀ := heightLimitWitness H.error₀ H.error₁
    (H.height.continuous.comp complexPlaneCoordinates.continuous) H.weak_gradient A
  let : IsFiniteMeasure (volume.restrict (ball (0 : EuclideanPlane) A)) :=
    isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  have hF := (W.weakGrad_memLp.sub W₀.weakGrad_memLp).norm.integrable_sq
  change Integrable (fun x => ‖W.weakGrad x-V x‖^2) (volume.restrict (ball 0 A)) at hF
  have hB := (W₀.weakGrad_memLp.sub (memLp_const Y)).norm.integrable_sq
  change Integrable (fun x => ‖V x-Y‖^2) (volume.restrict (ball 0 A)) at hB
  have hW := (W.weakGrad_memLp.sub (memLp_const Y)).norm.integrable_sq
  change Integrable (fun x => ‖W.weakGrad x-Y‖^2) (volume.restrict (ball 0 A)) at hW
  have he' : (∫ x in ball 0 A, ‖W.weakGrad x-V x‖^2) < ε := by
    apply (ENNReal.ofReal_lt_ofReal_iff hε).mp
    rw [ofReal_integral_eq_lintegral_ofReal hF (Eventually.of_forall (fun _ => sq_nonneg _))]
    exact he
  have hlim : (∫ x in ball 0 A, ‖V x-Y‖^2) ≤ 2*Real.pi*d := by
    calc
      _ = ∫ x in ball 0 A, H.error₀ x^2+H.error₁ x^2 := by
        apply integral_congr_ae
        exact Eventually.of_forall (heightLimitGradient_vertical_error _ _)
      _ ≤ ∫ x, H.error₀ x^2+H.error₁ x^2 :=
        setIntegral_le_integral ((Lp.memLp H.error₀).integrable_sq.add (Lp.memLp H.error₁).integrable_sq)
          (Eventually.of_forall (fun _ => add_nonneg (sq_nonneg _) (sq_nonneg _)))
      _ ≤ _ := H.error_bound
  have hbound : (∫ x in ball 0 A, ‖W.weakGrad x-Y‖^2) ≤
      2*(∫ x in ball 0 A, ‖W.weakGrad x-V x‖^2)+
      2*(∫ x in ball 0 A, ‖V x-Y‖^2) := by
    rw [← integral_const_mul, ← integral_const_mul, ← integral_add (hF.const_mul 2) (hB.const_mul 2)]
    apply integral_mono hW ((hF.const_mul 2).add (hB.const_mul 2))
    intro x
    change ‖W.weakGrad x-Y‖^2 ≤ 2*‖W.weakGrad x-V x‖^2+2*‖V x-Y‖^2
    simpa only [sub_add_sub_cancel] using
      norm_add_sq_le_twice (W.weakGrad x-V x) (V x-Y)
  change (∫ x in ball 0 A, ‖W.weakGrad x-Y‖^2) < _
  nlinarith

end CircleDomainRigidity

end

end OAI
