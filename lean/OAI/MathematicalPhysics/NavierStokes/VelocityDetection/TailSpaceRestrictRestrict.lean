import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.TailSpaceIntegrableKernelValue
import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.IntegrableSumNormed

namespace OAI

noncomputable section
namespace VelocityDetection.TailSpace.Jets
open scoped BigOperators Topology ContDiff
open Set Function Filter
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ContDiff
open scoped Topology ContDiff BigOperators
open scoped Topology ContDiff ZeroAtInfty
open scoped Topology ContDiff ZeroAtInfty BigOperators
open scoped Topology
open HeatKernels SpatialCalculus

@[simp] theorem restrict_restrict {n a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c)
    (J : compatibleJets n c) : restrict hab (restrict hbc J) = restrict (hab.trans hbc) J := by
  apply value_injective
  rfl

@[simp] theorem restrict_differentiate {n a b : ℕ} (hab : a ≤ b) (i : Fin n)
    (J : compatibleJets n (b + 1)) :
    restrict hab (differentiate i J) =
      differentiate i (restrict (Nat.add_le_add_right hab 1) J) := by
  apply value_injective
  simp only [restrict_value, value_differentiate]

theorem heatGradient_restrict {a : ℕ} {ν t : ℝ} (hν : 0 < ν) (ht : 0 < t)
    (i : Fin 2) (J : compatibleJets 2 (a + 1)) :
    heatGradient ν t i (restrict (Nat.le_succ a) J) = heat ν t (differentiate i J) := by
  have hr : Real.sqrt (2 * ν * t) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
  change -(Real.sqrt (2 * ν * t))⁻¹ • average (momentKernel i)
    (-Real.sqrt (2 * ν * t)) (restrict (Nat.le_succ a) J) = _
  rw [moment_average_eq, smul_smul]
  simp only [neg_mul_neg, inv_mul_cancel₀ hr, one_smul]
  rfl

private theorem normal_translate_directional {a : ℕ} (J : compatibleJets 2 (a + 1))
    (s : ℝ) (Y : Coord 2) :
    normal 2 Y • translate (s • Y) (directional Y J) =
      ∑ i : Fin 2, momentKernel i Y • translate (s • Y) (differentiate i J) := by
  change normal 2 Y • translateLI (s • Y) (∑ i : Fin 2, Y i • differentiate i J) = _
  rw [map_sum, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul, smul_smul]
  change (normal 2 Y * Y i) • translate (s • Y) (differentiate i J) = _
  rw [mul_comm]
  rfl

private def normalAverageDerivative {a : ℕ} (J : compatibleJets 2 (a + 1))
    (r : ℝ) (Y : Coord 2) : compatibleJets 2 a :=
  ∑ i : Fin 2, momentKernel i Y • translate (r • Y) (differentiate i J)

private theorem normalAverageDerivative_integrable {a : ℕ}
    (J : compatibleJets 2 (a + 1)) (r : ℝ) : Integrable (normalAverageDerivative J r) :=
  integrable_sum_normed (fun i =>
    integrable_average (integrable_momentKernel i) r (differentiate i J))

private theorem norm_normalAverageDerivative {a : ℕ} (J : compatibleJets 2 (a + 1))
    (Y : Coord 2) (r : ℝ) :
    ‖normalAverageDerivative J r Y‖ ≤ (∑ i : Fin 2, ‖momentKernel i Y‖) * ‖J‖ := by
  calc
    ‖normalAverageDerivative J r Y‖ ≤
        ∑ i : Fin 2, ‖momentKernel i Y • translate (r • Y) (differentiate i J)‖ := norm_sum_le _ _
    _ ≤ ∑ i : Fin 2, ‖momentKernel i Y‖ * ‖J‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul, norm_translate]
      exact mul_le_mul_of_nonneg_left (norm_differentiate_le i J) (norm_nonneg _)
    _ = _ := (Finset.sum_mul ..).symm

private theorem hasDerivAt_normal_integrand {a : ℕ} (J : compatibleJets 2 (a + 1))
    (Y : Coord 2) (r : ℝ) :
    HasDerivAt (fun s => normal 2 Y • translate (s • Y) (restrict (Nat.le_succ a) J))
      (normalAverageDerivative J r Y) r := by
  have hd := (hasDerivAt_translate J Y r).const_smul (normal 2 Y)
  simp only [normal_translate_directional] at hd
  convert hd using 1
  rfl

theorem hasDerivAt_average_normal {a : ℕ} (J : compatibleJets 2 (a + 1)) (s : ℝ) :
    HasDerivAt (fun r => average (normal 2) r (restrict (Nat.le_succ a) J))
      (∑ i : Fin 2, average (momentKernel i) s (differentiate i J)) s := by
  have hB : Integrable (fun Y => (∑ i : Fin 2, ‖momentKernel i Y‖) * ‖J‖) :=
    (integrable_sum_normed (fun i : Fin 2 => (integrable_momentKernel i).norm)).mul_const ‖J‖
  have hh := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun r Y => normal 2 Y • translate (r • Y) (restrict (Nat.le_succ a) J))
    (F' := normalAverageDerivative J) (bound := fun Y => (∑ i : Fin 2, ‖momentKernel i Y‖) * ‖J‖)
    (x₀ := s) (s := univ) (univ_mem : Set.univ ∈ 𝓝 s)
    (Eventually.of_forall (fun r => (integrable_average (a := a) (integrable_normal 2) r (restrict (Nat.le_succ a) J)).aestronglyMeasurable))
    (integrable_average (a := a) (integrable_normal 2) s (restrict (Nat.le_succ a) J)) (normalAverageDerivative_integrable J s).aestronglyMeasurable
    (Eventually.of_forall (fun Y r _ => norm_normalAverageDerivative J Y r)) hB
    (Eventually.of_forall (fun Y r _ => hasDerivAt_normal_integrand J Y r))
  have he : (∫ Y, normalAverageDerivative J s Y) =
      ∑ i : Fin 2, average (momentKernel i) s (differentiate i J) := by
    change (∫ Y, ∑ i : Fin 2, momentKernel i Y • translate (s • Y) (differentiate i J)) = _
    exact integral_finsetSum Finset.univ (fun i _ =>
      integrable_average (a := a) (integrable_momentKernel i) s (differentiate i J))
  rw [he] at hh
  exact hh.2

def laplaceJet {n a : ℕ} (J : compatibleJets n (a + 2)) : compatibleJets n a :=
  ∑ i : Fin n, differentiate i (differentiate i J)

def laplaceL (n a : ℕ) : compatibleJets n (a + 2) →L[ℝ] compatibleJets n a :=
  ∑ i : Fin n, (differentiateL i).comp (differentiateL i)

@[simp] theorem laplaceL_apply {n a : ℕ} (J : compatibleJets n (a + 2)) :
    laplaceL n a J = laplaceJet J := by simp [laplaceL, laplaceJet, differentiateL]

theorem value_laplaceJet {n a : ℕ} (J : compatibleJets n (a + 2)) (X : Coord n) :
    value (laplaceJet J) X = ∑ i : Fin n, partialD i (partialD i (value J)) X := by
  change evaluate X (∑ i : Fin n, differentiate i (differentiate i J)) = _
  rw [map_sum]
  simp only [evaluate_apply, value_differentiate]

theorem hasDerivAt_average_normal_laplace {a : ℕ}
    (J : compatibleJets 2 (a + 2)) (s : ℝ) :
    HasDerivAt (fun r => average (normal 2) r (restrict (by omega : a ≤ a + 2) J))
      (s • average (normal 2) s (laplaceJet J)) s := by
  have hh := hasDerivAt_average_normal (restrict (Nat.le_succ (a + 1)) J) s
  simp only [restrict_restrict] at hh
  have hi (i : Fin 2) : average (momentKernel i) s
      (differentiate i (restrict (Nat.le_succ (a + 1)) J)) =
      s • average (normal 2) s (differentiate i (differentiate i J)) := by
    rw [← restrict_differentiate (Nat.le_succ a) i J, moment_average_eq]
  simp only [hi] at hh
  have he : (∑ i : Fin 2, s • average (normal 2) s (differentiate i (differentiate i J))) =
      s • average (normal 2) s (laplaceJet J) := by
    change (∑ i : Fin 2, s • averageL (integrable_normal 2) s
      (differentiate i (differentiate i J))) = s • averageL (integrable_normal 2) s _
    rw [laplaceJet, map_sum, Finset.smul_sum]
  simpa only [he] using hh

theorem hasDerivAt_heat {a : ℕ} {ν t : ℝ} (hν : 0 < ν) (ht : 0 < t)
    (J : compatibleJets 2 (a + 2)) :
    HasDerivAt (fun r => heat ν r (restrict (by omega : a ≤ a + 2) J))
      (ν • heat ν t (laplaceJet J)) t := by
  have hpos : 0 < 2 * ν * t := by positivity
  have hr : Real.sqrt (2 * ν * t) ≠ 0 := (Real.sqrt_pos.mpr hpos).ne'
  have hd : HasDerivAt (fun r : ℝ => -Real.sqrt (2 * ν * r))
      (-(ν / Real.sqrt (2 * ν * t))) t := by
    have hs := ((Real.hasDerivAt_sqrt hpos.ne').comp t
      ((hasDerivAt_id t).const_mul (2 * ν))).neg
    have he : 1 / (2 * Real.sqrt (2 * ν * t)) * (2 * ν * 1) =
        ν / Real.sqrt (2 * ν * t) := by ring
    simp only [he] at hs
    convert hs using 1
    rfl
  have hh := (hasDerivAt_average_normal_laplace J (-Real.sqrt (2 * ν * t))).scomp t hd
  have he : -(ν / Real.sqrt (2 * ν * t)) * (-Real.sqrt (2 * ν * t)) = ν := by
    field_simp
  simp only [comp_def, smul_smul, he] at hh
  convert hh using 1 <;> rfl

theorem hasDerivWithinAt_heat_zero {a : ℕ} {ν : ℝ} (hν : 0 < ν)
    (J : compatibleJets 2 (a + 2)) :
    HasDerivWithinAt (fun r => heat ν r (restrict (by omega : a ≤ a + 2) J))
      (ν • laplaceJet J) (Ici (0 : ℝ)) 0 := by
  apply hasDerivWithinAt_Ici_of_tendsto_deriv (E := compatibleJets 2 a)
    (f := fun r => heat ν r (restrict (by omega : a ≤ a + 2) J)) (s := Ioi (0 : ℝ))
  · intro t ht
    exact (hasDerivAt_heat hν ht J).differentiableAt.differentiableWithinAt
  · have hc : Continuous (fun r : ℝ => heat ν r (restrict (by omega : a ≤ a + 2) J)) :=
      continuous_heat (a := a) ν _
    exact hc.continuousWithinAt
  · exact self_mem_nhdsWithin
  · have hc : Continuous (fun r : ℝ => ν • heat ν r (laplaceJet J)) :=
      (continuous_heat (a := a) ν _).const_smul ν
    have ht := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    have he : (fun r : ℝ => deriv (fun s => heat ν s (restrict (by omega : a ≤ a + 2) J)) r) =ᶠ[𝓝[>] (0 : ℝ)]
        (fun r => ν • heat ν r (laplaceJet J)) := by
      filter_upwards [self_mem_nhdsWithin] with r hr
      exact (hasDerivAt_heat hν hr J).deriv
    simpa only [heat_zero] using ht.congr' he.symm

end VelocityDetection.TailSpace.Jets
end

end OAI
