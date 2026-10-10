import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.JointCalculusHorizontalLinear
import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.TailSpaceContDiffPartialDInfty
import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.TimeIntegral
import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.PeriodicSpaceRestrictLApply
import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.PeriodicIntegrableSumNormed

namespace OAI

noncomputable section
namespace VelocityDetection.PeriodicSpace.Jets
open Set Function Filter MeasureTheory
open scoped Topology ContDiff BigOperators BoundedContinuousFunction
open scoped Topology ContDiff ZeroAtInfty BigOperators
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
  periodic_integrable_sum_normed (fun i =>
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
    (periodic_integrable_sum_normed (fun i : Fin 2 => (integrable_momentKernel i).norm)).mul_const ‖J‖
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

end VelocityDetection.PeriodicSpace.Jets
end

noncomputable section
namespace VelocityDetection.PeriodicSpace.Jets
open Set Function Filter MeasureTheory
open scoped Topology ContDiff BigOperators BoundedContinuousFunction
open scoped Topology ContDiff ZeroAtInfty BigOperators

def heatExtension {a : ℕ} (ν s : ℝ) (J : compatibleJets 2 (a + 2)) : compatibleJets 2 a :=
  heat ν s (restrict (by omega : a ≤ a + 2) J) + min s 0 • (ν • laplaceJet J)

@[simp] theorem heatExtension_of_nonneg {a : ℕ} (ν : ℝ) {s : ℝ} (hs : 0 ≤ s)
    (J : compatibleJets 2 (a + 2)) :
    heatExtension ν s J = heat ν s (restrict (by omega : a ≤ a + 2) J) := by
  simp only [heatExtension, min_eq_right hs, zero_smul, add_zero]

theorem heat_of_nonpos {a : ℕ} {ν s : ℝ} (hν : 0 ≤ ν) (hs : s ≤ 0)
    (J : compatibleJets 2 a) : heat ν s J = J := by
  have he : Real.sqrt (2 * ν * s) = 0 := Real.sqrt_eq_zero_of_nonpos (mul_nonpos_of_nonneg_of_nonpos (by positivity) hs)
  simpa only [heat, he, mul_zero, Real.sqrt_zero, neg_zero] using heat_zero ν J

theorem heatExtension_of_nonpos {a : ℕ} {ν s : ℝ} (hν : 0 ≤ ν) (hs : s ≤ 0)
    (J : compatibleJets 2 (a + 2)) :
    heatExtension ν s J = restrict (by omega : a ≤ a + 2) J + s • (ν • laplaceJet J) := by
  rw [heatExtension, heat_of_nonpos hν hs, min_eq_left hs]

theorem continuous_heatExtension {a : ℕ} (ν : ℝ) :
    Continuous (fun p : ℝ × compatibleJets 2 (a + 2) => heatExtension ν p.1 p.2) := by
  have hc : Continuous (fun p : ℝ × compatibleJets 2 (a + 2) =>
      (p.1, restrict (by omega : a ≤ a + 2) p.2)) := by
    have hr := (restrictL (n := 2) (a := a) (b := a + 2) (by omega : a ≤ a + 2)).continuous
    exact continuous_fst.prodMk (hr.comp continuous_snd)
  have hh := (continuous_heat_joint (a := a) ν).comp hc
  have hl : Continuous (fun p : ℝ × compatibleJets 2 (a + 2) => laplaceJet p.2) :=
    (laplaceL 2 a).continuous.comp continuous_snd
  have hm : Continuous (fun p : ℝ × compatibleJets 2 (a + 2) => min p.1 0) :=
    continuous_fst.min continuous_const
  have hg := hh.add (hm.smul (hl.const_smul ν))
  convert hg using 1
  rfl

theorem continuous_heatExtension_derivative {a : ℕ} (ν : ℝ) :
    Continuous (fun p : ℝ × compatibleJets 2 (a + 2) => ν • heat ν p.1 (laplaceJet p.2)) := by
  have hc : Continuous (fun p : ℝ × compatibleJets 2 (a + 2) => (p.1, laplaceJet p.2)) :=
    continuous_fst.prodMk ((laplaceL 2 a).continuous.comp continuous_snd)
  have hh := ((continuous_heat_joint (a := a) ν).comp hc).const_smul ν
  convert hh using 1
  rfl

theorem hasDerivAt_heatExtension {a : ℕ} {ν : ℝ} (hν : 0 < ν)
    (J : compatibleJets 2 (a + 2)) (s : ℝ) :
    HasDerivAt (fun r => heatExtension ν r J) (ν • heat ν s (laplaceJet J)) s := by
  rcases lt_trichotomy s 0 with hs | rfl | hs
  · have he : (fun r => heatExtension ν r J) =ᶠ[𝓝 s]
        (fun r => restrict (by omega : a ≤ a + 2) J + r • (ν • laplaceJet J)) := by
      filter_upwards [Iio_mem_nhds hs] with r hr
      exact heatExtension_of_nonpos hν.le hr.le J
    rw [heat_of_nonpos hν.le hs.le]
    apply HasDerivAt.congr_of_eventuallyEq _ he
    have hh := ((hasDerivAt_id s).smul_const (ν • laplaceJet J)).const_add
      (restrict (by omega : a ≤ a + 2) J)
    simp only [one_smul, id_eq] at hh
    convert hh using 1
  · rw [heat_zero]
    have hl : HasDerivWithinAt (fun r => heatExtension ν r J) (ν • laplaceJet J) (Iic (0 : ℝ)) 0 := by
      have hh : HasDerivAt (fun r : ℝ => restrict (by omega : a ≤ a + 2) J + r • (ν • laplaceJet J))
          (ν • laplaceJet J) 0 := by
        have he := ((hasDerivAt_id (0 : ℝ)).smul_const (ν • laplaceJet J)).const_add
          (restrict (by omega : a ≤ a + 2) J)
        simp only [one_smul, id_eq] at he
        convert he using 1
      exact hh.hasDerivWithinAt.congr_of_mem (fun r hr => heatExtension_of_nonpos hν.le hr J) (by simp)
    have hr : HasDerivWithinAt (fun r => heatExtension ν r J) (ν • laplaceJet J) (Ici (0 : ℝ)) 0 :=
      (hasDerivWithinAt_heat_zero hν J).congr_of_mem (fun r hr => heatExtension_of_nonneg ν hr J) (by simp)
    have hh := hl.union hr
    rwa [Iic_union_Ici, hasDerivWithinAt_univ] at hh
  · have he : (fun r => heatExtension ν r J) =ᶠ[𝓝 s]
        (fun r => heat ν r (restrict (by omega : a ≤ a + 2) J)) := by
      filter_upwards [Ioi_mem_nhds hs] with r hr
      exact heatExtension_of_nonneg ν hr.le J
    exact (hasDerivAt_heat hν hs J).congr_of_eventuallyEq he

def duhamel {a : ℕ} (ν : ℝ) (F : ℝ → compatibleJets 2 (a + 2)) (t : ℝ) :
    compatibleJets 2 a := ∫ r in (0 : ℝ)..t, heat ν (t-r) (restrict (by omega : a ≤ a + 2) (F r))

def extendedDuhamel {a : ℕ} (ν : ℝ) (F : ℝ → compatibleJets 2 (a + 2)) (t : ℝ) :
    compatibleJets 2 a := ∫ r in (0 : ℝ)..t, heatExtension ν (t-r) (F r)

theorem extendedDuhamel_eq {a : ℕ} (ν : ℝ) (F : ℝ → compatibleJets 2 (a + 2))
    {t : ℝ} (ht : 0 ≤ t) : extendedDuhamel ν F t = duhamel ν F t := by
  apply intervalIntegral.integral_congr
  intro r hr
  rw [uIcc_of_le ht] at hr
  exact heatExtension_of_nonneg ν (sub_nonneg.mpr hr.2) (F r)

theorem hasDerivAt_extendedDuhamel {a : ℕ} {ν : ℝ} (hν : 0 < ν)
    {F : ℝ → compatibleJets 2 (a + 2)} (hF : Continuous F) (t : ℝ) :
    HasDerivAt (extendedDuhamel ν F)
      ((∫ r in (0 : ℝ)..t, ν • heat ν (t-r) (laplaceJet (F r))) +
        restrict (by omega : a ≤ a + 2) (F t)) t := by
  have hc : Continuous (fun p : ℝ × ℝ => (p.1-p.2, F p.2)) :=
    (continuous_fst.sub continuous_snd).prodMk (hF.comp continuous_snd)
  have hK := (continuous_heatExtension (a := a) ν).comp hc
  have hL := (continuous_heatExtension_derivative (a := a) ν).comp hc
  have hd (s r : ℝ) : HasDerivAt (fun t => heatExtension ν (t-r) (F r))
      (ν • heat ν (s-r) (laplaceJet (F r))) s := by
    have hh := (hasDerivAt_heatExtension hν (F r) (s-r)).scomp s ((hasDerivAt_id s).sub_const r)
    simpa only [one_smul, comp_def, id_eq] using hh
  have hh := TimeIntegral.hasDerivAt_diagonal
    (K := fun s r => heatExtension ν (s-r) (F r))
    (L := fun s r => ν • heat ν (s-r) (laplaceJet (F r))) hK hL hd 0 t
  simp only [sub_self, heatExtension_of_nonneg ν le_rfl, heat_zero] at hh
  convert hh using 1
  rfl

theorem hasDerivWithinAt_duhamel {a : ℕ} {ν : ℝ} (hν : 0 < ν)
    {F : ℝ → compatibleJets 2 (a + 2)} (hF : Continuous F) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (duhamel ν F)
      ((∫ r in (0 : ℝ)..t, ν • heat ν (t-r) (laplaceJet (F r))) +
        restrict (by omega : a ≤ a + 2) (F t)) (Ici (0 : ℝ)) t := by
  exact (hasDerivAt_extendedDuhamel hν hF t).hasDerivWithinAt.congr_of_mem
    (fun r hr => (extendedDuhamel_eq ν F hr).symm) ht

end VelocityDetection.PeriodicSpace.Jets
end

noncomputable section
namespace VelocityDetection.PeriodicSpace.Jets
open Set Function Filter MeasureTheory
open scoped Topology ContDiff BigOperators BoundedContinuousFunction
open scoped Topology ContDiff ZeroAtInfty BigOperators

@[simp] theorem differentiateL_apply {n a : ℕ} (i : Fin n)
    (J : compatibleJets n (a+1)) : differentiateL i J = differentiate i J := rfl

@[simp] theorem differentiate_translate {n a : ℕ} (i : Fin n) (Y : Coord n)
    (J : compatibleJets n (a+1)) :
    differentiate i (translate Y J) = translate Y (differentiate i J) := by
  apply Subtype.ext
  rfl

@[simp] theorem differentiate_average {n a : ℕ} (i : Fin n) {k : Coord n → ℝ}
    (hk : Integrable k) (s : ℝ) (J : compatibleJets n (a+1)) :
    differentiate i (average k s J) = average k s (differentiate i J) := by
  have hh := (differentiateL (n := n) (a := a) i).integral_comp_comm
    (integrable_average (a := a+1) hk s J)
  simpa only [map_smul, differentiateL_apply, differentiate_translate, average] using hh.symm

@[simp] theorem differentiate_heat {a : ℕ} (i : Fin 2) (ν t : ℝ)
    (J : compatibleJets 2 (a+1)) :
    differentiate i (heat ν t J) = heat ν t (differentiate i J) :=
  differentiate_average i (HeatKernels.integrable_normal 2) _ J

@[simp] theorem laplace_heat {a : ℕ} (ν t : ℝ) (J : compatibleJets 2 (a+2)) :
    laplaceJet (heat ν t J) = heat ν t (laplaceJet J) := by
  simp only [laplaceJet, differentiate_heat, map_sum]

@[simp] theorem restrict_laplace {n a b : ℕ} (hab : a ≤ b)
    (J : compatibleJets n (b+2)) :
    restrict hab (laplaceJet J) = laplaceJet (restrict (Nat.add_le_add_right hab 2) J) := by
  change restrictL hab (∑ i : Fin n, differentiate i (differentiate i J)) = _
  rw [map_sum]
  simp only [restrictL_apply, restrict_differentiate, laplaceJet]

theorem laplace_integral_heat {a : ℕ} {F : ℝ → compatibleJets 2 (a+2)}
    (hF : Continuous F) (ν t : ℝ) :
    laplaceJet (∫ r in (0:ℝ)..t, heat ν (t-r) (F r)) =
      ∫ r in (0:ℝ)..t, heat ν (t-r) (laplaceJet (F r)) := by
  have hc : Continuous (fun r : ℝ => (t-r,F r)) :=
    (continuous_const.sub continuous_id).prodMk hF
  have hh := (continuous_heat_joint (a := a+2) ν).comp hc
  have he := (laplaceL 2 a).intervalIntegral_comp_comm (μ := volume) (hh.intervalIntegrable 0 t)
  simpa only [comp_def, laplaceL_apply, laplace_heat] using he.symm

end VelocityDetection.PeriodicSpace.Jets
end

noncomputable section
namespace VelocityDetection.PeriodicSpace
open Set Function Filter MeasureTheory
open scoped Topology ContDiff BigOperators

@[simp] theorem cover_sub {n : ℕ} (X Y : Coord n) : cover (X-Y) = cover X - cover Y := rfl

theorem openQuotient_cover (n : ℕ) : IsOpenQuotientMap (@cover n) := by
  exact IsOpenQuotientMap.piMap (fun _ => QuotientAddGroup.isOpenQuotientMap_mk)

def ofPeriodic {n : ℕ} (f : Coord n → ℝ) (hf : Continuous f)
    (hp : FactorsThrough f cover) : compatible n :=
  (openQuotient_cover n).isQuotientMap.lift (f := ⟨cover, continuous_cover n⟩) ⟨f,hf⟩ hp

@[simp] theorem realLift_ofPeriodic {n : ℕ} (f : Coord n → ℝ) (hf : Continuous f)
    (hp : FactorsThrough f cover) (X : Coord n) :
    realLift (ofPeriodic f hf hp) X = f X := by
  exact congrArg (fun q : C(Coord n,ℝ) => q X)
    ((openQuotient_cover n).isQuotientMap.lift_comp (f := ⟨cover, continuous_cover n⟩) ⟨f,hf⟩ hp)

theorem periodic_partialD {n : ℕ} {f : Coord n → ℝ}
    (hf : Differentiable ℝ f) (hp : FactorsThrough f cover) (i : Fin n) :
    FactorsThrough (SpatialCalculus.partialD i f) cover := by
  intro X Y hXY
  have hzero : cover (Y-X) = 0 := by rw [cover_sub, hXY, sub_self]
  have he : (fun Z => f (Z + (Y-X))) = f := by
    funext Z
    apply hp
    rw [cover_add, hzero, add_zero]
  have hd := fderiv_comp_add_right (𝕜 := ℝ) (f := f) (x := X) (Y-X)
  rw [he] at hd
  have heXY : X + (Y-X) = Y := by abel
  rw [heXY] at hd
  rw [SpatialCalculus.partialD_eq_fderiv i hf X,
    SpatialCalculus.partialD_eq_fderiv i hf Y, hd]

theorem continuous_ofPeriodic_curve {n : ℕ} {f : ScalarField n}
    (hf : Continuous (uncurry f)) (hp : ∀ t, FactorsThrough (f t) cover) :
    Continuous (fun t => ofPeriodic (f t) (hf.comp (continuous_const.prodMk continuous_id)) (hp t)) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  apply ((IsOpenQuotientMap.id.prodMap (openQuotient_cover n)).continuous_comp_iff).mp
  change Continuous (fun p : ℝ × Coord n =>
    ofPeriodic (f p.1) (hf.comp (continuous_const.prodMk continuous_id)) (hp p.1) (cover p.2))
  convert hf using 1
  funext p
  exact realLift_ofPeriodic (f p.1) (hf.comp (continuous_const.prodMk continuous_id)) (hp p.1) p.2

end VelocityDetection.PeriodicSpace
end

noncomputable section
namespace VelocityDetection.PeriodicSpace.Jets
open Set Function Filter MeasureTheory
open scoped Topology ContDiff BigOperators
open SpatialCalculus

theorem wordPartial_tailWordPartial {n k : ℕ} (w : Fin k → Fin n) (f : Coord n → ℝ) :
    wordPartial w f = TailSpace.Jets.wordPartial w f := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change partialD (w 0) (wordPartial (Fin.tail w) f) =
      partialD (w 0) (TailSpace.Jets.wordPartial (Fin.tail w) f)
    rw [ih]

theorem contDiff_wordPartial {n k : ℕ} {f : Coord n → ℝ}
    (hf : ContDiff ℝ ∞ f) (w : Fin k → Fin n) : ContDiff ℝ ∞ (wordPartial w f) := by
  rw [wordPartial_tailWordPartial]
  exact TailSpace.Jets.contDiff_wordPartial hf w

theorem contDiff_uncurry_wordPartial {n k : ℕ} {f : ScalarField n}
    (hf : ContDiff ℝ ∞ (uncurry f)) (w : Fin k → Fin n) :
    ContDiff ℝ ∞ (fun p : ℝ × Coord n => wordPartial w (f p.1) p.2) := by
  simp only [wordPartial_tailWordPartial]
  exact TailSpace.Jets.contDiff_uncurry_wordPartial hf w

theorem periodic_wordPartial {n k : ℕ} {f : Coord n → ℝ}
    (hf : ContDiff ℝ ∞ f) (hp : FactorsThrough f cover) (w : Fin k → Fin n) :
    FactorsThrough (wordPartial w f) cover := by
  induction k with
  | zero => exact hp
  | succ k ih =>
    exact periodic_partialD
      ((contDiff_wordPartial hf (Fin.tail w)).differentiable (by simp)) (ih (Fin.tail w)) (w 0)

def ofSmoothPeriodic {n : ℕ} (a : ℕ) (f : Coord n → ℝ)
    (hf : ContDiff ℝ ∞ f) (hp : FactorsThrough f cover) : compatibleJets n a :=
  ⟨fun ⟨_,w⟩ => ofPeriodic (wordPartial w f)
      (contDiff_wordPartial hf w).continuous (periodic_wordPartial hf hp w), by
    intro k w X
    have hd := (contDiff_wordPartial hf w).differentiable (by simp)
    simp only [gradient, realLift_ofPeriodic]
    have he : (∑ i : Fin n, wordPartial (Fin.cons i w) f X •
        (ContinuousLinearMap.proj i : Coord n →L[ℝ] ℝ)) = fderiv ℝ (wordPartial w f) X := by
      ext v
      simp only [sum_apply, smul_apply, smul_eq_mul, ContinuousLinearMap.proj_apply,
        wordPartial_cons, fderiv_apply_eq_sum hd]
      exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)
    rw [he]
    exact (hd X).hasFDerivAt⟩

@[simp] theorem value_ofSmoothPeriodic {n : ℕ} (a : ℕ) (f : Coord n → ℝ)
    (hf : ContDiff ℝ ∞ f) (hp : FactorsThrough f cover) :
    value (ofSmoothPeriodic a f hf hp) = f := by
  funext X
  exact realLift_ofPeriodic f hf.continuous hp X

end VelocityDetection.PeriodicSpace.Jets
end

end OAI
