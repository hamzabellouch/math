import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.PeriodicMildPeriodicData
import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.PeriodicMildTimeDerivative
import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.PeriodicSpaceContinuousProduct

namespace OAI

noncomputable section
namespace VelocityDetection.PeriodicMild
open Set Function Filter MeasureTheory
open scoped Topology ContDiff ZeroAtInfty BigOperators
open PeriodicSpace.Jets WeakVolterra
variable {ν : ℝ} (hν : 0 < ν) (W : Fin 2 → PeriodicData) (g : PeriodicData)

@[simp] theorem globalJets_clamp (a : ℕ) (t : ℝ) :
    globalJets hν W g a (max t 0) = globalJets hν W g a t := by
  exact globalJets_eq_finite hν W g
    (show 0 ≤ max t 0 + 1 by positivity)
    (show max t 0 ∈ Icc 0 (max t 0 + 1) from ⟨le_max_right _ _, by linarith⟩) a

theorem continuous_globalJets (a : ℕ) : Continuous (globalJets hν W g a) := by
  have hh := (continuousOn_globalJets hν W g a).comp_continuous
    (continuous_id.max continuous_const) (fun t : ℝ => le_max_right t 0)
  simp only [Function.comp_def, globalJets_clamp, id_eq] at hh
  convert hh using 1

def pdeSource (a : ℕ) (t : ℝ) : E a :=
  g.jets a t - ∑ i : Fin 2, differentiate i
    (product ((W i).jets (a+1) t) (globalJets hν W g (a+1) t))

theorem continuous_pdeSource (a : ℕ) : Continuous (pdeSource hν W g a) := by
  have hm (i : Fin 2) : Continuous (fun t : ℝ =>
      product ((W i).jets (a+1) t) (globalJets hν W g (a+1) t)) :=
    continuous_product.comp
      (((W i).continuous_jets (a+1)).prodMk (continuous_globalJets hν W g (a+1)))
  have hd (i : Fin 2) : Continuous (fun t : ℝ =>
      differentiate i (product ((W i).jets (a+1) t) (globalJets hν W g (a+1) t))) :=
    (differentiateL (n := 2) (a := a) i).continuous.comp (hm i)
  exact (g.continuous_jets a).sub (continuous_finsetSum _ (fun i _ => hd i))

@[simp] theorem restrict_pdeSource {a b : ℕ} (hab : a ≤ b) (t : ℝ) :
    restrict hab (pdeSource hν W g b t) = pdeSource hν W g a t := by
  change restrictL hab (g.jets b t - ∑ i : Fin 2,
    differentiate i (product ((W i).jets (b+1) t) (globalJets hν W g (b+1) t))) = _
  rw [map_sub, map_sum]
  simp only [restrictL_apply, PeriodicData.restrict_jets, restrict_differentiate,
    restrict_product, restrict_globalJets, pdeSource]

private theorem drift_global {T : ℝ} (hT : 0 ≤ T) {r s : ℝ}
    (hr : r ∈ Icc 0 T) (hs : 0 < s) (a : ℕ) :
    driftKernel hT (ν := ν) (fun i => (W i).curve T a) s r
      (extend hT (finiteSolution hν W g hT a) r) =
      -∑ i : Fin 2, heat ν s (differentiate i
        (product ((W i).jets (a+1) r) (globalJets hν W g (a+1) r))) := by
  simp only [driftKernel_apply, extend_of_mem hT _ hr, PeriodicData.curve_apply]
  rw [← globalJets_eq_finite hν W g hT hr a]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  have hh := heatGradient_restrict hν hs i
    (product ((W i).jets (a+1) r) (globalJets hν W g (a+1) r))
  simpa only [restrict_product, PeriodicData.restrict_jets, restrict_globalJets] using hh

theorem globalJets_mild (a : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    globalJets hν W g a t =
      (∫ s in Ioc (0:ℝ) t, heat ν s (extend ht (g.curve t a) (t-s))) +
        ∫ s in Ioc (0:ℝ) t,
          driftKernel ht (ν := ν) (fun i => (W i).curve t a) s (t-s)
            (extend ht (finiteSolution hν W g ht a) (t-s)) := by
  have he := evolution_mild ht hν (fun i => (W i).curve t a) (g.curve t a)
    (show Icc (0:ℝ) t from ⟨t,ht,le_rfl⟩)
  change finiteSolution hν W g ht a ⟨t,ht,le_rfl⟩ = _ at he
  rw [← globalJets_eq_finite hν W g ht ⟨ht,le_rfl⟩ a] at he
  rw [sourceCurve_apply] at he
  change globalJets hν W g a t =
    (∫ s in Ioc (0:ℝ) t, heat ν s (extend ht (g.curve t a) (t-s))) +
      ∫ s in Ioc (0:ℝ) t,
        driftKernel ht (ν := ν) (fun i => (W i).curve t a) s (t-s)
          (extend ht (finiteSolution hν W g ht a) (t-s)) at he
  exact he

private theorem heat_sub_sum (a : ℕ) (ν s : ℝ) (v : E a) (z : Fin 2 → E a) :
    heat ν s (v - ∑ i, z i) = heat ν s v + -(∑ i, heat ν s (z i)) := by
  have h := (heat (a := a) ν s).map_sub v (∑ i, z i)
  have hh := map_sum (heat (a := a) ν s) z Finset.univ
  rw [hh] at h
  exact h.trans (sub_eq_add_neg _ _)

private theorem combined_integrands (a : ℕ) {t s : ℝ} (ht : 0 ≤ t)
    (hs : s ∈ Ioc (0:ℝ) t) :
    heat ν s (extend ht (g.curve t a) (t-s)) +
      driftKernel ht (ν := ν) (fun i => (W i).curve t a) s (t-s)
        (extend ht (finiteSolution hν W g ht a) (t-s)) =
      heat ν s (pdeSource hν W g a (t-s)) := by
  have hr : t-s ∈ Icc 0 t := ⟨by linarith [hs.2], by linarith [hs.1]⟩
  rw [extend_of_mem ht (g.curve t a) hr, PeriodicData.curve_apply,
    drift_global hν W g ht hr hs.1 a]
  exact (heat_sub_sum a ν s (g.jets a (t-s)) (fun i =>
    differentiate i (product ((W i).jets (a+1) (t-s))
      (globalJets hν W g (a+1) (t-s))))).symm

theorem globalJets_integral (a : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    globalJets hν W g a t =
      ∫ s in Ioc (0:ℝ) t, heat ν s (pdeSource hν W g a (t-s)) := by
  have he := globalJets_mild hν W g a ht
  have hiS := integrableOn_source ht (g.curve t a) ν t
  have hiD := integrableOn_drift ht hν (fun i => (W i).curve t a)
    (finiteSolution hν W g ht a) (show t ∈ Icc 0 t from ⟨ht,le_rfl⟩)
  rw [← integral_add hiS hiD] at he
  refine he.trans ?_
  apply setIntegral_congr_fun measurableSet_Ioc
  intro s hs
  exact combined_integrands hν W g a ht hs

end VelocityDetection.PeriodicMild
end

noncomputable section
namespace VelocityDetection.PeriodicMild
open Set Function Filter MeasureTheory
open scoped Topology ContDiff ZeroAtInfty BigOperators
open PeriodicSpace.Jets WeakVolterra
variable {ν : ℝ} (hν : 0 < ν) (W : Fin 2 → PeriodicData) (g : PeriodicData)

theorem globalJets_integral_time (a : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    globalJets hν W g a t =
      ∫ r in (0:ℝ)..t, heat ν (t-r) (pdeSource hν W g a r) := by
  rw [globalJets_integral hν W g a ht]
  rw [← intervalIntegral.integral_of_le ht]
  have hh := intervalIntegral.integral_comp_sub_left
    (f := fun r : ℝ => heat ν (t-r) (pdeSource hν W g a r)) (a := 0) (b := t) t
  simpa only [sub_sub_cancel, sub_self, sub_zero] using hh

@[simp] theorem globalJets_zero (a : ℕ) : globalJets hν W g a 0 = 0 := by
  rw [globalJets_integral_time hν W g a (le_refl 0), intervalIntegral.integral_same]

@[simp] theorem globalJets_nonpos (a : ℕ) {t : ℝ} (ht : t ≤ 0) :
    globalJets hν W g a t = 0 := by
  rw [← globalJets_clamp hν W g a t, max_eq_right ht, globalJets_zero]

theorem globalJets_duhamel (a : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    globalJets hν W g a t = duhamel ν (pdeSource hν W g (a+2)) t := by
  rw [globalJets_integral_time hν W g a ht]
  simp only [duhamel, restrict_pdeSource]

def timeGenerator (a : ℕ) (t : ℝ) : E a :=
  ν • laplaceJet (globalJets hν W g (a+2) t) + pdeSource hν W g a t

theorem continuous_timeGenerator (a : ℕ) : Continuous (timeGenerator hν W g a) := by
  have hc : Continuous (fun t : ℝ => laplaceJet (globalJets hν W g (a+2) t)) :=
    (laplaceL 2 a).continuous.comp (continuous_globalJets hν W g (a+2))
  exact (hc.const_smul ν).add (continuous_pdeSource hν W g a)

theorem hasDerivWithinAt_globalJets (a : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (globalJets hν W g a) (timeGenerator hν W g a t) (Ici (0:ℝ)) t := by
  have hh := hasDerivWithinAt_duhamel hν (continuous_pdeSource hν W g (a+2)) ht
  have he : ((∫ r in (0:ℝ)..t, ν • heat ν (t-r) (laplaceJet (pdeSource hν W g (a+2) r))) +
      restrict (by omega : a ≤ a+2) (pdeSource hν W g (a+2) t)) =
      timeGenerator hν W g a t := by
    rw [restrict_pdeSource, intervalIntegral.integral_smul,
      ← laplace_integral_heat (continuous_pdeSource hν W g (a+2)) ν t,
      ← globalJets_integral_time hν W g (a+2) ht]
    rfl
  rw [he] at hh
  exact hh.congr_of_mem (fun r hr => globalJets_duhamel hν W g a hr) ht

theorem c1_globalJets (a : ℕ) :
    ContDiffOn ℝ 1 (globalJets hν W g a) (Ici (0:ℝ)) := by
  apply (contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn (n := 0) (uniqueDiffOn_Ici (0:ℝ))).mpr
  refine ⟨by simp, fun t => (1 : ℝ →L[ℝ] ℝ).smulRight (timeGenerator hν W g a t), ?_, ?_⟩
  · apply contDiffOn_zero.mpr
    exact ((ContinuousLinearMap.smulRightL ℝ ℝ (E a) 1).continuous.comp
      (continuous_timeGenerator hν W g a)).continuousOn
  · intro t ht
    exact (hasDerivWithinAt_globalJets hν W g a ht).hasFDerivWithinAt

end VelocityDetection.PeriodicMild
end

noncomputable section
namespace VelocityDetection.PeriodicMild
open Set Function Filter MeasureTheory
open scoped Topology ContDiff ZeroAtInfty BigOperators
open PeriodicSpace.Jets WeakVolterra
variable {ν : ℝ} (hν : 0 < ν) (W : Fin 2 → PeriodicData) (g : PeriodicData)
variable (hg : ∀ t : ℝ, t ≤ 0 → ∀ X, g.scalar t X = 0)
include hg

theorem sourceJets_nonpos (a : ℕ) {t : ℝ} (ht : t ≤ 0) : g.jets a t = 0 := by
  apply value_injective
  funext X
  rw [PeriodicData.jets_value]
  exact hg t ht X

@[simp] theorem timeGenerator_nonpos (a : ℕ) {t : ℝ} (ht : t ≤ 0) :
    timeGenerator hν W g a t = 0 := by
  have hm (i : Fin 2) :
      product ((W i).jets (a+1) t) (globalJets hν W g (a+1) t) = 0 := by
    rw [globalJets_nonpos hν W g (a+1) ht]
    exact (productL 2 (a+1) ((W i).jets (a+1) t)).map_zero
  simp only [timeGenerator, pdeSource, sourceJets_nonpos g hg a ht,
    globalJets_nonpos hν W g (a+2) ht, ← laplaceL_apply, map_zero,
    hm, ← differentiateL_apply, map_zero, smul_zero, Finset.sum_const_zero,
    sub_zero, zero_add]

theorem hasDerivAt_globalJets (a : ℕ) (t : ℝ) :
    HasDerivAt (globalJets hν W g a) (timeGenerator hν W g a t) t := by
  by_cases ht : 0 < t
  · exact (hasDerivWithinAt_globalJets hν W g a ht.le).hasDerivAt (Ici_mem_nhds ht)
  · have ht' : t ≤ 0 := le_of_not_gt ht
    rw [timeGenerator_nonpos hν W g hg a ht']
    by_cases hlt : t < 0
    · apply (hasDerivAt_const t (0 : E a)).congr_of_eventuallyEq
      filter_upwards [Iio_mem_nhds hlt] with r hr
      exact globalJets_nonpos hν W g a (le_of_lt hr)
    · have he : t = 0 := le_antisymm ht' (le_of_not_gt hlt)
      subst t
      have hl : HasDerivWithinAt (globalJets hν W g a) 0 (Iic (0:ℝ)) 0 := by
        apply (hasDerivWithinAt_const (0:ℝ) (Iic 0) (0 : E a)).congr_of_mem
        · intro r hr
          exact globalJets_nonpos hν W g a hr
        · exact (show (0:ℝ) ∈ Iic (0:ℝ) from le_refl (0:ℝ))
      have hr := hasDerivWithinAt_globalJets hν W g a (le_refl 0)
      rw [timeGenerator_nonpos hν W g hg a (le_refl 0)] at hr
      simpa only [Iic_union_Ici, hasDerivWithinAt_univ] using hl.union hr

theorem contDiff_globalJets_nat (k : ℕ) (a : ℕ) :
    ContDiff ℝ k (globalJets hν W g a) := by
  induction k generalizing a with
  | zero => exact contDiff_zero.mpr (continuous_globalJets hν W g a)
  | succ k ih =>
    have hp : ContDiff ℝ k (pdeSource hν W g a) := by
      have hm (i : Fin 2) : ContDiff ℝ k (fun t : ℝ =>
          product ((W i).jets (a+1) t) (globalJets hν W g (a+1) t)) :=
        ((productL 2 (a+1)).contDiff.comp
          ((W i).contDiff_jets_nat k (a+1))).clm_apply (ih (a+1))
      have hd (i : Fin 2) : ContDiff ℝ k (fun t : ℝ =>
          differentiate i (product ((W i).jets (a+1) t) (globalJets hν W g (a+1) t))) :=
        (differentiateL (n := 2) (a := a) i).contDiff.comp (hm i)
      exact (g.contDiff_jets_nat k a).sub (ContDiff.sum (fun i _ => hd i))
    have hg' : ContDiff ℝ k (timeGenerator hν W g a) :=
      (((laplaceL 2 a).contDiff.comp (ih (a+2))).const_smul ν).add hp
    apply contDiff_succ_iff_hasFDerivAt.mpr
    refine ⟨fun t => (1 : ℝ →L[ℝ] ℝ).smulRight (timeGenerator hν W g a t), ?_, ?_⟩
    · exact (ContinuousLinearMap.smulRightL ℝ ℝ (E a) 1).contDiff.comp hg'
    · intro t
      exact (hasDerivAt_globalJets hν W g hg a t).hasFDerivAt

theorem contDiff_globalJets (a : ℕ) : ContDiff ℝ ∞ (globalJets hν W g a) :=
  contDiff_infty.mpr (fun k => contDiff_globalJets_nat hν W g hg k a)

end VelocityDetection.PeriodicMild
end

end OAI
