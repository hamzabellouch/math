import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.MachineCylinder
import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.PeriodicMild
import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.PeriodicSpaceRestrictLApply

namespace OAI

noncomputable section
namespace VelocityDetection.PeriodicMild
open Set Function Filter MeasureTheory
open scoped Topology ContDiff BigOperators BoundedContinuousFunction
open scoped Topology ContDiff ZeroAtInfty BigOperators
open PeriodicSpace.Jets WeakVolterra
variable {T S ν : ℝ} {a b : ℕ}

def Mild (hT : 0 ≤ T) (ν : ℝ) (W : Fin 2 → TimeCurve T a)
    (g q : TimeCurve T a) : Prop := ∀ t : Icc (0 : ℝ) T,
  q t = sourceCurve hT (ν := ν) g t +
    ∫ s in Ioc (0 : ℝ) t.val,
      driftKernel hT (ν := ν) W s (t.val - s) (extend hT q (t.val - s))

def evolution (hT : 0 ≤ T) (hν : 0 < ν) (W : Fin 2 → TimeCurve T a)
    (g : TimeCurve T a) : TimeCurve T a := (existsUnique_mild hT hν W g).exists.choose

theorem evolution_mild (hT : 0 ≤ T) (hν : 0 < ν) (W : Fin 2 → TimeCurve T a)
    (g : TimeCurve T a) : Mild hT ν W g (evolution hT hν W g) := by
  intro t
  have hh := (existsUnique_mild hT hν W g).exists.choose_spec t
  simpa only [sourceCurve_apply, driftKernel_apply, integral_neg, sub_eq_add_neg,
    evolution] using hh

theorem mild_unique (hT : 0 ≤ T) (hν : 0 < ν) (W : Fin 2 → TimeCurve T a)
    (g : TimeCurve T a) {q r : TimeCurve T a}
    (hq : Mild hT ν W g q) (hr : Mild hT ν W g r) : q = r := by
  apply (existsUnique_mild hT hν W g).unique
  · intro t
    simpa only [sourceCurve_apply, driftKernel_apply, integral_neg, sub_eq_add_neg] using hq t
  · intro t
    simpa only [sourceCurve_apply, driftKernel_apply, integral_neg, sub_eq_add_neg] using hr t

def lowerCurve (hab : a ≤ b) (q : TimeCurve T b) : TimeCurve T a :=
  ⟨fun t => restrict hab (q t), (restrictL hab).continuous.comp q.continuous⟩

@[simp] theorem lowerCurve_apply (hab : a ≤ b) (q : TimeCurve T b) (t : Icc (0 : ℝ) T) :
    lowerCurve hab q t = restrict hab (q t) := rfl

@[simp] theorem extend_lowerCurve (hT : 0 ≤ T) (hab : a ≤ b) (q : TimeCurve T b) (r : ℝ) :
    extend hT (lowerCurve hab q) r = restrict hab (extend hT q r) := rfl

theorem integrableOn_source (hT : 0 ≤ T) (g : TimeCurve T a) (ν t : ℝ) :
    IntegrableOn (fun s => heat ν s (extend hT g (t - s))) (Ioc (0 : ℝ) t) := by
  have hc : Continuous (fun s : ℝ => heat ν s (extend hT g (t - s))) :=
    by
      change Continuous ((fun p : ℝ × E a => heat ν p.1 p.2) ∘
        (fun s : ℝ => (s, extend hT g (t - s))))
      apply Continuous.comp
      · exact continuous_heat_joint (a := a) ν
      · exact continuous_id.prodMk ((continuous_extend hT g).comp (continuous_const.sub continuous_id))
  exact hc.integrableOn_Icc.mono_set Ioc_subset_Icc_self

theorem integrableOn_drift (hT : 0 ≤ T) (hν : 0 < ν)
    (W : Fin 2 → TimeCurve T a) (q : TimeCurve T a) {t : ℝ} (ht : t ∈ Icc 0 T) :
    IntegrableOn (fun s => driftKernel hT (ν := ν) W s (t - s) (extend hT q (t - s)))
      (Ioc (0 : ℝ) t) :=
  integrable_causal hT (driftKernel hT (ν := ν) W) (driftBound (ν := ν) W)
    (continuousOn_driftKernel hT hν W) (integrableOn_driftBound hT W)
    (fun s _ => driftBound_nonneg W s) (fun _ hs r J => norm_driftKernel_le hT hν W hs.1 r J) q ht

@[simp] theorem restrict_sourceCurve (hT : 0 ≤ T) (hab : a ≤ b) (g : TimeCurve T b)
    (ν : ℝ) (t : Icc (0 : ℝ) T) :
    restrict hab (sourceCurve hT (ν := ν) g t) =
      sourceCurve hT (ν := ν) (lowerCurve hab g) t := by
  simp only [sourceCurve_apply, extend_lowerCurve]
  change restrictL hab (∫ s in Ioc (0 : ℝ) t.val, heat ν s (extend hT g (t.val - s))) = _
  rw [← (restrictL hab).integral_comp_comm (integrableOn_source hT g ν t.val)]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro s _
  exact restrict_heat hab ν s _

@[simp] theorem restrict_driftKernel (hT : 0 ≤ T) (hab : a ≤ b)
    (W : Fin 2 → TimeCurve T b) (ν s r : ℝ) (J : E b) :
    restrict hab (driftKernel hT (ν := ν) W s r J) =
      driftKernel hT (ν := ν) (fun i => lowerCurve hab (W i)) s r (restrict hab J) := by
  simp only [driftKernel_apply]
  change restrictL hab (-∑ i : Fin 2, _) = _
  rw [map_neg, map_sum]
  simp only [restrictL_apply, restrict_heatGradient, restrict_product, extend_lowerCurve]

theorem lower_evolution (hT : 0 ≤ T) (hν : 0 < ν) (hab : a ≤ b)
    (W : Fin 2 → TimeCurve T b) (g : TimeCurve T b) :
    lowerCurve hab (evolution hT hν W g) =
      evolution hT hν (fun i => lowerCurve hab (W i)) (lowerCurve hab g) := by
  apply mild_unique hT hν _ _ ?_ (evolution_mild hT hν _ _)
  intro t
  let q := evolution hT hν W g
  have hh := congrArg (restrictL hab) (evolution_mild hT hν W g t)
  rw [map_add, ← (restrictL hab).integral_comp_comm (integrableOn_drift hT hν W q t.property)] at hh
  simpa only [restrictL_apply, restrict_sourceCurve, restrict_driftKernel,
    lowerCurve_apply, extend_lowerCurve] using hh

def shortCurve (hST : S ≤ T) (q : TimeCurve T a) : TimeCurve S a :=
  ⟨fun t => q ⟨t.val, t.property.1, t.property.2.trans hST⟩,
    q.continuous.comp (continuous_subtype_val.subtype_mk _)⟩

@[simp] theorem shortCurve_apply (hST : S ≤ T) (q : TimeCurve T a) (t : Icc (0 : ℝ) S) :
    shortCurve hST q t = q ⟨t.val, t.property.1, t.property.2.trans hST⟩ := rfl

theorem extend_shortCurve (hS : 0 ≤ S) (hT : 0 ≤ T) (hST : S ≤ T)
    (q : TimeCurve T a) {r : ℝ} (hr : r ∈ Icc 0 S) :
    extend hS (shortCurve hST q) r = extend hT q r := by
  rw [extend_of_mem _ _ hr, extend_of_mem _ _ ⟨hr.1, hr.2.trans hST⟩]
  rfl

theorem short_driftKernel (hS : 0 ≤ S) (hT : 0 ≤ T) (hST : S ≤ T)
    (W : Fin 2 → TimeCurve T a) (q : TimeCurve T a) (ν s : ℝ) {r : ℝ}
    (hr : r ∈ Icc 0 S) :
    driftKernel hS (ν := ν) (fun i => shortCurve hST (W i)) s r
      (extend hS (shortCurve hST q) r) =
      driftKernel hT (ν := ν) W s r (extend hT q r) := by
  simp only [driftKernel_apply, extend_shortCurve hS hT hST _ hr]

theorem short_evolution (hS : 0 ≤ S) (hT : 0 ≤ T) (hST : S ≤ T) (hν : 0 < ν)
    (W : Fin 2 → TimeCurve T a) (g : TimeCurve T a) :
    shortCurve hST (evolution hT hν W g) =
      evolution hS hν (fun i => shortCurve hST (W i)) (shortCurve hST g) := by
  apply mild_unique hS hν _ _ ?_ (evolution_mild hS hν _ _)
  intro t
  let t' : Icc (0 : ℝ) T := ⟨t.val, t.property.1, t.property.2.trans hST⟩
  have hh := evolution_mild hT hν W g t'
  change evolution hT hν W g t' = _
  rw [hh, sourceCurve_apply, sourceCurve_apply]
  apply congrArg₂ (· + ·)
  · apply setIntegral_congr_fun measurableSet_Ioc
    intro s hs
    change heat ν s (extend hT g (t.val - s)) = heat ν s (extend hS (shortCurve hST g) (t.val - s))
    rw [extend_shortCurve hS hT hST g (show t.val - s ∈ Icc 0 S by
      constructor <;> linarith [hs.1, hs.2, t.property.2])]
  · apply setIntegral_congr_fun measurableSet_Ioc
    intro s hs
    have hr : t.val - s ∈ Icc 0 S := by
      constructor <;> linarith [hs.1, hs.2, t.property.2]
    exact (short_driftKernel hS hT hST W (evolution hT hν W g) ν s hr).symm

end VelocityDetection.PeriodicMild
end

end OAI
