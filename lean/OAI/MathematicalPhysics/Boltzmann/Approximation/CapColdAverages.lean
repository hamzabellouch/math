import OAI.MathematicalPhysics.Boltzmann.Approximation.CapFiniteBackgroundLimit
import OAI.MathematicalPhysics.Boltzmann.Approximation.CapLabelFreeLimit
import OAI.MathematicalPhysics.Boltzmann.Approximation.CapColdBounds
import OAI.MathematicalPhysics.Boltzmann.Compactness.MeasurableResolvent
import OAI.MathematicalPhysics.Boltzmann.Compactness.WeakL1Operations

namespace OAI

section

/-! # The fixed-window cold truncation loses only escaped mass -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotLimitExtraction.central_le_meshCold (E : HotLimitExtraction S)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq : q < 2)
    {δ R : ℝ} (hδ : 0 < δ) (n : ℕ) (t : ℝ) (x v : Velocity)
    (ht : S.radius (E.indices n)*t ≤ 1/32)
    (hx : S.radius (E.indices n) • x ∈ TorusChart.cube)
    (hlo : δ ≤ ‖transverse x‖) (hhi : ‖transverse x‖ ≤ R)
    (hU : GeometricMesh.index R η < GeometricMesh.index (s₀/S.radius (E.indices n)) η) :
    (F.approximation (E.indices n)).centralTotal ((S.radius (E.indices n)*t,S.radius (E.indices n) • x),v) ≤
      E.meshCold n (GeometricMesh.index (δ/Real.exp η) η) (GeometricMesh.index R η)
        (S.radius (E.indices n)*t,(JetPeriodicDatum.spatialMap (S.radius (E.indices n) • x),v)) := by
  classical
  rw [E.centralTotal_mesh_window hs₀ hsmax hη hδ n t x v ht hx hlo hhi hU,
    E.meshCold_sum n _ _ hU]
  have hc := (F.approximation (E.indices n)).cold_properties hs₀ hsmax hη hηmax hK hd₀ hq
    (shrinkingHorizon_pos F.horizonScale_pos _).le
  apply Finset.sum_le_sum
  intro a _
  apply Finset.sum_le_sum
  intro k _
  split_ifs with hk
  · by_cases hx' : S.radius (E.indices n) • x ∈
        JetLattice.spatialEnlargement s₀ η (S.radius (E.indices n)*t) (E.coldLabel k a n)
    · rw [indicator_of_mem hx']
    · rw [indicator_of_notMem hx']
      exact hc.2.1 _ _
  · exact le_rfl

theorem HotLimitExtraction.meshCold_gap_le_escaped (E : HotLimitExtraction S)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq : q < 2)
    {δ R : ℝ} (hδ : 0 < δ) (n : ℕ) (t : ℝ) (x v : Velocity)
    (ht : S.radius (E.indices n)*t ≤ 1/32)
    (hx : S.radius (E.indices n) • x ∈ TorusChart.cube)
    (hlo : δ ≤ ‖transverse x‖) (hhi : ‖transverse x‖ ≤ R)
    (hU : GeometricMesh.index R η < GeometricMesh.index (s₀/S.radius (E.indices n)) η) :
    let u := (S.radius (E.indices n)*t,(JetPeriodicDatum.spatialMap (S.radius (E.indices n) • x),v))
    let M := E.meshCold n (GeometricMesh.index (δ/Real.exp η) η) (GeometricMesh.index R η) u
    0 ≤ (F.approximation (E.indices n)).coldTotal u-M ∧
      (F.approximation (E.indices n)).coldTotal u-M ≤
        (F.approximation (E.indices n)).escapedTotal
          ((S.radius (E.indices n)*t,S.radius (E.indices n) • x),v) := by
  intro u M
  have hu := E.meshCold_le_total hs₀ hsmax hη hηmax hK hd₀ hq n
    (GeometricMesh.index (δ/Real.exp η) η) (GeometricMesh.index R η) u
  have hl := E.central_le_meshCold hs₀ hsmax hη hηmax hK hd₀ hq hδ n t x v ht hx hlo hhi hU
  have he := (F.approximation (E.indices n)).coldTotal_eq_central_add_escaped hs₀ hsmax hη hηmax hK hd₀ hq
    (shrinkingHorizon_pos F.horizonScale_pos _).le ((S.radius (E.indices n)*t,S.radius (E.indices n) • x),v)
  exact ⟨sub_nonneg.mpr hu,by dsimp only [M,u] at *; linarith⟩

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # Actual dilated cold density on a finite mesh window -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

def HotLimitExtraction.meshColdDensity (E : HotLimitExtraction S) (n : ℕ) (L U : ℤ)
    (z : Published.KineticPhase) : ℝ :=
  S.radius (E.indices n)*H q z.2*E.meshCold n L U
    (S.radius (E.indices n)*z.1.1,(S.radius (E.indices n) • JetPeriodicDatum.spatialMap z.1.2,z.2))

theorem HotLimitExtraction.meshCold_measurable (E : HotLimitExtraction S)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq : q < 2) (n : ℕ) (L U : ℤ) :
    Measurable (E.meshCold n L U) := by
  classical
  have hc := (F.approximation (E.indices n)).cold_properties hs₀ hsmax hη hηmax hK hd₀ hq
    (shrinkingHorizon_pos F.horizonScale_pos _).le
  apply Finset.measurable_sum
  intro i _
  by_cases hi : i.annulus < F.indices (E.indices n)
  · simpa only [hi,ite_true] using hc.1 i
  · simpa only [hi,ite_false] using (measurable_const : Measurable (fun _ : ℝ × JetPrototype.Phase => (0:ℝ)))

theorem HotLimitExtraction.meshColdDensity_measurable (E : HotLimitExtraction S)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq : q < 2) (n : ℕ) (L U : ℤ) :
    Measurable (E.meshColdDensity n L U) := by
  have hm := E.meshCold_measurable hs₀ hsmax hη hηmax hK hd₀ hq n L U
  have hp : Measurable (fun z : Published.KineticPhase =>
      (S.radius (E.indices n)*z.1.1,(S.radius (E.indices n) • JetPeriodicDatum.spatialMap z.1.2,z.2))) := by
    unfold JetPeriodicDatum.spatialMap transverse axial
    fun_prop
  exact (((ChartKernel.measurable_H q).comp measurable_snd).const_mul _).mul (hm.comp hp)

theorem HotLimitExtraction.scaled_mesh_gap_le_escaped (E : HotLimitExtraction S)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq : q < 2)
    {δ R : ℝ} (hδ : 0 < δ) (n : ℕ) (z : Published.KineticPhase)
    (ht : S.radius (E.indices n)*z.1.1 ≤ 1/32)
    (hx : S.radius (E.indices n) • z.1.2 ∈ TorusChart.cube)
    (hlo : δ ≤ ‖transverse z.1.2‖) (hhi : ‖transverse z.1.2‖ ≤ R)
    (hU : GeometricMesh.index R η < GeometricMesh.index (s₀/S.radius (E.indices n)) η) :
    let D := S.rescaledColdDensity (E.indices n) ((z.1.1,JetPeriodicDatum.spatialMap z.1.2),z.2)-
      E.meshColdDensity n (GeometricMesh.index (δ/Real.exp η) η) (GeometricMesh.index R η) z
    0 ≤ D ∧ D ≤ S.rescaledEscapedDensity (E.indices n) z := by
  intro D
  have hb := E.meshCold_gap_le_escaped hs₀ hsmax hη hηmax hK hd₀ hq hδ n z.1.1 z.1.2 z.2
    ht hx hlo hhi hU
  have hmap : JetPeriodicDatum.spatialMap (S.radius (E.indices n) • z.1.2) =
      S.radius (E.indices n) • JetPeriodicDatum.spatialMap z.1.2 := rfl
  dsimp only at hb
  rw [hmap] at hb
  have hH : 0 ≤ S.radius (E.indices n)*H q z.2 :=
    mul_nonneg (S.radius_pos hs₀ _).le (H_nonneg q z.2)
  constructor
  · simpa only [D,rescaledColdDensity,meshColdDensity,mul_sub] using mul_nonneg hH hb.1
  · simpa only [D,rescaledColdDensity,meshColdDensity,rescaledEscapedDensity,mul_sub] using
      mul_le_mul_of_nonneg_left hb.2 hH

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # A fixed set of retained labels on every finite mesh interval -/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotLimitExtraction.meshColdDensity_sum (E : HotLimitExtraction S) (n : ℕ) (L U : ℤ)
    (hU : U < GeometricMesh.index (s₀/S.radius (E.indices n)) η) (z : Published.KineticPhase) :
    E.meshColdDensity n L U z = ∑ a : Bool, ∑ k ∈ Finset.Icc L U,
      if (E.coldLabel k a n).annulus < F.indices (E.indices n) then
        E.coldLabelDensity k a n z.1.1 (JetPeriodicDatum.spatialMap z.1.2,z.2) else 0 := by
  classical
  unfold meshColdDensity
  rw [E.meshCold_sum n L U hU,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hk : (E.coldLabel k a n).annulus < F.indices (E.indices n)
  · simp only [hk,ite_true,coldLabelDensity]
    ring
  · simp only [hk,ite_false,mul_zero]

theorem HotLimitExtraction.eventually_meshColdDensity_fixed (E : HotLimitExtraction S)
    (hs₀ : 0 < s₀) (hη : 0 < η) (L U : ℤ) :
    ∀ᶠ n in atTop, ∀ z : Published.KineticPhase,
      E.meshColdDensity n L U z = ∑ a : Bool, ∑ k ∈ Finset.Icc L U,
        if E.fraction < E.phase*Real.exp (η*(k:ℝ)) then
          E.coldLabelDensity k a n z.1.1 (JetPeriodicDatum.spatialMap z.1.2,z.2) else 0 := by
  classical
  have hret : ∀ᶠ n in atTop, ∀ k ∈ Finset.Icc L U, ∀ a : Bool,
      ((E.coldLabel k a n).annulus < F.indices (E.indices n) ↔
        E.fraction < E.phase*Real.exp (η*(k:ℝ))) := by
    rw [Filter.eventually_all_finset]
    intro k _
    exact Filter.eventually_all.mpr (fun a => E.coldLabel_retained_iff hs₀ hη k a)
  have htop := (GeometricMesh.index_tendsto_atTop hs₀ hη
    (fun n => S.radius_pos hs₀ (E.indices n))
    ((S.radius_tendsto_zero hs₀).comp E.indices_strict.tendsto_atTop)).eventually_gt_atTop U
  filter_upwards [hret,htop] with n hn htop
  intro z
  rw [E.meshColdDensity_sum n L U htop z]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro k hk
  simp only [hn k hk a]

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # Velocity averages of the finite retained mesh -/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotLimitExtraction.eventually_meshColdDensity_average (E : HotLimitExtraction S)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq : q < 2) (L U : ℤ)
    {B : ℝ} {ψ : Velocity → ℝ} (hψ : Measurable ψ) (hψB : ∀ v, |ψ v| ≤ B) :
    ∀ᶠ n in atTop, ∀ (t : ℝ) (x : Velocity),
      (∫ v, ψ v*E.meshColdDensity n L U ((t,x),v)) =
        E.finiteColdAverage L U n t ψ (JetPeriodicDatum.spatialMap x) := by
  classical
  filter_upwards [E.eventually_meshColdDensity_fixed hs₀ hη L U] with n hn
  intro t x
  let f : Bool → ℤ → Velocity → ℝ := fun a k v =>
    if E.fraction < E.phase*Real.exp (η*(k:ℝ)) then
      ψ v*E.coldLabelDensity k a n t (JetPeriodicDatum.spatialMap x,v) else 0
  have hi (a k) : Integrable (f a k) := by
    by_cases hk : E.fraction < E.phase*Real.exp (η*(k:ℝ))
    · simpa only [f,hk,ite_true] using
        (E.coldLabelDensity_fiber_integrable hs₀ hsmax hη hηmax hK hd₀ hq k a n t
          (JetPeriodicDatum.spatialMap x)).bdd_mul hψ.aestronglyMeasurable
            (ae_of_all _ hψB)
    · simp only [f,hk,ite_false]
      exact integrable_const_iff.mpr (Or.inl rfl)
  have heq : (fun v => ψ v*E.meshColdDensity n L U ((t,x),v)) =
      (fun v => ∑ a : Bool, ∑ k ∈ Finset.Icc L U, f a k v) := by
    funext v
    rw [hn ((t,x),v),Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    by_cases hk : E.fraction < E.phase*Real.exp (η*(k:ℝ)) <;>
      simp only [f,hk,ite_true,ite_false,mul_zero]
  rw [heq,integral_finsetSum _ (fun a _ =>
    integrable_finsetSum _ (fun k _ => hi a k))]
  unfold finiteColdAverage
  apply Finset.sum_congr rfl
  intro a _
  rw [integral_finsetSum _ (fun k _ => hi a k)]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hk : E.fraction < E.phase*Real.exp (η*(k:ℝ)) <;>
    simp only [f,hk,ite_true,ite_false,integral_zero,coldLabelAverage]

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # Weak space-time convergence of the actual retained cold labels -/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology ENNReal

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotLimitExtraction.coldLabel_spacetime_weak_limit (E : HotLimitExtraction S)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1/4) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1) (hq : q < 2)
    (k : ℤ) (σ : Bool) (hk : E.fraction < E.phase*Real.exp (η*(k:ℝ)))
    {a A : ℝ} (ha : 0 < a) (hA : ENNReal.ofReal A < E.horizon)
    (Ω₁ : Set VelocityWeight.Transverse) (hΩ₁ : IsCompact Ω₁)
    (Ω₂ : Set ℝ) (hΩ₂ : IsCompact Ω₂)
    {B : ℝ} {ψ : Velocity → ℝ} (hψ : Continuous ψ) (hψB : ∀ v, |ψ v| ≤ B) :
    Published.WeakL1Converges
      ((volume.restrict (Icc a A)).prod (JetPrototype.spaceVolume.restrict (Ω₁ ×ˢ Ω₂)))
      (fun n z => E.coldLabelAverage k σ n z.1 ψ z.2)
      (fun z => E.coldLabelLimitProfile k σ (max 0 z.1) ψ z.2) := by
  let ρ := JetPrototype.spaceVolume.restrict (Ω₁ ×ˢ Ω₂)
  let ν := (volume : Measure ℝ).restrict (Icc a A)
  let _ : IsFiniteMeasure ρ := isFiniteMeasure_restrict.mpr (hΩ₁.prod hΩ₂).measure_lt_top.ne
  have hB : 0 ≤ B := (abs_nonneg (ψ 0)).trans (hψB 0)
  apply Published.WeakL1Converges.prod_of_fibers
    (fun n => E.coldLabelAverage_joint_integrable hs₀ hsmax hη hηmax hK hd₀.le hq k σ n
      hψ.measurable hψB (ν.prod ρ))
    (E.coldLabelLimitProfile_clamped_measurable hK hα.le hγ.le k σ hψ.measurable)
    (E.coldLabelLimitProfile_clamped_integrable hK hα hγ k σ ha hψ.measurable hψB ρ)
  · have hb := E.eventually_coldLabelAverage_bound hs₀ hsmax hη hηmax hK hα
      (hαmax.trans (by norm_num)) hγ hd₀ hd₀max hsmall hq ha hA hB hψB
    filter_upwards [hb] with n hn
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Icc)] with z hz
    exact hn z.1 hz k σ z.2
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    have htp : 0 < t := ha.trans_le ht.1
    have hw := E.coldLabel_weak_limit hs₀ hsmax hη hηmax hK hα hαmax hγ hd₀ hd₀max
      hsmall hq k σ hk htp ((ENNReal.ofReal_le_ofReal ht.2).trans_lt hA)
      Ω₁ hΩ₁ Ω₂ hΩ₂ hψ hψB
    simpa only [max_eq_right htp.le] using hw

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # Weak space-time convergence of the finite retained cold mesh -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotLimitExtraction.finite_cold_spacetime_weak_limit (E : HotLimitExtraction S)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1/4) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq : q < 2) (L U : ℤ) {a A : ℝ} (ha : 0 < a) (hA : ENNReal.ofReal A < E.horizon)
    (Ω₁ : Set VelocityWeight.Transverse) (hΩ₁ : IsCompact Ω₁)
    (Ω₂ : Set ℝ) (hΩ₂ : IsCompact Ω₂)
    {B : ℝ} {ψ : Velocity → ℝ} (hψ : Continuous ψ) (hψB : ∀ v, |ψ v| ≤ B) :
    Published.WeakL1Converges
      ((volume.restrict (Icc a A)).prod (JetPrototype.spaceVolume.restrict (Ω₁ ×ˢ Ω₂)))
      (fun n z => E.finiteColdAverage L U n z.1 ψ z.2)
      (fun z => E.finiteColdLimitProfile L U (max 0 z.1) ψ z.2) := by
  classical
  let ρ := (volume.restrict (Icc a A)).prod (JetPrototype.spaceVolume.restrict (Ω₁ ×ˢ Ω₂))
  let _ : IsFiniteMeasure (JetPrototype.spaceVolume.restrict (Ω₁ ×ˢ Ω₂)) :=
    isFiniteMeasure_restrict.mpr (hΩ₁.prod hΩ₂).measure_lt_top.ne
  let f : Bool → ℤ → ℕ → (ℝ × JetPrototype.Space) → ℝ := fun σ k n z =>
    if E.fraction < E.phase*Real.exp (η*(k:ℝ)) then E.coldLabelAverage k σ n z.1 ψ z.2 else 0
  let g : Bool → ℤ → (ℝ × JetPrototype.Space) → ℝ := fun σ k z =>
    if E.fraction < E.phase*Real.exp (η*(k:ℝ)) then E.coldLabelLimitProfile k σ (max 0 z.1) ψ z.2 else 0
  have hi (σ k n) : Integrable (f σ k n) ρ := by
    by_cases hk : E.fraction < E.phase*Real.exp (η*(k:ℝ))
    · simpa only [f,hk,ite_true] using E.coldLabelAverage_joint_integrable hs₀ hsmax hη hηmax
        hK hd₀.le hq k σ n hψ.measurable hψB ρ
    · simpa only [f,hk,ite_false] using (integrable_const (μ := ρ) (0:ℝ))
  have hw (σ k) : Published.WeakL1Converges ρ (f σ k) (g σ k) := by
    by_cases hk : E.fraction < E.phase*Real.exp (η*(k:ℝ))
    · simpa only [f,g,hk,ite_true] using E.coldLabel_spacetime_weak_limit hs₀ hsmax hη hηmax
        hK hα hαmax hγ hd₀ hd₀max hsmall hq k σ hk ha hA Ω₁ hΩ₁ Ω₂ hΩ₂ hψ hψB
    · simp only [f,g,hk,ite_false]
      refine ⟨measurable_const,integrable_const 0,?_⟩
      intro φ _ _
      simp only [mul_zero,integral_zero]
      exact tendsto_const_nhds
  have hinner (σ) := Published.WeakL1Converges.finset_sum (Finset.Icc L U)
    (fun k _ => hw σ k) (fun k _ n => hi σ k n)
  exact Published.WeakL1Converges.finset_sum (Finset.univ : Finset Bool)
    (fun σ _ => hinner σ)
    (fun σ _ n => integrable_finsetSum (Finset.Icc L U) (fun k _ => hi σ k n))

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # Finite mesh truncation of the actual cold density in local L1 -/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

def meshWindowSet (a A δ R : ℝ) : Set Published.KineticPhase :=
  coldSlabSet a A R ∩ {z | δ ≤ ‖transverse z.1.2‖}

def meshWindowVolume (a A δ R : ℝ) : Measure Published.KineticPhase :=
  volume.restrict (meshWindowSet a A δ R)

theorem meshWindowSet_measurable (a A δ R : ℝ) : MeasurableSet (meshWindowSet a A δ R) := by
  apply ((measurableSet_Icc.prod measurableSet_closedBall).prod MeasurableSet.univ).inter
  exact measurableSet_le measurable_const (by unfold transverse; fun_prop)

theorem HotLimitExtraction.eventually_mesh_gap (E : HotLimitExtraction S)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq : q < 2)
    {a A δ R : ℝ} (ha : 0 < a) (hδ : 0 < δ) (hA : ENNReal.ofReal A < E.horizon) :
    ∀ᶠ n in atTop, ∀ z ∈ meshWindowSet a A δ R,
      0 ≤ S.rescaledColdDensity (E.indices n) ((z.1.1,JetPeriodicDatum.spatialMap z.1.2),z.2)-
        E.meshColdDensity n (GeometricMesh.index (δ/Real.exp η) η) (GeometricMesh.index R η) z ∧
      S.rescaledColdDensity (E.indices n) ((z.1.1,JetPeriodicDatum.spatialMap z.1.2),z.2)-
        E.meshColdDensity n (GeometricMesh.index (δ/Real.exp η) η) (GeometricMesh.index R η) z ≤
        S.rescaledEscapedDensity (E.indices n) z := by
  have hrlim : Tendsto (fun n => S.radius (E.indices n)) atTop (𝓝 0) :=
    (S.radius_tendsto_zero hs₀).comp E.indices_strict.tendsto_atTop
  have hrR := (hrlim.mul_const R).eventually (gt_mem_nhds (by norm_num : (0:ℝ)*R < 1/2))
  filter_upwards [hrR,GeometricMesh.window_eventually_below_top hs₀ hη
    (fun n => S.radius_pos hs₀ (E.indices n)) hrlim,
    S.eventually_scaled_slab hs₀ E.horizon_limit hA] with n hn htop hslab
  intro z hz
  have htime : z.1.1 ∈ Icc a A := hz.1.1.1
  have hx : ‖z.1.2‖ ≤ R := by
    simpa only [Metric.mem_closedBall,dist_zero_right] using hz.1.1.2
  have htrans : ‖transverse z.1.2‖ ≤ R := by
    have he := norm_sq_split z.1.2
    have hb : ‖transverse z.1.2‖ ≤ ‖z.1.2‖ := by
      nlinarith [sq_nonneg (axial z.1.2),norm_nonneg (transverse z.1.2),norm_nonneg z.1.2]
    exact hb.trans hx
  apply E.scaled_mesh_gap_le_escaped hs₀ hsmax hη hηmax hK hd₀ hq hδ n z
    ((hslab z.1.1 ⟨(ha.trans_le htime.1).le,htime.2⟩).2.trans
      ((shrinkingHorizon_le F.horizonScale_pos _).trans F.horizonScale_le)) _ hz.2 htrans htop
  intro i
  have hi : |(S.radius (E.indices n) • z.1.2) i| < 1/2 := by
    calc
      _ = S.radius (E.indices n)*|z.1.2 i| := by
        change |S.radius (E.indices n)*z.1.2 i| = _
        rw [abs_mul,abs_of_pos (S.radius_pos hs₀ _)]
      _ ≤ S.radius (E.indices n)*‖z.1.2‖ := mul_le_mul_of_nonneg_left
        (by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le z.1.2 i) (S.radius_pos hs₀ _).le
      _ ≤ S.radius (E.indices n)*R := mul_le_mul_of_nonneg_left hx (S.radius_pos hs₀ _).le
      _ < _ := hn
  exact ⟨(abs_lt.mp hi).1,(abs_lt.mp hi).2.le⟩

theorem HotLimitExtraction.mesh_truncation_L1_limit (E : HotLimitExtraction S)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 ≤ α) (hαmax : α ≤ 1) (hγ : 0 ≤ γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1) (hq : q < 2)
    {a A δ R : ℝ} (ha : 0 < a) (hδ : 0 < δ) (hA : ENNReal.ofReal A < E.horizon) :
    Tendsto (fun n => eLpNorm (fun z : Published.KineticPhase =>
      S.rescaledColdDensity (E.indices n) ((z.1.1,JetPeriodicDatum.spatialMap z.1.2),z.2)-
        E.meshColdDensity n (GeometricMesh.index (δ/Real.exp η) η) (GeometricMesh.index R η) z)
      1 (meshWindowVolume a A δ R)) atTop (𝓝 0) := by
  have hmeasure : meshWindowVolume a A δ R ≤ coldSlabVolume a A R := by
    rw [coldSlabVolume_eq]
    exact Measure.restrict_mono inter_subset_left le_rfl
  have he := S.rescaledEscapedDensity_tendsto_zero hs₀ hsmax hη hηmax hK hα hαmax hγ
    hd₀ hd₀max hsmall hq E.indices_strict E.horizon_limit ha hA R
  have hl := tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds he
    (fun _ => zero_le) (fun n => eLpNorm_mono_measure _ hmeasure)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hl
    (Eventually.of_forall (fun _ => zero_le))
  filter_upwards [E.eventually_mesh_gap hs₀ hsmax hη hηmax hK hd₀.le hq ha hδ hA] with n hn
  have hp : Measurable (fun z : Published.KineticPhase => ((z.1.1,JetPeriodicDatum.spatialMap z.1.2),z.2)) := by
    unfold JetPeriodicDatum.spatialMap transverse axial
    fun_prop
  apply eLpNorm_mono_ae
    (((S.rescaledColdDensity_measurable hs₀ hsmax hη hηmax hK hd₀.le hq _).comp hp).sub
      (E.meshColdDensity_measurable hs₀ hsmax hη hηmax hK hd₀.le hq n _ _)).aestronglyMeasurable
  filter_upwards [ae_restrict_mem (meshWindowSet_measurable a A δ R)] with z hz
  change |S.rescaledColdDensity (E.indices n) ((z.1.1,JetPeriodicDatum.spatialMap z.1.2),z.2)-
    E.meshColdDensity n (GeometricMesh.index (δ/Real.exp η) η) (GeometricMesh.index R η) z| ≤
    |S.rescaledEscapedDensity (E.indices n) z|
  rw [abs_of_nonneg (hn z hz).1,abs_of_nonneg
    (S.rescaledEscapedDensity_nonneg hs₀ hsmax hη hηmax hK hd₀.le hq _ z)]
  exact (hn z hz).2

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # Spacetime resolvents and velocity averages of the actual rescaled hot solution -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.TransportCutoff

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}

theorem hot_spacetime_resolvent (S : AttainedCapSequence F)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq : q < 2) (n : ℕ) {A : ℝ}
    (hA : S.radius n*A ≤ shrinkingHorizon F.horizonScale n)
    {χ : Published.KineticPhase → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hzero : ∀ p : Velocity × Velocity, χ (TransportCutoff.characteristic p 0) = 0) :
    (fun z => χ z*S.euclideanHot n z) =ᵐ[
      ((volume.restrict (Icc 0 A)).prod (volume : Measure Velocity)).prod volume]
      Published.transportResolvent (localizedSource A χ (S.euclideanHot n) (S.euclideanHotSource n)) := by
  let f := S.euclideanHot n
  let r := localizedSource A χ f (S.euclideanHotSource n)
  have hfm : Measurable f := S.euclideanHot_measurable hs₀ hsmax hη hηmax hK hd₀ hq n
  have hrm : Measurable r := localizedSource_measurable hχ hfm
    (S.euclideanHotSource_measurable hs₀ hsmax hη hηmax hK hd₀ hq n)
  have hm : MeasurableSet {z : ℝ × (Velocity × Velocity) |
      χ ((z.1,z.2.1),z.2.2)*f ((z.1,z.2.1),z.2.2) =
        Published.transportResolvent r ((z.1,z.2.1),z.2.2)} :=
    (measurableSet_eq_fun (hχ.continuous.measurable.mul hfm)
      (Published.transportResolvent_measurable hrm)).preimage (by fun_prop)
  have ht : ∀ᵐ t ∂volume.restrict (Icc 0 A), ∀ᵐ p ∂(volume : Measure (Velocity × Velocity)),
      χ ((t,p.1),p.2)*f ((t,p.1),p.2) = Published.transportResolvent r ((t,p.1),p.2) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact S.hot_resolvent hs₀ hsmax hη hηmax hK hd₀ hq n hA ht hχ hzero
  have hfull := (Measure.ae_prod_iff_ae_ae hm).mpr ht
  exact (measurePreserving_prodAssoc (volume.restrict (Icc 0 A))
    (volume : Measure Velocity) (volume : Measure Velocity)).quasiMeasurePreserving.ae hfull

theorem hot_velocity_averages_resolvent (S : AttainedCapSequence F)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq : q < 2) (n : ℕ) {A : ℝ}
    (hA : S.radius n*A ≤ shrinkingHorizon F.horizonScale n)
    {χ : Published.KineticPhase → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hzero : ∀ p : Velocity × Velocity, χ (TransportCutoff.characteristic p 0) = 0)
    (ψ : Velocity → ℝ) :
    (fun z : Published.SpaceTime => ∫ v, ψ v*(χ (z,v)*S.euclideanHot n (z,v))) =ᵐ[
      (volume.restrict (Icc 0 A)).prod (volume : Measure Velocity)]
      Published.resolventAverage (localizedSource A χ (S.euclideanHot n) (S.euclideanHotSource n)) ψ := by
  have he := Measure.ae_ae_of_ae_prod
    (S.hot_spacetime_resolvent hs₀ hsmax hη hηmax hK hd₀ hq n hA hχ hzero)
  filter_upwards [he] with z hz
  apply integral_congr_ae
  filter_upwards [hz] with v hv
  rw [hv]

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # The atomic background is the space-time limit of the finite cold mesh -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotLimitExtraction.finite_cold_spacetime_background_limit (E : HotLimitExtraction S)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1/4) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq : q < 2) {a A δ R : ℝ} (ha : 0 < a) (hA : ENNReal.ofReal A < E.horizon) (hδ : 0 < δ)
    (Ω₁ : Set VelocityWeight.Transverse) (hΩ₁ : IsCompact Ω₁)
    (hlo : ∀ y ∈ Ω₁, δ ≤ ‖y‖) (hhi : ∀ y ∈ Ω₁, ‖y‖ ≤ R)
    (Ω₂ : Set ℝ) (hΩ₂ : IsCompact Ω₂)
    {B : ℝ} {ψ : Velocity → ℝ} (hψ : Continuous ψ) (hψB : ∀ v, |ψ v| ≤ B) :
    Published.WeakL1Converges
      ((volume.restrict (Icc a A)).prod (JetPrototype.spaceVolume.restrict (Ω₁ ×ˢ Ω₂)))
      (fun n z => E.finiteColdAverage (GeometricMesh.index (δ/Real.exp η) η)
        (GeometricMesh.index R η) n z.1 ψ z.2)
      (fun z => ∫ v, ψ v ∂E.background (max 0 z.1) z.2) := by
  have hw := E.finite_cold_spacetime_weak_limit hs₀ hsmax hη hηmax hK hα hαmax hγ hd₀ hd₀max
    hsmall hq (GeometricMesh.index (δ/Real.exp η) η) (GeometricMesh.index R η)
    ha hA Ω₁ hΩ₁ Ω₂ hΩ₂ hψ hψB
  have hm : Measurable (fun z : ℝ × JetPrototype.Space => ∫ v, ψ v ∂E.background (max 0 z.1) z.2) :=
    GeometricBackground.clamped_background_test_measurable (zero_lt_one.trans_le E.phase_mem.1)
      hK hα.le hγ.le η E.fraction hψ.measurable
  apply hw.congr_limit hm
  filter_upwards [Measure.quasiMeasurePreserving_snd.ae
    (ae_restrict_mem (hΩ₁.prod hΩ₂).measurableSet)] with z hz
  exact E.finiteColdLimitProfile_eq_background hη hK hα.le hγ.le (le_max_left 0 z.1) hδ z.2
    (hlo z.2.1 hz.1) (hhi z.2.1 hz.1) ψ

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # The actual finite-mesh velocity averages converge to the background -/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology ENNReal

namespace BoltzmannNonuniqueness

theorem JetPeriodicDatum.spatialMap_join (x : JetPrototype.Space) :
    JetPeriodicDatum.spatialMap (SheetMeasures.join x) = x := by
  have h := VelocityWeight.split.apply_symm_apply (x.2,x.1)
  apply Prod.ext
  · change VelocityWeight.transverse (VelocityWeight.split.symm (x.2,x.1)) = x.1
    simpa only [VelocityWeight.split_apply] using congrArg Prod.snd h
  · change VelocityWeight.axial (VelocityWeight.split.symm (x.2,x.1)) = x.2
    simpa only [VelocityWeight.split_apply] using congrArg Prod.fst h

namespace JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

def HotLimitExtraction.meshColdChartAverage (E : HotLimitExtraction S) (n : ℕ) (L U : ℤ)
    (t : ℝ) (ψ : Velocity → ℝ) (x : JetPrototype.Space) : ℝ :=
  ∫ v, ψ v*E.meshColdDensity n L U ((t,SheetMeasures.join x),v)

theorem HotLimitExtraction.eventually_meshColdChartAverage (E : HotLimitExtraction S)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq : q < 2) (L U : ℤ)
    {B : ℝ} {ψ : Velocity → ℝ} (hψ : Measurable ψ) (hψB : ∀ v, |ψ v| ≤ B) :
    ∀ᶠ n in atTop, ∀ (t : ℝ) (x : JetPrototype.Space),
      E.meshColdChartAverage n L U t ψ x = E.finiteColdAverage L U n t ψ x := by
  filter_upwards [E.eventually_meshColdDensity_average hs₀ hsmax hη hηmax hK hd₀ hq L U hψ hψB]
    with n hn
  intro t x
  simpa only [meshColdChartAverage,JetPeriodicDatum.spatialMap_join] using hn t (SheetMeasures.join x)

theorem HotLimitExtraction.mesh_cold_spacetime_background_limit (E : HotLimitExtraction S)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1/4) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq : q < 2) {a A δ R : ℝ} (ha : 0 < a) (hA : ENNReal.ofReal A < E.horizon) (hδ : 0 < δ)
    (Ω₁ : Set VelocityWeight.Transverse) (hΩ₁ : IsCompact Ω₁)
    (hlo : ∀ y ∈ Ω₁, δ ≤ ‖y‖) (hhi : ∀ y ∈ Ω₁, ‖y‖ ≤ R)
    (Ω₂ : Set ℝ) (hΩ₂ : IsCompact Ω₂)
    {B : ℝ} {ψ : Velocity → ℝ} (hψ : Continuous ψ) (hψB : ∀ v, |ψ v| ≤ B) :
    Published.WeakL1Converges
      ((volume.restrict (Icc a A)).prod (JetPrototype.spaceVolume.restrict (Ω₁ ×ˢ Ω₂)))
      (fun n z => E.meshColdChartAverage n (GeometricMesh.index (δ/Real.exp η) η)
        (GeometricMesh.index R η) z.1 ψ z.2)
      (fun z => ∫ v, ψ v ∂E.background (max 0 z.1) z.2) := by
  apply (E.finite_cold_spacetime_background_limit hs₀ hsmax hη hηmax hK hα hαmax hγ hd₀ hd₀max
    hsmall hq ha hA hδ Ω₁ hΩ₁ hlo hhi Ω₂ hΩ₂ hψ hψB).congr_eventually
  filter_upwards [E.eventually_meshColdChartAverage hs₀ hsmax hη hηmax hK hd₀.le hq
    (GeometricMesh.index (δ/Real.exp η) η) (GeometricMesh.index R η) hψ.measurable hψB] with n hn
  exact ae_of_all _ (fun z => (hn z.1 z.2).symm)

end JetCopyDatum.AttainedCapSequence
end BoltzmannNonuniqueness

end

end

section

/-! # Positivity and integrability of finite-mesh averages -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotLimitExtraction.meshColdDensity_bounds (E : HotLimitExtraction S)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq : q < 2) (n : ℕ) (L U : ℤ)
    (z : Published.KineticPhase) :
    0 ≤ E.meshColdDensity n L U z ∧ E.meshColdDensity n L U z ≤
      S.rescaledColdDensity (E.indices n) ((z.1.1,JetPeriodicDatum.spatialMap z.1.2),z.2) := by
  have hc := (F.approximation (E.indices n)).cold_properties hs₀ hsmax hη hηmax hK hd₀ hq
    (shrinkingHorizon_pos F.horizonScale_pos _).le
  have hnon : 0 ≤ E.meshCold n L U
      (S.radius (E.indices n)*z.1.1,(S.radius (E.indices n) • JetPeriodicDatum.spatialMap z.1.2,z.2)) := by
    apply Finset.sum_nonneg
    intro i _
    split_ifs
    · exact hc.2.1 _ _
    · exact le_rfl
  have hH := mul_nonneg (S.radius_pos hs₀ (E.indices n)).le (H_nonneg q z.2)
  exact ⟨mul_nonneg hH hnon,mul_le_mul_of_nonneg_left
    (E.meshCold_le_total hs₀ hsmax hη hηmax hK hd₀ hq n L U _) hH⟩

theorem HotLimitExtraction.meshColdChart_fiber_integrable (E : HotLimitExtraction S)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq : q < 2) (n : ℕ) (L U : ℤ)
    (x : ℝ × JetPrototype.Space) :
    Integrable (fun v => E.meshColdDensity n L U ((x.1,SheetMeasures.join x.2),v)) := by
  have hm : Measurable (fun v => E.meshColdDensity n L U ((x.1,SheetMeasures.join x.2),v)) :=
    (E.meshColdDensity_measurable hs₀ hsmax hη hηmax hK hd₀ hq n L U).comp
    (measurable_const.prodMk measurable_id)
  apply (S.rescaledColdDensity_integrable hs₀ hsmax hη hηmax hK hd₀ hq (E.indices n) x).mono'
    hm.aestronglyMeasurable
  filter_upwards [] with v
  have hb := E.meshColdDensity_bounds hs₀ hsmax hη hηmax hK hd₀ hq n L U
    ((x.1,SheetMeasures.join x.2),v)
  simpa only [Real.norm_of_nonneg hb.1,JetPeriodicDatum.spatialMap_join] using hb.2

theorem HotLimitExtraction.meshColdChartAverage_measurable (E : HotLimitExtraction S)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq : q < 2) (n : ℕ) (L U : ℤ)
    {ψ : Velocity → ℝ} (hψ : Measurable ψ) :
    Measurable (fun x : ℝ × JetPrototype.Space => E.meshColdChartAverage n L U x.1 ψ x.2) := by
  have hp : Measurable (fun z : (ℝ × JetPrototype.Space) × Velocity =>
      ((z.1.1,SheetMeasures.join z.1.2),z.2)) :=
    (measurable_fst.fst.prodMk (SheetMeasures.join.measurable.comp measurable_fst.snd)).prodMk measurable_snd
  have hm := (hψ.comp measurable_snd).mul
    ((E.meshColdDensity_measurable hs₀ hsmax hη hηmax hK hd₀ hq n L U).comp hp)
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

theorem HotLimitExtraction.meshColdChartAverage_global_bound (E : HotLimitExtraction S)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq : q < 2) (n : ℕ) (L U : ℤ)
    {B : ℝ} {ψ : Velocity → ℝ} (hψB : ∀ v, |ψ v| ≤ B) (x : ℝ × JetPrototype.Space) :
    |E.meshColdChartAverage n L U x.1 ψ x.2| ≤
      (B*(S.radius (E.indices n)*(2*(F.approximation (E.indices n)).amplitude)))*(∫ v, H q v) := by
  have hB : 0 ≤ B := (abs_nonneg (ψ 0)).trans (hψB 0)
  have hb := norm_integral_le_of_norm_le
    (f := fun v => ψ v*E.meshColdDensity n L U ((x.1,SheetMeasures.join x.2),v))
    ((integrable_H hq).const_mul (B*(S.radius (E.indices n)*(2*(F.approximation (E.indices n)).amplitude)))) ?_
  · simpa only [Real.norm_eq_abs,integral_const_mul,meshColdChartAverage] using hb
  · filter_upwards [] with v
    have hd := E.meshColdDensity_bounds hs₀ hsmax hη hηmax hK hd₀ hq n L U
      ((x.1,SheetMeasures.join x.2),v)
    have ht := S.rescaledColdDensity_bounds hs₀ hsmax hη hηmax hK hd₀ hq (E.indices n)
      ((x.1,JetPeriodicDatum.spatialMap (SheetMeasures.join x.2)),v)
    rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg hd.1]
    exact (mul_le_mul (hψB v) (hd.2.trans ht.2) hd.1 hB).trans_eq (by ring)

theorem HotLimitExtraction.meshColdChartAverage_integrable (E : HotLimitExtraction S)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq : q < 2) (n : ℕ) (L U : ℤ)
    {B : ℝ} {ψ : Velocity → ℝ} (hψ : Measurable ψ) (hψB : ∀ v, |ψ v| ≤ B)
    (ρ : Measure (ℝ × JetPrototype.Space)) [IsFiniteMeasure ρ] :
    Integrable (fun x => E.meshColdChartAverage n L U x.1 ψ x.2) ρ :=
  Integrable.of_bound
    (E.meshColdChartAverage_measurable hs₀ hsmax hη hηmax hK hd₀ hq n L U hψ).aestronglyMeasurable
    _ (ae_of_all _ (E.meshColdChartAverage_global_bound hs₀ hsmax hη hηmax hK hd₀ hq n L U hψB))

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # The escaped-mass estimate controls the error of actual cold averages -/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotLimitExtraction.eventually_cold_mesh_average_error (E : HotLimitExtraction S)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 ≤ α) (hαmax : α ≤ 1) (hγ : 0 ≤ γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1) (hq : q < 2)
    {a A δ R B : ℝ} (ha : 0 < a) (hA : ENNReal.ofReal A < E.horizon) (hδ : 0 < δ)
    {ψ : Velocity → ℝ} (hψ : Measurable ψ) (hψB : ∀ v, |ψ v| ≤ B) :
    ∀ᶠ n in atTop, ∀ t ∈ Icc a A, ∀ x : JetPrototype.Space,
      δ ≤ ‖x.1‖ → ‖SheetMeasures.join x‖ ≤ R →
      |S.coldAverage (E.indices n) ψ (t,x)-E.meshColdChartAverage n
        (GeometricMesh.index (δ/Real.exp η) η) (GeometricMesh.index R η) t ψ x| ≤
      (B*JetEscapedEnvelope.constant s₀ η α K d₀ (JetEscapedEnvelope.exponent 0)*
        (∫ v, H q v))*S.radius (E.indices n) := by
  let C := JetEscapedEnvelope.constant s₀ η α K d₀ (JetEscapedEnvelope.exponent 0)
  have hB : 0 ≤ B := (abs_nonneg (ψ 0)).trans (hψB 0)
  filter_upwards [E.eventually_mesh_gap hs₀ hsmax hη hηmax hK hd₀.le hq ha hδ hA,
    S.eventually_rescaledEscapedDensity_bound hs₀ hsmax hη hηmax hK hα hαmax hγ
      hd₀ hd₀max hsmall hq E.indices_strict E.horizon_limit ha hA R] with n hgap hesc
  intro t ht x hxδ hxR
  let L := GeometricMesh.index (δ/Real.exp η) η
  let U := GeometricMesh.index R η
  have hf := (S.rescaledColdDensity_integrable hs₀ hsmax hη hηmax hK hd₀.le hq
    (E.indices n) (t,x)).bdd_mul hψ.aestronglyMeasurable (ae_of_all _ hψB)
  have hg := (E.meshColdChart_fiber_integrable hs₀ hsmax hη hηmax hK hd₀.le hq n L U
    (t,x)).bdd_mul hψ.aestronglyMeasurable (ae_of_all _ hψB)
  change |(∫ v, ψ v*S.rescaledColdDensity (E.indices n) ((t,x),v))-
    (∫ v, ψ v*E.meshColdDensity n L U ((t,SheetMeasures.join x),v))| ≤ _
  rw [← integral_sub hf hg]
  have hb := norm_integral_le_of_norm_le
    (f := fun v => ψ v*S.rescaledColdDensity (E.indices n) ((t,x),v)-
      ψ v*E.meshColdDensity n L U ((t,SheetMeasures.join x),v))
    ((integrable_H hq).const_mul (B*(C*S.radius (E.indices n)))) ?_
  · rw [Real.norm_eq_abs,integral_const_mul] at hb
    exact hb.trans_eq (by dsimp only [C]; ring)
  · filter_upwards [] with v
    have hz : ((t,SheetMeasures.join x),v) ∈ meshWindowSet a A δ R := by
      refine ⟨⟨⟨ht,?_⟩,mem_univ _⟩,?_⟩
      · simpa only [Metric.mem_closedBall,dist_zero_right] using hxR
      · have he := congrArg Prod.fst (JetPeriodicDatum.spatialMap_join x)
        change transverse (SheetMeasures.join x) = x.1 at he
        change δ ≤ ‖transverse (SheetMeasures.join x)‖
        rw [he]
        exact hxδ
    have hgv := hgap ((t,SheetMeasures.join x),v) hz
    simp only [JetPeriodicDatum.spatialMap_join] at hgv
    have hev := hesc ((t,SheetMeasures.join x),v) ht hxR
    rw [← mul_sub,Real.norm_eq_abs,abs_mul,abs_of_nonneg hgv.1]
    have hd := hgv.2.trans ((le_abs_self _).trans hev)
    exact (mul_le_mul (hψB v) hd hgv.1 hB).trans_eq (by dsimp only [C]; ring)

theorem HotLimitExtraction.cold_mesh_average_L1_limit (E : HotLimitExtraction S)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 ≤ α) (hαmax : α ≤ 1) (hγ : 0 ≤ γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1) (hq : q < 2)
    {a A δ R B : ℝ} (ha : 0 < a) (hA : ENNReal.ofReal A < E.horizon) (hδ : 0 < δ)
    {ψ : Velocity → ℝ} (hψ : Measurable ψ) (hψB : ∀ v, |ψ v| ≤ B)
    (ρ : Measure (ℝ × JetPrototype.Space)) [IsFiniteMeasure ρ]
    (hρ : ∀ᵐ z ∂ρ, z.1 ∈ Icc a A ∧ δ ≤ ‖z.2.1‖ ∧ ‖SheetMeasures.join z.2‖ ≤ R) :
    Tendsto (fun n => ∫ z, |S.coldAverage (E.indices n) ψ z-E.meshColdChartAverage n
      (GeometricMesh.index (δ/Real.exp η) η) (GeometricMesh.index R η) z.1 ψ z.2| ∂ρ)
      atTop (𝓝 0) := by
  let C := B*JetEscapedEnvelope.constant s₀ η α K d₀ (JetEscapedEnvelope.exponent 0)*(∫ v, H q v)
  have hlim : Tendsto (fun n => ρ.real univ*(C*S.radius (E.indices n))) atTop (𝓝 0) := by
    simpa only [Function.comp_def,mul_zero] using
      (((S.radius_tendsto_zero hs₀).comp E.indices_strict.tendsto_atTop).const_mul C).const_mul (ρ.real univ)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall (fun _ => integral_nonneg (fun _ => abs_nonneg _)))
  filter_upwards [E.eventually_cold_mesh_average_error hs₀ hsmax hη hηmax hK hα hαmax hγ
    hd₀ hd₀max hsmall hq ha hA hδ hψ hψB] with n hn
  have hi := ((S.coldAverage_integrable hs₀ hsmax hη hηmax hK hd₀.le hq (E.indices n) hψ hψB ρ).sub
    (E.meshColdChartAverage_integrable hs₀ hsmax hη hηmax hK hd₀.le hq n
      (GeometricMesh.index (δ/Real.exp η) η) (GeometricMesh.index R η) hψ hψB ρ)).abs
  calc
    _ ≤ ∫ _z, C*S.radius (E.indices n) ∂ρ := integral_mono_ae hi (integrable_const _) (by
      filter_upwards [hρ] with z hz
      exact hn z.1 hz.1 z.2 hz.2.1 hz.2.2)
    _ = _ := by rw [integral_const,smul_eq_mul]

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # Full cold-average convergence on compact cylinders away from the axis -/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace BoltzmannNonuniqueness

theorem SheetMeasures.norm_join_le_add (x : VelocityWeight.Transverse × ℝ) :
    ‖SheetMeasures.join x‖ ≤ ‖x.1‖+|x.2| := by
  have he := SheetMeasures.norm_join_sq x
  nlinarith [norm_nonneg (SheetMeasures.join x),norm_nonneg x.1,abs_nonneg x.2,sq_abs x.2]

namespace JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotLimitExtraction.cold_away_axis_weak_limit (E : HotLimitExtraction S)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1/4) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq : q < 2) {a A δ R : ℝ} (ha : 0 < a) (hA : ENNReal.ofReal A < E.horizon)
    (hδ : 0 < δ) (hR : 0 ≤ R)
    (Ω₁ : Set VelocityWeight.Transverse) (hΩ₁ : IsCompact Ω₁)
    (hlo : ∀ y ∈ Ω₁, δ ≤ ‖y‖) (hhi : ∀ y ∈ Ω₁, ‖y‖ ≤ R)
    (Ω₂ : Set ℝ) (hΩ₂ : IsCompact Ω₂) (hax : ∀ z ∈ Ω₂, |z| ≤ R)
    {B : ℝ} {ψ : Velocity → ℝ} (hψ : Continuous ψ) (hψB : ∀ v, |ψ v| ≤ B) :
    Published.WeakL1Converges
      ((volume.restrict (Icc a A)).prod (JetPrototype.spaceVolume.restrict (Ω₁ ×ˢ Ω₂)))
      (fun n => S.coldAverage (E.indices n) ψ)
      (fun z => ∫ v, ψ v ∂E.background (max 0 z.1) z.2) := by
  let ρ := (volume.restrict (Icc a A)).prod (JetPrototype.spaceVolume.restrict (Ω₁ ×ˢ Ω₂))
  let _ : IsFiniteMeasure (JetPrototype.spaceVolume.restrict (Ω₁ ×ˢ Ω₂)) :=
    isFiniteMeasure_restrict.mpr (hΩ₁.prod hΩ₂).measure_lt_top.ne
  have hα1 : α ≤ 1 := hαmax.trans (by norm_num)
  have hw := E.mesh_cold_spacetime_background_limit hs₀ hsmax hη hηmax hK hα hαmax hγ hd₀ hd₀max
    hsmall hq (R := 2*R) ha hA hδ Ω₁ hΩ₁ hlo (fun y hy => (hhi y hy).trans (by linarith))
    Ω₂ hΩ₂ hψ hψB
  apply hw.of_integral_abs_sub
    (fun n => E.meshColdChartAverage_integrable hs₀ hsmax hη hηmax hK hd₀.le hq n
      (GeometricMesh.index (δ/Real.exp η) η) (GeometricMesh.index (2*R) η) hψ.measurable hψB ρ)
    (fun n => S.coldAverage_integrable hs₀ hsmax hη hηmax hK hd₀.le hq (E.indices n) hψ.measurable hψB ρ)
  apply E.cold_mesh_average_L1_limit hs₀ hsmax hη hηmax hK hα.le hα1 hγ.le
    hd₀ hd₀max hsmall hq ha hA hδ hψ.measurable hψB ρ
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Icc),
    Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem (hΩ₁.prod hΩ₂).measurableSet)] with z ht hx
  exact ⟨ht,hlo _ hx.1,(SheetMeasures.norm_join_le_add z.2).trans (by
    have hy := hhi _ hx.1
    have hz := hax _ hx.2
    linarith)⟩

end JetCopyDatum.AttainedCapSequence
end BoltzmannNonuniqueness

end

end

end OAI
