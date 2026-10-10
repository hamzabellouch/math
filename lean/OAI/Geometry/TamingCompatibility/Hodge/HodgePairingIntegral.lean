import Mathlib
import OAI.Geometry.TamingCompatibility.DifferentialForms.SmoothingKernel
import OAI.Geometry.TamingCompatibility.HeatFlow.HodgeHeatEvaluation
import OAI.Geometry.TamingCompatibility.Hodge.HodgeGammaSplit
import OAI.Geometry.TamingCompatibility.Hodge.HodgeSmoothSpatial

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart ManifoldVolume Set Filter MeasureTheory
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable {A : FiniteCharts X} {J : AlmostComplexStructure X} {α : TwoForm X}
  {hs : IsSmooth α} {ht : Tames α J}
  {D : ∀ p : A.centers, HodgeChart.Data J α ht p.val}
  {hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source}
omit [T2Space X] in
lemma hodgeRegularization_symmetric (r : ℝ) (u v : L2 A J α hs ht true) :
    ⟪hodgeRegularization A J α hs ht r u,v⟫ = ⟪u,hodgeRegularization A J α hs ht r v⟫ := by
  have hsym (f g : L2 A J α hs ht true) :
      ⟪hodgeResolvent A J α hs ht r f,g⟫ = ⟪f,hodgeResolvent A J α hs ht r g⟫ :=
    hodgeResolvent_symmetric A J α hs ht r f g
  change ⟪hodgeResolvent A J α hs ht r (hodgeResolvent A J α hs ht r
    (hodgeResolvent A J α hs ht r u)),v⟫ =
    ⟪u,hodgeResolvent A J α hs ht r (hodgeResolvent A J α hs ht r
    (hodgeResolvent A J α hs ht r v))⟫
  rw [hsym,hsym,hsym]

namespace HodgeSmoothingCover
variable {r : ℝ} {hr : 0 < r} (C : HodgeSmoothingCover A J α hs ht D hD r hr)

def pairingEvaluationVector (b : PreL2 A J α hs ht true) (x : X) : L2 A J α hs ht true :=
  (C.pairingEvaluation b x).adjoint 1

lemma pairingEvaluationVector_continuous (b : PreL2 A J α hs ht true) :
    Continuous (C.pairingEvaluationVector b) :=
  ((ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := L2 A J α hs ht true) (F := ℝ)).continuous.comp
    (C.pairingEvaluation_continuous b)).clm_apply continuous_const

lemma pairingEvaluationVector_integrable (b : PreL2 A J α hs ht true) :
    Integrable (C.pairingEvaluationVector b) (geometricVolume A J α) := by
  let := geometricVolume_finite A J α hs ht
  exact (C.pairingEvaluationVector_continuous b).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

lemma pairingEvaluationVector_pair (b : PreL2 A J α hs ht true) (f : L2 A J α hs ht true) :
    ⟪∫ x, C.pairingEvaluationVector b x ∂geometricVolume A J α,f⟫ =
      ∫ x, C.pairingEvaluation b x f ∂geometricVolume A J α := by
  have h := HilbertKernel.regularize_pair (geometricVolume A J α) (C.pairingEvaluation b)
    (fun _ => (1:ℝ)) (C.pairingEvaluationVector_integrable b) f
  simpa only [HilbertKernel.regularize,pairingEvaluationVector,Real.inner_apply,one_mul,mul_one] using h

lemma pairingEvaluationVector_integral (b : PreL2 A J α hs ht true) :
    ∫ x, C.pairingEvaluationVector b x ∂geometricVolume A J α =
      hodgeRegularization A J α hs ht r (smoothL2 A J α hs ht true b) := by
  apply ext_inner_right ℝ
  intro f
  refine (smoothL2_dense A J α hs ht true).induction_on f
    (_root_.isClosed_eq (continuous_const.inner continuous_id) (continuous_const.inner continuous_id)) ?_
  intro a
  obtain ⟨c,hc⟩ := hodgeRegularization_smooth A J α hs ht D hD r hr a
  rw [C.pairingEvaluationVector_pair,hodgeRegularization_symmetric,← hc,(smoothL2 A J α hs ht true).inner_map_map,preL2_inner]
  unfold l2Pairing
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => C.pairingEvaluation_smooth b x _ c hc.symm

lemma pairingEvaluationVector_gram (a b : PreL2 A J α hs ht true) :
    (∫ x, ∫ y, ⟪C.pairingEvaluationVector b x,C.pairingEvaluationVector a y⟫
      ∂geometricVolume A J α ∂geometricVolume A J α) =
      ⟪(hodgeRegularization A J α hs ht r ^ 2) (smoothL2 A J α hs ht true a),
        smoothL2 A J α hs ht true b⟫ := by
  have h := HilbertKernel.regularize_kernel_pair (geometricVolume A J α) (geometricVolume A J α)
    (C.pairingEvaluation b) (C.pairingEvaluation a) (fun _ => (1:ℝ)) (fun _ => (1:ℝ))
    (C.pairingEvaluationVector_integrable b) (C.pairingEvaluationVector_integrable a)
  simp only [HilbertKernel.kernel_inner] at h
  change ⟪∫ x, C.pairingEvaluationVector b x ∂geometricVolume A J α,
    ∫ y, C.pairingEvaluationVector a y ∂geometricVolume A J α⟫ =
      ∫ x, ∫ y, ⟪C.pairingEvaluationVector b x,C.pairingEvaluationVector a y⟫
        ∂geometricVolume A J α ∂geometricVolume A J α at h
  rw [← h,C.pairingEvaluationVector_integral,C.pairingEvaluationVector_integral,real_inner_comm]
  rw [← hodgeRegularization_symmetric]
  rfl

end HodgeSmoothingCover
end TamingCompatibility.GeometricHilbert

end
end

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization Set MeasureTheory
open scoped Manifold ContDiff RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p, tsupport (A.partition p) ⊆ (D p).source)

lemma hodgeGammaShift_integrable {T : ℝ} (hT : 0 ≤ T) (r δ : ℝ)
    (f : L2 A J α hs ht true) :
    IntegrableOn (fun s : ℝ => hodgeGammaWeight s •
      hodgeSpectralHeat A J α hs ht D hD (r^2*s-δ) f) (Ioi (T/r^2)) := by
  have hc : Continuous (fun s : ℝ => hodgeGammaWeight s •
      hodgeSpectralHeat A J α hs ht D hD (r^2*s-δ) f) := hodgeGammaWeight_continuous.smul
    ((hodgeSpectralHeat_continuous A J α hs ht D hD f).comp (by fun_prop))
  have hsub : Ioi (T/r^2) ⊆ Ioi (0:ℝ) := fun _ h => (div_nonneg hT (sq_nonneg r)).trans_lt h
  apply ((hodgeGammaWeight_integrable.mono_set hsub).mul_const ‖f‖).mono' hc.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hsp
  have hs0 : 0 ≤ s := (hsub hsp).le
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (hodgeGammaWeight_nonneg hs0)]
  exact mul_le_mul_of_nonneg_left (hodgeSpectralHeat_norm_le A J α hs ht D hD _ f)
    (hodgeGammaWeight_nonneg hs0)

def hodgeGammaShiftLinear (T : ℝ) (hT : 0 ≤ T) (r δ : ℝ) :
    L2 A J α hs ht true →ₗ[ℝ] L2 A J α hs ht true where
  toFun f := (1/120 : ℝ) • ∫ s : ℝ in Ioi (T/r^2), hodgeGammaWeight s •
    hodgeSpectralHeat A J α hs ht D hD (r^2*s-δ) f
  map_add' f g := by
    simp only [map_add,smul_add]
    rw [integral_add (hodgeGammaShift_integrable A J α hs ht D hD hT r δ f)
      (hodgeGammaShift_integrable A J α hs ht D hD hT r δ g),smul_add]
  map_smul' c f := by
    simp only [map_smul,RingHom.id_apply,smul_comm (hodgeGammaWeight _) c]
    rw [integral_smul,smul_comm]

lemma hodgeGammaShiftLinear_bound (T : ℝ) (hT : 0 ≤ T) (r δ : ℝ)
    (f : L2 A J α hs ht true) :
    ‖hodgeGammaShiftLinear A J α hs ht D hD T hT r δ f‖ ≤
      (1/120 : ℝ) * HodgeKernelBounds.gammaTail (T/r^2)*‖f‖ := by
  have hsub : Ioi (T/r^2) ⊆ Ioi (0:ℝ) := fun _ h => (div_nonneg hT (sq_nonneg r)).trans_lt h
  have hi := hodgeGammaShift_integrable A J α hs ht D hD hT r δ f
  have hw := hodgeGammaWeight_integrable.mono_set hsub
  have hh : ‖∫ s : ℝ in Ioi (T/r^2), hodgeGammaWeight s •
      hodgeSpectralHeat A J α hs ht D hD (r^2*s-δ) f‖ ≤ HodgeKernelBounds.gammaTail (T/r^2)*‖f‖ := by
    calc
      _ ≤ ∫ s : ℝ in Ioi (T/r^2), ‖hodgeGammaWeight s •
          hodgeSpectralHeat A J α hs ht D hD (r^2*s-δ) f‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ s : ℝ in Ioi (T/r^2), hodgeGammaWeight s*‖f‖ := by
        apply integral_mono_ae hi.norm (hw.mul_const _)
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hsp
        have hs0 : 0 ≤ s := (hsub hsp).le
        rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (hodgeGammaWeight_nonneg hs0)]
        exact mul_le_mul_of_nonneg_left (hodgeSpectralHeat_norm_le A J α hs ht D hD _ f)
          (hodgeGammaWeight_nonneg hs0)
      _ = _ := by rw [integral_mul_const]; rfl
  change ‖(1/120 : ℝ) • (∫ s : ℝ in Ioi (T/r^2), hodgeGammaWeight s •
    hodgeSpectralHeat A J α hs ht D hD (r^2*s-δ) f)‖ ≤ _
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos (by norm_num : (0:ℝ)<1/120)]
  exact (mul_le_mul_of_nonneg_left hh (by norm_num)).trans_eq (by ring)

def hodgeGammaShift (T : ℝ) (hT : 0 ≤ T) (r δ : ℝ) :
    L2 A J α hs ht true →L[ℝ] L2 A J α hs ht true :=
  (hodgeGammaShiftLinear A J α hs ht D hD T hT r δ).mkContinuous
    ((1/120 : ℝ)*HodgeKernelBounds.gammaTail (T/r^2))
    (hodgeGammaShiftLinear_bound A J α hs ht D hD T hT r δ)

lemma hodgeGammaTailAction_factor {T r ρ : ℝ} (hT : 0 ≤ T) (hr : 0 < r)
    (hρ : 2*ρ^2 ≤ T) (f : L2 A J α hs ht true) :
    hodgeGammaTailAction A J α hs ht D hD T r f =
      hodgeSpectralHeat A J α hs ht D hD (ρ^2)
        (hodgeGammaShift A J α hs ht D hD T hT r (2*ρ^2)
          (hodgeSpectralHeat A J α hs ht D hD (ρ^2) f)) := by
  let H := hodgeSpectralHeat A J α hs ht D hD (ρ^2)
  have hi := hodgeGammaShift_integrable A J α hs ht D hD hT r (2*ρ^2) (H f)
  change (1/120 : ℝ) • _ = H ((1/120 : ℝ) • _)
  rw [map_smul,← H.integral_comp_comm hi]
  congr 1
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hsp
  rw [map_smul]
  congr 1
  have hTime : 2*ρ^2 ≤ r^2*s := hρ.trans (by
    have hh := ((div_lt_iff₀ (sq_pos_of_pos hr)).mp hsp).le
    simpa only [mul_comm] using hh)
  have he : hodgeSpectralHeat A J α hs ht D hD (r^2*s) =
      H * hodgeSpectralHeat A J α hs ht D hD (r^2*s-2*ρ^2) * H := by
    rw [← hodgeSpectralHeat_add A J α hs ht D hD (ρ^2) (r^2*s-2*ρ^2)
      (sq_nonneg _) (sub_nonneg.mpr hTime),
      ← hodgeSpectralHeat_add A J α hs ht D hD (ρ^2+(r^2*s-2*ρ^2)) (ρ^2)
        (by nlinarith [sq_nonneg ρ]) (sq_nonneg _)]
    congr 1
    ring
  exact congrArg (fun F : L2 A J α hs ht true →L[ℝ] L2 A J α hs ht true => F f) he

variable [T2Space X]
attribute [local instance] unitMeasurable unitBorel unitT2
namespace HodgeSmoothingCover
variable {A J α hs ht D hD} {ρ : ℝ} {hρ : 0 < ρ}
  (C : HodgeSmoothingCover A J α hs ht D hD ρ hρ)
  (g : ContMDiffRiemannianMetric Model ∞ Space (TangentSpace Model : X → Type))

def gammaTailKernel (T : ℝ) (hT : 0 ≤ T) (r : ℝ) (u v : MetricUnit g) : ℝ :=
  ⟪C.heatEvaluationVector g u,
    hodgeGammaShift A J α hs ht D hD T hT r (2*ρ^2) (C.heatEvaluationVector g v)⟫

lemma gammaTailKernel_continuous (T : ℝ) (hT : 0 ≤ T) (r : ℝ) :
    Continuous (fun p : MetricUnit g × MetricUnit g => C.gammaTailKernel g T hT r p.1 p.2) :=
  ((C.heatEvaluationVector_continuous g).comp continuous_fst).inner
    ((hodgeGammaShift A J α hs ht D hD T hT r (2*ρ^2)).continuous.comp
      ((C.heatEvaluationVector_continuous g).comp continuous_snd))

lemma gammaTailKernel_bound (T : ℝ) (hT : 0 ≤ T) (r : ℝ) (u v : MetricUnit g) :
    |C.gammaTailKernel g T hT r u v| ≤
      (1/120 : ℝ)*HodgeKernelBounds.gammaTail (T/r^2)*
        ‖C.heatEvaluationVector g u‖*‖C.heatEvaluationVector g v‖ := by
  apply (abs_real_inner_le_norm _ _).trans
  have hh := mul_le_mul_of_nonneg_left
    (hodgeGammaShiftLinear_bound A J α hs ht D hD T hT r (2*ρ^2) (C.heatEvaluationVector g v))
    (norm_nonneg (C.heatEvaluationVector g u))
  exact hh.trans_eq (by ring)

lemma gammaTailKernel_uniform (T : ℝ) (hT : 0 ≤ T) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ r : ℝ, ∀ u v : MetricUnit g,
      |C.gammaTailKernel g T hT r u v| ≤ (1/120 : ℝ)*HodgeKernelBounds.gammaTail (T/r^2)*B^2 := by
  obtain ⟨B,hB⟩ := isCompact_univ.exists_bound_of_continuousOn
    (C.heatEvaluationVector_continuous g).continuousOn
  let M := max B 0
  have hM : 0 ≤ M := le_max_right _ _
  have hb (u : MetricUnit g) : ‖C.heatEvaluationVector g u‖ ≤ M := (hB u (mem_univ _)).trans (le_max_left _ _)
  refine ⟨M,hM,fun r u v => (C.gammaTailKernel_bound g T hT r u v).trans ?_⟩
  have htail : 0 ≤ HodgeKernelBounds.gammaTail (T/r^2) := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hsp
    exact mul_nonneg (Real.exp_pos _).le (pow_nonneg ((div_nonneg hT (sq_nonneg r)).trans_lt hsp).le _)
  have hh := mul_le_mul_of_nonneg_left (mul_le_mul (hb u) (hb v) (norm_nonneg _) hM)
    (mul_nonneg (by norm_num : (0:ℝ) ≤ 1/120) htail)
  simpa only [sq,mul_assoc] using hh

end HodgeSmoothingCover
end TamingCompatibility.GeometricHilbert

end
end

end

end OAI
