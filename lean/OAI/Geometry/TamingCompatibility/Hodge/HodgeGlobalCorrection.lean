import Mathlib
import OAI.Geometry.TamingCompatibility.Hodge.HodgeKernelSeriesCore
import OAI.Geometry.TamingCompatibility.Hodge.HodgeKernelAction

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.VolterraKernel
open MeasureTheory Set
variable {X B : Type*} [MeasurableSpace X] [PseudoMetricSpace X] [NormedRing B]
  (μ : Measure X)
lemma HeatBound.mono_time {N : ℕ} {S T A : ℝ} {K : Kernel (X := X) (B := B)}
    (h : HeatBound μ N T A K) (hST : S ≤ T) : HeatBound μ N S A K := by
  have hsub : Ioc 0 S ⊆ Ioc 0 T := Ioc_subset_Ioc_right hST
  exact ⟨h.measurable,h.nonneg,fun t ht => h.sup t (hsub ht),
    fun t ht => h.row_int t (hsub ht),fun t ht => h.row t (hsub ht),
    fun t ht => h.col_int t (hsub ht),fun t ht => h.col t (hsub ht)⟩
end TamingCompatibility.GeometricHilbert.VolterraKernel

namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldVolume ManifoldLocalization HodgeFrame Set MeasureTheory
open scoped Manifold ContDiff Topology
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [ConnectedSpace X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (hs : IsSmooth α) (ht : Tames α J)
  (A : FiniteCharts X) (D : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hD : ∀ p, tsupport (A.partition p) ⊆ (D p).source)

def globalCorrection (T : ℝ) :=
  KernelSeries.correction (geometricVolume A J α) T (globalResidual J α ht A D)

def globalError (T : ℝ) := VolterraKernel.convolution (geometricVolume A J α)
  (globalLeading J α ht A D) (globalCorrection J α ht A D T)

def globalCandidate (T t : ℝ) (x y : X) :=
  globalLeading J α ht A D t x y + globalError J α ht A D T t x y

include hD in
lemma globalCorrection_bound (n : ℕ) :
    let := geometricMetricSpace J α hs ht
  let := geometricVolume_finite A J α hs ht
    ∃ T L C : ℝ, 0 < T ∧
      VolterraKernel.HeatBound (geometricVolume A J α) n T L (globalLeading J α ht A D) ∧
      VolterraKernel.HeatBound (geometricVolume A J α) n T C (globalCorrection J α ht A D T) ∧
      (∀ t ∈ Ioc 0 T, ∀ x y, globalResidual J α ht A D t x y +
        globalCorrection J α ht A D T t x y +
        VolterraKernel.convolution (geometricVolume A J α) (globalResidual J α ht A D)
          (globalCorrection J α ht A D T) t x y = 0) := by
  dsimp only
  let := geometricMetricSpace J α hs ht
  let := geometricVolume_finite A J α hs ht
  obtain ⟨L,hL⟩ := globalLeading_heatBound J α hs ht A D hD n 1
  obtain ⟨R,hR⟩ := globalResidual_heatBound J α hs ht A D hD n 1
  let T := (8*(R+1))⁻¹
  have hp : 0 < 8*(R+1) := by have := hR.nonneg; positivity
  have hT : 0 < T := inv_pos.mpr hp
  have hT1 : T ≤ 1 := (inv_le_one₀ hp).mpr (by linarith [hR.nonneg])
  have hq : 4*T*R < 1 := by
    dsimp [T]
    rw [show 4*(8*(R+1))⁻¹*R = (4*R)/(8*(R+1)) by ring]
    exact (div_lt_one hp).mpr (by linarith [hR.nonneg])
  have hR' := hR.mono_time _ hT1
  refine ⟨T,L,R/(1-4*T*R),hT,hL.mono_time _ hT1,?_,?_⟩
  · exact KernelSeries.correction_heatBound (geometricVolume A J α) n hT.le _ hR' hq
  · intro t htp x y
    exact KernelSeries.correction_equation (geometricVolume A J α) n hT.le _ hR' hq htp x y

include hD in

lemma globalError_bound (n : ℕ) :
    let := geometricMetricSpace J α hs ht
  let := geometricVolume_finite A J α hs ht
    ∃ T C : ℝ, 0 < T ∧ 0 ≤ C ∧
      VolterraKernel.MeasurableKernel (globalError J α ht A D T) ∧
      (∀ t ∈ Ioc 0 T, ∀ x y,
        VolterraBounds.weight n t x y*‖globalError J α ht A D T t x y‖ ≤ C/t) ∧
      (∀ t ∈ Ioc 0 T, ∀ x,
        Integrable (fun y => VolterraBounds.weight n t x y*‖globalError J α ht A D T t x y‖) (geometricVolume A J α) ∧
        (∫ y, VolterraBounds.weight n t x y*‖globalError J α ht A D T t x y‖ ∂geometricVolume A J α) ≤ t*C) ∧
      (∀ t ∈ Ioc 0 T, ∀ y,
        Integrable (fun x => VolterraBounds.weight n t x y*‖globalError J α ht A D T t x y‖) (geometricVolume A J α) ∧
        (∫ x, VolterraBounds.weight n t x y*‖globalError J α ht A D T t x y‖ ∂geometricVolume A J α) ≤ t*C) := by
  dsimp only
  let := geometricMetricSpace J α hs ht
  let := geometricVolume_finite A J α hs ht
  obtain ⟨T,L,C,hT,hL,hC,-⟩ := globalCorrection_bound J α hs ht A D hD n
  have hn : 0 ≤ L*C := mul_nonneg hL.nonneg hC.nonneg
  refine ⟨T,4*L*C,hT,by nlinarith,
    VolterraKernel.convolution_measurable _ _ _ hL.measurable hC.measurable,?_,?_,?_⟩
  · intro t htp x y
    exact (VolterraKernel.convolution_sup _ n _ _ hL hC htp x y).2
  · intro t htp x
    obtain ⟨hi,hb⟩ := VolterraKernel.convolution_row _ n _ _ hL hC htp x
    exact ⟨hi,hb.trans (by nlinarith [mul_nonneg htp.1.le hn])⟩
  · intro t htp y
    obtain ⟨hi,hb⟩ := VolterraKernel.convolution_col _ n _ _ hL hC htp y
    exact ⟨hi,hb.trans (by nlinarith [mul_nonneg htp.1.le hn])⟩

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.KernelL2
open MeasureTheory Set Filter
variable {X F : Type*} [MeasurableSpace X] [PseudoMetricSpace X] [BorelSpace X]
  [SecondCountableTopology X] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
variable (μ : Measure X) [IsFiniteMeasure μ]
variable (K L : ℝ → X → X → F →L[ℝ] F) {T A C : ℝ}
  (hK : VolterraKernel.HeatBound μ 0 T A K) (hL : VolterraKernel.HeatBound μ 0 T C L)

include hK hL in
omit [BorelSpace X] in
lemma spatial_action {t s : ℝ} (ht : t ∈ Ioc 0 T) (hs : s ∈ Ioo 0 t)
    (v : X → F) (hvm : StronglyMeasurable v) {V : ℝ} (_hV : 0 ≤ V)
    (hv : ∀ y, ‖v y‖ ≤ V) (x : X) :
    action μ (VolterraKernel.spatial μ K L t s) v x =
      action μ (K (t-s)) (action μ (L s) v) x := by
  have ha : t-s ∈ Ioc 0 T := ⟨sub_pos.mpr hs.2,(sub_le_self _ hs.1.le).trans ht.2⟩
  have hb : s ∈ Ioc 0 T := ⟨hs.1,hs.2.le.trans ht.2⟩
  have hKi := hK.row_int (t-s) ha x
  have hLi (z : X) := hL.row_int s hb z
  have hLb (z : X) := hL.row s hb z
  have hLs (z y : X) := hL.sup s hb z y
  simp only [VolterraBounds.weight,pow_zero,one_mul] at hKi hLi hLb hLs
  have hKm : StronglyMeasurable (fun z => K (t-s) x z) :=
    hK.measurable.comp_measurable (measurable_const.prodMk (measurable_const.prodMk measurable_id))
  have hLm := VolterraKernel.kernel_section L hL.measurable s
  have hn := SchurIntegration.product_integrable μ μ (g := fun z y => ‖L s z y‖) hKi (fun _ => norm_nonneg _)
    hLm.norm (fun _ _ => norm_nonneg _) hLi hLb
  have hpm : StronglyMeasurable (fun p : X × X => K (t-s) x p.1 (L s p.1 p.2 (v p.2))) :=
    (continuous_fst.clm_apply continuous_snd).comp_stronglyMeasurable
      ((hKm.comp_measurable measurable_fst).prodMk (applied_measurable (L s) hLm v hvm))
  have hpi : Integrable (fun p : X × X => K (t-s) x p.1 (L s p.1 p.2 (v p.2))) (μ.prod μ) := by
    apply (hn.mul_const V).mono' hpm.aestronglyMeasurable
    filter_upwards [] with p
    exact (ContinuousLinearMap.le_opNorm _ _).trans ((mul_le_mul_of_nonneg_left
      ((ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul_of_nonneg_left (hv _) (norm_nonneg _))) (norm_nonneg _)).trans_eq (by ring))
  have hz (y : X) : Integrable (fun z => K (t-s) x z * L s z y) μ := by
    apply (hKi.mul_const (C/s^2)).mono'
      (VolterraKernel.product_section K L hK.measurable hL.measurable t s x y).aestronglyMeasurable
    filter_upwards [] with z
    exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left (hLs z y) (norm_nonneg _))
  calc
    _ = ∫ y, ∫ z, K (t-s) x z (L s z y (v y)) ∂μ ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with y
      exact ContinuousLinearMap.integral_apply (hz y) (v y)
    _ = ∫ z, ∫ y, K (t-s) x z (L s z y (v y)) ∂μ ∂μ := (integral_integral_swap hpi).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with z
      exact (K (t-s) x z).integral_comp_comm (action_integrable μ (L s) hLm v hvm hv z (hLi z))

include hK hL in
lemma convolution_action {t : ℝ} (ht : t ∈ Ioc 0 T)
    (v : X → F) (hvm : StronglyMeasurable v) {V : ℝ} (hV : 0 ≤ V)
    (hv : ∀ y, ‖v y‖ ≤ V) (x : X) :
    action μ (VolterraKernel.convolution μ K L t) v x =
      ∫ s in Ioo 0 t, action μ (K (t-s)) (action μ (L s) v) x := by
  have hsm : StronglyMeasurable (fun p : ℝ × X => VolterraKernel.spatial μ K L t p.1 x p.2) :=
    (VolterraKernel.spatial_measurable μ K L hK.measurable hL.measurable).comp_measurable
      (show Measurable (fun p : ℝ × X => ((t,x,p.2),p.1)) by fun_prop)
  have hm : StronglyMeasurable (fun p : ℝ × X => VolterraKernel.spatial μ K L t p.1 x p.2 (v p.2)) :=
    (continuous_fst.clm_apply continuous_snd).comp_stronglyMeasurable
      (hsm.prodMk (hvm.comp_measurable measurable_snd))
  have hrow (s : ℝ) (hs : s ∈ Ioo 0 t) := VolterraKernel.spatial_row μ 0 K L hK hL ht hs x
  simp only [VolterraBounds.weight,pow_zero,one_mul] at hrow
  have hi := SchurIntegration.integral_row_bound_ae (volume.restrict (Ioo 0 t)) μ
    (integrable_const (A*C*V)) (fun s y => VolterraKernel.spatial μ K L t s x y (v y))
    hm.aestronglyMeasurable
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
      apply ((hrow s hs).1.mul_const V).mono'
        ((hm.comp_measurable (measurable_const.prodMk measurable_id)).aestronglyMeasurable)
      exact Eventually.of_forall fun y => (ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul_of_nonneg_left (hv y) (norm_nonneg _)))
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
      calc
        _ ≤ ∫ y, ‖VolterraKernel.spatial μ K L t s x y‖*V ∂μ := by
          apply integral_mono_ae
            (((hrow s hs).1.mul_const V).mono'
              ((hm.comp_measurable (measurable_const.prodMk measurable_id)).aestronglyMeasurable)
              (Eventually.of_forall fun y => (ContinuousLinearMap.le_opNorm _ _).trans
                (mul_le_mul_of_nonneg_left (hv y) (norm_nonneg _)))).norm
            ((hrow s hs).1.mul_const V)
          exact Eventually.of_forall fun y => (ContinuousLinearMap.le_opNorm _ _).trans
            (mul_le_mul_of_nonneg_left (hv y) (norm_nonneg _))
        _ = (∫ y, ‖VolterraKernel.spatial μ K L t s x y‖ ∂μ)*V := integral_mul_const _ _
        _ ≤ _ := mul_le_mul_of_nonneg_right (hrow s hs).2 hV)
  calc
    _ = ∫ y, (∫ s in Ioo 0 t, VolterraKernel.spatial μ K L t s x y (v y)) ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with y
      exact ContinuousLinearMap.integral_apply (VolterraKernel.convolution_sup μ 0 K L hK hL ht x y).1 (v y)
    _ = ∫ s in Ioo 0 t, ∫ y, VolterraKernel.spatial μ K L t s x y (v y) ∂μ :=
      (integral_integral_swap hi.1).symm
    _ = _ := by
      apply setIntegral_congr_fun measurableSet_Ioo
      intro s hs
      exact spatial_action μ K L hK hL ht hs v hvm hV hv x

end TamingCompatibility.GeometricHilbert.KernelL2

end
end

end

end OAI
