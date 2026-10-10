import OAI.Geometry.Perimeter.Regularity.SurfaceGradientComp

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
open scoped Topology ENNReal NNReal
open scoped ENNReal Topology ContDiff Pointwise
open scoped Topology ENNReal ContDiff
namespace RPISingularHarnack

theorem perimeter_eq_of_ae {n : ℕ} {E F : Set (Euc n)}
    (hEF : E =ᵐ[volume] F) (U : Set (Euc n)) : perimeter E U = perimeter F U := by
  unfold perimeter
  rw [Measure.restrict_congr_set hEF]

theorem perimeterSupport_eq_of_ae {n : ℕ} {E F : Set (Euc n)}
    (hEF : E =ᵐ[volume] F) : perimeterSupport E = perimeterSupport F := by
  ext x
  simp only [perimeterSupport, mem_ofPred_eq, perimeter_eq_of_ae hEF]

theorem hasHalfspaceBlowup_iff_of_ae {n : ℕ} {E F : Set (Euc n)}
    (hEF : E =ᵐ[volume] F) (x v : Euc n) :
    HasHalfspaceBlowup E x v ↔ HasHalfspaceBlowup F x v := by
  classical
  have hi : E.indicator (fun _ ↦ (1 : ℝ)) =ᵐ[volume] F.indicator (fun _ ↦ (1 : ℝ)) := by
    filter_upwards [hEF.mem_iff] with y hy
    by_cases hx : y ∈ E
    · simp only [indicator_of_mem hx, indicator_of_mem (hy.mp hx)]
    · simp only [indicator_of_notMem hx, indicator_of_notMem (mt hy.mpr hx)]
  have hint : ∀ r : ℝ, (∫ y in Metric.ball x r,
      |E.indicator (fun _ ↦ (1 : ℝ)) y -
        {z | inner ℝ (z - x) v < 0}.indicator (fun _ ↦ (1 : ℝ)) y|) =
      ∫ y in Metric.ball x r,
      |F.indicator (fun _ ↦ (1 : ℝ)) y -
        {z | inner ℝ (z - x) v < 0}.indicator (fun _ ↦ (1 : ℝ)) y| := by
    intro r
    apply integral_congr_ae
    filter_upwards [hi.filter_mono (ae_mono Measure.restrict_le_self)] with y hy
    rw [hy]
  unfold HasHalfspaceBlowup
  simp only [hint]

theorem approximateNormal_eq_of_ae {n : ℕ} {E F : Set (Euc n)}
    (hEF : E =ᵐ[volume] F) (x : Euc n) : approximateNormal E x = approximateNormal F x := by
  have hp : HasHalfspaceBlowup E x = HasHalfspaceBlowup F x :=
    funext fun v ↦ propext (hasHalfspaceBlowup_iff_of_ae hEF x v)
  unfold approximateNormal
  rw [hp]

theorem tangentialGradient_eq_of_ae {n : ℕ} {E F : Set (Euc n)}
    (hEF : E =ᵐ[volume] F) (φ : Euc n → ℝ) :
    tangentialGradient E φ = tangentialGradient F φ := by
  funext x
  simp only [tangentialGradient, approximateNormal_eq_of_ae hEF]

theorem boundaryArea_eq_of_ae {n : ℕ} {E F : Set (Euc n)}
    (hEF : E =ᵐ[volume] F) : boundaryArea E = boundaryArea F := by
  simp only [boundaryArea, perimeterSupport_eq_of_ae hEF]

theorem wholeBoundarySobolev_iff_of_ae {n : ℕ} {E F : Set (Euc n)}
    (hEF : E =ᵐ[volume] F) (h : Euc n → ℝ) (G : Euc n → Euc n) :
    WholeBoundarySobolev E h G ↔ WholeBoundarySobolev F h G := by
  simp only [WholeBoundarySobolev, boundaryArea_eq_of_ae hEF, tangentialGradient_eq_of_ae hEF]

theorem wholeBoundarySupersolution_iff_of_ae {n : ℕ} {E F : Set (Euc n)}
    (hEF : E =ᵐ[volume] F) (G : Euc n → Euc n) :
    WholeBoundarySupersolution E G ↔ WholeBoundarySupersolution F G := by
  simp only [WholeBoundarySupersolution, boundaryArea_eq_of_ae hEF, tangentialGradient_eq_of_ae hEF]

theorem zeroEssentialInfAtVertex_iff_of_ae {n : ℕ} {E F : Set (Euc n)}
    (hEF : E =ᵐ[volume] F) (h : Euc n → ℝ) :
    ZeroEssentialInfAtVertex E h ↔ ZeroEssentialInfAtVertex F h := by
  simp only [ZeroEssentialInfAtVertex, boundaryArea_eq_of_ae hEF]

end RPISingularHarnack

end

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
open scoped Topology ENNReal NNReal
open scoped ENNReal Topology ContDiff Pointwise
open scoped Topology ENNReal ContDiff
namespace RPISingularHarnack

theorem IsLocallyPerimeterMinimizing.of_ae {n : ℕ} {E F : Set (Euc n)}
    (hmin : IsLocallyPerimeterMinimizing E) (hEF : E =ᵐ[volume] F)
    (hF : MeasurableSet F) : IsLocallyPerimeterMinimizing F := by
  obtain ⟨hE, hfin, hcomp⟩ := hmin
  refine ⟨hF, ?_, ?_⟩
  · intro x r hr
    rw [← perimeter_eq_of_ae hEF]
    exact hfin x r hr
  · intro x r hr G hG hKc hKB
    let K := closure (symmDiff F G)
    let H := (G ∩ K) ∪ (E \ K)
    have hK : IsClosed K := isClosed_closure
    have hHm : MeasurableSet H := (hG.inter hK.measurableSet).union (hE.diff hK.measurableSet)
    have hFGout : ∀ y ∉ K, y ∈ F ↔ y ∈ G := by
      intro y hy
      have hdiff : y ∉ symmDiff F G := fun h ↦ hy (subset_closure h)
      simp only [mem_symmDiff] at hdiff
      tauto
    have hHG : H =ᵐ[volume] G := by
      apply Filter.eventuallyEqSet_iff.mpr
      filter_upwards [hEF.mem_iff] with y hy
      by_cases hyK : y ∈ K
      · simp only [H, mem_union, mem_inter_iff, Set.mem_sdiff, hyK, and_true, not_true_eq_false,
          and_false, or_false]
      · have ho := hFGout y hyK
        simp only [H, mem_union, mem_inter_iff, Set.mem_sdiff, hyK, and_false, not_false_eq_true,
          and_true, false_or]
        exact hy.trans ho
    have hEH : symmDiff E H ⊆ K := by
      intro y hy
      by_contra hn
      have hne : y ∈ H ↔ y ∈ E := by
        simp only [H, mem_union, mem_inter_iff, Set.mem_sdiff, hn, and_false, not_false_eq_true,
          and_true, false_or]
      simp only [mem_symmDiff] at hy
      tauto
    have hcl : closure (symmDiff E H) ⊆ K := closure_minimal hEH hK
    calc
      perimeter F (Metric.ball x r) = perimeter E (Metric.ball x r) := (perimeter_eq_of_ae hEF _).symm
      _ ≤ perimeter H (Metric.ball x r) := hcomp x r hr H hHm
        (hKc.of_isClosed_subset isClosed_closure hcl) (hcl.trans hKB)
      _ = perimeter G (Metric.ball x r) := perimeter_eq_of_ae hHG _

end RPISingularHarnack

end

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
open scoped Topology ENNReal NNReal
open scoped ENNReal Topology ContDiff Pointwise
open scoped Topology ENNReal ContDiff
namespace RPISingularHarnack

theorem tsupport_divergence_subset {n : ℕ} (V : Euc n → Euc n) :
    tsupport (divergence V) ⊆ tsupport V := by
  apply closure_minimal
  · intro x hx
    by_contra h
    have hd : fderiv ℝ V x = 0 := fderiv_of_notMem_tsupport ℝ h
    exact hx (by simp only [divergence, hd, zero_apply, inner_zero_right,
      Finset.sum_const_zero])
  · exact isClosed_tsupport V

theorem continuous_divergence {n : ℕ} {V : Euc n → Euc n}
    (hV : ContDiff ℝ ∞ V) : Continuous (divergence V) := by
  unfold divergence
  apply continuous_finsetSum
  intro i hi
  exact continuous_const.inner ((hV.continuous_fderiv (by norm_num)).clm_apply continuous_const)

theorem integrable_divergence {n : ℕ} {V : Euc n → Euc n}
    (hV : ContDiff ℝ ∞ V) (hc : HasCompactSupport V) :
    Integrable (divergence V) volume :=
  (continuous_divergence hV).integrable_of_hasCompactSupport
    (hc.of_isClosed_subset (isClosed_tsupport _) (tsupport_divergence_subset V))

theorem divergence_add {n : ℕ} {V W : Euc n → Euc n}
    (hV : Differentiable ℝ V) (hW : Differentiable ℝ W) :
    divergence (V + W) = divergence V + divergence W := by
  funext x
  simp only [divergence, fderiv_add (hV x) (hW x), add_apply,
    inner_add_right, Finset.sum_add_distrib, Pi.add_apply]

theorem raw_perimeter_mono_region {n : ℕ} (E : Set (Euc n)) {U V : Set (Euc n)}
    (hUV : U ⊆ V) : perimeter E U ≤ perimeter E V := by
  unfold perimeter
  refine iSup_le fun f ↦ iSup_le fun hf ↦ iSup_le fun hc ↦ iSup_le fun hs ↦ iSup_le fun hb ↦ ?_
  exact le_iSup_of_le f (le_iSup_of_le hf (le_iSup_of_le hc
    (le_iSup_of_le (hs.trans hUV) (le_iSup_of_le hb le_rfl))))

def PerimeterAdmissible {n : ℕ} (U : Set (Euc n)) (V : Euc n → Euc n) : Prop :=
  ContDiff ℝ ∞ V ∧ HasCompactSupport V ∧ tsupport V ⊆ U ∧ (∀ x, ‖V x‖ ≤ 1)

theorem perimeterAdmissible_zero {n : ℕ} (U : Set (Euc n)) :
    PerimeterAdmissible U (fun _ ↦ 0) := by
  exact ⟨contDiff_const, (by simp [HasCompactSupport]), by simp, by simp⟩

theorem perimeter_eq_iSup_tests {n : ℕ} (E U : Set (Euc n)) :
    perimeter E U = ⨆ V, ⨆ (_ : PerimeterAdmissible U V),
      ENNReal.ofReal (∫ x in E, divergence V x) := by
  simp only [perimeter, PerimeterAdmissible, iSup_and]

theorem perimeter_disjoint_superadditive {n : ℕ} (E : Set (Euc n))
    {U V Z : Set (Euc n)} (hUZ : U ⊆ Z) (hVZ : V ⊆ Z) (hUV : Disjoint U V) :
    perimeter E U + perimeter E V ≤ perimeter E Z := by
  rw [perimeter_eq_iSup_tests E U, perimeter_eq_iSup_tests E V]
  apply ENNReal.biSup_add_biSup_le'
    ⟨_, perimeterAdmissible_zero U⟩ ⟨_, perimeterAdmissible_zero V⟩
  rintro F ⟨hF, hcF, hsF, hbF⟩ G ⟨hG, hcG, hsG, hbG⟩
  by_cases hf : 0 ≤ ∫ x in E, divergence F x
  · by_cases hg : 0 ≤ ∫ x in E, divergence G x
    · have hs : tsupport (F + G) ⊆ Z := (tsupport_add F G).trans (union_subset (hsF.trans hUZ) (hsG.trans hVZ))
      have hb : ∀ x, ‖(F + G) x‖ ≤ 1 := by
        intro x
        by_cases hx : x ∈ tsupport F
        · have hn : x ∉ tsupport G := fun hg ↦ Set.disjoint_left.mp hUV (hsF hx) (hsG hg)
          simp only [Pi.add_apply, image_eq_zero_of_notMem_tsupport hn, add_zero]
          exact hbF x
        · simp only [Pi.add_apply, image_eq_zero_of_notMem_tsupport hx, zero_add]
          exact hbG x
      rw [← ENNReal.ofReal_add hf hg]
      have hi : (∫ x in E, divergence F x) + (∫ x in E, divergence G x) =
          ∫ x in E, divergence (F + G) x := by
        rw [divergence_add (hF.differentiable (by norm_num)) (hG.differentiable (by norm_num))]
        exact (integral_add (integrable_divergence hF hcF).integrableOn
          (integrable_divergence hG hcG).integrableOn).symm
      rw [hi]
      unfold perimeter
      exact le_iSup_of_le (F + G) (le_iSup_of_le (hF.add hG) (le_iSup_of_le (hcF.add hcG)
        (le_iSup_of_le hs (le_iSup_of_le hb le_rfl))))
    · rw [ENNReal.ofReal_of_nonpos (le_of_lt (lt_of_not_ge hg)), add_zero]
      unfold perimeter
      exact le_iSup_of_le F (le_iSup_of_le hF (le_iSup_of_le hcF
        (le_iSup_of_le (hsF.trans hUZ) (le_iSup_of_le hbF le_rfl))))
  · rw [ENNReal.ofReal_of_nonpos (le_of_lt (lt_of_not_ge hf)), zero_add]
    unfold perimeter
    exact le_iSup_of_le G (le_iSup_of_le hG (le_iSup_of_le hcG
      (le_iSup_of_le (hsG.trans hVZ) (le_iSup_of_le hbG le_rfl))))

theorem divergence_smul {n : ℕ} {η : Euc n → ℝ} {V : Euc n → Euc n}
    (hη : Differentiable ℝ η) (hV : Differentiable ℝ V) (x : Euc n) :
    divergence (fun y ↦ η y • V y) x =
      η x * divergence V x + inner ℝ (gradient η x) (V x) := by
  simp only [divergence, fderiv_fun_smul (hη x) (hV x),
    add_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, inner_add_right, inner_smul_right,
    Finset.sum_add_distrib, ← Finset.mul_sum]
  congr 1
  simp_rw [← inner_gradient_left]
  exact (EuclideanSpace.basisFun (Fin n) ℝ).sum_inner_mul_inner _ _

theorem smoothTransition_deriv_zero_of_nonpos {s : ℝ} (hs : s ≤ 0) :
    deriv Real.smoothTransition s = 0 := by
  have hm : IsLocalMin Real.smoothTransition s := by
    filter_upwards [] with x
    rw [Real.smoothTransition.zero_of_nonpos hs]
    exact Real.smoothTransition.nonneg x
  exact hm.deriv_eq_zero

theorem smoothTransition_deriv_zero_of_one_le {s : ℝ} (hs : 1 ≤ s) :
    deriv Real.smoothTransition s = 0 := by
  have hm : IsLocalMax Real.smoothTransition s := by
    filter_upwards [] with x
    rw [Real.smoothTransition.one_of_one_le hs]
    exact Real.smoothTransition.le_one x
  exact hm.deriv_eq_zero

theorem exists_smoothTransition_deriv_bound :
    ∃ L : ℝ, 0 < L ∧ ∀ s, |deriv Real.smoothTransition s| ≤ L := by
  have hc : Continuous (deriv Real.smoothTransition) :=
    (Real.smoothTransition.contDiff : ContDiff ℝ ∞ _).continuous_deriv (by norm_num)
  obtain ⟨L₀, hL₀⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1)).exists_bound_of_continuousOn hc.continuousOn
  refine ⟨max L₀ 0 + 1, by positivity, ?_⟩
  intro s
  by_cases hs : s ∈ Icc (0 : ℝ) 1
  · have h := hL₀ s hs
    rw [Real.norm_eq_abs] at h
    linarith [le_max_left L₀ (0 : ℝ)]
  · have hh : s ≤ 0 ∨ 1 ≤ s := by simp only [mem_Icc] at hs; by_contra h; push Not at h; exact hs ⟨h.1.le, h.2.le⟩
    rcases hh with hh | hh
    · rw [smoothTransition_deriv_zero_of_nonpos hh, abs_zero]; positivity
    · rw [smoothTransition_deriv_zero_of_one_le hh, abs_zero]; positivity

end RPISingularHarnack

end

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
open scoped Topology ENNReal NNReal
open scoped ENNReal Topology ContDiff Pointwise
open scoped Topology ENNReal ContDiff
namespace RPISingularHarnack

def annularCutoff {n : ℕ} (c : Euc n) (a b : ℝ) (x : Euc n) : ℝ :=
  Real.smoothTransition ((‖x - c‖ ^ 2 - a ^ 2) / (b ^ 2 - a ^ 2))

theorem annularCutoff_contDiff {n : ℕ} (c : Euc n) (a b : ℝ) :
    ContDiff ℝ ∞ (annularCutoff c a b) := by
  apply Real.smoothTransition.contDiff.comp
  exact (((contDiff_id.sub contDiff_const).norm_sq ℝ).sub contDiff_const).div_const _

theorem annularCutoff_mem_Icc {n : ℕ} (c : Euc n) (a b : ℝ) (x : Euc n) :
    annularCutoff c a b x ∈ Icc (0 : ℝ) 1 :=
  ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

theorem annularCutoff_zero {n : ℕ} {c x : Euc n} {a b : ℝ}
    (ha : 0 < a) (hab : a < b) (hx : dist x c ≤ a) :
    annularCutoff c a b x = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  apply div_nonpos_of_nonpos_of_nonneg
  · rw [dist_eq_norm] at hx
    nlinarith [norm_nonneg (x - c)]
  · nlinarith

theorem annularCutoff_one {n : ℕ} {c x : Euc n} {a b : ℝ}
    (ha : 0 < a) (hab : a < b) (hx : b ≤ dist x c) :
    annularCutoff c a b x = 1 := by
  apply Real.smoothTransition.one_of_one_le
  rw [le_div_iff₀ (by nlinarith : 0 < b ^ 2 - a ^ 2)]
  rw [dist_eq_norm] at hx
  nlinarith [norm_nonneg (x - c)]

theorem tsupport_annularCutoff_subset {n : ℕ} {c : Euc n} {a b : ℝ}
    (ha : 0 < a) (hab : a < b) :
    tsupport (annularCutoff c a b) ⊆ {x | a ≤ dist x c} := by
  apply closure_minimal
  · intro x hx
    exact (lt_of_not_ge (fun h ↦ hx (annularCutoff_zero ha hab h))).le
  · exact isClosed_le continuous_const (continuous_id.dist continuous_const)

theorem gradient_annularCutoff {n : ℕ} (c x : Euc n) (a b : ℝ) :
    gradient (annularCutoff c a b) x =
      (deriv Real.smoothTransition ((‖x - c‖ ^ 2 - a ^ 2) / (b ^ 2 - a ^ 2)) *
        (2 / (b ^ 2 - a ^ 2))) • (x - c) := by
  let q : Euc n → ℝ := fun y ↦ (‖y - c‖ ^ 2 - a ^ 2) / (b ^ 2 - a ^ 2)
  have h0 : HasFDerivAt (fun y : Euc n ↦ ‖y - c‖ ^ 2 - a ^ 2)
      (2 • innerSL ℝ (x - c)) x := by
    simpa using (((hasFDerivAt_id (𝕜 := ℝ) x).sub_const c).norm_sq.sub_const (a ^ 2))
  have hq : HasFDerivAt q ((2 • innerSL ℝ (x - c)).smulRight
      ((b ^ 2 - a ^ 2)⁻¹ : ℝ)) x := by
    simpa only [q, div_eq_mul_inv, smul_eq_mul] using h0.smul_const
      ((b ^ 2 - a ^ 2)⁻¹ : ℝ)
  have hT : DifferentiableAt ℝ Real.smoothTransition (q x) :=
    (Real.smoothTransition.contDiff : ContDiff ℝ ∞ _).differentiable (by norm_num) _
  apply (InnerProductSpace.toDual ℝ (Euc n)).injective
  rw [toDual_gradient]
  have hchain := (hT.hasDerivAt.comp_hasFDerivAt x hq).fderiv
  change fderiv ℝ (Real.smoothTransition ∘ q) x = _
  rw [hchain]
  ext y
  simp only [map_smul, smul_apply, ContinuousLinearMap.smulRight_apply,
    InnerProductSpace.toDual_apply_apply, innerSL_apply_apply]
  simp only [smul_eq_mul]
  dsimp [q]
  ring

theorem gradient_annularCutoff_zero {n : ℕ} {c x : Euc n} {a b : ℝ}
    (ha : 0 < a) (hab : a < b) (hx : dist x c ≤ a ∨ b ≤ dist x c) :
    gradient (annularCutoff c a b) x = 0 := by
  rcases hx with hx | hx
  · have hm : IsLocalMin (annularCutoff c a b) x := by
      filter_upwards [] with y
      rw [annularCutoff_zero ha hab hx]
      exact (annularCutoff_mem_Icc c a b y).1
    simp only [gradient, hm.fderiv_eq_zero, map_zero]
  · have hm : IsLocalMax (annularCutoff c a b) x := by
      filter_upwards [] with y
      rw [annularCutoff_one ha hab hx]
      exact (annularCutoff_mem_Icc c a b y).2
    simp only [gradient, hm.fderiv_eq_zero, map_zero]

theorem gradient_annularCutoff_bound {n : ℕ} {c : Euc n} {a b L : ℝ}
    (ha : 0 < a) (hab : a < b) (hL : 0 < L)
    (hbound : ∀ s, |deriv Real.smoothTransition s| ≤ L) (x : Euc n) :
    ‖gradient (annularCutoff c a b) x‖ ≤ 2 * L * b / (b ^ 2 - a ^ 2) := by
  have hb : 0 < b := ha.trans hab
  have hden : 0 < b ^ 2 - a ^ 2 := by nlinarith
  by_cases hx : b ≤ dist x c
  · rw [gradient_annularCutoff_zero ha hab (Or.inr hx), norm_zero]
    exact div_nonneg (mul_nonneg (by positivity) (by linarith)) (by nlinarith)
  · have hxb : ‖x - c‖ ≤ b := by simpa only [dist_eq_norm] using (lt_of_not_ge hx).le
    rw [gradient_annularCutoff, norm_smul, Real.norm_eq_abs, abs_mul,
      abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_pos (by nlinarith : 0 < b ^ 2 - a ^ 2)]
    calc
      _ ≤ (L * (2 / (b ^ 2 - a ^ 2))) * b := by
        gcongr
        exact hbound _
      _ = _ := by ring

end RPISingularHarnack

end

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
open scoped Topology ENNReal NNReal
open scoped ENNReal Topology ContDiff Pointwise
open scoped Topology ENNReal ContDiff
namespace RPISingularHarnack

theorem volume_real_annulus {n : ℕ} (c : Euc n) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) :
    volume.real (Metric.closedBall c b \ Metric.closedBall c a) =
      (b ^ n - a ^ n) * volume.real (Metric.ball (0 : Euc n) 1) := by
  rw [measureReal_sdiff (Metric.closedBall_subset_closedBall hab) measurableSet_closedBall
      (isCompact_closedBall c b).measure_ne_top,
    Measure.addHaar_real_closedBall volume c (ha.trans hab),
    Measure.addHaar_real_closedBall volume c ha]
  simp only [finrank_euclideanSpace, Fintype.card_fin]
  ring

theorem gradient_annularCutoff_continuous {n : ℕ} (c : Euc n) (a b : ℝ) :
    Continuous (gradient (annularCutoff c a b)) := by
  exact (InnerProductSpace.toDual ℝ (Euc n)).symm.continuous.comp
    ((annularCutoff_contDiff c a b).continuous_fderiv (by norm_num))

theorem gradient_annularCutoff_compact {n : ℕ} (c : Euc n) {a b : ℝ}
    (ha : 0 < a) (hab : a < b) :
    HasCompactSupport (gradient (annularCutoff c a b)) := by
  apply (isCompact_closedBall c b).of_isClosed_subset (isClosed_tsupport _)
  apply closure_minimal
  · intro x hx
    by_contra hb
    exact hx (gradient_annularCutoff_zero ha hab (Or.inr (le_of_lt (lt_of_not_ge hb))))
  · exact Metric.isClosed_closedBall

theorem integral_gradient_annularCutoff_le {n : ℕ} (c : Euc n) {a b L : ℝ}
    (ha : 0 < a) (hab : a < b) (hL : 0 < L)
    (hbound : ∀ s, |deriv Real.smoothTransition s| ≤ L) :
    (∫ x, ‖gradient (annularCutoff c a b) x‖) ≤
      2 * L * n * b ^ (n - 1) * volume.real (Metric.ball (0 : Euc n) 1) := by
  have hb : 0 < b := ha.trans hab
  have hden : 0 < b ^ 2 - a ^ 2 := by nlinarith
  have hpow : b ^ n - a ^ n ≤ (b - a) * n * b ^ (n - 1) := by
    have hh := abs_pow_sub_pow_le (a := b) (b := a) (n := n)
    rw [abs_of_pos hb, abs_of_pos ha, max_eq_left hab.le, abs_of_pos (sub_pos.mpr hab)] at hh
    exact (le_abs_self _).trans hh
  let A := Metric.closedBall c b \ Metric.closedBall c a
  have hid : (∫ x in A, ‖gradient (annularCutoff c a b) x‖) =
      ∫ x, ‖gradient (annularCutoff c a b) x‖ := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    rw [gradient_annularCutoff_zero ha hab, norm_zero]
    by_cases hh : x ∈ Metric.closedBall c a
    · exact Or.inl hh
    · exact Or.inr (le_of_lt (lt_of_not_ge (fun h ↦ hx ⟨h, hh⟩)))
  rw [← hid]
  calc
    _ ≤ ‖∫ x in A, ‖gradient (annularCutoff c a b) x‖‖ := le_abs_self _
    _ ≤ (2 * L * b / (b ^ 2 - a ^ 2)) * volume.real A := by
      apply norm_setIntegral_le_of_norm_le_const
        ((measure_mono sdiff_subset).trans_lt (isCompact_closedBall c b).measure_lt_top)
      intro x hx
      simpa only [norm_norm] using gradient_annularCutoff_bound ha hab hL hbound x
    _ = (2 * L * b / (b ^ 2 - a ^ 2)) *
        ((b ^ n - a ^ n) * volume.real (Metric.ball (0 : Euc n) 1)) := by
      rw [volume_real_annulus c ha.le hab.le]
    _ ≤ (2 * L * b / (b ^ 2 - a ^ 2)) *
        (((b - a) * n * b ^ (n - 1)) * volume.real (Metric.ball (0 : Euc n) 1)) := by
      gcongr
    _ ≤ _ := by
      have heq : (2 * L * b / (b ^ 2 - a ^ 2)) *
          (((b - a) * n * b ^ (n - 1)) * volume.real (Metric.ball (0 : Euc n) 1)) =
          (b / (b + a)) * (2 * L * n * b ^ (n - 1) *
            volume.real (Metric.ball (0 : Euc n) 1)) := by
        field_simp
        ring
      rw [heq]
      exact mul_le_of_le_one_left (by positivity)
        ((div_le_one (by linarith : 0 < b + a)).mpr (by linarith))

end RPISingularHarnack

end

end OAI
