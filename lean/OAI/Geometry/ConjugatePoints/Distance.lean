import OAI.Geometry.ConjugatePoints.Continuation

namespace OAI

noncomputable section

/-!
# Riemannian distance and the nonpositively curved universal-cover metric.
-/

section
open Set Filter Topology Bundle Manifold MeasureTheory
open scoped ContDiff ENNReal NNReal
namespace ThreeManifold.RiemannianDistance

section

lemma edist_finite_of_preconnected {X : Type*} [PseudoEMetricSpace X] [PreconnectedSpace X]
    (x y : X) : edist x y ≠ ⊤ := by
  let S := {z : X | edist x z ≠ ⊤}
  have hopen : IsOpen S := by
    apply EMetric.isOpen_iff.mpr
    intro z hz
    refine ⟨1,by norm_num,fun w hw => ?_⟩
    have hwz : edist z w ≠ ⊤ := ne_top_of_lt (by simpa only [edist_comm] using (Metric.mem_eball.mp hw))
    exact ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hz,hwz⟩) (edist_triangle x z w)
  have hcomp : IsOpen Sᶜ := by
    apply EMetric.isOpen_iff.mpr
    intro z hz
    refine ⟨1,by norm_num,fun w hw => ?_⟩
    intro hwS
    have hwz : edist w z ≠ ⊤ := ne_top_of_lt (Metric.mem_eball.mp hw)
    exact hz (ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hwS,hwz⟩) (edist_triangle x w z))
  have he : S = univ := (show IsClopen S from ⟨by simpa only [compl_compl] using hcomp.isClosed_compl,hopen⟩).eq_univ
    ⟨x,by simp [S]⟩
  have : y ∈ S := he ▸ mem_univ y
  exact this

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
local notation "I" => 𝓘(ℝ,E)

abbrev metricSpace (g : ContinuousRiemannianMetric E (TangentSpace 𝓘(ℝ,E) : E → Type _)) : MetricSpace E :=
  letI : RiemannianBundle (TangentSpace 𝓘(ℝ,E) : E → Type _) := ⟨g.toRiemannianMetric⟩
  letI : EMetricSpace E := .ofRiemannianMetric I E
  EMetricSpace.toMetricSpace (edist_finite_of_preconnected)

variable (g : ContinuousRiemannianMetric E (TangentSpace 𝓘(ℝ,E) : E → Type _))

lemma tangent_enorm (x : E) (v : TangentSpace 𝓘(ℝ,E) x) :
    letI : RiemannianBundle (TangentSpace 𝓘(ℝ,E) : E → Type _) := ⟨g.toRiemannianMetric⟩
    ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)) := by
  let : RiemannianBundle (TangentSpace 𝓘(ℝ,E) : E → Type _) := ⟨g.toRiemannianMetric⟩
  rw [← ofReal_norm,norm_eq_sqrt_real_inner]
  rfl

lemma norm_sub_le_pathELength (R : ℝ≥0)
    (hR : ∀ (x : E) (v : E), ‖v‖ ≤ R * Real.sqrt (g.inner x v v))
    {γ : ℝ → E} {a b : ℝ} (hγ : ContDiffOn ℝ 1 γ (Icc a b)) (hab : a ≤ b) :
    letI : RiemannianBundle (TangentSpace 𝓘(ℝ,E) : E → Type _) := ⟨g.toRiemannianMetric⟩
    ‖γ b - γ a‖ₑ ≤ (R : ℝ≥0∞) * pathELength I γ a b := by
  let : RiemannianBundle (TangentSpace 𝓘(ℝ,E) : E → Type _) := ⟨g.toRiemannianMetric⟩
  apply (enorm_sub_le_lintegral_deriv_of_contDiffOn_Icc hγ hab).trans
  rw [pathELength_eq_lintegral_mfderiv_Icc,← lintegral_const_mul' _ _ ENNReal.coe_ne_top]
  apply lintegral_mono
  intro t
  have h := ENNReal.ofReal_le_ofReal (hR (γ t) (deriv γ t))
  rw [ENNReal.ofReal_mul R.coe_nonneg] at h
  have hv : (mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,E) γ t 1 : E) = deriv γ t := by
    rw [mfderiv_eq_fderiv]
    rfl
  have hx := congrArg (fun v : E => g.inner (γ t) v v) hv
  dsimp only
  rw [tangent_enorm g]
  rw [hx]
  simpa only [ofReal_norm,ENNReal.ofReal_coe_nnreal] using h

lemma norm_sub_le_riemannianEDist (R : ℝ≥0) (hRp : 0 < R)
    (hR : ∀ (x : E) (v : E), ‖v‖ ≤ R * Real.sqrt (g.inner x v v)) (x y : E) :
    letI : RiemannianBundle (TangentSpace 𝓘(ℝ,E) : E → Type _) := ⟨g.toRiemannianMetric⟩
    ‖y-x‖ₑ ≤ (R : ℝ≥0∞) * riemannianEDist I x y := by
  let : RiemannianBundle (TangentSpace 𝓘(ℝ,E) : E → Type _) := ⟨g.toRiemannianMetric⟩
  rw [mul_comm]
  apply (ENNReal.div_le_iff (by exact_mod_cast hRp.ne') ENNReal.coe_ne_top).mp
  apply le_of_forall_gt
  intro r hr
  obtain ⟨γ,h0,h1,hγ,hlen⟩ := exists_lt_of_riemannianEDist_lt hr
  have hb := norm_sub_le_pathELength g R hR (contMDiffOn_iff_contDiffOn.mp hγ) (by norm_num : (0:ℝ) ≤ 1)
  rw [h0,h1,mul_comm] at hb
  exact ((ENNReal.div_le_iff (by exact_mod_cast hRp.ne') ENNReal.coe_ne_top).mpr hb).trans_lt hlen

lemma norm_sub_le_dist (R : ℝ≥0) (hRp : 0 < R)
    (hR : ∀ (x : E) (v : E), ‖v‖ ≤ R * Real.sqrt (g.inner x v v)) (x y : E) :
    ‖y-x‖ ≤ R * @dist E (metricSpace g).toPseudoMetricSpace.toDist x y := by
  have h := norm_sub_le_riemannianEDist g R hRp hR x y
  let : RiemannianBundle (TangentSpace 𝓘(ℝ,E) : E → Type _) := ⟨g.toRiemannianMetric⟩
  let : MetricSpace E := metricSpace g
  have hh : ‖y-x‖ₑ ≤ (R : ℝ≥0∞) * edist x y := h
  have hh' := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.coe_ne_top (@edist_ne_top E (metricSpace g).toPseudoMetricSpace x y)) hh
  rw [ENNReal.toReal_mul,ENNReal.coe_toReal,toReal_enorm] at hh'
  rw [@edist_dist E (metricSpace g).toPseudoMetricSpace,
    ENNReal.toReal_ofReal (@dist_nonneg E (metricSpace g).toPseudoMetricSpace x y)] at hh'
  exact hh'

theorem properSpace [ProperSpace E] (R : ℝ≥0) (hRp : 0 < R)
    (hR : ∀ (x : E) (v : E), ‖v‖ ≤ R * Real.sqrt (g.inner x v v)) :
    @ProperSpace E (metricSpace g).toPseudoMetricSpace := by
  have hc (x : E) (r : ℝ) : IsCompact {y : E | ‖y-x‖ ≤ R*r} := by
    simpa only [Metric.closedBall,dist_eq_norm] using isCompact_closedBall x ((R:ℝ)*r)
  let : PseudoMetricSpace E := (metricSpace g).toPseudoMetricSpace
  constructor
  intro x r
  apply (hc x r).of_isClosed_subset Metric.isClosed_closedBall
  intro y hy
  exact (norm_sub_le_dist g R hRp hR x y).trans
    (mul_le_mul_of_nonneg_left (by simpa only [Metric.mem_closedBall,dist_comm] using hy) R.coe_nonneg)
end

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (g : ContinuousRiemannianMetric E (TangentSpace 𝓘(ℝ,E) : E → Type _))

lemma pathELength_comp_eq {f : E → E} (hf : ContDiff ℝ 1 f)
    (hi : ∀ (x u v : E), g.inner (f x) (fderiv ℝ f x u) (fderiv ℝ f x v) = g.inner x u v)
    {γ : ℝ → E} {a b : ℝ} (hγ : ContDiffOn ℝ 1 γ (Icc a b)) :
    letI : RiemannianBundle (TangentSpace 𝓘(ℝ,E) : E → Type _) := ⟨g.toRiemannianMetric⟩
    pathELength 𝓘(ℝ,E) (f ∘ γ) a b = pathELength 𝓘(ℝ,E) γ a b := by
  let : RiemannianBundle (TangentSpace 𝓘(ℝ,E) : E → Type _) := ⟨g.toRiemannianMetric⟩
  simp only [pathELength_eq_lintegral_mfderiv_Ioo]
  apply setLIntegral_congr_fun measurableSet_Ioo
  intro t ht
  have hγt := (hγ.contDiffAt (Icc_mem_nhds ht.1 ht.2)).differentiableAt (by simp)
  dsimp only
  rw [tangent_enorm g,tangent_enorm g]
  have hv : (mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,E) (f ∘ γ) t 1 : E) =
      fderiv ℝ f (γ t) (mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,E) γ t 1 : E) := by
    rw [mfderiv_eq_fderiv,mfderiv_eq_fderiv,fderiv_comp t
      (hf.differentiable (by simp) (γ t)) hγt]
    rfl
  apply congrArg (ENNReal.ofReal ∘ Real.sqrt)
  calc
    _ = g.inner (f (γ t))
        (fderiv ℝ f (γ t) (mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,E) γ t 1 : E))
        (fderiv ℝ f (γ t) (mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,E) γ t 1 : E)) :=
      congrArg₂ (fun u v : E => g.inner (f (γ t)) u v) hv hv
    _ = _ := hi _ _ _

lemma riemannianEDist_map_le {f : E → E} (hf : ContDiff ℝ 1 f)
    (hi : ∀ (x u v : E), g.inner (f x) (fderiv ℝ f x u) (fderiv ℝ f x v) = g.inner x u v)
    (x y : E) :
    letI : RiemannianBundle (TangentSpace 𝓘(ℝ,E) : E → Type _) := ⟨g.toRiemannianMetric⟩
    riemannianEDist 𝓘(ℝ,E) (f x) (f y) ≤ riemannianEDist 𝓘(ℝ,E) x y := by
  let : RiemannianBundle (TangentSpace 𝓘(ℝ,E) : E → Type _) := ⟨g.toRiemannianMetric⟩
  apply le_of_forall_gt
  intro r hr
  obtain ⟨γ,h0,h1,hγ,hlen⟩ := exists_lt_of_riemannianEDist_lt hr
  have hc := hf.contMDiff.comp_contMDiffOn hγ
  have hl := riemannianEDist_le_pathELength (I := 𝓘(ℝ,E)) hc rfl rfl (by norm_num : (0:ℝ) ≤ 1)
  simp only [Function.comp_apply,h0,h1] at hl
  rw [pathELength_comp_eq g hf hi (contMDiffOn_iff_contDiffOn.mp hγ)] at hl
  exact hl.trans_lt hlen

theorem isometry_of_inner (f : E ≃ E) (hf : ContDiff ℝ 1 f) (hfi : ContDiff ℝ 1 f.symm)
    (hi : ∀ (x u v : E), g.inner (f x) (fderiv ℝ f x u) (fderiv ℝ f x v) = g.inner x u v)
    (hii : ∀ (x u v : E), g.inner (f.symm x) (fderiv ℝ f.symm x u) (fderiv ℝ f.symm x v) = g.inner x u v) :
    @Isometry E E (metricSpace g).toPseudoEMetricSpace (metricSpace g).toPseudoEMetricSpace f := by
  have hle := riemannianEDist_map_le g hf hi
  have hlei := riemannianEDist_map_le g hfi hii
  let : MetricSpace E := metricSpace g
  intro x y
  apply le_antisymm (hle x y)
  simpa only [Equiv.symm_apply_apply] using hlei (f x) (f y)
end ThreeManifold.RiemannianDistance
end

section
open Set Filter Topology Bundle Manifold IsManifold Bornology
open scoped ContDiff
namespace ThreeManifold.MetricConstruction
variable {E F M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ,F) ∞ N]
lemma flip_contAt {X G A B C : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [TopologicalSpace G] [ChartedSpace X G]
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup C] [NormedSpace ℝ C]
    {f : G → A →L[ℝ] B →L[ℝ] C} {x : G}
    (hf : ContMDiffAt 𝓘(ℝ,X) 𝓘(ℝ,A →L[ℝ] B →L[ℝ] C) 0 f x) :
    ContMDiffAt 𝓘(ℝ,X) 𝓘(ℝ,B →L[ℝ] A →L[ℝ] C) 0 (fun y => (f y).flip) x := by
  let : NormedAddCommGroup (B →L[ℝ] C) := ContinuousLinearMap.toNormedAddCommGroup
  let : NormedSpace ℝ (B →L[ℝ] C) := ContinuousLinearMap.toNormedSpace
  let : NormedAddCommGroup (A →L[ℝ] B →L[ℝ] C) := ContinuousLinearMap.toNormedAddCommGroup
  let : NormedSpace ℝ (A →L[ℝ] B →L[ℝ] C) := ContinuousLinearMap.toNormedSpace
  let : NormedAddCommGroup (A →L[ℝ] C) := ContinuousLinearMap.toNormedAddCommGroup
  let : NormedSpace ℝ (A →L[ℝ] C) := ContinuousLinearMap.toNormedSpace
  let : NormedAddCommGroup (B →L[ℝ] A →L[ℝ] C) := ContinuousLinearMap.toNormedAddCommGroup
  let : NormedSpace ℝ (B →L[ℝ] A →L[ℝ] C) := ContinuousLinearMap.toNormedSpace
  have hc : ContDiff ℝ 0 (fun L : A →L[ℝ] B →L[ℝ] C => L.flip) :=
    (ContinuousLinearMap.flipₗᵢ ℝ A B C).toContinuousLinearEquiv.contDiff
  exact hc.comp_contMDiffAt hf

lemma bilin_comp_contAt {X G H : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [TopologicalSpace G] [ChartedSpace X G]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    {q : G → F →L[ℝ] F →L[ℝ] ℝ} {L : G → H →L[ℝ] F} {x : G}
    (hq : ContMDiffAt 𝓘(ℝ,X) 𝓘(ℝ,F →L[ℝ] F →L[ℝ] ℝ) 0 q x)
    (hL : ContMDiffAt 𝓘(ℝ,X) 𝓘(ℝ,H →L[ℝ] F) 0 L x) :
    ContMDiffAt 𝓘(ℝ,X) 𝓘(ℝ,H →L[ℝ] H →L[ℝ] ℝ) 0
      (fun y => (q y).bilinearComp (L y) (L y)) x := by
  exact flip_contAt ((flip_contAt (hq.clm_comp hL)).clm_comp hL)

lemma pullback_inner_contAt (g : Metric (E := F) N) {f : M → N}
    {x : M} (hf : ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,F) 1 f x) :
    ContMDiffAt 𝓘(ℝ,E) (𝓘(ℝ,E).prod 𝓘(ℝ,E →L[ℝ] E →L[ℝ] ℝ)) 0
      (fun x => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun y => TangentSpace 𝓘(ℝ,E) y →L[ℝ] TangentSpace 𝓘(ℝ,E) y →L[ℝ] ℝ)
        x (pullInner g f x)) x := by
  rw [contMDiffAt_section]
  have hg := g.contMDiff (f x)
  rw [contMDiffAt_section] at hg
  simp only [hom_trivializationAt_apply] at hg ⊢
  have hgc := (hg.of_le (show (0:ℕ∞ω) ≤ ∞ by simp)).comp x (hf.of_le (by simp))
  have hL := hf.mfderiv_const (m := 0) (by simp)
  apply (bilin_comp_contAt hgc hL).congr_of_eventuallyEq
  filter_upwards [(trivializationAt E (TangentSpace 𝓘(ℝ,E)) x).open_baseSet.mem_nhds
    (mem_baseSet_trivializationAt E (TangentSpace 𝓘(ℝ,E)) x),
    hf.continuousAt
      ((trivializationAt F (TangentSpace 𝓘(ℝ,F)) (f x)).open_baseSet.mem_nhds
        (mem_baseSet_trivializationAt F (TangentSpace 𝓘(ℝ,F)) (f x)))] with y hy hy'
  exact pullback_coordinates g f x y hy hy'

def continuousPullback (g : Metric (E := F) N) {f : M → N}
    (hf : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,F) 1 f)
    (e : ∀ x, TangentSpace 𝓘(ℝ,E) x ≃L[ℝ] TangentSpace 𝓘(ℝ,F) (f x))
    (he : ∀ x, (e x : TangentSpace 𝓘(ℝ,E) x →L[ℝ] TangentSpace 𝓘(ℝ,F) (f x)) =
      mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) f x) :
    ContinuousRiemannianMetric E (TangentSpace 𝓘(ℝ,E) : M → Type _) where
  inner x := pullInner g f x
  symm x u v := g.symm (f x) _ _
  pos x u hu := by
    rw [pullInner_apply,← he]
    apply g.pos
    intro hh
    apply hu
    apply (e x).injective
    rw [(e x).map_zero]
    exact hh
  isVonNBounded x := by
    have hb := (g.isVonNBounded (f x)).image (e x).symm.toContinuousLinearMap
    apply hb.subset
    intro u hu
    refine ⟨e x u,?_,by simp⟩
    change g.inner (f x) (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) f x u)
      (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) f x u) < 1 at hu
    rw [← he] at hu
    exact hu
  continuous := continuous_iff_continuousAt.mpr (fun x => (pullback_inner_contAt g (hf x)).continuousAt)
end ThreeManifold.MetricConstruction

namespace ThreeManifold.RiemannianCoordinates
variable {M : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]
  [CompactSpace M] [T2Space M]

def exponentialTangentEquiv (g : SmoothMetric M) (hn : NonpositiveSectionalCurvature g)
    (p : M) (v : E3) : E3 ≃L[ℝ] TangentSpace I3 (exponential g p v) :=
  (LinearEquiv.ofInjectiveEndo (show E3 →ₗ[ℝ] E3 from
    (mfderiv 𝓘(ℝ,E3) I3 (exponential g p) v).toLinearMap)
      (exponential_mfderiv_injective g (npc_noConjugatePoints g hn) p v)).toContinuousLinearEquiv

def exponentialMetric (g : SmoothMetric M) (hn : NonpositiveSectionalCurvature g) (p : M) :
    ContinuousRiemannianMetric E3 (TangentSpace 𝓘(ℝ,E3) : E3 → Type _) :=
  MetricConstruction.continuousPullback g (exponential_contMDiff g p)
    (exponentialTangentEquiv g hn p) (fun _ => rfl)

lemma exponentialMetric_inner (g : SmoothMetric M) (hn : NonpositiveSectionalCurvature g)
    (p : M) (v a b : E3) :
    (exponentialMetric g hn p).inner v a b = g.inner (exponential g p v)
      (mfderiv 𝓘(ℝ,E3) I3 (exponential g p) v a)
      (mfderiv 𝓘(ℝ,E3) I3 (exponential g p) v b) := rfl

lemma exponentialMetric_expanding (g : SmoothMetric M) (hn : NonpositiveSectionalCurvature g)
    (p : M) (v b : E3) :
    g.inner p b b ≤ (exponentialMetric g hn p).inner v b b :=
  npc_exponential_differential_expanding g hn p v b
end ThreeManifold.RiemannianCoordinates
end

section
open Set Filter Topology
namespace ThreeManifold.UniversalDeck
variable {E X : Type*} [TopologicalSpace E] [TopologicalSpace X] {p : E → X}

def group (p : E → X) : Subgroup (Equiv.Perm E) where
  carrier := {d | Continuous d ∧ Continuous d.symm ∧ ∀ z, p (d z) = p z}
  one_mem' := ⟨continuous_id,continuous_id,fun _ => rfl⟩
  mul_mem' := by
    rintro a b ⟨ha,hai,hap⟩ ⟨hb,hbi,hbp⟩
    exact ⟨ha.comp hb,hbi.comp hai,fun z => (hap (b z)).trans (hbp z)⟩
  inv_mem' := by
    rintro a ⟨ha,hai,hap⟩
    refine ⟨hai,ha,fun z => ?_⟩
    simpa using (hap (a.symm z)).symm

instance deckAction : MulAction (group p) E where
  smul d z := d.val z
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
instance deckContinuous : ContinuousConstSMul (group p) E :=
  ⟨fun d => d.property.1⟩
lemma map_smul (d : group p) (z : E) : p (d • z) = p z := by
  let _ : TopologicalSpace X := inferInstance
  exact d.property.2.2 z

lemma deck_ext [PreconnectedSpace E] (hp : IsCoveringMap p)
    {a b : group p} {z : E} (h : a • z = b • z) : a = b := by
  apply Subtype.ext
  apply Equiv.ext
  exact congr_fun (hp.eq_of_comp_eq a.property.1 b.property.1
    (funext (fun w => (map_smul a w).trans (map_smul b w).symm)) z h)

lemma covering_surjective [Nonempty E] [PathConnectedSpace X] (hp : IsCoveringMap p) :
    Function.Surjective p := by
  let e : E := Classical.choice inferInstance
  intro y
  let γ := PathConnectedSpace.somePath (p e) y
  obtain ⟨v,hv,hv0⟩ := hp.exists_path_lifts γ.toContinuousMap e γ.source
  exact ⟨v 1,(congr_fun hv 1).trans γ.target⟩

variable [SimplyConnectedSpace E] [LocallyPathConnectedSpace E]

lemma exists_deck (hp : IsCoveringMap p) {a b : E} (hab : p a = p b) :
    ∃ d : group p, d • a = b := by
  obtain ⟨f,⟨hfa,hfp⟩,_⟩ := hp.existsUnique_continuousMap_lifts
    ⟨p,hp.continuous⟩ a b hab.symm
  obtain ⟨g,⟨hgb,hgp⟩,_⟩ := hp.existsUnique_continuousMap_lifts
    ⟨p,hp.continuous⟩ b a hab
  have hfg : Function.RightInverse g f := by
    have he : f ∘ g = id := hp.eq_of_comp_eq
      (f.continuous.comp g.continuous) continuous_id
      (funext (fun z => (congr_fun hfp (g z)).trans (congr_fun hgp z))) b (by simp [hgb,hfa])
    exact congr_fun he
  have hgf : Function.LeftInverse g f := by
    have he : g ∘ f = id := hp.eq_of_comp_eq
      (g.continuous.comp f.continuous) continuous_id
      (funext (fun z => (congr_fun hgp (f z)).trans (congr_fun hfp z))) a (by simp [hfa,hgb])
    exact congr_fun he
  let d : Equiv.Perm E := ⟨f,g,hgf,hfg⟩
  exact ⟨⟨d,f.continuous,g.continuous,fun z => congr_fun hfp z⟩,hfa⟩

theorem quotient_cover [PathConnectedSpace X] (hp : IsCoveringMap p) :
    IsQuotientCoveringMap p (group p) := by
  refine {
    toIsQuotientMap := hp.isQuotientMap (covering_surjective hp)
    continuous_const_smul := fun d => d.property.1
    apply_eq_iff_mem_orbit := ?_
    disjoint := ?_ }
  · intro a b
    constructor
    · intro h
      obtain ⟨d,hd⟩ := exists_deck hp h.symm
      exact ⟨d,hd⟩
    · rintro ⟨d,rfl⟩
      exact map_smul d b
  · intro z
    obtain ⟨U,hU,hz,hi⟩ := hp.isLocalHomeomorph.isLocallyInjective z
    refine ⟨U,hU.mem_nhds hz,?_⟩
    rintro d ⟨w,⟨y,hy,rfl⟩,hdy⟩
    apply deck_ext hp (z := y)
    exact hi hdy hy (map_smul d y)

def fundamentalGroupEquiv [PathConnectedSpace X] (hp : IsCoveringMap p) (z : E) :
    FundamentalGroup X (p z) ≃* (group p)ᵐᵒᵖ :=
  (quotient_cover hp).fundamentalGroupEquiv ⟨z,rfl⟩
end ThreeManifold.UniversalDeck
end

section
open Set Filter Topology Bundle Manifold IsManifold
open scoped ContDiff
namespace ThreeManifold.RiemannianCoordinates
variable {M : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]

lemma lift_contDiff {f : E3 → M} (hf : ContMDiff 𝓘(ℝ,E3) I3 1 f)
    (hi : ∀ a, Function.Injective (mfderiv 𝓘(ℝ,E3) I3 f a))
    (hl : IsLocalHomeomorph f) {d : E3 → E3} (hd : Continuous d)
    (he : ∀ x, f (d x) = f x) : ContDiff ℝ 1 d := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  let i := hl.localInverseAt (d x)
  have hic := localInverseAt_contMDiffAt hf hi hl (d x)
  rw [he x] at hic
  have heq : d =ᶠ[𝓝 x] fun z => i (f z) := by
    filter_upwards [hd.continuousAt.preimage_mem_nhds
      (i.open_target.mem_nhds hl.self_mem_localInverseAt_target)] with z hz
    have hh := i.right_inv hz
    rw [hl.localInverseAt_symm,he z] at hh
    exact hh.symm
  exact (contMDiffAt_iff_contDiffAt.mp (hic.comp x hf.contMDiffAt)).congr_of_eventuallyEq heq

variable [CompactSpace M] [T2Space M]
lemma exponentialDeck_contDiff (g : SmoothMetric M) (hn : NonpositiveSectionalCurvature g)
    (p : M) (d : UniversalDeck.group (exponential g p)) : ContDiff ℝ 1 (fun v : E3 => d • v) :=
  lift_contDiff (exponential_contMDiff g p)
    (exponential_mfderiv_injective g (npc_noConjugatePoints g hn) p)
    (npc_exponential_isLocalHomeomorph g hn p) d.property.1 (UniversalDeck.map_smul d)

lemma exponentialDeck_inner (g : SmoothMetric M) (hn : NonpositiveSectionalCurvature g)
    (p : M) (d : UniversalDeck.group (exponential g p)) (x u v : E3) :
    (exponentialMetric g hn p).inner (d • x)
      (fderiv ℝ (fun z => d • z) x u) (fderiv ℝ (fun z => d • z) x v) =
    (exponentialMetric g hn p).inner x u v := by
  have hd := (exponentialDeck_contDiff g hn p d).differentiable (by simp)
  have heq : (exponential g p) ∘ (fun z => d • z) = exponential g p :=
    funext (UniversalDeck.map_smul d)
  have hdif := mfderiv_comp x ((exponential_contMDiff g p).mdifferentiable (by simp) (d • x))
    ((exponentialDeck_contDiff g hn p d).contMDiff.mdifferentiable (by simp) x)
  rw [heq,mfderiv_eq_fderiv] at hdif
  have hu := congrArg (fun L : E3 →L[ℝ] E3 => L u) hdif
  have hv := congrArg (fun L : E3 →L[ℝ] E3 => L v) hdif
  change mfderiv 𝓘(ℝ,E3) I3 (exponential g p) x u =
    mfderiv 𝓘(ℝ,E3) I3 (exponential g p) (d • x) (fderiv ℝ (fun z => d • z) x u) at hu
  change mfderiv 𝓘(ℝ,E3) I3 (exponential g p) x v =
    mfderiv 𝓘(ℝ,E3) I3 (exponential g p) (d • x) (fderiv ℝ (fun z => d • z) x v) at hv
  change g.inner (exponential g p (d • x)) _ _ = g.inner (exponential g p x) _ _
  calc
    _ = g.inner (exponential g p (d • x))
        (mfderiv 𝓘(ℝ,E3) I3 (exponential g p) x u)
        (mfderiv 𝓘(ℝ,E3) I3 (exponential g p) x v) :=
      congrArg₂ (fun a b : E3 => g.inner (exponential g p (d • x)) a b) hu.symm hv.symm
    _ = _ := congrArg (fun z : M => g.inner z
      (mfderiv 𝓘(ℝ,E3) I3 (exponential g p) x u : E3)
      (mfderiv 𝓘(ℝ,E3) I3 (exponential g p) x v : E3)) (UniversalDeck.map_smul d x)
end ThreeManifold.RiemannianCoordinates
end

section
open Set Filter Topology
namespace ThreeManifold.QuotientCoverGeometry
variable {E X G : Type*} [TopologicalSpace E] [TopologicalSpace X] [Group G] [MulAction G E]
variable {p : E → X} (hp : IsQuotientCoveringMap p G)
include hp

lemma locallyFinite_graphs [T2Space X] :
    LocallyFinite (fun g : G => {q : E × E | q.2 = g • q.1}) := by
  let := hp.toContinuousConstSMul
  intro q
  by_cases hq : p q.2 = p q.1
  · obtain ⟨d,hd⟩ := hp.apply_eq_iff_mem_orbit.mp hq
    obtain ⟨U,hU,hdis⟩ := hp.disjoint q.1
    have hV : (fun z : E => d • z) '' U ∈ 𝓝 q.2 := by
      rw [← hd]
      exact (Homeomorph.smul d).isOpenEmbedding.image_mem_nhds.mpr hU
    refine ⟨U ×ˢ ((fun z : E => d • z) '' U),prod_mem_nhds hU hV,?_⟩
    apply (finite_singleton d).subset
    rintro g ⟨⟨a,b⟩,hgraph,ha,⟨c,hc,hcb⟩⟩
    have hmove : (d⁻¹*g) • a = c := by
      rw [mul_smul,← hgraph,← hcb,inv_smul_smul]
    have he := hdis (d⁻¹*g) ⟨c,⟨a,ha,hmove⟩,hc⟩
    exact (inv_mul_eq_one.mp he).symm
  · let V := {q : E × E | p q.2 ≠ p q.1}
    have hV : IsOpen V := isClosed_eq (hp.continuous.comp continuous_snd)
      (hp.continuous.comp continuous_fst) |>.isOpen_compl
    refine ⟨V,hV.mem_nhds hq,?_⟩
    apply finite_empty.subset
    rintro g ⟨⟨a,b⟩,hgraph,hne⟩
    exact False.elim (hne (hgraph ▸ hp.map_smul g))

theorem properlyDiscontinuous [T2Space X] : ProperlyDiscontinuousSMul G E := by
  constructor
  intro K L hK hL
  apply ((locallyFinite_graphs hp).finite_nonempty_inter_compact (hK.prod hL)).subset
  rintro g ⟨b,⟨a,ha,rfl⟩,hb⟩
  exact ⟨(a,g•a),rfl,ha,hb⟩

theorem compact_fundamental_set [LocallyCompactSpace E] [CompactSpace X] :
    ∃ K : Set E, IsCompact K ∧ ∀ z : E, ∃ g : G, g • z ∈ K := by
  choose e he using hp.surjective
  choose K hK hKn using fun x : X => exists_compact_mem_nhds (e x)
  have hn : ∀ x : X, p '' K x ∈ 𝓝 x := by
    intro x
    have h := hp.isCoveringMap.isOpenMap.image_mem_nhds (hKn x)
    simpa only [he x] using h
  obtain ⟨s,hs,hcover⟩ := isCompact_univ.elim_nhds_subcover (fun x => p '' K x) (fun x _ => hn x)
  refine ⟨⋃ x ∈ s, K x,s.finite_toSet.isCompact_biUnion (fun x _ => hK x),?_⟩
  intro z
  obtain ⟨x,hxs,y,hy,hpy⟩ := mem_iUnion₂.mp (hcover (mem_univ (p z)))
  obtain ⟨g,hg⟩ := hp.apply_eq_iff_mem_orbit.mp hpy
  refine ⟨g,mem_iUnion₂.mpr ⟨x,hxs,?_⟩⟩
  have hz : g • z = y := hg
  rw [hz]
  exact hy
end ThreeManifold.QuotientCoverGeometry
end

section

open Set Metric

namespace ThreeManifold.NoNPC

section Attainment
variable {G X : Type*} [Group G] [MetricSpace X] [ProperSpace X]
  [MulAction G X] [IsIsometricSMul G X] [ProperlyDiscontinuousSMul G X]

omit [ProperSpace X] [ProperlyDiscontinuousSMul G X] in
lemma conjugate_displacement (g k : G) (x : X) :
    dist (k • x) ((k * g * k⁻¹) • (k • x)) = dist x (g • x) := by
  simp only [mul_smul, inv_smul_smul, dist_smul]

theorem displacement_attains_minimum [Nonempty X] (g : G)
    {K : Set X} (hK : IsCompact K) (hcover : ∀ x : X, ∃ k : G, k • x ∈ K) :
    ∃ x : X, ∀ y : X, dist x (g • x) ≤ dist y (g • y) := by
  let x₀ : X := Classical.choice inferInstance
  let R : ℝ := dist x₀ (g • x₀)
  let S : Set G := {h | (∃ k : G, h = k * g * k⁻¹) ∧
    ∃ y ∈ K, dist y (h • y) ≤ R}
  have hS : S.Finite := by
    apply (finite_disjoint_inter_image (Γ := G) hK (hK.cthickening (r := R))).subset
    rintro h ⟨_, y, hy, hd⟩
    exact ⟨h • y, ⟨y, hy, rfl⟩,
      mem_cthickening_of_dist_le (h • y) y R K hy (by rwa [dist_comm])⟩
  let A : Set ℝ := ⋃ h ∈ S, (fun y : X => dist y (h • y)) '' K
  have hA : IsCompact A := hS.isCompact_biUnion fun h _ =>
    hK.image (continuous_id.dist (isometry_smul X h).continuous)
  have hmem (x : X) (hx : dist x (g • x) ≤ R) : dist x (g • x) ∈ A := by
    obtain ⟨k, hk⟩ := hcover x
    have hd := conjugate_displacement g k x
    apply mem_iUnion.mpr ⟨k * g * k⁻¹, ?_⟩
    apply mem_iUnion.mpr ⟨⟨⟨k, rfl⟩, k • x, hk, hd.trans_le hx⟩, ?_⟩
    exact ⟨k • x, hk, hd⟩
  have hR : R ∈ A := hmem x₀ le_rfl
  obtain ⟨r, hrA, hr⟩ := hA.exists_isLeast ⟨R, hR⟩
  rcases mem_iUnion.mp hrA with ⟨h, hrA⟩
  rcases mem_iUnion.mp hrA with ⟨hh, y, hy, hyr⟩
  obtain ⟨k, rfl⟩ := hh.1
  refine ⟨k⁻¹ • y, fun z => ?_⟩
  have hdisp : dist (k⁻¹ • y) (g • (k⁻¹ • y)) = r := by
    have he := conjugate_displacement g k (k⁻¹ • y)
    simpa only [smul_inv_smul, hyr] using he.symm
  rw [hdisp]
  by_cases hz : dist z (g • z) ≤ R
  · exact hr (hmem z hz)
  · exact (hr hR).trans (le_of_not_ge hz)

omit [ProperSpace X] [IsIsometricSMul G X] [ProperlyDiscontinuousSMul G X] in
lemma attained_minimum_positive (g : G) (hg : g ≠ 1)
    (hfree : ∀ {g : G} {x : X}, g • x = x → g = 1) (x : X) :
    0 < dist x (g • x) := by
  exact dist_pos.mpr (fun h => hg (hfree h.symm))
end Attainment

section ProductShift

lemma product_shift_constant {Y : Type*} [PseudoMetricSpace Y]
    (f : Y → Y) (τ : Y → ℝ)
    (h : ∀ (y z : Y) (t s : ℝ),
      dist (f y) (f z) ^ 2 + ((t + τ y) - (s + τ z)) ^ 2 =
        dist y z ^ 2 + (t - s) ^ 2) :
    ∀ y z, τ y = τ z := by
  intro y z
  have h₀ := h y z 0 0
  have h₁ := h y z 1 0
  nlinarith

lemma zero_shift_pythagoras {Y : Type*} [PseudoMetricSpace Y]
    (y y' : Y) (t ℓ : ℝ) :
    dist y y' ^ 2 + ((t + ℓ) - t) ^ 2 =
      (dist y y' ^ 2 + (t - t) ^ 2) + (dist y y ^ 2 + ((t + ℓ) - t) ^ 2) := by
  simp
end ProductShift

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem shear_orthogonality_impossible {u v : E} (hu : u ≠ 0)
    (h₁ : inner ℝ u v = 0) (h₂ : inner ℝ (u + v) u = 0) : False := by
  have hvu : inner ℝ v u = 0 := by simpa only [real_inner_comm] using h₁
  rw [inner_add_left, hvu, add_zero] at h₂
  exact hu (inner_self_eq_zero.mp h₂)

theorem shear_pythagoras_impossible {u v : E} (hu : u ≠ 0)
    (h₁ : ‖u + v‖ ^ 2 = ‖u‖ ^ 2 + ‖v‖ ^ 2)
    (h₂ : ‖(u + v) + u‖ ^ 2 = ‖u + v‖ ^ 2 + ‖u‖ ^ 2) : False := by
  apply shear_orthogonality_impossible hu
  · have h := norm_add_sq_real u v
    linarith
  · have h := norm_add_sq_real (u + v) u
    linarith
end ThreeManifold.NoNPC
end

section
open Set Filter Topology Bundle Manifold
open scoped ContDiff NNReal
namespace ThreeManifold.RiemannianCoordinates
variable {M : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]
  [CompactSpace M] [T2Space M]

lemma exponentialMetric_coercive (g : SmoothMetric M) (hn : NonpositiveSectionalCurvature g)
    (p : M) : ∃ R : ℝ≥0, 0 < R ∧ ∀ (x v : E3),
      ‖v‖ ≤ R * Real.sqrt ((exponentialMetric g hn p).inner x v v) := by
  obtain ⟨C,hC,hb⟩ := positive_bilinear_norm_bound (show E3 →L[ℝ] E3 →L[ℝ] ℝ from g.inner p)
    (fun v hv => g.pos p v hv)
  refine ⟨⟨Real.sqrt C,Real.sqrt_nonneg C⟩,Real.sqrt_pos.mpr hC,fun x v => ?_⟩
  have hx := exponentialMetric_expanding g hn p x v
  have hy : 0 ≤ (exponentialMetric g hn p).inner x v v :=
    (inner_self_nonneg g p v).trans hx
  have hs := Real.sq_sqrt hC.le
  have ht := Real.sq_sqrt hy
  have hh := (hb v).trans (mul_le_mul_of_nonneg_left hx hC.le)
  change ‖v‖ ≤ Real.sqrt C * Real.sqrt ((exponentialMetric g hn p).inner x v v)
  nlinarith [norm_nonneg v,Real.sqrt_nonneg C,
    Real.sqrt_nonneg ((exponentialMetric g hn p).inner x v v),
    mul_nonneg (Real.sqrt_nonneg C) (Real.sqrt_nonneg ((exponentialMetric g hn p).inner x v v)),
    sq_nonneg (‖v‖-Real.sqrt C*Real.sqrt ((exponentialMetric g hn p).inner x v v))]

abbrev universalMetric (g : SmoothMetric M) (hn : NonpositiveSectionalCurvature g) (p : M) : MetricSpace E3 :=
  RiemannianDistance.metricSpace (exponentialMetric g hn p)

lemma universalMetric_proper (g : SmoothMetric M) (hn : NonpositiveSectionalCurvature g) (p : M) :
    @ProperSpace E3 (universalMetric g hn p).toPseudoMetricSpace := by
  obtain ⟨R,hR,hb⟩ := exponentialMetric_coercive g hn p
  exact RiemannianDistance.properSpace _ R hR hb

lemma universalMetric_deck_isometry (g : SmoothMetric M) (hn : NonpositiveSectionalCurvature g)
    (p : M) (d : UniversalDeck.group (exponential g p)) :
    @Isometry E3 E3 (universalMetric g hn p).toPseudoEMetricSpace
      (universalMetric g hn p).toPseudoEMetricSpace (fun x => d • x) :=
  RiemannianDistance.isometry_of_inner (exponentialMetric g hn p) d.val
    (exponentialDeck_contDiff g hn p d) (exponentialDeck_contDiff g hn p d⁻¹)
    (exponentialDeck_inner g hn p d) (exponentialDeck_inner g hn p d⁻¹)

theorem npc_deck_displacement_minimum [PathConnectedSpace M]
    (g : SmoothMetric M) (hn : NonpositiveSectionalCurvature g) (p : M)
    (d : UniversalDeck.group (exponential g p)) :
    ∃ x : E3, ∀ y : E3,
      @dist E3 (universalMetric g hn p).toPseudoMetricSpace.toDist x (d • x) ≤
      @dist E3 (universalMetric g hn p).toPseudoMetricSpace.toDist y (d • y) := by
  let : MetricSpace E3 := universalMetric g hn p
  let : PseudoMetricSpace E3 := (universalMetric g hn p).toPseudoMetricSpace
  let : PseudoEMetricSpace E3 := (universalMetric g hn p).toPseudoEMetricSpace
  let : ProperSpace E3 := universalMetric_proper g hn p
  let : IsIsometricSMul (UniversalDeck.group (exponential g p)) E3 :=
    ⟨fun d => universalMetric_deck_isometry g hn p d⟩
  have hq := UniversalDeck.quotient_cover (npc_exponential_isCoveringMap g hn p)
  let := QuotientCoverGeometry.properlyDiscontinuous hq
  obtain ⟨K,hK,hcover⟩ := QuotientCoverGeometry.compact_fundamental_set hq
  exact NoNPC.displacement_attains_minimum d hK hcover
end ThreeManifold.RiemannianCoordinates
end

section
open Set Filter Topology Bundle Manifold MeasureTheory
open scoped ContDiff ENNReal NNReal
namespace ThreeManifold.RiemannianDistance
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable (h : ContinuousRiemannianMetric F (TangentSpace 𝓘(ℝ,F) : F → Type _))
variable (g : ContinuousRiemannianMetric E (TangentSpace 𝓘(ℝ,E) : E → Type _))

lemma pathELength_comp_eq_between {f : E → F} (hf : ContDiff ℝ 1 f)
    (hi : ∀ (x u v : E), h.inner (f x) (fderiv ℝ f x u) (fderiv ℝ f x v) = g.inner x u v)
    {γ : ℝ → E} {a b : ℝ} (hγ : ContDiffOn ℝ 1 γ (Icc a b)) :
    letI : RiemannianBundle (TangentSpace 𝓘(ℝ,E) : E → Type _) := ⟨g.toRiemannianMetric⟩
    letI : RiemannianBundle (TangentSpace 𝓘(ℝ,F) : F → Type _) := ⟨h.toRiemannianMetric⟩
    pathELength 𝓘(ℝ,F) (f ∘ γ) a b = pathELength 𝓘(ℝ,E) γ a b := by
  let : RiemannianBundle (TangentSpace 𝓘(ℝ,E) : E → Type _) := ⟨g.toRiemannianMetric⟩
  let : RiemannianBundle (TangentSpace 𝓘(ℝ,F) : F → Type _) := ⟨h.toRiemannianMetric⟩
  simp only [pathELength_eq_lintegral_mfderiv_Ioo]
  apply setLIntegral_congr_fun measurableSet_Ioo
  intro t ht
  have hγt := (hγ.contDiffAt (Icc_mem_nhds ht.1 ht.2)).differentiableAt (by simp)
  dsimp only
  rw [tangent_enorm h,tangent_enorm g]
  have hv : (mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,F) (f ∘ γ) t 1 : F) =
      fderiv ℝ f (γ t) (mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,E) γ t 1 : E) := by
    rw [mfderiv_eq_fderiv,mfderiv_eq_fderiv,fderiv_comp t
      (hf.differentiable (by simp) (γ t)) hγt]
    rfl
  apply congrArg (ENNReal.ofReal ∘ Real.sqrt)
  calc
    _ = h.inner (f (γ t))
        (fderiv ℝ f (γ t) (mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,E) γ t 1 : E))
        (fderiv ℝ f (γ t) (mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,E) γ t 1 : E)) :=
      congrArg₂ (fun u v : F => h.inner (f (γ t)) u v) hv hv
    _ = _ := hi _ _ _

lemma riemannianEDist_map_le_between {f : E → F} (hf : ContDiff ℝ 1 f)
    (hi : ∀ (x u v : E), h.inner (f x) (fderiv ℝ f x u) (fderiv ℝ f x v) = g.inner x u v)
    (x y : E) :
    letI : RiemannianBundle (TangentSpace 𝓘(ℝ,E) : E → Type _) := ⟨g.toRiemannianMetric⟩
    letI : RiemannianBundle (TangentSpace 𝓘(ℝ,F) : F → Type _) := ⟨h.toRiemannianMetric⟩
    riemannianEDist 𝓘(ℝ,F) (f x) (f y) ≤ riemannianEDist 𝓘(ℝ,E) x y := by
  let : RiemannianBundle (TangentSpace 𝓘(ℝ,E) : E → Type _) := ⟨g.toRiemannianMetric⟩
  let : RiemannianBundle (TangentSpace 𝓘(ℝ,F) : F → Type _) := ⟨h.toRiemannianMetric⟩
  apply le_of_forall_gt
  intro r hr
  obtain ⟨γ,h0,h1,hγ,hlen⟩ := exists_lt_of_riemannianEDist_lt hr
  have hc := hf.contMDiff.comp_contMDiffOn hγ
  have hl := riemannianEDist_le_pathELength (I := 𝓘(ℝ,F)) hc rfl rfl (by norm_num : (0:ℝ) ≤ 1)
  simp only [Function.comp_apply,h0,h1] at hl
  rw [pathELength_comp_eq_between h g hf hi (contMDiffOn_iff_contDiffOn.mp hγ)] at hl
  exact hl.trans_lt hlen

theorem isometry_between (f : E ≃ F) (hf : ContDiff ℝ 1 f) (hfi : ContDiff ℝ 1 f.symm)
    (hi : ∀ (x u v : E), h.inner (f x) (fderiv ℝ f x u) (fderiv ℝ f x v) = g.inner x u v)
    (hii : ∀ (x u v : F), g.inner (f.symm x) (fderiv ℝ f.symm x u) (fderiv ℝ f.symm x v) = h.inner x u v) :
    @Isometry E F (metricSpace g).toPseudoEMetricSpace (metricSpace h).toPseudoEMetricSpace f := by
  have hle := riemannianEDist_map_le_between h g hf hi
  have hlei := riemannianEDist_map_le_between g h hfi hii
  intro x y
  apply le_antisymm (hle x y)
  simpa only [Equiv.symm_apply_apply] using hlei (f x) (f y)
end ThreeManifold.RiemannianDistance
end

section
open Set Filter Topology
namespace ThreeManifold.UniversalCover
variable {E F X : Type*} [TopologicalSpace E] [TopologicalSpace F] [TopologicalSpace X]
  [SimplyConnectedSpace E] [LocallyPathConnectedSpace E]
  [SimplyConnectedSpace F] [LocallyPathConnectedSpace F]
  {p : E → X} {q : F → X}

theorem exists_based_homeomorph (hp : IsCoveringMap p) (hq : IsCoveringMap q)
    (a : E) (b : F) (hab : p a = q b) :
    ∃ e : E ≃ₜ F, e a = b ∧ ∀ z, q (e z) = p z := by
  obtain ⟨f,⟨hfa,hfp⟩,_⟩ := hq.existsUnique_continuousMap_lifts ⟨p,hp.continuous⟩ a b hab.symm
  obtain ⟨g,⟨hgb,hgp⟩,_⟩ := hp.existsUnique_continuousMap_lifts ⟨q,hq.continuous⟩ b a hab
  have hfg : Function.RightInverse g f := by
    have he : f ∘ g = id := hq.eq_of_comp_eq (f.continuous.comp g.continuous) continuous_id
      (funext (fun z => (congr_fun hfp (g z)).trans (congr_fun hgp z))) b (by simp [hgb,hfa])
    exact congr_fun he
  have hgf : Function.LeftInverse g f := by
    have he : g ∘ f = id := hp.eq_of_comp_eq (g.continuous.comp f.continuous) continuous_id
      (funext (fun z => (congr_fun hgp (f z)).trans (congr_fun hfp z))) a (by simp [hfa,hgb])
    exact congr_fun he
  exact ⟨⟨⟨f,g,hgf,hfg⟩,f.continuous,g.continuous⟩,hfa,fun z => congr_fun hfp z⟩
end ThreeManifold.UniversalCover
end

section
open Set Filter Topology Bundle Manifold IsManifold
open scoped ContDiff
namespace ThreeManifold.RiemannianCoordinates
variable {M : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]

lemma lift_map_contDiff {f k : E3 → M} (hf : ContMDiff 𝓘(ℝ,E3) I3 1 f)
    (hk : ContMDiff 𝓘(ℝ,E3) I3 1 k)
    (hi : ∀ a, Function.Injective (mfderiv 𝓘(ℝ,E3) I3 f a))
    (hl : IsLocalHomeomorph f) {d : E3 → E3} (hd : Continuous d)
    (he : ∀ x, f (d x) = k x) : ContDiff ℝ 1 d := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  let i := hl.localInverseAt (d x)
  have hic := localInverseAt_contMDiffAt hf hi hl (d x)
  rw [he x] at hic
  have heq : d =ᶠ[𝓝 x] fun z => i (k z) := by
    filter_upwards [hd.continuousAt.preimage_mem_nhds
      (i.open_target.mem_nhds hl.self_mem_localInverseAt_target)] with z hz
    have hh := i.right_inv hz
    rw [hl.localInverseAt_symm,he z] at hh
    exact hh.symm
  exact (contMDiffAt_iff_contDiffAt.mp (hic.comp x hk.contMDiffAt)).congr_of_eventuallyEq heq

variable [CompactSpace M] [T2Space M]
lemma exponentialChange_contDiff (g : SmoothMetric M) (hn : NonpositiveSectionalCurvature g)
    {p q : M} {e : E3 → E3} (hc : Continuous e)
    (he : ∀ v, exponential g q (e v) = exponential g p v) : ContDiff ℝ 1 e :=
  lift_map_contDiff (exponential_contMDiff g q) (exponential_contMDiff g p)
    (exponential_mfderiv_injective g (npc_noConjugatePoints g hn) q)
    (npc_exponential_isLocalHomeomorph g hn q) hc he

lemma exponentialChange_inner (g : SmoothMetric M) (hn : NonpositiveSectionalCurvature g)
    {p q : M} {e : E3 → E3} (hc : Continuous e)
    (he : ∀ v, exponential g q (e v) = exponential g p v) (x u v : E3) :
    (exponentialMetric g hn q).inner (e x) (fderiv ℝ e x u) (fderiv ℝ e x v) =
      (exponentialMetric g hn p).inner x u v := by
  have heq : exponential g q ∘ e = exponential g p := funext he
  have hdif := mfderiv_comp x ((exponential_contMDiff g q).mdifferentiable (by simp) (e x))
    ((exponentialChange_contDiff g hn hc he).contMDiff.mdifferentiable (by simp) x)
  rw [heq,mfderiv_eq_fderiv] at hdif
  have hu := congrArg (fun L : E3 →L[ℝ] E3 => L u) hdif
  have hv := congrArg (fun L : E3 →L[ℝ] E3 => L v) hdif
  change mfderiv 𝓘(ℝ,E3) I3 (exponential g p) x u =
    mfderiv 𝓘(ℝ,E3) I3 (exponential g q) (e x) (fderiv ℝ e x u) at hu
  change mfderiv 𝓘(ℝ,E3) I3 (exponential g p) x v =
    mfderiv 𝓘(ℝ,E3) I3 (exponential g q) (e x) (fderiv ℝ e x v) at hv
  change g.inner (exponential g q (e x)) _ _ = g.inner (exponential g p x) _ _
  calc
    _ = g.inner (exponential g q (e x))
        (mfderiv 𝓘(ℝ,E3) I3 (exponential g p) x u)
        (mfderiv 𝓘(ℝ,E3) I3 (exponential g p) x v) :=
      congrArg₂ (fun a b : E3 => g.inner (exponential g q (e x)) a b) hu.symm hv.symm
    _ = _ := congrArg (fun z : M => g.inner z
      (mfderiv 𝓘(ℝ,E3) I3 (exponential g p) x u : E3)
      (mfderiv 𝓘(ℝ,E3) I3 (exponential g p) x v : E3)) (he x)

theorem exists_exponential_coordinates (g : SmoothMetric M) (hn : NonpositiveSectionalCurvature g)
    {p q : M} (a b : E3) (hab : exponential g p a = exponential g q b) :
    ∃ e : E3 ≃ₜ E3, e a = b ∧ (∀ z, exponential g q (e z) = exponential g p z) ∧
      ContDiff ℝ 1 e ∧ ContDiff ℝ 1 e.symm ∧
      @Isometry E3 E3 (universalMetric g hn p).toPseudoEMetricSpace
        (universalMetric g hn q).toPseudoEMetricSpace e := by
  obtain ⟨e,hea,he⟩ := UniversalCover.exists_based_homeomorph
    (npc_exponential_isCoveringMap g hn p) (npc_exponential_isCoveringMap g hn q) a b hab
  have hei (z : E3) : exponential g p (e.symm z) = exponential g q z := by
    simpa only [e.apply_symm_apply] using (he (e.symm z)).symm
  have hc := exponentialChange_contDiff g hn e.continuous he
  have hci := exponentialChange_contDiff g hn e.symm.continuous hei
  refine ⟨e,hea,he,hc,hci,?_⟩
  exact RiemannianDistance.isometry_between (exponentialMetric g hn q) (exponentialMetric g hn p)
    e.toEquiv hc hci (exponentialChange_inner g hn e.continuous he)
      (exponentialChange_inner g hn e.symm.continuous hei)
end ThreeManifold.RiemannianCoordinates
end

section
open Set Filter Topology Bundle Manifold MeasureTheory
open scoped ContDiff ENNReal NNReal
namespace ThreeManifold.RiemannianDistance
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (g : ContinuousRiemannianMetric E (TangentSpace 𝓘(ℝ,E) : E → Type _))

lemma functional_le_pathELength (L : E →L[ℝ] ℝ)
    (hL : ∀ (x v : E), |L v| ≤ Real.sqrt (g.inner x v v))
    {γ : ℝ → E} {a b : ℝ} (hγ : ContDiffOn ℝ 1 γ (Icc a b)) (hab : a ≤ b) :
    letI : RiemannianBundle (TangentSpace 𝓘(ℝ,E) : E → Type _) := ⟨g.toRiemannianMetric⟩
    ENNReal.ofReal |L (γ b-γ a)| ≤ pathELength 𝓘(ℝ,E) γ a b := by
  let : RiemannianBundle (TangentSpace 𝓘(ℝ,E) : E → Type _) := ⟨g.toRiemannianMetric⟩
  have h := enorm_sub_le_lintegral_deriv_of_contDiffOn_Icc (L.contDiff.comp_contDiffOn hγ) hab
  simp only [Function.comp_apply,← L.map_sub,← ofReal_norm,Real.norm_eq_abs] at h
  apply h.trans
  rw [pathELength_eq_lintegral_mfderiv_Ioo]
  rw [Measure.restrict_congr_set (Ioo_ae_eq_Icc (μ := volume)).symm]
  apply setLIntegral_mono' measurableSet_Ioo
  intro t ht
  have htγ := (hγ.contDiffAt (Icc_mem_nhds ht.1 ht.2)).differentiableAt (by simp)
  have hd := L.hasFDerivAt.comp t htγ.hasDerivAt.hasFDerivAt
  have he : deriv (L ∘ γ) t = L (deriv γ t) := by
    rw [hd.hasDerivAt.deriv]
    simp
  have hv : (mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,E) γ t 1 : E) = deriv γ t := by
    rw [mfderiv_eq_fderiv]
    rfl
  rw [tangent_enorm g]
  rw [congrArg (fun v : E => g.inner (γ t) v v) hv,he]
  exact ENNReal.ofReal_le_ofReal (hL (γ t) (deriv γ t))

lemma functional_le_riemannianEDist (L : E →L[ℝ] ℝ)
    (hL : ∀ (x v : E), |L v| ≤ Real.sqrt (g.inner x v v)) (x y : E) :
    letI : RiemannianBundle (TangentSpace 𝓘(ℝ,E) : E → Type _) := ⟨g.toRiemannianMetric⟩
    ENNReal.ofReal |L (y-x)| ≤ riemannianEDist 𝓘(ℝ,E) x y := by
  let : RiemannianBundle (TangentSpace 𝓘(ℝ,E) : E → Type _) := ⟨g.toRiemannianMetric⟩
  apply le_of_forall_gt
  intro r hr
  obtain ⟨γ,h0,h1,hγ,hlen⟩ := exists_lt_of_riemannianEDist_lt hr
  have hb := functional_le_pathELength g L hL (contMDiffOn_iff_contDiffOn.mp hγ) (by norm_num : (0:ℝ) ≤ 1)
  rw [h0,h1] at hb
  exact hb.trans_lt hlen

lemma positive_bilinear_cauchy_schwarz (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hs : ∀ v w, B v w = B w v) (hp : ∀ v, 0 ≤ B v v) (v w : E) :
    B v w ^ 2 ≤ B v v * B w w := by
  have h (t : ℝ) := hp (v + t • w)
  simp only [map_add,map_smul,_root_.add_apply,_root_.smul_apply,
    smul_eq_mul] at h
  rw [hs w v] at h
  have hd := discrim_le_zero (a := B w w) (b := 2*B v w) (c := B v v)
    (fun t => by nlinarith only [h t])
  unfold discrim at hd
  nlinarith only [hd]

theorem bilinear_le_riemannianEDist (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hs : ∀ v w, B v w = B w v) (hp : ∀ v ≠ 0, 0 < B v v)
    (hB : ∀ (x v : E), B v v ≤ g.inner x v v) (x y : E) :
    letI : RiemannianBundle (TangentSpace 𝓘(ℝ,E) : E → Type _) := ⟨g.toRiemannianMetric⟩
    ENNReal.ofReal (Real.sqrt (B (y-x) (y-x))) ≤ riemannianEDist 𝓘(ℝ,E) x y := by
  let : RiemannianBundle (TangentSpace 𝓘(ℝ,E) : E → Type _) := ⟨g.toRiemannianMetric⟩
  by_cases he : y-x = 0
  · simp [he]
  have hpn (v : E) : 0 ≤ B v v := by
    by_cases hv : v = 0
    · simp [hv]
    · exact (hp v hv).le
  let d := y-x
  let c := Real.sqrt (B d d)
  have hc : 0 < c := Real.sqrt_pos.mpr (hp d he)
  have hc2 : c^2 = B d d := Real.sq_sqrt (hpn d)
  let L : E →L[ℝ] ℝ := c⁻¹ • B d
  have hL (z v : E) : |L v| ≤ Real.sqrt (g.inner z v v) := by
    have hcs := positive_bilinear_cauchy_schwarz B hs hpn d v
    have hg : 0 ≤ g.inner z v v := (hpn v).trans (hB z v)
    have hh := mul_le_mul_of_nonneg_left (hB z v) (hpn d)
    have hsq := Real.sq_sqrt hg
    change |c⁻¹ * B d v| ≤ _
    rw [abs_mul,abs_of_pos (inv_pos.mpr hc)]
    apply (inv_mul_le_iff₀ hc).mpr
    have hab : |B d v|^2 = B d v^2 := sq_abs _
    nlinarith [abs_nonneg (B d v),Real.sqrt_nonneg (g.inner z v v),
      mul_nonneg hc.le (Real.sqrt_nonneg (g.inner z v v))]
  have hd : |L (y-x)| = c := by
    change |c⁻¹ * B d d| = c
    rw [← hc2]
    have hh : c⁻¹ * c^2 = c := by field_simp
    rw [hh,abs_of_pos hc]
  simpa only [hd] using functional_le_riemannianEDist g L hL x y
end ThreeManifold.RiemannianDistance
end

section
open Set Filter Topology Bundle Manifold IsManifold MeasureTheory
open scoped ContDiff ENNReal
namespace ThreeManifold.RiemannianCoordinates
variable {M : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]
  [CompactSpace M] [T2Space M]

lemma globalGeodesic_speed (g : SmoothMetric M) (p : M) (v : E3) (t : ℝ) :
    g.inner (globalGeodesic g (fiberPhase p v) t)
      (velocity (globalGeodesic g (fiberPhase p v)) t)
      (velocity (globalGeodesic g (fiberPhase p v)) t) = g.inner p v v := by
  let γ := globalGeodesic g (fiberPhase p v)
  have hγ := globalGeodesic_isGeodesic g (fiberPhase p v)
  let f : ℝ → ℝ := fun r => g.inner (γ r) (velocity γ r) (velocity γ r)
  have hd (r : ℝ) : HasDerivAt f 0 r := geodesic_speed_hasDerivAt g isOpen_univ hγ (mem_univ r)
  have he : f t = f 0 := isOpen_univ.is_const_of_deriv_eq_zero isPreconnected_univ
    (fun r _ => (hd r).differentiableAt.differentiableWithinAt)
    (fun r _ => (hd r).deriv) (mem_univ t) (mem_univ 0)
  refine he.trans ?_
  exact congrArg (phaseEnergy g) (globalGeodesic_initial g (fiberPhase p v))

lemma exponentialMetric_radial (g : SmoothMetric M) (hn : NonpositiveSectionalCurvature g)
    (p : M) (v : E3) (t : ℝ) :
    (exponentialMetric g hn p).inner (t • v) v v = g.inner p v v := by
  have hr : ContDiff ℝ 1 (fun r : ℝ => r • v) := contDiff_id.smul contDiff_const
  have hd : mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,E3) (fun r : ℝ => r • v) t 1 = v := by
    rw [mfderiv_eq_fderiv]
    change deriv (fun r : ℝ => r • v) t = v
    simpa only [one_smul,id_eq] using ((hasDerivAt_id t).smul_const v).deriv
  have heq : exponential g p ∘ (fun r : ℝ => r • v) = globalGeodesic g (fiberPhase p v) :=
    funext (exponential_scale g p v)
  have hc := mfderiv_comp t ((exponential_contMDiff g p).mdifferentiable (by simp) (t • v))
    (hr.contMDiff.mdifferentiable (by simp) t)
  rw [heq] at hc
  have hv := congrArg (fun L : ℝ →L[ℝ] E3 => L 1) hc
  change (velocity (globalGeodesic g (fiberPhase p v)) t : E3) =
    mfderiv 𝓘(ℝ,E3) I3 (exponential g p) (t • v)
      (mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,E3) (fun r : ℝ => r • v) t 1) at hv
  rw [hd] at hv
  rw [exponentialMetric_inner]
  calc
    _ = g.inner (exponential g p (t • v))
      (velocity (globalGeodesic g (fiberPhase p v)) t : E3)
      (velocity (globalGeodesic g (fiberPhase p v)) t : E3) :=
        congrArg₂ (fun a b : E3 => g.inner (exponential g p (t • v)) a b) hv.symm hv.symm
    _ = g.inner (globalGeodesic g (fiberPhase p v) t)
      (velocity (globalGeodesic g (fiberPhase p v)) t : E3)
      (velocity (globalGeodesic g (fiberPhase p v)) t : E3) := by
        rw [exponential_scale]
    _ = _ := globalGeodesic_speed g p v t

lemma exponentialMetric_radial_length (g : SmoothMetric M) (hn : NonpositiveSectionalCurvature g)
    (p : M) (v : E3) (a b : ℝ) :
    letI : RiemannianBundle (TangentSpace 𝓘(ℝ,E3) : E3 → Type _) :=
      ⟨(exponentialMetric g hn p).toRiemannianMetric⟩
    pathELength 𝓘(ℝ,E3) (fun r : ℝ => r • v) a b =
      ENNReal.ofReal (Real.sqrt (g.inner p v v)) * ENNReal.ofReal (b-a) := by
  let : RiemannianBundle (TangentSpace 𝓘(ℝ,E3) : E3 → Type _) :=
      ⟨(exponentialMetric g hn p).toRiemannianMetric⟩
  rw [pathELength_eq_lintegral_mfderiv_Icc]
  have hh (t : ℝ) : ‖mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,E3) (fun r : ℝ => r • v) t 1‖ₑ =
      ENNReal.ofReal (Real.sqrt (g.inner p v v)) := by
    rw [RiemannianDistance.tangent_enorm (exponentialMetric g hn p)]
    have hd : (mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,E3) (fun r : ℝ => r • v) t 1 : E3) = v := by
      rw [mfderiv_eq_fderiv]
      change deriv (fun r : ℝ => r • v) t = v
      simpa only [one_smul,id_eq] using ((hasDerivAt_id t).smul_const v).deriv
    rw [congrArg (fun w : E3 => (exponentialMetric g hn p).inner (t • v) w w) hd,
      exponentialMetric_radial]
  simp_rw [hh]
  simp [Real.volume_Icc]

lemma universalMetric_lower (g : SmoothMetric M) (hn : NonpositiveSectionalCurvature g)
    (p : M) (x y : E3) :
    Real.sqrt (g.inner p (y-x) (y-x)) ≤
      @dist E3 (universalMetric g hn p).toPseudoMetricSpace.toDist x y := by
  have hh := RiemannianDistance.bilinear_le_riemannianEDist (exponentialMetric g hn p)
    (show E3 →L[ℝ] E3 →L[ℝ] ℝ from g.inner p) (g.symm p) (g.pos p)
    (exponentialMetric_expanding g hn p) x y
  let : RiemannianBundle (TangentSpace 𝓘(ℝ,E3) : E3 → Type _) :=
      ⟨(exponentialMetric g hn p).toRiemannianMetric⟩
  change ENNReal.ofReal _ ≤ @edist E3 (universalMetric g hn p).toPseudoEMetricSpace.toEDist x y at hh
  rw [@edist_dist E3 (universalMetric g hn p).toPseudoMetricSpace] at hh
  exact (ENNReal.ofReal_le_ofReal_iff (@dist_nonneg E3 (universalMetric g hn p).toPseudoMetricSpace x y)).mp hh

lemma universalMetric_radial_zero (g : SmoothMetric M) (hn : NonpositiveSectionalCurvature g)
    (p : M) (v : E3) :
    @dist E3 (universalMetric g hn p).toPseudoMetricSpace.toDist 0 v = Real.sqrt (g.inner p v v) := by
  apply le_antisymm
  · let : RiemannianBundle (TangentSpace 𝓘(ℝ,E3) : E3 → Type _) :=
      ⟨(exponentialMetric g hn p).toRiemannianMetric⟩
    have hc : ContMDiff 𝓘(ℝ,ℝ) 𝓘(ℝ,E3) 1 (fun r : ℝ => r • v) :=
      (contDiff_id.smul contDiff_const).contMDiff
    have hh := riemannianEDist_le_pathELength hc.contMDiffOn (by simp : (0:ℝ) • v = 0)
      (by simp : (1:ℝ) • v = v) (by norm_num : (0:ℝ) ≤ 1)
    rw [exponentialMetric_radial_length] at hh
    simp only [sub_zero,ENNReal.ofReal_one,mul_one] at hh
    change @edist E3 (universalMetric g hn p).toPseudoEMetricSpace.toEDist 0 v ≤ _ at hh
    rw [@edist_dist E3 (universalMetric g hn p).toPseudoMetricSpace] at hh
    exact (ENNReal.ofReal_le_ofReal_iff (Real.sqrt_nonneg _)).mp hh
  · simpa only [sub_zero] using universalMetric_lower g hn p 0 v
end ThreeManifold.RiemannianCoordinates
end

open Set Filter Topology Bundle Manifold IsManifold
open scoped ContDiff
namespace ThreeManifold.RiemannianCoordinates
variable {M : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]
  [CompactSpace M] [T2Space M]

lemma exponential_recenter (g : SmoothMetric M) (p : M) (v : E3) (t s : ℝ) :
    exponential g (globalGeodesic g (fiberPhase p v) t)
      (s • (velocity (globalGeodesic g (fiberPhase p v)) t : E3)) =
        exponential g p ((t+s) • v) := by
  trans globalGeodesic g (fiberPhase (globalGeodesic g (fiberPhase p v) t)
    (velocity (globalGeodesic g (fiberPhase p v)) t : E3)) s
  · exact exponential_scale g _ _ s
  rw [exponential_scale]
  exact congrArg Bundle.TotalSpace.proj (geodesicFlow_add g (fiberPhase p v) t s)

lemma recenter_radial_line (g : SmoothMetric M) (hn : NonpositiveSectionalCurvature g)
    (p : M) (v : E3) (t : ℝ) {e : E3 ≃ₜ E3}
    (he0 : e (t • v) = 0)
    (he : ∀ z, exponential g (globalGeodesic g (fiberPhase p v) t) (e z) = exponential g p z)
    (s : ℝ) : e ((t+s) • v) = s • (velocity (globalGeodesic g (fiberPhase p v)) t : E3) := by
  let q := globalGeodesic g (fiberPhase p v) t
  let w : E3 := velocity (globalGeodesic g (fiberPhase p v)) t
  change e ((t+s) • v) = s • w
  have hh : (fun r : ℝ => e ((t+r) • v)) =
      (fun r : ℝ => r • w) := by
    refine (npc_exponential_isCoveringMap g hn q).eq_of_comp_eq
      (e.continuous.comp ((continuous_const.add continuous_id).smul continuous_const))
      (continuous_id.smul continuous_const) ?_ 0 ?_
    · funext r
      exact (he _).trans (exponential_recenter g p v t r).symm
    · simpa only [add_zero,zero_smul] using he0
  exact congrFun hh s

lemma positive_form_smul (g : SmoothMetric M) (p : M) (v : E3) (t : ℝ) :
    g.inner p (t • v) (t • v) = t^2 * g.inner p v v := by
  let _ : CompactSpace M := inferInstance
  let _ : T2Space M := inferInstance
  let B : E3 →L[ℝ] E3 →L[ℝ] ℝ := g.inner p
  change B (t • v) (t • v) = t^2 * B v v
  simp only [map_smul,_root_.smul_apply,smul_eq_mul]
  ring

lemma positive_form_parallelogram (g : SmoothMetric M) (p : M) (u v : E3) :
    g.inner p (u+v) (u+v) + g.inner p (u-v) (u-v) =
      2*g.inner p u u + 2*g.inner p v v := by
  let _ : CompactSpace M := inferInstance
  let _ : T2Space M := inferInstance
  let B : E3 →L[ℝ] E3 →L[ℝ] ℝ := g.inner p
  change B (u+v) (u+v) + B (u-v) (u-v) = 2*B u u + 2*B v v
  simp only [map_add,map_sub,_root_.add_apply,_root_.sub_apply]
  ring

lemma universalMetric_lower_sq (g : SmoothMetric M) (hn : NonpositiveSectionalCurvature g)
    (p : M) (x y : E3) :
    g.inner p (y-x) (y-x) ≤
      (@dist E3 (universalMetric g hn p).toPseudoMetricSpace.toDist x y)^2 := by
  have h := universalMetric_lower g hn p x y
  have hs := Real.sq_sqrt (inner_self_nonneg g p (y-x))
  have hd := @dist_nonneg E3 (universalMetric g hn p).toPseudoMetricSpace x y
  nlinarith [Real.sqrt_nonneg (g.inner p (y-x) (y-x))]

lemma universalMetric_distance_zero_sq (g : SmoothMetric M) (hn : NonpositiveSectionalCurvature g)
    (p : M) (x : E3) :
    (@dist E3 (universalMetric g hn p).toPseudoMetricSpace.toDist 0 x)^2 =
      g.inner p x x := by
  rw [universalMetric_radial_zero,Real.sq_sqrt (inner_self_nonneg g p x)]

theorem universalMetric_radial_CN (g : SmoothMetric M) (hn : NonpositiveSectionalCurvature g)
    (p : M) (v z : E3) :
    let D := @dist E3 (universalMetric g hn p).toPseudoMetricSpace.toDist
    D ((1/2:ℝ) • v) z ^2 ≤ (D 0 z ^2 + D v z ^2)/2 - D 0 v ^2/4 := by
  let m := (1/2:ℝ) • v
  let q := globalGeodesic g (fiberPhase p v) (1/2)
  let w : E3 := velocity (globalGeodesic g (fiberPhase p v)) (1/2)
  have hbase : exponential g p m = exponential g q 0 := by
    rw [exponential_zero]
    exact exponential_scale g p v (1/2)
  obtain ⟨e,he0,he,hc,hci,hi⟩ := exists_exponential_coordinates g hn m 0 hbase
  have heA : e 0 = (-1/2:ℝ) • w := by
    have hh : e (((1/2:ℝ)+(-1/2)) • v) = (-1/2:ℝ) • w :=
      recenter_radial_line g hn p v (1/2) he0 he (-1/2)
    norm_num only [show (1/2:ℝ)+(-1/2)=0 by norm_num,zero_smul] at hh
    simpa only [neg_div] using hh
  have heB : e v = (1/2:ℝ) • w := by
    have hh : e (((1/2:ℝ)+(1/2)) • v) = (1/2:ℝ) • w :=
      recenter_radial_line g hn p v (1/2) he0 he (1/2)
    norm_num only [show (1/2:ℝ)+(1/2)=1 by norm_num,one_smul] at hh
    exact hh
  let D := @dist E3 (universalMetric g hn p).toPseudoMetricSpace.toDist
  let Q := @dist E3 (universalMetric g hn q).toPseudoMetricSpace.toDist
  have hid (a b : E3) : Q (e a) (e b) = D a b := by
    exact @Isometry.dist_eq E3 E3 (universalMetric g hn p).toPseudoMetricSpace
      (universalMetric g hn q).toPseudoMetricSpace e hi a b
  have hmid : D m z ^2 = g.inner q (e z) (e z) := by
    rw [← hid,he0]
    exact universalMetric_distance_zero_sq g hn q (e z)
  have ha : g.inner q (e z + (1/2:ℝ) • w) (e z + (1/2:ℝ) • w) ≤ D 0 z ^2 := by
    have hh := universalMetric_lower_sq g hn q (e 0) (e z)
    change g.inner q (e z - e 0) (e z - e 0) ≤ Q (e 0) (e z) ^2 at hh
    rw [hid,heA] at hh
    simpa only [neg_div,neg_smul,sub_neg_eq_add] using hh
  have hb : g.inner q (e z - (1/2:ℝ) • w) (e z - (1/2:ℝ) • w) ≤ D v z ^2 := by
    have hh := universalMetric_lower_sq g hn q (e v) (e z)
    change g.inner q (e z - e v) (e z - e v) ≤ Q (e v) (e z) ^2 at hh
    rwa [hid,heB] at hh
  have hp := positive_form_parallelogram g q (e z) ((1/2:ℝ) • w)
  rw [positive_form_smul] at hp
  have hw : g.inner q w w = g.inner p v v := globalGeodesic_speed g p v (1/2)
  have hv : D 0 v ^2 = g.inner p v v := universalMetric_distance_zero_sq g hn p v
  change D m z ^2 ≤ _
  nlinarith only [ha,hb,hp,hw,hv,hmid]
end ThreeManifold.RiemannianCoordinates

end

end OAI
