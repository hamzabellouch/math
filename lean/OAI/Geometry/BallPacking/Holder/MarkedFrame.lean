import Mathlib
import OAI.Geometry.BallPacking.Holder.MarkedJets

namespace OAI

noncomputable section
namespace HigherDimensionalBallPacking.Rigidity.HolderCompletion

section
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
local instance markedFrameInst1 : NormedAddCommGroup (E →L[ℝ] E) := ContinuousLinearMap.toNormedAddCommGroup
local instance markedFrameInst2 : NormedSpace ℝ (E →L[ℝ] E) := ContinuousLinearMap.toNormedSpace
local instance markedFrameInst3 : NormedAddCommGroup (COne ℂ E) := inferInstance
local instance markedFrameInst4 : NormedSpace ℝ (COne ℂ E) := inferInstance
local instance markedFrameInst5 : NormedAddCommGroup (HMap ℂ E) := inferInstance
local instance markedFrameInst6 : NormedSpace ℝ (HMap ℂ E) := inferInstance

omit [CompleteSpace E] in
lemma coefficientDeriv_zero_outside {K : Set ℂ} (hK : IsClosed K)
    (M : COne ℂ (E →L[ℝ] E)) (c : ℝ)
    (hM : ∀ z ∉ K, cValue M z = c • ContinuousLinearMap.id ℝ E)
    {z : ℂ} (hz : z ∉ K) : cDeriv M z = 0 := by
  have he : (cValue M : ℂ → E →L[ℝ] E) =ᶠ[𝓝 z] fun _ => c • ContinuousLinearMap.id ℝ E := by
    filter_upwards [hK.isOpen_compl.mem_nhds hz] with w hw
    exact hM w hw
  rw [← c_fderiv,he.fderiv_eq]
  exact (hasFDerivAt_const (𝕜 := ℝ) (c • ContinuousLinearMap.id ℝ E) z).fderiv

omit [CompleteSpace E] in
lemma coefficientAction_mem_marked {K : Set ℂ} (hK : IsClosed K)
    (M : COne ℂ (E →L[ℝ] E)) (c : ℝ)
    (hM : ∀ z ∉ K, cValue M z = c • ContinuousLinearMap.id ℝ E)
    {u : COne ℂ E} (hu : u ∈ markedModel K) : coefficientAction M u ∈ markedModel K := by
  refine ⟨?_,?_⟩
  · change cValue M 0 (cValue u 0) = 0
    have hu0 : cValue u 0 = 0 := hu.1
    rw [hu0,map_zero]
  · change standardJetCR (coefficientAction M u) ∈ supportedHolder K
    apply (mem_supportedHolder _ K).mpr
    intro z hz
    have hzD := coefficientDeriv_zero_outside hK M c hM hz
    have hzC := hM z hz
    have huZ := (mem_supportedHolder (standardJetCR u) K).mp hu.2 z hz
    rw [standardJetCR_value] at huZ
    rw [standardJetCR_value,coefficientAction_deriv]
    simp only [add_apply,ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.flip_apply,hzD,zero_apply,add_zero,hzC,
      smul_apply,ContinuousLinearMap.id_apply]
    rw [smul_comm Complex.I c,←smul_sub]
    exact (congrArg (fun v : E => c • v) huZ).trans (smul_zero c)

variable {K : Set ℂ}
local instance markedFrameInst7 : NormedAddCommGroup (markedModel (E := E) K) := inferInstance
local instance markedFrameInst8 : NormedSpace ℝ (markedModel (E := E) K) := inferInstance
local instance markedFrameInst9 : NormedAddCommGroup (supportedHolder (E := E) K) := inferInstance
local instance markedFrameInst10 : NormedSpace ℝ (supportedHolder (E := E) K) := inferInstance

def markedCoefficientAction (hK : IsClosed K) (M : COne ℂ (E →L[ℝ] E)) (c : ℝ)
    (hM : ∀ z ∉ K, cValue M z = c • ContinuousLinearMap.id ℝ E) :
    markedModel (E := E) K →L[ℝ] markedModel (E := E) K :=
  (coefficientAction M).restrict (fun _u hu => coefficientAction_mem_marked hK M c hM hu)

omit [CompleteSpace E] in
@[simp] lemma markedCoefficientAction_value (hK : IsClosed K) (M : COne ℂ (E →L[ℝ] E)) (c : ℝ)
    (hM : ∀ z ∉ K, cValue M z = c • ContinuousLinearMap.id ℝ E)
    (u : markedModel (E := E) K) (z : ℂ) :
    cValue (markedCoefficientAction hK M c hM u).val z = cValue M z (cValue u.val z) := rfl

def holderCoefficientAction (M : HMap ℂ (E →L[ℝ] E)) : HMap ℂ E →L[ℝ] HMap ℂ E :=
  bilinCLM (X := ℂ) (α := (1:ℝ)/3) (ContinuousLinearMap.apply (E := E) ℝ E).flip M

omit [CompleteSpace E] in
@[simp] lemma holderCoefficientAction_value (M : HMap ℂ (E →L[ℝ] E)) (g : HMap ℂ E) (z : ℂ) :
    valueCLM _ (holderCoefficientAction M g) z = valueCLM _ M z (valueCLM _ g z) := rfl

def supportedCoefficientAction (M : HMap ℂ (E →L[ℝ] E)) :
    supportedHolder (E := E) K →L[ℝ] supportedHolder (E := E) K :=
  (holderCoefficientAction M).restrict (fun g hg => by
    apply (mem_supportedHolder _ K).mpr
    intro z hz
    rw [holderCoefficientAction_value,(mem_supportedHolder g K).mp hg z hz,map_zero])

omit [CompleteSpace E] in
@[simp] lemma supportedCoefficientAction_value (M : HMap ℂ (E →L[ℝ] E))
    (g : supportedHolder (E := E) K) (z : ℂ) :
    valueCLM _ (supportedCoefficientAction M g).val z = valueCLM _ M z (valueCLM _ g.val z) := rfl

def markedCoefficientEquiv (hK : IsClosed K) (M N : COne ℂ (E →L[ℝ] E)) (c d : ℝ)
    (hM : ∀ z ∉ K, cValue M z = c • ContinuousLinearMap.id ℝ E)
    (hN : ∀ z ∉ K, cValue N z = d • ContinuousLinearMap.id ℝ E)
    (hNM : ∀ z v, cValue N z (cValue M z v) = v)
    (hMN : ∀ z v, cValue M z (cValue N z v) = v) :
    markedModel (E := E) K ≃L[ℝ] markedModel (E := E) K :=
  ContinuousLinearEquiv.equivOfInverse (markedCoefficientAction hK M c hM)
    (markedCoefficientAction hK N d hN)
    (by
      intro u; apply Subtype.ext; apply cValue_ext; intro z
      simpa only [markedCoefficientAction_value] using hNM z (cValue u.val z))
    (by
      intro u; apply Subtype.ext; apply cValue_ext; intro z
      simpa only [markedCoefficientAction_value] using hMN z (cValue u.val z))

def supportedCoefficientEquiv (M N : HMap ℂ (E →L[ℝ] E))
    (hNM : ∀ z v, valueCLM _ N z (valueCLM _ M z v) = v)
    (hMN : ∀ z v, valueCLM _ M z (valueCLM _ N z v) = v) :
    supportedHolder (E := E) K ≃L[ℝ] supportedHolder (E := E) K :=
  ContinuousLinearEquiv.equivOfInverse (supportedCoefficientAction M) (supportedCoefficientAction N)
    (by intro g; apply Subtype.ext; apply value_ext; intro z; exact hNM z _)
    (by intro g; apply Subtype.ext; apply value_ext; intro z; exact hMN z _)


end
section
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
local instance affineCutInst1 : NormedAddCommGroup (COne ℂ E) := inferInstance
local instance affineCutInst2 : NormedSpace ℝ (COne ℂ E) := inferInstance
local instance affineCutInst3 : NormedAddCommGroup (HMap ℂ E) := inferInstance
local instance affineCutInst4 : NormedSpace ℝ (HMap ℂ E) := inferInstance
local instance affineCutInst5 : NormedAddCommGroup (ℂ →L[ℝ] E) := ContinuousLinearMap.toNormedAddCommGroup
local instance affineCutInst6 : NormedSpace ℝ (ℂ →L[ℝ] E) := ContinuousLinearMap.toNormedSpace

def complexSlopeCLM : E →L[ℝ] (ℂ →L[ℝ] E) :=
  (ContinuousLinearMap.lsmul ℝ ℂ (E := E)).flip

omit [CompleteSpace E] in
@[simp] lemma complexSlopeCLM_apply (a : E) : complexSlopeCLM a = complexSlope a := rfl

variable (b : ContDiffBump (0:ℂ))

lemma cutoffCoordinate_smooth : ContDiff ℝ ∞ (fun z : ℂ => b z • z) :=
  b.contDiff.smul contDiff_id
lemma cutoffCoordinate_compact : HasCompactSupport (fun z : ℂ => b z • z) :=
  b.hasCompactSupport.smul_right

def cutoffCoordinate : COne ℂ ℂ :=
  ofBoundedCThree (boundedCThree_of_compactSupport (cutoffCoordinate_smooth b) (cutoffCoordinate_compact b))

@[simp] lemma cutoffCoordinate_value (z : ℂ) : cValue (cutoffCoordinate b) z = b z • z := rfl

def cutoffSlope : E →L[ℝ] COne ℂ E :=
  ((mapJetBilinear (D := ℂ) (E := ℂ) (F := E)).flip (cutoffCoordinate b)).comp complexSlopeCLM

omit [CompleteSpace E] in
@[simp] lemma cutoffSlope_value (a : E) (z : ℂ) :
    cValue (cutoffSlope b a) z = b z • (z • a) := by
  change (b z • z) • a = _
  exact smul_assoc (b z) z a

def truncateShift : COne ℂ E →L[ℝ] COne ℂ E :=
  ContinuousLinearMap.id ℝ _ - (cutoffSlope b).comp (jetEval 1)

omit [CompleteSpace E] in
@[simp] lemma truncateShift_value (h : COne ℂ E) (z : ℂ) :
    cValue (truncateShift b h) z = cValue h z-b z • (z • cValue h 1) := by
  change cValue h z-cValue (cutoffSlope b (cValue h 1)) z = _
  rw [cutoffSlope_value]

omit [CompleteSpace E] in
lemma markedSlope_add (p q : E) (u h : COne ℂ E) :
    markedSlope p q (u+h) = markedSlope p q u-cValue h 1 := by
  simp only [markedSlope,cValue_add]
  abel

def truncatedCurve (p q : E) (u h : COne ℂ E) (z : ℂ) : E :=
  affineCurve p (complexSlope (markedSlope p q u)) (u+truncateShift b h) z

omit [CompleteSpace E] in
lemma truncatedCurve_value (p q : E) (u h : COne ℂ E) (z : ℂ) :
    truncatedCurve b p q u h z = p+z • markedSlope p q u+cValue u z+cValue h z-
      b z • (z • cValue h 1) := by
  simp only [truncatedCurve,affineCurve,affine,complexSlope_apply,cValue_add,truncateShift_value]
  abel

omit [CompleteSpace E] in
lemma truncatedCurve_eq_marked (p q : E) (u h : COne ℂ E) {z : ℂ}
    (hz : z ∈ Metric.closedBall 0 b.rIn) :
    truncatedCurve b p q u h z = markedCurve p q (u+h) z := by
  rw [truncatedCurve_value,b.one_of_mem_closedBall hz,one_smul,markedCurve,markedSlope_add]
  simp only [cValue_add,smul_sub]
  abel

omit [CompleteSpace E] in
lemma cValue_norm_le (u : COne ℂ E) (z : ℂ) : ‖cValue u z‖ ≤ ‖u‖ :=
  (norm_value_le (jetValueCLM _ u) z).trans (jetValue_norm_le u)

omit [CompleteSpace E] in
lemma truncatedCurve_norm_lower (p q : E) (u h : COne ℂ E) (z : ℂ) :
    ‖z‖*(‖markedSlope p q u‖-‖h‖)-‖p‖-‖u‖-‖h‖ ≤ ‖truncatedCurve b p q u h z‖ := by
  have hb : ‖b z • (z • cValue h 1)‖ ≤ ‖z‖*‖h‖ := by
    rw [norm_smul,norm_smul,Real.norm_eq_abs,abs_of_nonneg (b.nonneg)]
    calc
      b z*(‖z‖*‖cValue h 1‖) ≤ 1*(‖z‖*‖cValue h 1‖) :=
        mul_le_mul_of_nonneg_right (b.le_one) (by positivity)
      _ ≤ ‖z‖*‖h‖ := by rw [one_mul]; exact mul_le_mul_of_nonneg_left (cValue_norm_le h 1) (norm_nonneg z)
  have he : z • markedSlope p q u = truncatedCurve b p q u h z -p-cValue u z-cValue h z+
      b z • (z • cValue h 1) := by rw [truncatedCurve_value]; abel
  have hn := calc
    ‖z • markedSlope p q u‖ = ‖truncatedCurve b p q u h z -p-cValue u z-cValue h z+
        b z • (z • cValue h 1)‖ := congrArg norm he
    _ ≤ ‖truncatedCurve b p q u h z‖+‖p‖+‖u‖+‖h‖+‖z‖*‖h‖ := by
      apply (norm_add_le _ _).trans
      apply add_le_add _ hb
      apply (norm_sub_le _ _).trans
      apply add_le_add _ (cValue_norm_le h z)
      apply (norm_sub_le _ _).trans
      apply add_le_add _ (cValue_norm_le u z)
      exact norm_sub_le _ _
  rw [norm_smul] at hn
  nlinarith

omit [CompleteSpace E] in
lemma markedCurve_norm_lower (p q : E) (u h : COne ℂ E) (z : ℂ) :
    ‖z‖*(‖markedSlope p q u‖-‖h‖)-‖p‖-‖u‖-‖h‖ ≤ ‖markedCurve p q (u+h) z‖ := by
  have he : z • markedSlope p q u = markedCurve p q (u+h) z-p-cValue u z-cValue h z+
      z • cValue h 1 := by
    simp only [markedCurve,markedSlope_add,cValue_add,smul_sub]
    abel
  have hn := calc
    ‖z • markedSlope p q u‖ = ‖markedCurve p q (u+h) z-p-cValue u z-cValue h z+z • cValue h 1‖ := congrArg norm he
    _ ≤ ‖markedCurve p q (u+h) z‖+‖p‖+‖u‖+‖h‖+‖z‖*‖h‖ := by
      apply (norm_add_le _ _).trans
      apply add_le_add _ (by rw [norm_smul]; exact mul_le_mul_of_nonneg_left (cValue_norm_le h 1) (norm_nonneg z))
      apply (norm_sub_le _ _).trans
      apply add_le_add _ (cValue_norm_le h z)
      apply (norm_sub_le _ _).trans
      apply add_le_add _ (cValue_norm_le u z)
      exact norm_sub_le _ _
  rw [norm_smul] at hn
  nlinarith


end
section
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
local instance sourceCutInst1 : NormedAddCommGroup (HMap ℂ E) := inferInstance
local instance sourceCutInst2 : NormedSpace ℝ (HMap ℂ E) := inferInstance

def constHolderCLM : E →L[ℝ] HMap ℂ E :=
  LinearMap.mkContinuous
    { toFun := const _
      map_add' := fun u v => by apply value_ext; intro z; rfl
      map_smul' := fun c v => by apply value_ext; intro z; rfl }
    1 (by intro v; change ‖const _ v‖ ≤ 1*‖v‖; rw [one_mul]; exact const_norm_le v)

@[simp] lemma constHolderCLM_value (v : E) (z : ℂ) : valueCLM _ (constHolderCLM v) z = v := rfl

variable (b : ContDiffBump (0:ℂ))

def bumpHolder : HMap ℂ ℝ :=
  jetValueCLM _ (ofBoundedCThree (boundedCThree_of_compactSupport b.contDiff b.hasCompactSupport))

@[simp] lemma bumpHolder_value (z : ℂ) : valueCLM _ (bumpHolder b) z = b z := rfl

def sourceCutoff : HMap ℂ E →L[ℝ] HMap ℂ E :=
  bilinCLM (X := ℂ) (α := (1:ℝ)/3) (ContinuousLinearMap.lsmul ℝ ℝ (E := E)) (bumpHolder b)

@[simp] lemma sourceCutoff_value (g : HMap ℂ E) (z : ℂ) :
    valueCLM _ (sourceCutoff b g) z = b z • valueCLM _ g z := rfl

local instance sourceCutInst3 : NormedAddCommGroup (supportedHolder (E := E) (Metric.closedBall (0:ℂ) b.rOut)) := inferInstance
local instance sourceCutInst4 : NormedSpace ℝ (supportedHolder (E := E) (Metric.closedBall (0:ℂ) b.rOut)) := inferInstance

def supportedSourceCutoff : HMap ℂ E →L[ℝ] supportedHolder (E := E) (Metric.closedBall (0:ℂ) b.rOut) :=
  (sourceCutoff b).codRestrict _ (fun g => by
    apply (mem_supportedHolder _ _).mpr
    intro z hz
    rw [sourceCutoff_value,b.zero_of_le_dist (by
      simp only [Metric.mem_closedBall] at hz
      exact (lt_of_not_ge hz).le),zero_smul])

@[simp] lemma supportedSourceCutoff_value (g : HMap ℂ E) (z : ℂ) :
    valueCLM _ (supportedSourceCutoff b g).val z = b z • valueCLM _ g z := rfl


end
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter
variable {X E : Type*} [MetricSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
local instance holderCompInst1 : NormedAddCommGroup (HMap X E) := inferInstance
local instance holderCompInst2 : NormedSpace ℝ (HMap X E) := inferInstance

omit [NormedSpace ℝ E] in
lemma third_interpolation {f : X → E} {M L A s : ℝ}
    (_hM : 0 ≤ M) (hL : 0 ≤ L) (hA : 0 ≤ A) (hs : 0 < s)
    (hb : ∀ x, ‖f x‖ ≤ M) (hl : ∀ x y, ‖f x-f y‖ ≤ L*dist x y)
    (hsmall : L*s^((2:ℝ)/3) ≤ A) (hlarge : 2*M ≤ A*s^((1:ℝ)/3)) :
    ∀ x y, ‖f x-f y‖ ≤ A*dist x y^((1:ℝ)/3) := by
  intro x y
  by_cases hxy : x = y
  · subst y; simp
  have hd : 0 < dist x y := dist_pos.mpr hxy
  by_cases hds : dist x y ≤ s
  · have hp : dist x y = dist x y^((2:ℝ)/3)*dist x y^((1:ℝ)/3) := by
      rw [← Real.rpow_add hd]; norm_num
    calc
      _ ≤ L*dist x y := hl x y
      _ = (L*dist x y^((2:ℝ)/3))*dist x y^((1:ℝ)/3) := (congrArg (fun t : ℝ => L*t) hp).trans (mul_assoc _ _ _).symm
      _ ≤ (L*s^((2:ℝ)/3))*dist x y^((1:ℝ)/3) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow hd.le hds (by norm_num)) hL) (by positivity)
      _ ≤ A*dist x y^((1:ℝ)/3) := mul_le_mul_of_nonneg_right hsmall (by positivity)
  · calc
      _ ≤ 2*M := (norm_sub_le _ _).trans (by linarith [hb x,hb y])
      _ ≤ A*s^((1:ℝ)/3) := hlarge
      _ ≤ A*dist x y^((1:ℝ)/3) := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow hs.le (le_of_not_ge hds) (by norm_num)) hA

lemma exists_small_third_scale {A : ℝ} (hA : 0 < A) (L : ℝ) :
    ∃ s > 0, L*s^((2:ℝ)/3) < A := by
  have ht : Tendsto (fun s : ℝ => L*s^((2:ℝ)/3)) (𝓝[>] 0) (𝓝 0) := by
    have h := (Real.continuousAt_rpow_const (0:ℝ) ((2:ℝ)/3) (Or.inr (by norm_num))).const_mul L
    simpa using h.tendsto.mono_left nhdsWithin_le_nhds
  have he : ∀ᶠ s : ℝ in 𝓝[>] 0, L*s^((2:ℝ)/3) < A := ht.eventually (gt_mem_nhds hA)
  have hh : ∀ᶠ s : ℝ in 𝓝[>] 0, 0 < s ∧ L*s^((2:ℝ)/3) < A := by
    filter_upwards [self_mem_nhdsWithin,he] with s hs h
    exact ⟨hs,h⟩
  exact hh.exists

lemma holder_small_of_small_value {L ε : ℝ} (hL : 0 ≤ L) (hε : 0 < ε) :
    ∃ δ > 0, ∀ u : HMap X E,
      (∀ x, ‖valueCLM _ u x‖ ≤ δ) →
      (∀ x y, ‖valueCLM _ u x-valueCLM _ u y‖ ≤ L*dist x y) → ‖u‖ < ε := by
  obtain ⟨s,hs,hscale⟩ := exists_small_third_scale (half_pos hε) L
  let δ : ℝ := min (ε/2) (ε/4*s^((1:ℝ)/3))
  have hδ : 0 < δ := lt_min (half_pos hε) (by positivity)
  refine ⟨δ,hδ,fun u hb hl => ?_⟩
  have hlarge : 2*δ ≤ ε/2*s^((1:ℝ)/3) := by
    have hh : δ ≤ ε/4*s^((1:ℝ)/3) := min_le_right _ _
    linarith
  have hh := third_interpolation hδ.le hL (half_pos hε).le hs hb hl hscale.le hlarge
  have hn : ‖u‖ ≤ ε/2 := (norm_le_of_bounds u hδ.le (half_pos hε).le hb hh).trans
    (max_le (min_le_left _ _) le_rfl)
  exact hn.trans_lt (half_lt_self hε)

def lipHolderSet (K : Set X) (M L : ℝ) : Set (HMap X E) :=
  {u | (∀ x, ‖valueCLM _ u x‖ ≤ M) ∧
    (∀ x y, ‖valueCLM _ u x-valueCLM _ u y‖ ≤ L*dist x y) ∧
    (∀ x ∉ K, valueCLM _ u x = 0)}

def restrictedValue (K : Set X) : HMap X E →L[ℝ] (K →ᵇ E) :=
  (BoundedContinuousFunction.compContinuousCLM E ℝ ⟨Subtype.val,continuous_subtype_val⟩).comp (valueCLM _)

@[simp] lemma restrictedValue_apply (K : Set X) (u : HMap X E) (x : K) :
    restrictedValue K u x = valueCLM _ u x.val := rfl

lemma restrictedValue_uniformInducing (K : Set X) (M : ℝ) {L : ℝ} (hL : 0 ≤ L) :
    IsUniformInducing (fun u : lipHolderSet (E := E) K M L => restrictedValue K u.val) := by
  apply Metric.isUniformInducing_iff.mpr
  refine ⟨(restrictedValue (E := E) K).uniformContinuous.comp uniformContinuous_subtype_val,?_⟩
  intro ε hε
  obtain ⟨δ,hδ,hd⟩ := holder_small_of_small_value (X := X) (E := E) (by linarith : 0 ≤ 2*L) hε
  refine ⟨δ,hδ,fun {u v} huv => ?_⟩
  change dist u.val v.val < ε
  rw [dist_eq_norm]
  apply hd (u.val-v.val)
  · intro x
    change ‖valueCLM _ u.val x-valueCLM _ v.val x‖ ≤ δ
    by_cases hx : x ∈ K
    · have h := BoundedContinuousFunction.dist_coe_le_dist (f := restrictedValue K u.val)
        (g := restrictedValue K v.val) (⟨x,hx⟩ : K)
      have hh : ‖valueCLM _ u.val x-valueCLM _ v.val x‖ ≤
          dist (restrictedValue K u.val) (restrictedValue K v.val) := by
        simpa only [restrictedValue_apply,dist_eq_norm] using h
      exact hh.trans huv.le
    · rw [u.property.2.2 x hx,v.property.2.2 x hx,sub_self,norm_zero]
      exact hδ.le
  · intro x y
    change ‖(valueCLM _ u.val x-valueCLM _ v.val x)-
      (valueCLM _ u.val y-valueCLM _ v.val y)‖ ≤ 2*L*dist x y
    have he : (valueCLM _ u.val x-valueCLM _ v.val x)-
        (valueCLM _ u.val y-valueCLM _ v.val y) =
        (valueCLM _ u.val x-valueCLM _ u.val y)-
        (valueCLM _ v.val x-valueCLM _ v.val y) := by abel
    rw [he]
    exact (norm_sub_le _ _).trans (by linarith [u.property.2.1 x y,v.property.2.1 x y])

lemma lipHolderSet_totallyBounded [ProperSpace E] {K : Set X} (hK : IsCompact K)
    (M : ℝ) {L : ℝ} (hL : 0 ≤ L) : TotallyBounded (lipHolderSet (E := E) K M L) := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let A : Set (K →ᵇ E) := restrictedValue K '' lipHolderSet (E := E) K M L
  have heq : Equicontinuous ((↑) : A → K → E) := by
    apply UniformEquicontinuous.equicontinuous
    rw [Metric.uniformEquicontinuous_iff]
    intro ε hε
    refine ⟨ε/(L+1),div_pos hε (by linarith),?_⟩
    intro x y hxy f
    obtain ⟨u,hu,huf⟩ := f.property
    change restrictedValue K u = f.val at huf
    rw [← huf,restrictedValue_apply,restrictedValue_apply,dist_eq_norm]
    have hdist : dist x.val y.val < ε/(L+1) := hxy
    have hb := hu.2.1 x.val y.val
    have hmul := (lt_div_iff₀ (by linarith : 0 < L+1)).mp hdist
    nlinarith [show 0 ≤ dist x.val y.val from dist_nonneg]
  have hc : IsCompact (closure A) := BoundedContinuousFunction.arzela_ascoli
    (Metric.closedBall (0:E) M) (isCompact_closedBall _ _) A (by
      intro f x hf
      obtain ⟨u,hu,rfl⟩ := hf
      simpa only [Metric.mem_closedBall,dist_zero_right,restrictedValue_apply] using hu.1 x.val) heq
  let F : lipHolderSet (E := E) K M L → (K →ᵇ E) := fun u => restrictedValue K u.val
  have ht : TotallyBounded (F '' Set.univ) := hc.totallyBounded.subset (by
    rintro _ ⟨u,_,rfl⟩
    exact subset_closure ⟨u.val,u.property,rfl⟩)
  have hu : TotallyBounded (Set.univ : Set (lipHolderSet (E := E) K M L)) :=
    (totallyBounded_image_iff (restrictedValue_uniformInducing K M hL)).mp ht
  have hh := hu.image uniformContinuous_subtype_val
  simpa only [Set.image_univ,Subtype.range_coe_subtype,Set.ofPred_mem_eq] using hh

variable (b : ContDiffBump (0:ℂ))
local instance holderLocInst1 : NormedAddCommGroup (COne ℂ E) := inferInstance
local instance holderLocInst2 : NormedSpace ℝ (COne ℂ E) := inferInstance

def localizedJetValue : COne ℂ E →L[ℝ] HMap ℂ E :=
  (sourceCutoff b).comp (jetValueCLM _)

@[simp] lemma localizedJetValue_apply (u : COne ℂ E) (z : ℂ) :
    valueCLM _ (localizedJetValue b u) z = b z • cValue u z := rfl

lemma localizedJetValue_bounds (u : COne ℂ E) (hu : ‖u‖ ≤ 1) :
    localizedJetValue b u ∈ lipHolderSet (Metric.closedBall (0:ℂ) b.rOut) 1
      (1+(boundedCThree_of_compactSupport b.contDiff b.hasCompactSupport).bound) := by
  let hb := boundedCThree_of_compactSupport b.contDiff b.hasCompactSupport
  have hbu : ∀ z : ℂ, ‖b z‖ ≤ 1 := fun z => by
    rw [Real.norm_of_nonneg b.nonneg]; exact b.le_one
  have huv : ∀ z : ℂ, ‖cValue u z‖ ≤ 1 := fun z => (c_value_bound u z).trans hu
  have hul : ∀ x y : ℂ, ‖cValue u x-cValue u y‖ ≤ dist x y := by
    intro x y
    have hd : ∀ z, ‖fderiv ℝ (cValue u) z‖ ≤ (1:ℝ) := fun z => by
      rw [c_fderiv]; exact (c_deriv_bound u z).trans hu
    simpa only [one_mul,dist_eq_norm] using norm_sub_le_of_deriv_bound (c_differentiable u) hd x y
  have hbl : ∀ x y : ℂ, ‖b x-b y‖ ≤ hb.bound*dist x y := by
    intro x y
    simpa only [dist_eq_norm] using norm_sub_le_of_deriv_bound
      (b.contDiff.differentiable (by simp : (∞ : WithTop ℕ∞) ≠ 0)) hb.norm_fderiv_le x y
  refine ⟨?_,?_,?_⟩
  · intro z
    rw [localizedJetValue_apply,norm_smul]
    calc
      _ ≤ (1:ℝ)*1 := mul_le_mul (hbu z) (huv z) (norm_nonneg _) zero_le_one
      _ = 1 := one_mul _
  · intro x y
    change ‖b x • cValue u x-b y • cValue u y‖ ≤ (1+hb.bound)*dist x y
    have he : b x • cValue u x-b y • cValue u y =
        b x • (cValue u x-cValue u y)+(b x-b y) • cValue u y := by module
    rw [he]
    calc
      _ ≤ ‖b x • (cValue u x-cValue u y)‖+‖(b x-b y) • cValue u y‖ := norm_add_le _ _
      _ = ‖b x‖*‖cValue u x-cValue u y‖+‖b x-b y‖*‖cValue u y‖ := by rw [norm_smul,norm_smul]
      _ ≤ 1*dist x y+(hb.bound*dist x y)*1 := add_le_add
        (mul_le_mul (hbu x) (hul x y) (norm_nonneg _) zero_le_one)
        (mul_le_mul (hbl x y) (huv y) (norm_nonneg _) (by positivity [hb.bound_nonneg]))
      _ = _ := by ring
  · intro z hz
    rw [localizedJetValue_apply,b.zero_of_le_dist (by
      simp only [Metric.mem_closedBall] at hz
      exact (lt_of_not_ge hz).le),zero_smul]

lemma localizedJetValue_isCompact [ProperSpace E] : IsCompactOperator (localizedJetValue (E := E) b) := by
  let hb := boundedCThree_of_compactSupport b.contDiff b.hasCompactSupport
  have ht := lipHolderSet_totallyBounded (E := E) (isCompact_closedBall (0:ℂ) b.rOut) 1
    (show 0 ≤ 1+hb.bound by linarith [hb.bound_nonneg])
  have hT : TotallyBounded (localizedJetValue (E := E) b '' Metric.closedBall 0 1) := ht.subset (by
    rintro _ ⟨u,hu,rfl⟩
    exact localizedJetValue_bounds b u (by simpa only [Metric.mem_closedBall,dist_zero_right] using hu))
  apply (isCompactOperator_iff_exists_mem_nhds_isCompact_closure_image
    (localizedJetValue (E := E) b)).mpr
  exact ⟨Metric.closedBall 0 1,Metric.closedBall_mem_nhds _ (by norm_num),
    hT.closure.isCompact_of_isClosed isClosed_closure⟩



end HigherDimensionalBallPacking.Rigidity.HolderCompletion
end

end OAI
