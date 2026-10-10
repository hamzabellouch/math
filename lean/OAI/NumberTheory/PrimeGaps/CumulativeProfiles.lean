import OAI.NumberTheory.PrimeGaps.LaplaceTransform

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

open Asymptotics

open Asymptotics

open Asymptotics

open scoped Classical

open scoped ContDiff

open Topology

open scoped Convolution ContDiff Pointwise

noncomputable def cumulativeExtension {ι : Type*} [Fintype ι]
    (T : ℝ) (f : EuclideanSpace ℝ ι → ℝ) : EuclideanSpace ℝ ι → ℝ :=
  cubeIndicator T ⋆[ContinuousLinearMap.mul ℝ ℝ,volume] f

theorem cumulativeExtension_compact {ι : Type*} [Fintype ι]
    (T : ℝ) (f : EuclideanSpace ℝ ι → ℝ) (hf : HasCompactSupport f) :
    HasCompactSupport (cumulativeExtension T f) :=
  HasCompactSupport.convolution (ContinuousLinearMap.mul ℝ ℝ) (cubeIndicator_compact T) hf

theorem cumulativeExtension_smooth {ι : Type*} [Fintype ι]
    (T : ℝ) (f : EuclideanSpace ℝ ι → ℝ) (hf : HasCompactSupport f)
    (hfs : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (cumulativeExtension T f) :=
  hf.contDiff_convolution_right _ (cubeIndicator_integrable T).locallyIntegrable hfs

noncomputable def cumulativeTail {ι : Type*} [Fintype ι]
    (f : EuclideanSpace ℝ ι → ℝ) (v : EuclideanSpace ℝ ι) : ℝ :=
  ∫ y in {y | ∀ i, v i≤y i}, f y

theorem cumulativeExtension_tail {ι : Type*} [Fintype ι]
    (T : ℝ) (f : EuclideanSpace ℝ ι → ℝ)
    (hf : ∀ y, f y≠0 → ∀ i, y i≤T)
    (v : EuclideanSpace ℝ ι) (hv : ∀ i, 0≤v i) :
    cumulativeExtension T f v = cumulativeTail f v := by
  have hs : MeasurableSet {y : EuclideanSpace ℝ ι | ∀ i, v i≤y i} := by
    rw [Set.ofPred_forall]
    exact (isClosed_iInter fun i => isClosed_le (continuous_const (y := v i)) (PiLp.continuous_apply 2 (fun _ : ι => ℝ) i)).measurableSet
  unfold cumulativeExtension cumulativeTail
  rw [convolution_def]
  change (∫ t, cubeIndicator T t * f (v-t)) = _
  rw [← integral_sub_left_eq_self (fun t => cubeIndicator T t * f (v-t)) volume v]
  rw [← integral_indicator hs]
  apply integral_congr_ae
  filter_upwards [] with y
  simp only [sub_sub_cancel]
  by_cases hfy : f y=0
  · simp [Set.indicator,hfy]
  · by_cases hy : ∀ i, v i≤y i
    · rw [Set.indicator_of_mem (s := {y : EuclideanSpace ℝ ι | ∀ i, v i≤y i}) hy]
      have hcube : v-y∈negativeCube T := by
        intro i
        change -T≤v i-y i ∧ v i-y i≤0
        constructor <;> linarith [hf y hfy i,hv i,hy i]
      simp [cubeIndicator,Set.indicator_of_mem hcube]
    · rw [Set.indicator_of_notMem (s := {y : EuclideanSpace ℝ ι | ∀ i, v i≤y i}) hy]
      have hcube : v-y∉negativeCube T := by
        intro h
        apply hy
        intro i
        have := (h i).2
        change v i-y i≤0 at this
        linarith
      simp [cubeIndicator,Set.indicator_of_notMem hcube]

theorem cumulativeTail_budget {ι : Type*} [Fintype ι]
    (tau : ℝ) (f : EuclideanSpace ℝ ι → ℝ)
    (hf : ∀ y, (∀ i, 0≤y i) → tau≤∑ i, y i → f y=0)
    (v : EuclideanSpace ℝ ι) (hv : ∀ i, 0≤v i) (hs : tau≤∑ i, v i) :
    cumulativeTail f v=0 := by
  apply setIntegral_eq_zero_of_forall_eq_zero
  intro y hy
  apply hf y (fun i => (hv i).trans (hy i))
  exact hs.trans (Finset.sum_le_sum fun i _ => hy i)

section GeneralDirections

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

noncomputable def signedDirectionalList (ms : List V) (F : V → ℂ) : V → ℂ :=
  ms.foldr (fun m H v => -fderiv ℝ H v m) F

theorem signedDirectionalList_smooth (ms : List V) (F : V → ℂ)
    (hF : ContDiff ℝ ∞ F) : ContDiff ℝ ∞ (signedDirectionalList ms F) := by
  induction ms with
  | nil => exact hF
  | cons m ms ih =>
    exact (ih.fderiv_right (by simp)).clm_apply contDiff_const |>.neg

theorem signedDirectionalList_compact (ms : List V) (F : V → ℂ)
    (hF : HasCompactSupport F) : HasCompactSupport (signedDirectionalList ms F) := by
  induction ms with
  | nil => exact hF
  | cons m ms ih => exact (ih.fderiv_apply ℝ m).neg

theorem signedDirectionalList_affine (ms : List V) (F : W → ℂ)
    (hF : ContDiff ℝ ∞ F) (A : V →L[ℝ] W) (c : W) :
    signedDirectionalList ms (fun v => F (c+A v)) =
      fun v => signedDirectionalList (ms.map A) F (c+A v) := by
  induction ms with
  | nil => rfl
  | cons m ms ih =>
    have hd := signedDirectionalList_smooth (ms.map A) F hF
    have hA (v : V) : HasFDerivAt (fun v => c+A v) A v := by
      simpa using (A.hasFDerivAt (x := v)).const_add c
    ext v
    change -fderiv ℝ (signedDirectionalList ms (fun v => F (c+A v))) v m = _
    rw [ih]
    have he := ((hd.differentiable (by simp) (c+A v)).hasFDerivAt.comp v (hA v)).fderiv
    simp only [Function.comp_def] at he
    rw [he]
    rfl

theorem signedDirectionalList_tsupport (ms : List V) (F : V → ℂ) :
    tsupport (signedDirectionalList ms F) ⊆ tsupport F := by
  induction ms with
  | nil => exact Set.Subset.rfl
  | cons m ms ih =>
    change tsupport (fun v => - fderiv ℝ (signedDirectionalList ms F) v m) ⊆ _
    change tsupport (-(fun v => fderiv ℝ (signedDirectionalList ms F) v m)) ⊆ _
    rw [tsupport_neg]
    exact (tsupport_fderiv_apply_subset ℝ m).trans ih

end GeneralDirections

noncomputable def finTailEmbed (n : ℕ) : (Fin n → ℝ) →L[ℝ] (Fin (n+1) → ℝ) :=
  let A : (Fin n → ℝ) →ₗ[ℝ] (Fin (n+1) → ℝ) :=
    { toFun := fun x => Fin.cons 0 x
      map_add' := by intros; ext i; cases i using Fin.cases <;> simp
      map_smul' := by intros; ext i; cases i using Fin.cases <;> simp }
  A.toContinuousLinearMap

@[simp] theorem finTailEmbed_apply (n : ℕ) (x : Fin n → ℝ) :
    finTailEmbed n x = Fin.cons 0 x := rfl

noncomputable def finDirections (n : ℕ) : List (Fin n → ℝ) :=
  (List.finRange n).map (fun i => Pi.single i 1)

theorem finTailEmbed_single (n : ℕ) (i : Fin n) :
    finTailEmbed n (Pi.single i 1) = Pi.single i.succ 1 := by
  ext j
  cases j using Fin.cases with
  | zero => simp
  | succ j => simp [Pi.single_apply,Fin.succ_inj]

theorem finDirections_succ (n : ℕ) :
    finDirections (n+1) = Pi.single 0 1 :: (finDirections n).map (finTailEmbed n) := by
  simp only [finDirections,List.finRange_succ,List.map_cons,List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  exact (finTailEmbed_single n i).symm

theorem fin_cons_affine {n : ℕ} (a : ℝ) (x : Fin n → ℝ) :
    Fin.cons a x = Pi.single 0 a + finTailEmbed n x := by
  ext i
  cases i using Fin.cases <;> simp

theorem fin_cons_closedEmbedding (n : ℕ) (a : ℝ) :
    IsClosedEmbedding (fun x : Fin n → ℝ => (Fin.cons a x : Fin (n+1) → ℝ)) := by
  have h : Function.Injective (finTailEmbed n) := by
    intro x y hxy
    ext i
    have := congrFun hxy i.succ
    simpa using this
  have he := LinearMap.isClosedEmbedding_of_injective (LinearMap.ker_eq_bot.mpr h)
  have hc := (Homeomorph.addLeft (Pi.single 0 a : Fin (n+1) → ℝ)).isClosedEmbedding.comp he
  convert hc using 1
  funext x
  exact fin_cons_affine a x

theorem fin_cons_head_closedEmbedding (n : ℕ) (y : Fin n → ℝ) :
    IsClosedEmbedding (fun a : ℝ => (Fin.cons a y : Fin (n+1) → ℝ)) := by
  have he : IsClosedEmbedding (fun a : ℝ => a • (Pi.single 0 1 : Fin (n+1) → ℝ)) :=
    isClosedEmbedding_smul_left (by intro h; have := congrFun h 0; simp at this)
  have hc := (Homeomorph.addRight (Fin.cons 0 y : Fin (n+1) → ℝ)).isClosedEmbedding.comp he
  convert hc using 1
  ext a i
  cases i using Fin.cases <;> simp

noncomputable def piTailMeasure {n : ℕ} (v : Fin n → ℝ) : Measure (Fin n → ℝ) :=
  Measure.pi (fun i => volume.restrict (Ioi (v i)))

instance {n : ℕ} (v : Fin n → ℝ) : SigmaFinite (piTailMeasure v) := by
  unfold piTailMeasure
  infer_instance

instance {n : ℕ} (v : Fin n → ℝ) : IsFiniteMeasureOnCompacts (piTailMeasure v) := by
  unfold piTailMeasure
  infer_instance

theorem piTail_integral_cons {n : ℕ} (v : Fin (n+1) → ℝ)
    (f : (Fin (n+1) → ℝ) → ℂ) (hf : Integrable f (piTailMeasure v)) :
    (∫ x, f x ∂piTailMeasure v) =
      ∫ y, (∫ a in Ioi (v 0), f (Fin.cons a y)) ∂piTailMeasure (fun i => v i.succ) := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0
  have hm := measurePreserving_piFinSuccAbove
    (fun i : Fin (n+1) => volume.restrict (Ioi (v i))) 0
  have he : ∀ p : ℝ × (Fin n → ℝ), e.symm p = Fin.cons p.1 p.2 := by
    intro p
    simp [e,MeasurableEquiv.piFinSuccAbove_symm_apply,Fin.insertNthEquiv]
  dsimp only [e] at he
  have hprod : Integrable (fun p : ℝ × (Fin n → ℝ) => f (Fin.cons p.1 p.2))
      ((volume.restrict (Ioi (v 0))).prod (piTailMeasure (fun i => v i.succ))) := by
    have hh := (hm.symm.integrable_comp_emb e.symm.measurableEmbedding).mpr hf
    simpa only [Fin.zero_succAbove,he,Function.comp_def,piTailMeasure] using hh
  calc
    _ = ∫ p : ℝ × (Fin n → ℝ), f (Fin.cons p.1 p.2)
        ∂((volume.restrict (Ioi (v 0))).prod (piTailMeasure (fun i => v i.succ))) := by
      have hh := hm.symm.integral_comp' f
      simpa only [Fin.zero_succAbove,he,piTailMeasure] using hh.symm
    _ = _ := integral_prod_symm _ hprod

theorem fin_cons_head_affine {n : ℕ} (a : ℝ) (y : Fin n → ℝ) :
    Fin.cons a y = a • (Pi.single 0 1 : Fin (n+1) → ℝ) + Fin.cons 0 y := by
  ext i
  cases i using Fin.cases <;> simp

theorem fin_cons_hasDerivAt {n : ℕ} (y : Fin n → ℝ) (a : ℝ) :
    HasDerivAt (fun a => (Fin.cons a y : Fin (n+1) → ℝ)) (Pi.single 0 1) a := by
  have he : (fun a : ℝ => (Fin.cons a y : Fin (n+1) → ℝ)) =
      fun a => a • (Pi.single 0 1 : Fin (n+1) → ℝ) + Fin.cons 0 y :=
    funext (fun a => fin_cons_head_affine a y)
  rw [he]
  simpa using ((hasDerivAt_id a).smul_const (Pi.single 0 1 : Fin (n+1) → ℝ)).add_const
    (Fin.cons 0 y)

theorem fin_cons_head_smooth {n : ℕ} (y : Fin n → ℝ) :
    ContDiff ℝ ∞ (fun a => (Fin.cons a y : Fin (n+1) → ℝ)) := by
  have he : (fun a : ℝ => (Fin.cons a y : Fin (n+1) → ℝ)) =
      fun a => a • (Pi.single 0 1 : Fin (n+1) → ℝ) + Fin.cons 0 y :=
    funext (fun a => fin_cons_head_affine a y)
  rw [he]
  fun_prop

theorem fin_cons_tail_smooth {n : ℕ} (a : ℝ) :
    ContDiff ℝ ∞ (fun y : Fin n → ℝ => (Fin.cons a y : Fin (n+1) → ℝ)) := by
  simp_rw [fin_cons_affine]
  fun_prop

theorem piTail_signedDirections_FTC (n : ℕ) (F : (Fin n → ℝ) → ℂ)
    (hF : HasCompactSupport F) (hFs : ContDiff ℝ ∞ F) (v : Fin n → ℝ) :
    (∫ x, signedDirectionalList (finDirections n) F x ∂piTailMeasure v) = F v := by
  induction n with
  | zero =>
    simp only [finDirections,List.finRange_zero,List.map_nil,signedDirectionalList,List.foldr_nil]
    unfold piTailMeasure
    rw [Measure.pi_of_empty (x := v)]
    exact integral_dirac F v
  | succ n ih =>
    rw [finDirections_succ]
    let ms := (finDirections n).map (finTailEmbed n)
    let H := signedDirectionalList ms F
    have hHc : HasCompactSupport H := signedDirectionalList_compact ms F hF
    have hHs : ContDiff ℝ ∞ H := signedDirectionalList_smooth ms F hFs
    have hfull : Integrable (signedDirectionalList (Pi.single 0 1 :: ms) F) (piTailMeasure v) :=
      (signedDirectionalList_smooth _ F hFs).continuous.integrable_of_hasCompactSupport
        (signedDirectionalList_compact _ F hF)
    rw [piTail_integral_cons v _ hfull]
    have hinner (y : Fin n → ℝ) :
        (∫ a in Ioi (v 0), signedDirectionalList (Pi.single 0 1 :: ms) F (Fin.cons a y)) =
          H (Fin.cons (v 0) y) := by
      have hc : HasCompactSupport (fun a : ℝ => H (Fin.cons a y)) :=
        hHc.comp_isClosedEmbedding (fin_cons_head_closedEmbedding n y)
      have hs : ContDiff ℝ ∞ (fun a : ℝ => H (Fin.cons a y)) :=
        hHs.comp (fin_cons_head_smooth y)
      have hd (a : ℝ) : deriv (fun a : ℝ => H (Fin.cons a y)) a =
          fderiv ℝ H (Fin.cons a y) (Pi.single 0 1) := by
        exact ((hHs.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt a
          (fin_cons_hasDerivAt y a)).deriv
      have he : (fun a : ℝ => signedDirectionalList (Pi.single 0 1 :: ms) F (Fin.cons a y)) =
          fun a => -deriv (fun a : ℝ => H (Fin.cons a y)) a := by
        funext a
        rw [hd]
        rfl
      rw [he,integral_neg,HasCompactSupport.integral_Ioi_deriv_eq (hs.of_le (by simp)) hc,neg_neg]
    simp_rw [hinner]
    let G : (Fin n → ℝ) → ℂ := fun y => F (Fin.cons (v 0) y)
    have hGc : HasCompactSupport G := hF.comp_isClosedEmbedding (fin_cons_closedEmbedding n (v 0))
    have hGs : ContDiff ℝ ∞ G := hFs.comp (fin_cons_tail_smooth (v 0))
    have hg : (fun y : Fin n → ℝ => H (Fin.cons (v 0) y)) = signedDirectionalList (finDirections n) G := by
      have he := signedDirectionalList_affine (finDirections n) F hFs (finTailEmbed n)
        (Pi.single 0 (v 0))
      simpa only [← fin_cons_affine] using he.symm
    rw [hg,ih G hGc hGs (fun i => v i.succ)]
    dsimp only [G]
    congr 1
    ext i
    cases i using Fin.cases <;> rfl

noncomputable def complexCumulativeExtension {ι : Type*} [Fintype ι]
    (T : ℝ) (F : EuclideanSpace ℝ ι → ℂ) : EuclideanSpace ℝ ι → ℂ :=
  cubeIndicator T ⋆[ContinuousLinearMap.lsmul ℝ ℝ,volume] F

theorem complexCumulativeExtension_compact {ι : Type*} [Fintype ι]
    (T : ℝ) (F : EuclideanSpace ℝ ι → ℂ) (hF : HasCompactSupport F) :
    HasCompactSupport (complexCumulativeExtension T F) :=
  HasCompactSupport.convolution (ContinuousLinearMap.lsmul ℝ ℝ) (cubeIndicator_compact T) hF

theorem complexCumulativeExtension_smooth {ι : Type*} [Fintype ι]
    (T : ℝ) (F : EuclideanSpace ℝ ι → ℂ) (hF : HasCompactSupport F)
    (hFs : ContDiff ℝ ∞ F) : ContDiff ℝ ∞ (complexCumulativeExtension T F) :=
  hF.contDiff_convolution_right _ (cubeIndicator_integrable T).locallyIntegrable hFs

theorem complexCumulativeExtension_tail {ι : Type*} [Fintype ι]
    (T : ℝ) (F : EuclideanSpace ℝ ι → ℂ)
    (hF : ∀ y, F y≠0 → ∀ i, y i≤T)
    (v : EuclideanSpace ℝ ι) (hv : ∀ i, 0≤v i) :
    complexCumulativeExtension T F v = ∫ y in {y | ∀ i, v i≤y i}, F y := by
  have hs : MeasurableSet {y : EuclideanSpace ℝ ι | ∀ i, v i≤y i} := by
    rw [Set.ofPred_forall]
    exact (isClosed_iInter fun i => isClosed_le (continuous_const (y := v i))
      (PiLp.continuous_apply 2 (fun _ : ι => ℝ) i)).measurableSet
  unfold complexCumulativeExtension
  rw [convolution_def]
  change (∫ t, cubeIndicator T t • F (v-t)) = _
  rw [← integral_sub_left_eq_self (fun t => cubeIndicator T t • F (v-t)) volume v]
  rw [← integral_indicator hs]
  apply integral_congr_ae
  filter_upwards [] with y
  simp only [sub_sub_cancel]
  by_cases hFy : F y=0
  · simp [Set.indicator,hFy]
  · by_cases hy : ∀ i, v i≤y i
    · rw [Set.indicator_of_mem (s := {y : EuclideanSpace ℝ ι | ∀ i, v i≤y i}) hy]
      have hcube : v-y∈negativeCube T := by
        intro i
        change -T≤v i-y i ∧ v i-y i≤0
        constructor <;> linarith [hF y hFy i,hv i,hy i]
      simp [cubeIndicator,Set.indicator_of_mem hcube]
    · rw [Set.indicator_of_notMem (s := {y : EuclideanSpace ℝ ι | ∀ i, v i≤y i}) hy]
      have hcube : v-y∉negativeCube T := by
        intro h
        apply hy
        intro i
        have := (h i).2
        change v i-y i≤0 at this
        linarith
      simp [cubeIndicator,Set.indicator_of_notMem hcube]

theorem signedDirections_cumulative {ι : Type*} [Fintype ι]
    (T : ℝ) (ms : List (EuclideanSpace ℝ ι)) (F : EuclideanSpace ℝ ι → ℂ)
    (hF : HasCompactSupport F) (hFs : ContDiff ℝ ∞ F) :
    signedDirections ms (complexCumulativeExtension T F) =
      complexCumulativeExtension T (signedDirections ms F) := by
  induction ms with
  | nil => rfl
  | cons m ms ih =>
    ext v
    change -fderiv ℝ (signedDirections ms (complexCumulativeExtension T F)) v m = _
    rw [ih]
    have hc := signedDirections_compact ms F hF
    have hs := signedDirections_smooth ms F hFs
    unfold complexCumulativeExtension
    rw [(hc.hasFDerivAt_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ)
      (cubeIndicator_integrable T).locallyIntegrable (hs.of_le (by simp)) v).fderiv]
    rw [convolution_precompR_apply _ (cubeIndicator_integrable T).locallyIntegrable
      (hc.fderiv ℝ) (hs.continuous_fderiv (by simp))]
    simp only [convolution_def,ContinuousLinearMap.lsmul_apply,
      signedDirections,List.foldr_cons,smul_neg,integral_neg]

noncomputable def euclideanFinDirections (n : ℕ) : List (EuclideanSpace ℝ (Fin n)) :=
  (finDirections n).map (EuclideanSpace.equiv (Fin n) ℝ).symm

theorem euclideanTail_signedDirections_FTC (n : ℕ) (F : EuclideanSpace ℝ (Fin n) → ℂ)
    (hF : HasCompactSupport F) (hFs : ContDiff ℝ ∞ F) (v : EuclideanSpace ℝ (Fin n)) :
    (∫ x in {x | ∀ i, v i≤x i}, signedDirections (euclideanFinDirections n) F x) = F v := by
  let e := (EuclideanSpace.equiv (Fin n) ℝ).symm
  have hc : HasCompactSupport (fun x => F (e x)) :=
    hF.comp_isClosedEmbedding e.toHomeomorph.isClosedEmbedding
  have hs : ContDiff ℝ ∞ (fun x => F (e x)) := hFs.comp e.contDiff
  have hFTC := piTail_signedDirections_FTC n (fun x => F (e x)) hc hs v.ofLp
  have ha := signedDirectionalList_affine (finDirections n) F hFs e.toContinuousLinearMap 0
  simp only [zero_add] at ha
  have htail : piTailMeasure v.ofLp = volume.restrict (Ici v.ofLp) := by
    unfold piTailMeasure
    rw [← Measure.restrict_pi_pi]
    exact Measure.restrict_congr_set (Measure.univ_pi_Ioi_ae_eq_Ici (μ := fun _ => volume))
  change signedDirectionalList (finDirections n) (fun x => F (e x)) =
    fun x => signedDirections (euclideanFinDirections n) F (e x) at ha
  rw [htail,ha] at hFTC
  have he := (PiLp.volume_preserving_toLp (Fin n)).setIntegral_preimage_emb
    (MeasurableEquiv.toLp 2 (Fin n → ℝ)).measurableEmbedding
    (signedDirections (euclideanFinDirections n) F) {x | ∀ i, v i≤x i}
  convert he.symm.trans hFTC using 1
  exact congrArg F (by simp [e])

@[simp] theorem euclideanFinDirections_multiplier (n : ℕ) (u : EuclideanSpace ℝ (Fin n)) :
    ((euclideanFinDirections n).map
      (fun m => laplaceFrequency (fourierCoordinateSum (Fin n)) m u)).prod =
      ∏ i, frequencyW (u i) := by
  simp only [euclideanFinDirections,finDirections,List.map_map]
  change ((List.finRange n).map (fun i =>
    laplaceFrequency (fourierCoordinateSum (Fin n)) (EuclideanSpace.single i (1:ℝ)) u)).prod = _
  rw [← Fin.prod_univ_def]
  apply Finset.prod_congr rfl
  intro i _
  convert laplaceFrequency_coordinate i u using 1
  congr 2
  exact Subsingleton.elim _ _

theorem signedDirections_coordinate_eq_fin (n : ℕ) (F : EuclideanSpace ℝ (Fin n) → ℂ)
    (hF : HasCompactSupport F) (hFs : ContDiff ℝ ∞ F) :
    signedDirections (coordinateDirectionList (Fin n)) F =
      signedDirections (euclideanFinDirections n) F := by
  ext v
  rw [← sourceFourier_derivative_inversion (fourierCoordinateSum (Fin n))
    (coordinateDirectionList (Fin n)) F hF hFs v,
    ← sourceFourier_derivative_inversion (fourierCoordinateSum (Fin n))
    (euclideanFinDirections n) F hF hFs v]
  apply integral_congr_ae
  filter_upwards [] with u
  change sourceFourier _ F hF hFs u *
    ((coordinateDirectionList (Fin n)).map (fun m => laplaceFrequency _ m u)).prod * _ =
    sourceFourier _ F hF hFs u *
    ((euclideanFinDirections n).map (fun m => laplaceFrequency _ m u)).prod * _
  rw [coordinateDirectionList_multiplier,euclideanFinDirections_multiplier]

theorem complexCumulativeExtension_signed_full (n : ℕ) (T : ℝ)
    (F : EuclideanSpace ℝ (Fin n) → ℂ) (hF : HasCompactSupport F)
    (hFs : ContDiff ℝ ∞ F) (hT : ∀ y∈tsupport F, ∀ i, y i≤T)
    (v : EuclideanSpace ℝ (Fin n)) (hv : ∀ i, 0≤v i) :
    signedDirections (coordinateDirectionList (Fin n)) (complexCumulativeExtension T F) v =
      F v := by
  rw [signedDirections_coordinate_eq_fin n _ (complexCumulativeExtension_compact T F hF)
    (complexCumulativeExtension_smooth T F hF hFs),signedDirections_cumulative T _ F hF hFs]
  rw [complexCumulativeExtension_tail T _ _ v hv]
  · exact euclideanTail_signedDirections_FTC n F hF hFs v
  · intro y hy i
    exact hT y (signedDirectionalList_tsupport (euclideanFinDirections n) F
      (subset_tsupport _ hy)) i

theorem complexCumulativeExtension_ofReal {ι : Type*} [Fintype ι]
    (T : ℝ) (f : EuclideanSpace ℝ ι → ℝ) :
    complexCumulativeExtension T (fun y => (f y:ℂ)) =
      fun v => (cumulativeExtension T f v:ℂ) := by
  ext v
  simp only [complexCumulativeExtension,cumulativeExtension,convolution_def,
    ContinuousLinearMap.lsmul_apply,ContinuousLinearMap.mul_apply',
    Complex.real_smul,← Complex.ofReal_mul,integral_complex_ofReal]

noncomputable def cumulativeProfile {n : ℕ} (tau : ℝ) (f : (Fin n → ℝ) → ℝ) :
    (Fin n → ℝ) → ℝ :=
  fun v => cumulativeExtension tau (fun y => f y.ofLp) (WithLp.toLp 2 v)

theorem cumulativeProfile_compact {n : ℕ} (tau : ℝ) (f : (Fin n → ℝ) → ℝ)
    (hf : HasCompactSupport f) : HasCompactSupport (cumulativeProfile tau f) := by
  have hfc : HasCompactSupport (fun y : EuclideanSpace ℝ (Fin n) => f y.ofLp) :=
    hf.comp_isClosedEmbedding (EuclideanSpace.equiv (Fin n) ℝ).toHomeomorph.isClosedEmbedding
  exact (cumulativeExtension_compact tau _ hfc).comp_isClosedEmbedding
    (EuclideanSpace.equiv (Fin n) ℝ).symm.toHomeomorph.isClosedEmbedding

theorem cumulativeProfile_smooth {n : ℕ} (tau : ℝ) (f : (Fin n → ℝ) → ℝ)
    (hf : HasCompactSupport f) (hfs : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (cumulativeProfile tau f) := by
  have hfc : HasCompactSupport (fun y : EuclideanSpace ℝ (Fin n) => f y.ofLp) :=
    hf.comp_isClosedEmbedding (EuclideanSpace.equiv (Fin n) ℝ).toHomeomorph.isClosedEmbedding
  have hF : ContDiff ℝ ∞ (fun y : EuclideanSpace ℝ (Fin n) => f y.ofLp) :=
    hfs.comp (EuclideanSpace.equiv (Fin n) ℝ).contDiff
  exact (cumulativeExtension_smooth tau _ hfc hF).comp
    (EuclideanSpace.equiv (Fin n) ℝ).symm.contDiff

theorem profile_coordinate_upper {n : ℕ} {tau : ℝ} {f : (Fin n → ℝ) → ℝ}
    (hf : tsupport f ⊆ positiveSimplex n tau) (y : Fin n → ℝ) (hy : y∈tsupport f)
    (i : Fin n) : y i≤tau := by
  have hh := hf hy
  exact (Finset.single_le_sum (fun j _ => (hh.1 j).le) (Finset.mem_univ i)).trans hh.2.le

theorem cumulativeProfile_tail {n : ℕ} (tau : ℝ) (f : (Fin n → ℝ) → ℝ)
    (hf : tsupport f ⊆ positiveSimplex n tau) (v : Fin n → ℝ) (hv : ∀ i, 0≤v i) :
    cumulativeProfile tau f v = ∫ y in Ici v, f y := by
  unfold cumulativeProfile
  rw [cumulativeExtension_tail tau _ _ _ hv]
  · unfold cumulativeTail
    have hm := (PiLp.volume_preserving_ofLp (Fin n)).setIntegral_preimage_emb
      (MeasurableEquiv.toLp 2 (Fin n → ℝ)).symm.measurableEmbedding f (Ici v)
    exact hm
  · intro y hy i
    exact profile_coordinate_upper hf y.ofLp (subset_tsupport f hy) i

end LargePrimeGaps

end OAI
