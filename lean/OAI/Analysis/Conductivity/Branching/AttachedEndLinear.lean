import Mathlib
import OAI.Analysis.Conductivity.Branching.AttachedEndGradientL2
import OAI.Analysis.Conductivity.Geometry.CollarLip

namespace OAI

noncomputable section

namespace ScalarConductivity
open Set MeasureTheory Filter Topology
open scoped ENNReal

lemma endPoissonField_add_pos (s : Fin 3 → ℝ)
    (hs : ∀ u v : ℝ,(1/2)*(u^2+v^2) ≤ s 0*u^2+2*s 1*u*v+s 2*v^2)
    (f g : spectralTraceGraph (torusRate s)) (j : Fin 4)
    {z : ℝ×UnitAddTorus (Fin 2)} (hz : 0<z.1) :
    endPoissonField s (f+g) j z=endPoissonField s f j z+endPoissonField s g j z := by
  have h := (endPoissonField_hasSum s hs f j hz).add (endPoissonField_hasSum s hs g j hz)
  apply (endPoissonField_hasSum s hs (f+g) j hz).unique
  convert h using 1
  ext h
  change endPoissonModeField s h ((f.val 0 h)+(g.val 0 h)) j z=_
  simp [endPoissonModeField,endModeCoefficient_add,mul_add,add_mul]

lemma endPoissonField_rsmul_pos (s : Fin 3 → ℝ)
    (hs : ∀ u v : ℝ,(1/2)*(u^2+v^2) ≤ s 0*u^2+2*s 1*u*v+s 2*v^2)
    (c : ℝ) (f : spectralTraceGraph (torusRate s)) (j : Fin 4)
    {z : ℝ×UnitAddTorus (Fin 2)} (hz : 0<z.1) :
    endPoissonField s (c•f) j z=c • endPoissonField s f j z := by
  have h := (endPoissonField_hasSum s hs f j hz).const_smul c
  apply (endPoissonField_hasSum s hs (c•f) j hz).unique
  convert h using 1
  ext h
  change endPoissonModeField s h ((c:ℂ)*f.val 0 h) j z=c • _
  simp only [endPoissonModeField,endModeCoefficient_smul,Complex.real_smul]
  ring

def attachedEndFlatCLM (s : Fin 3 → ℝ)
    (hs : ∀ u v : ℝ,(1/2)*(u^2+v^2) ≤ s 0*u^2+2*s 1*u*v+s 2*v^2)
    {a b l r R : ℝ} (ha : a≠0) (hR : 0≤R) (hlr : l≤r)
    (hl : -(1:ℝ)/100≤l) (hr : r≤1/100)
    (hT : ∀ t∈Icc l r,affineEndTime a b t∈Icc 0 R) (j : Fin 4) :
    spectralTraceGraph (torusRate s) →L[ℝ] Lp ℂ 2 (volume.restrict (sourceClosedCollarBand l r)) :=
  (Lp.LpToLpOfMeasureLeSMul (c:=1) (by simp)
    (by simpa only [one_smul] using sourceClosedCollarBand_measure_le hl hr)).comp
    ((sourceCollarPullback hlr hl hr).comp ((affineEndPullback ha hT).comp
      (((PiLp.proj 2 (fun _ : Fin 4 => Lp ℂ 2 (sourceCylinderMeasure 0 R)) (𝕜:=ℂ) j).restrictScalars ℝ).comp ((endPoissonCLM s hs R hR).restrictScalars ℝ))))

lemma attachedEndFlatCLM_ae (s : Fin 3 → ℝ)
    (hs : ∀ u v : ℝ,(1/2)*(u^2+v^2) ≤ s 0*u^2+2*s 1*u*v+s 2*v^2)
    (f : spectralTraceGraph (torusRate s)) {a b l r R : ℝ}
    (ha : a≠0) (hR : 0≤R) (hlr : l≤r) (hl : -(1:ℝ)/100≤l) (hr : r≤1/100)
    (hT : ∀ t∈Icc l r,affineEndTime a b t∈Icc 0 R) (j : Fin 4) :
    attachedEndFlatCLM s hs ha hR hlr hl hr hT j f=ᵐ[volume.restrict (sourceClosedCollarBand l r)]
      attachedEndPoissonField s f a b j := by
  apply (Lp.coeFn_LpToLpOfMeasureLeSMul (c:=1) (by simp)
    (by simpa only [one_smul] using sourceClosedCollarBand_measure_le hl hr) _).trans
  exact (Measure.absolutelyContinuous_of_le (sourceClosedCollarBand_measure_le hl hr)).ae_eq
    (attachedEndPoissonJet_ae s hs f ha hR hlr hl hr hT j)

lemma attachedEndPoisson_real_fderiv_add_ae (s : Fin 3 → ℝ)
    (hs : ∀ u v : ℝ,(1/2)*(u^2+v^2) ≤ s 0*u^2+2*s 1*u*v+s 2*v^2)
    (f g : spectralTraceGraph (torusRate s)) (a b : ℝ) :
    ∀ᵐ y : Fin 3 → ℝ,y∈sourceClosedCollarBand (-(1:ℝ)/100) (1/100) →
      0<a*(sourceCollarTime y-b) →
      fderiv ℝ (fun y => (attachedEndPoissonField s (f+g) a b 0 y).re) y=
        fderiv ℝ (fun y => (attachedEndPoissonField s f a b 0 y).re) y+
        fderiv ℝ (fun y => (attachedEndPoissonField s g a b 0 y).re) y := by
  filter_upwards [attachedEndPoisson_real_differentiable_ae s hs f a b,
    attachedEndPoisson_real_differentiable_ae s hs g a b] with y hf hg hy ht
  have he : (fun y => (attachedEndPoissonField s (f+g) a b 0 y).re)=ᶠ[𝓝 y]
      (fun y => (attachedEndPoissonField s f a b 0 y).re+(attachedEndPoissonField s g a b 0 y).re) := by
    filter_upwards [((attachedEndTime_lipschitz a b).choose_spec.continuous.continuousAt).eventually
      (lt_mem_nhds ht)] with z hz
    change (endPoissonField s (f+g) 0 _).re=_
    rw [endPoissonField_add_pos s hs f g 0 hz]
    rfl
  rw [he.fderiv_eq]
  exact fderiv_fun_add (hf hy ht) (hg hy ht)

lemma attachedEndPoisson_real_fderiv_rsmul_ae (s : Fin 3 → ℝ)
    (hs : ∀ u v : ℝ,(1/2)*(u^2+v^2) ≤ s 0*u^2+2*s 1*u*v+s 2*v^2)
    (c : ℝ) (f : spectralTraceGraph (torusRate s)) (a b : ℝ) :
    ∀ᵐ y : Fin 3 → ℝ,y∈sourceClosedCollarBand (-(1:ℝ)/100) (1/100) →
      0<a*(sourceCollarTime y-b) →
      fderiv ℝ (fun y => (attachedEndPoissonField s (c•f) a b 0 y).re) y=
        c • fderiv ℝ (fun y => (attachedEndPoissonField s f a b 0 y).re) y := by
  filter_upwards [attachedEndPoisson_real_differentiable_ae s hs f a b] with y hf hy ht
  have he : (fun y => (attachedEndPoissonField s (c•f) a b 0 y).re)=ᶠ[𝓝 y]
      (fun y => c*(attachedEndPoissonField s f a b 0 y).re) := by
    filter_upwards [((attachedEndTime_lipschitz a b).choose_spec.continuous.continuousAt).eventually
      (lt_mem_nhds ht)] with z hz
    change (endPoissonField s (c•f) 0 _).re=_
    rw [endPoissonField_rsmul_pos s hs c f 0 hz]
    simp [attachedEndPoissonField]
  rw [he.fderiv_eq]
  exact fderiv_const_mul (hf hy ht) c

lemma attachedEndPoisson_grad_bound_uniform (s : Fin 3 → ℝ)
    (hs : ∀ u v : ℝ,(1/2)*(u^2+v^2) ≤ s 0*u^2+2*s 1*u*v+s 2*v^2)
    (a b : ℝ) :
    ∃ C : ℝ,0<C ∧ ∀ (f : spectralTraceGraph (torusRate s)) (k : Fin 3),∀ᵐ y : Fin 3 → ℝ,
      y∈sourceClosedCollarBand (-(1:ℝ)/100) (1/100) → 0<a*(sourceCollarTime y-b) →
      |fderiv ℝ (fun y => (attachedEndPoissonField s f a b 0 y).re) y (Pi.single k 1)|≤
        C*∑ d : Fin 3,‖attachedEndPoissonField s f a b d.succ y‖ := by
  obtain ⟨C,hC,hbound⟩ := sourceCartesianGradient_uniform_bound
  refine ⟨C*(|a|+1),mul_pos hC (by positivity),?_⟩
  intro f k
  filter_upwards [sourceCollar_open_charts_ae] with y hy hb ht
  obtain ⟨i,j,x,hx,rfl⟩ := hy hb
  rw [sourceCollarPiece_time_open hx] at ht
  rw [attachedEndPoisson_real_fderiv s hs f a b i j hx ht,dotProduct_single,mul_one]
  rw [Matrix.mulVec]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro d _
  rw [abs_mul,endAxialMatrix,Matrix.mulVec_diagonal,abs_mul]
  have hd : |![a,1,1] d|≤|a|+1 := by
    fin_cases d
    · change |a|≤|a|+1; linarith
    · change |(1:ℝ)|≤|a|+1; rw [abs_one]; linarith [abs_nonneg a]
    · change |(1:ℝ)|≤|a|+1; rw [abs_one]; linarith [abs_nonneg a]
  have he := Complex.abs_re_le_norm (attachedEndPoissonField s f a b d.succ (sourceCollarPiece i j x))
  calc
    _ ≤ C*((|a|+1)*‖attachedEndPoissonField s f a b d.succ (sourceCollarPiece i j x)‖) :=
      mul_le_mul (hbound i j x (sourceCollarOpenBox_subset hx) k d)
        (mul_le_mul hd he (abs_nonneg _) (by positivity)) (by positivity) hC.le
    _ = _ := by ring

lemma lp_norm_le_sum_norm_of_ae {X ι : Type*} [MeasurableSpace X] [Fintype ι]
    {μ : Measure X} {u : Lp ℝ 2 μ} {v : ι → Lp ℂ 2 μ} {C : ℝ} (hC : 0≤C)
    (h : ∀ᵐ x∂μ,‖u x‖≤C*∑ i,‖v i x‖) : ‖u‖≤C*∑ i,‖v i‖ := by
  let w : ι → Lp ℝ 2 μ := fun i => ((Lp.memLp (v i)).norm).toLp (fun x => ‖v i x‖)
  have he (i : ι) : w i=ᵐ[μ] (fun x => ‖v i x‖) := ((Lp.memLp (v i)).norm).coeFn_toLp
  have hn (i : ι) : ‖w i‖=‖v i‖ := by
    dsimp only [w]
    rw [Lp.norm_toLp,eLpNorm_norm (v i) (Lp.memLp (v i)).aestronglyMeasurable,Lp.norm_def]
  have hh : ‖u‖≤‖C • ∑ i,w i‖ := by
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [h,Lp.coeFn_smul C (∑ i,w i),Lp.coeFn_fun_finsetSum Finset.univ w,
      ae_all_iff.mpr he] with x hx hs hsum hw
    rw [hs]
    simp only [Pi.smul_apply,smul_eq_mul,hsum,hw]
    simpa only [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg hC (Finset.sum_nonneg (fun i _ => norm_nonneg (v i x))))] using hx
  calc
    ‖u‖ ≤ ‖C • ∑ i,w i‖ := hh
    _ = C*‖∑ i,w i‖ := by rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hC]
    _ ≤ C*∑ i,‖w i‖ := mul_le_mul_of_nonneg_left (norm_sum_le _ _) hC
    _ = C*∑ i,‖v i‖ := by simp only [hn]

variable (s : Fin 3 → ℝ)
  (hs : ∀ u v : ℝ,(1/2)*(u^2+v^2) ≤ s 0*u^2+2*s 1*u*v+s 2*v^2)
  {a b l r R : ℝ} (ha : a≠0) (hR : 0≤R)
  (hb : b∈Icc (-(1:ℝ)/100) (1/100)) (hlr : l≤r)
  (hl : -(1:ℝ)/100≤l) (hr : r≤1/100)
  (hT : ∀ t∈Icc l r,affineEndTime a b t∈Icc 0 R)

include ha hb hl hr hT in
lemma attachedEndBand_positive_ae :
    ∀ᵐ y∂volume.restrict (sourceClosedCollarBand l r),
      y∈sourceClosedCollarBand (-(1:ℝ)/100) (1/100) ∧ 0<a*(sourceCollarTime y-b) := by
  filter_upwards [ae_restrict_mem ((isCompact_sourceClosedCollarBand hl hr).measurableSet),
    ae_restrict_of_ae (sourceColevel_ae_ne hb)] with y hy hne
  exact ⟨⟨hl.trans hy.1,hy.2.trans hr⟩,
    lt_of_le_of_ne (hT _ hy).1 (Ne.symm (mul_ne_zero ha (sub_ne_zero.mpr hne)))⟩

def attachedEndGradientL (k : Fin 3) :
    spectralTraceGraph (torusRate s) →ₗ[ℝ] Lp ℝ 2 (volume.restrict (sourceClosedCollarBand l r)) where
  toFun f := (attachedEndPoisson_grad_memLp s hs f ha hR hb hlr hl hr hT k).toLp _
  map_add' f g := by
    apply Lp.ext
    filter_upwards [(attachedEndPoisson_grad_memLp s hs (f+g) ha hR hb hlr hl hr hT k).coeFn_toLp,
      (attachedEndPoisson_grad_memLp s hs f ha hR hb hlr hl hr hT k).coeFn_toLp,
      (attachedEndPoisson_grad_memLp s hs g ha hR hb hlr hl hr hT k).coeFn_toLp,
      Lp.coeFn_add ((attachedEndPoisson_grad_memLp s hs f ha hR hb hlr hl hr hT k).toLp _)
        ((attachedEndPoisson_grad_memLp s hs g ha hR hb hlr hl hr hT k).toLp _),
      ae_restrict_of_ae (attachedEndPoisson_real_fderiv_add_ae s hs f g a b),
      attachedEndBand_positive_ae ha hb hl hr hT] with x hfg hf hg he hd hx
    rw [hfg,he]
    simp only [Pi.add_apply,hf,hg,hd hx.1 hx.2]
    rfl
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [(attachedEndPoisson_grad_memLp s hs (c•f) ha hR hb hlr hl hr hT k).coeFn_toLp,
      (attachedEndPoisson_grad_memLp s hs f ha hR hb hlr hl hr hT k).coeFn_toLp,
      Lp.coeFn_smul c ((attachedEndPoisson_grad_memLp s hs f ha hR hb hlr hl hr hT k).toLp _),
      ae_restrict_of_ae (attachedEndPoisson_real_fderiv_rsmul_ae s hs c f a b),
      attachedEndBand_positive_ae ha hb hl hr hT] with x hcf hf he hd hx
    change _ = (c • _ : Lp ℝ 2 (volume.restrict (sourceClosedCollarBand l r))) x
    rw [hcf,he]
    simp only [Pi.smul_apply,hf,hd hx.1 hx.2]
    rfl

lemma attachedEndGradientL_ae (k : Fin 3) (f : spectralTraceGraph (torusRate s)) :
    attachedEndGradientL s hs ha hR hb hlr hl hr hT k f=ᵐ[volume.restrict (sourceClosedCollarBand l r)]
      (fun y => fderiv ℝ (fun y => (attachedEndPoissonField s f a b 0 y).re) y (Pi.single k 1)) :=
  (attachedEndPoisson_grad_memLp s hs f ha hR hb hlr hl hr hT k).coeFn_toLp

lemma attachedEndGradientL_bound (k : Fin 3) :
    ∃ C : ℝ,∀ f,‖attachedEndGradientL s hs ha hR hb hlr hl hr hT k f‖≤C*‖f‖ := by
  obtain ⟨C,hC,hbound⟩ := attachedEndPoisson_grad_bound_uniform s hs a b
  refine ⟨C*∑ d : Fin 3,‖attachedEndFlatCLM s hs ha hR hlr hl hr hT d.succ‖,fun f => ?_⟩
  have h : ‖attachedEndGradientL s hs ha hR hb hlr hl hr hT k f‖≤
      C*∑ d : Fin 3,‖attachedEndFlatCLM s hs ha hR hlr hl hr hT d.succ f‖ := by
    apply lp_norm_le_sum_norm_of_ae hC.le
    filter_upwards [attachedEndGradientL_ae s hs ha hR hb hlr hl hr hT k f,
      ae_all_iff.mpr (fun d : Fin 3 => attachedEndFlatCLM_ae s hs f ha hR hlr hl hr hT d.succ),
      ae_restrict_of_ae (hbound f k),attachedEndBand_positive_ae ha hb hl hr hT] with x hx hj hb hxpos
    rw [hx,Real.norm_eq_abs]
    simp only [hj]
    exact hb hxpos.1 hxpos.2
  calc
    _ ≤ C*∑ d : Fin 3,‖attachedEndFlatCLM s hs ha hR hlr hl hr hT d.succ f‖ := h
    _ ≤ C*∑ d : Fin 3,‖attachedEndFlatCLM s hs ha hR hlr hl hr hT d.succ‖*‖f‖ :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun d _ => ContinuousLinearMap.le_opNorm _ _)) hC.le
    _ = _ := by rw [← Finset.sum_mul]; ring

def attachedEndGradientCLM (k : Fin 3) :
    spectralTraceGraph (torusRate s) →L[ℝ] Lp ℝ 2 (volume.restrict (sourceClosedCollarBand l r)) :=
  (attachedEndGradientL s hs ha hR hb hlr hl hr hT k).mkContinuousOfExistsBound
    (attachedEndGradientL_bound s hs ha hR hb hlr hl hr hT k)

end ScalarConductivity

end

end OAI
