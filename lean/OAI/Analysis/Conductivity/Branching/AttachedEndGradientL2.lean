import Mathlib
import OAI.Analysis.Conductivity.Branching.AttachedEndL2
import OAI.Analysis.Conductivity.Flux.AttachedEndDifferential

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus Matrix
open scoped ENNReal

lemma sourceAngularCollarMeasure_self (b : ℝ) : sourceAngularCollarMeasure b b=0 := by
  simp [sourceAngularCollarMeasure]

lemma sourceCollarTime_level_null {b : ℝ} (hb : b∈Icc (-(1:ℝ)/100) (1/100)) :
    volume {y : Fin 3 → ℝ | sourceCollarTime y=b}=0 := by
  have hle := (sourceClosedCollarBand_measure_le hb.1 hb.2).trans
    (sourcePhysicalCollarMeasure_le (le_refl b) hb.1 hb.2)
  rw [sourceAngularCollarMeasure_self,smul_zero] at hle
  have he := Measure.le_iff.mp hle univ MeasurableSet.univ
  have hs : sourceClosedCollarBand b b={y : Fin 3 → ℝ | sourceCollarTime y=b} := by
    ext y; simp [sourceClosedCollarBand]
  simp only [Measure.restrict_apply_univ,Measure.coe_zero,Pi.zero_apply,hs] at he
  exact le_antisymm he bot_le

lemma sourceColevel_ae_ne {b : ℝ} (hb : b∈Icc (-(1:ℝ)/100) (1/100)) :
    ∀ᵐ y : Fin 3 → ℝ,sourceCollarTime y≠b := by
  rw [ae_iff]
  simpa only [not_not] using sourceCollarTime_level_null hb

lemma attachedEndPoisson_grad_bound (s : Fin 3 → ℝ)
    (hs : ∀ u v : ℝ,(1/2)*(u^2+v^2) ≤ s 0*u^2+2*s 1*u*v+s 2*v^2)
    (f : spectralTraceGraph (torusRate s)) (a b : ℝ) :
    ∃ C : ℝ,0<C ∧ ∀ k : Fin 3,∀ᵐ y : Fin 3 → ℝ,
      y∈sourceClosedCollarBand (-(1:ℝ)/100) (1/100) → 0<a*(sourceCollarTime y-b) →
      |fderiv ℝ (fun y => (attachedEndPoissonField s f a b 0 y).re) y (Pi.single k 1)|≤
        C*∑ d : Fin 3,‖attachedEndPoissonField s f a b d.succ y‖ := by
  obtain ⟨C,hC,hbound⟩ := sourceCartesianGradient_uniform_bound
  refine ⟨C*(|a|+1),mul_pos hC (by positivity),?_⟩
  intro k
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

lemma attachedEndPoisson_grad_memLp (s : Fin 3 → ℝ)
    (hs : ∀ u v : ℝ,(1/2)*(u^2+v^2) ≤ s 0*u^2+2*s 1*u*v+s 2*v^2)
    (f : spectralTraceGraph (torusRate s)) {a b l r R : ℝ}
    (ha : a≠0) (hR : 0≤R) (hb : b∈Icc (-(1:ℝ)/100) (1/100))
    (hlr : l≤r) (hl : -(1:ℝ)/100≤l) (hr : r≤1/100)
    (hT : ∀ t∈Icc l r,affineEndTime a b t∈Icc 0 R) (k : Fin 3) :
    MemLp (fun y => fderiv ℝ (fun y => (attachedEndPoissonField s f a b 0 y).re) y (Pi.single k 1))
      2 (volume.restrict (sourceClosedCollarBand l r)) := by
  obtain ⟨C,hC,hbound⟩ := attachedEndPoisson_grad_bound s hs f a b
  have hjet (d : Fin 3) := (attachedEndPoissonField_memLp s hs f ha hR hlr hl hr hT d.succ).norm
  have hsum : MemLp (fun y => C*∑ d : Fin 3,‖attachedEndPoissonField s f a b d.succ y‖) 2
      (volume.restrict (sourceClosedCollarBand l r)) :=
    (memLp_finsetSum Finset.univ (fun d _ => hjet d)).const_mul C
  apply hsum.mono' (measurable_fderiv_apply_const ℝ _ _).aestronglyMeasurable
  have hband : MeasurableSet (sourceClosedCollarBand l r) :=
    measurableSet_Icc.preimage measurable_sourcePhysicalCoordinates.fst
  filter_upwards [ae_restrict_mem hband,ae_restrict_of_ae (hbound k),
    ae_restrict_of_ae (sourceColevel_ae_ne hb)] with y hy hbd hne
  rw [Real.norm_eq_abs]
  exact hbd ⟨hl.trans hy.1,hy.2.trans hr⟩
    (lt_of_le_of_ne (hT _ hy).1 (Ne.symm (mul_ne_zero ha (sub_ne_zero.mpr hne))))

end ScalarConductivity

end

end OAI
