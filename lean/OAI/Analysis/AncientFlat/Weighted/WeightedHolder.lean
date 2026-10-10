import OAI.Analysis.AncientFlat.Evolution.EarlyRows
import OAI.Analysis.AncientFlat.Regularity.MeasurableHolder

namespace OAI
noncomputable section
open Set Filter MeasureTheory
namespace SourceFrozenRows
open scoped ContDiff BoundedContinuousFunction SchwartzMap
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
theorem weighted_fourth_derivative_holder (K : SchwartzMap V ℂ)
    (A : ℝ → V → ℝ) (hA : Continuous (Function.uncurry A))
    (α β γ L σ p M H T : ℝ) (hα : 0<α) (hγ : 0<γ) (hγ1 : γ<1) (hL : 0≤L)
    (hAr : ∀ t y, A t y ∈ Set.Icc α β)
    (hAL : ∀ t x y, ‖A t x-A t y‖≤L*‖x-y‖)
    (hσ₀ : 0≤σ) (hσ : σ<1) (hp₀ : 0≤p) (hp : p<1) (hM : 0≤M) (hH : 0≤H) (hT : T≤1)
    (f : ℝ → (V →ᵇ ℂ)) (hf : MeasureTheory.StronglyMeasurable f)
    (hm : ∀ t∈Set.Ioo 0 T, ‖f t‖≤M*t^(-σ))
    (hh : ∀ t∈Set.Ioo 0 T, ∀ x y, ‖f t x-f t y‖≤H*t^(-p)*‖x-y‖^γ)
    (a : ℝ) (ha : 0<a) :
    (∀ t∈Set.Ioc 0 T, ContDiff ℝ 4 (duhamel K A f t)) ∧
    ∃ C : ℝ, 0≤C ∧
      (∀ t∈Set.Icc a T, ∀ x, ‖iteratedFDeriv ℝ 4 (duhamel K A f t) x‖≤C) ∧
      (∀ t∈Set.Icc a T, ∀ s∈Set.Icc a T, ∀ x y,
        ‖iteratedFDeriv ℝ 4 (duhamel K A f t) x-iteratedFDeriv ℝ 4 (duhamel K A f s) y‖≤
          C*(‖x-y‖^γ+|t-s|^(γ/4))) := by
  have hfn (t) (ht : t∈Ioc 0 T) : ∀ r∈Ioo 0 t, ‖f r‖≤M*r^(-σ) :=
    fun r hr => hm r ⟨hr.1,hr.2.trans_le ht.2⟩
  have hfh (t) (ht : t∈Ioc 0 T) : ∀ r∈Ioo 0 t, ∀ x y,
      ‖f r x-f r y‖≤(H*r^(-p))*‖x-y‖^γ := fun r hr => hh r ⟨hr.1,hr.2.trans_le ht.2⟩
  refine ⟨fun t ht => WeightedSourceFrozenRows.contDiff_duhamel K A hA α β hα hAr L hL hAL
    f hf σ p M H γ t hσ hp hM hH ht.1 hγ hγ1.le (hfn t ht) (hfh t ht),?_⟩
  by_cases haT : a≤T
  swap
  · refine ⟨0,le_rfl,?_,?_⟩
    · intro t ht; exact (haT (ht.1.trans ht.2)).elim
    · intro t ht; exact (haT (ht.1.trans ht.2)).elim
  have hT₀ : 0≤T := ha.le.trans haT
  let b := a/2
  have hb : 0<b := by dsimp [b]; positivity
  have hba : 2*b≤a := by dsimp [b]; linarith
  obtain ⟨B,hB,hbn,hbh⟩ := early_fourth_holder K A hA α β γ L σ p M H T a b hα hγ hγ1 hL hAr hAL
    hσ hp hM hH hT f hf hm hh hb hba haT
  let g : ℝ → (V →ᵇ ℂ) := (Ioo b T).indicator f
  have hg : StronglyMeasurable g := hf.indicator measurableSet_Ioo
  let M' := M*b^(-σ)
  let H' := H*b^(-p)
  have hM' : 0≤M' := by dsimp [M']; positivity
  have hH' : 0≤H' := by dsimp [H']; positivity
  have hgn (r : ℝ) : ‖g r‖≤M' := by
    by_cases hr : r∈Ioo b T
    · rw [show g r=f r by exact indicator_of_mem hr f]
      exact (hm r ⟨hb.trans hr.1,hr.2⟩).trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos hb hr.1.le (neg_nonpos.mpr hσ₀)) hM)
    · rw [show g r=0 by exact indicator_of_notMem hr f,norm_zero]; exact hM'
  have hgh (r : ℝ) (x y : V) : ‖g r x-g r y‖≤H'*‖x-y‖^γ := by
    by_cases hr : r∈Ioo b T
    · rw [show g r=f r by exact indicator_of_mem hr f]
      exact (hh r ⟨hb.trans hr.1,hr.2⟩ x y).trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hb hr.1.le (neg_nonpos.mpr hp₀)) hH)
        (Real.rpow_nonneg (norm_nonneg _) _))
    · rw [show g r=0 by exact indicator_of_notMem hr f]
      simp only [BoundedContinuousFunction.coe_zero,Pi.zero_apply,sub_self,norm_zero]
      positivity
  obtain ⟨C,hC,hch⟩ := MeasurableSchauder.integratedJet_fourth_holder (V := V) K α β γ L hα hγ hγ1 hL
  obtain ⟨hcn,hch⟩ := hch A hA hAr hAL g M' H' T hM' hH' hT₀ hT hg (fun r _ => hgn r) (fun r _ => hgh r)
  have hsplit (t) (ht : t∈Icc a T) (x : V) :
      iteratedFDeriv ℝ 4 (duhamel K A f t) x =
        (∫ r in Ioo 0 b,VariableSchauder.jet K (A r) (t-r) (f r) 4 x)+
        VariableSchauder.integratedJet K A g t 4 x := by
    have ht' : t∈Ioc 0 T := ⟨ha.trans_le ht.1,ht.2⟩
    rw [WeightedSourceFrozenRows.iteratedFDeriv_duhamel K A hA α β hα hAr L hL hAL f hf σ p M H γ t hσ hp hM hH
      ht'.1 hγ hγ1.le (hfn t ht') (hfh t ht') 4 le_rfl]
    have hi := WeightedSourceFrozenRows.integrableOn_row K A hA α β hα hAr L hL hAL f hf σ p M H γ t hσ hp hM hH
      ht'.1 hγ hγ1.le (hfn t ht') (hfh t ht') 4 le_rfl x
    change (∫ r in Ioo 0 t,VariableSchauder.jet K (A r) (t-r) (f r) 4 x)=_
    rw [ParabolicSchauder.integral_Ioo_split 0 b t hb.le (by linarith [ht.1])
      (fun r => VariableSchauder.jet K (A r) (t-r) (f r) 4 x) hi]
    congr 1
    unfold VariableSchauder.integratedJet
    have heq : (fun r => VariableSchauder.jet K (A r) (t-r) (g r) 4 x)=
        (Ioo b T).indicator (fun r => VariableSchauder.jet K (A r) (t-r) (f r) 4 x) := by
      funext r
      by_cases hr : r∈Ioo b T
      · simp only [g,indicator_of_mem hr]
      · simp only [g,indicator_of_notMem hr]
        simp [VariableSchauder.jet,row,ScaledSchwartzConvolution.value]
        apply integral_eq_zero_of_ae
        filter_upwards with y
        change (_ : ℝ) • (0 : V [×4]→L[ℝ] ℂ)=0
        exact smul_zero (M := ℝ) (A := V [×4]→L[ℝ] ℂ) _
    rw [heq,setIntegral_indicator measurableSet_Ioo]
    have he : Ioo 0 t ∩ Ioo b T=Ioo b t := by
      ext r
      simp only [mem_inter_iff,mem_Ioo]
      constructor
      · intro hr; exact ⟨hr.2.1,hr.1.2⟩
      · intro hr; exact ⟨⟨hb.trans hr.1,hr.2⟩,hr.1,hr.2.trans_le ht.2⟩
    rw [he]
  let Q := C*(H'+M')
  have hQ : 0≤Q := mul_nonneg hC (add_nonneg hH' hM')
  refine ⟨B+Q,add_nonneg hB hQ,?_,?_⟩
  · intro t ht x
    rw [hsplit t ht x]
    exact (norm_add_le ..).trans (add_le_add (hbn t ht x) (hcn t ⟨ha.le.trans ht.1,ht.2⟩ x))
  · intro t ht s hs x y
    rw [hsplit t ht x,hsplit s hs y]
    have he : ∀ u v w z : V [×4]→L[ℝ] ℂ, ‖u+v-(w+z)‖≤‖u-w‖+‖v-z‖ := by
      intro u v w z; rw [show u+v-(w+z)=(u-w)+(v-z) by abel]; exact norm_add_le ..
    apply (he _ _ _ _).trans
    have h1 := hbh t ht s hs x y
    have h2 := hch t ⟨ha.le.trans ht.1,ht.2⟩ s ⟨ha.le.trans hs.1,hs.2⟩ x y
    exact (add_le_add h1 h2).trans_eq (by dsimp [Q]; ring)
end SourceFrozenRows


end

end OAI
