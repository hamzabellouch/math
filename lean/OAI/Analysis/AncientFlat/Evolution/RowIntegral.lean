import OAI.Analysis.AncientFlat.Evolution.BetaRow

namespace OAI
noncomputable section
open Set Filter MeasureTheory
open scoped SchwartzMap Topology ZeroAtInfty BoundedContinuousFunction ContDiff
namespace ParametrixVolterra
section RowIntegralBCF
open SourceFrozenRows StrongWeightedVolterra
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
local instance : ContinuousENorm (V →ᵇ (V [×4]→L[ℝ] ℂ)) :=
  @SeminormedAddGroup.toContinuousENorm (V →ᵇ (V [×4]→L[ℝ] ℂ)) inferInstance
variable {T α β : ℝ} (K : SchwartzMap V ℂ) (hα : 0 < α)
  (A : C(Slab T,V →ᵇ Icc α β)) (j : Time T →ᵇ C₀(V,ℂ))

def rowIntegralBCF (t : Time T) : V →ᵇ (V [×4]→L[ℝ] ℂ) :=
  t.val • ∫ u : UnitTime, rowData K hα A j t u

variable (L H : ℝ) (hL : 0 ≤ L) (hH : 0 ≤ H)
    (hLip : ∀ s : Slab T, ∀ x y, ‖(A s x).val-(A s y).val‖ ≤ L*‖x-y‖)
    (hhold : ∀ s : Time T, ∀ x y, ‖unweighted j s.val x-unweighted j s.val y‖ ≤
      H*s.val^(-7/8 : ℝ)*‖x-y‖^(1/4 : ℝ))
include hL hH hLip hhold

lemma integrable_rowData (t : Time T) : Integrable (rowData K hα A j t) := by
  obtain ⟨b,hbi,hb⟩ := exists_rowData_bound K hα A j L H hL hH hLip hhold t.val t.property.1
  apply hbi.mono' (f := rowData K hα A j t)
  · exact ((continuous_rowData K hα A j).comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · exact Eventually.of_forall (hb t le_rfl)

lemma continuous_rowIntegralBCF : Continuous (rowIntegralBCF K hα A j) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  obtain ⟨b,hbi,hb⟩ := exists_rowData_bound K hα A j L H hL hH hLip hhold (t.val/2) (half_pos t.property.1)
  apply continuous_subtype_val.continuousAt.smul
  apply continuousAt_of_dominated
  · exact Eventually.of_forall (fun r => ((continuous_rowData K hα A j).comp
      (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
  · filter_upwards [continuous_subtype_val.continuousAt
      (Ioi_mem_nhds (by linarith [t.property.1] : t.val/2<t.val))] with r hr
    exact Eventually.of_forall (hb r hr.le)
  · exact hbi
  · exact Eventually.of_forall (fun u => ((continuous_rowData K hα A j).comp
      (continuous_id.prodMk continuous_const)).continuousAt)

lemma rowIntegralBCF_apply (hT : 0 ≤ T) (t : Time T) (x : V) :
    rowIntegralBCF K hα A j t x = SourceFrozenRows.integralRow K (extendedA A hT)
      (fun s => (unweighted j s).toBCF) t.val 4 x := by
  let ev := BoundedContinuousFunction.evalCLM ℝ x (β := V [×4]→L[ℝ] ℂ)
  have hi := integrable_rowData K hα A j L H hL hH hLip hhold t
  change t.val • ev (∫ u : UnitTime, rowData K hα A j t u) = _
  have hev := ev.integral_comp_comm (𝕜 := ℝ) (Fₗ := V [×4]→L[ℝ] ℂ) (φ := rowData K hα A j t) hi
  rw [← hev]
  let F : ℝ → (V [×4]→L[ℝ] ℂ) := fun s =>
    row K (extendedA A hT s) ((t.val-s)^(1/4 : ℝ)) (unweighted j s).toBCF 4 x
  change t.val • (∫ u : UnitTime, rowData K hα A j t u x) = ∫ s in Ioo 0 t.val, F s
  have hc := intervalIntegral.smul_integral_comp_mul_left (a := 0) (b := 1) F t.val
  simp only [mul_zero,mul_one] at hc
  rw [intervalIntegral.integral_of_le t.property.1.le,integral_Ioc_eq_integral_Ioo] at hc
  rw [← hc,intervalIntegral.integral_of_le zero_le_one,integral_Ioc_eq_integral_Ioo,
    ← integral_subtype measurableSet_Ioo]
  congr 1
  apply integral_congr_ae
  filter_upwards with u
  rw [rowData,timeBCF_apply]
  dsimp [F]
  have he : extendedA A hT (t.val*u.val) = fun y => (A (now (lag t u)) y).val := by
    funext y
    unfold extendedA
    rw [projIcc_of_mem hT (show t.val*u.val ∈ Icc 0 T from
      ⟨(lag t u).property.1.le,(lag t u).property.2⟩)]
    rfl
  rw [he,show t.val-t.val*u.val = t.val*(1-u.val) by ring]
  rfl
end RowIntegralBCF

open SourceFrozenRows StrongWeightedVolterra BiharmonicKernel
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
variable {T α β : ℝ} (hα : 0 < α) (A : C(Slab T,V →ᵇ Icc α β))

lemma iteratedFDeriv_duhamel_four (hT : 0 ≤ T) (L : ℝ) (hL : 0 ≤ L)
    (hLip : ∀ s r : Slab T, ∀ x z : V,
      |(A s x).val-(A r z).val| ≤ L*(‖x-z‖+|s.val-r.val|))
    (j : Time T →ᵇ C₀(V,ℂ)) (H : ℝ) (hH : 0 ≤ H)
    (hj : ∀ s : Time T, ∀ x y,
      ‖unweighted j s.val x-unweighted j s.val y‖ ≤ H*s.val^(-7/8 : ℝ)*‖x-y‖^(1/4 : ℝ))
    (t : Time T) : iteratedFDeriv ℝ 4 (fun x => duhamel hα A j t.val x) =
      rowIntegralBCF (heatKernel 1 zero_lt_one) hα A j t := by
  have hf : StronglyMeasurable (fun s => (unweighted j s).toBCF) :=
    ZeroAtInftyContinuousMap.isometry_toBCF.continuous.comp_stronglyMeasurable
      (stronglyMeasurable_unweighted j)
  have hn : ∀ s ∈ Ioo 0 t.val, ‖(unweighted j s).toBCF‖ ≤ ‖j‖*s^(-(3/4 : ℝ)) := by
    intro s hs
    rw [ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]
    simpa only [neg_div,mul_comm] using norm_unweighted_le j s hs.1
  have hh : ∀ s ∈ Ioo 0 t.val, ∀ x y : V,
      ‖(unweighted j s).toBCF x-(unweighted j s).toBCF y‖ ≤
        (H*s^(-(7/8 : ℝ)))*‖x-y‖^(1/4 : ℝ) := by
    intro s hs x y
    change ‖unweighted j s x-unweighted j s y‖ ≤ _
    simpa only [neg_div] using hj ⟨s,hs.1,hs.2.le.trans t.property.2⟩ x y
  have hl : ∀ s : Slab T, ∀ x y, ‖(A s x).val-(A s y).val‖ ≤ L*‖x-y‖ := by
    intro s x y
    simpa only [Real.norm_eq_abs,sub_self,abs_zero,add_zero] using hLip s s x y
  rw [funext (duhamel_eq_sourceDuhamel A hT hα j t),
    WeightedSourceFrozenRows.iteratedFDeriv_duhamel (heatKernel 1 zero_lt_one) (extendedA A hT)
      (continuous_extendedA A hT) α β hα (extendedA_range A hT) L hL (extendedA_lipschitz A hT L hLip)
      (fun s => (unweighted j s).toBCF) hf (3/4) (7/8) ‖j‖ H (1/4) t.val
      (by norm_num) (by norm_num) (norm_nonneg j) hH t.property.1 (by norm_num) (by norm_num) hn hh 4 le_rfl]
  exact (funext (rowIntegralBCF_apply (heatKernel 1 zero_lt_one) hα A j L H hL hH hl hj hT t)).symm
end ParametrixVolterra

end

end OAI
