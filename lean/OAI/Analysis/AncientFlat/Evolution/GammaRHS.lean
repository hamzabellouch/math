import OAI.Analysis.AncientFlat.Evolution.PairClassical
import OAI.Analysis.AncientFlat.Evolution.GammaRowIntegral

namespace OAI
noncomputable section
open Set Filter MeasureTheory
open scoped SchwartzMap Topology ZeroAtInfty BoundedContinuousFunction Laplacian ContDiff
namespace ParametrixVolterra
section ContinuousMildRowFourGamma
open FrozenParametrix SourceFrozenRows StrongWeightedVolterra BiharmonicKernel
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
variable {T α β : ℝ} (hα : 0 < α) (A : C(Slab T,V →ᵇ Icc α β))
    (hT : 0 ≤ T) (d : C₀(V,ℂ)) (j : Time T →ᵇ C₀(V,ℂ))

variable (γ : ℝ) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (L H : ℝ) (hL : 0 ≤ L) (hH : 0 ≤ H)
    (hLip : ∀ s r : Slab T, ∀ x z : V,
      |(A s x).val-(A r z).val| ≤ L*(‖x-z‖+|s.val-r.val|))
    (hhold : ∀ s : Time T, ∀ x y, ‖unweighted j s.val x-unweighted j s.val y‖ ≤
      H*s.val^(-7/8 : ℝ)*‖x-y‖^γ)
include hγ hγ1 hL hH hLip hhold

lemma continuous_mildRowFour_gamma : Continuous (mildRowFour hα A hT d j) := by
  let : NormedAddCommGroup (V →ᵇ (V [×4]→L[ℝ] ℂ)) := inferInstance
  have h0 : Continuous (fun t : Time T => timeBCF (heatKernel 1 zero_lt_one) hα
      (A (initial hT)) t.val t.property.1 d.toBCF 4) :=
    continuous_timeBCF (heatKernel 1 zero_lt_one) hα (fun _ => A (initial hT))
      (fun t : Time T => t.val) (fun t => t.property.1) (fun _ => d.toBCF) 4
      continuous_const continuous_subtype_val continuous_const
  exact h0.add (continuous_rowIntegralBCF_gamma (heatKernel 1 zero_lt_one) hα A j γ hγ hγ1 L H hL hH
      (fun s x y => by simpa only [Real.norm_eq_abs,sub_self,abs_zero,add_zero] using hLip s s x y) hhold)

lemma mildRowFour_eq_gamma (t : Time T) :
    (mildRowFour hα A hT d j t : V → (V [×4]→L[ℝ] ℂ)) =
      iteratedFDeriv ℝ 4 (fun x => mildTime hα A hT d j t.val x) := by
  have h0 : ContDiff ℝ 4 (fun x => c0Time hα (A (initial hT)) t.val d x) := by
    rw [funext (c0Time_eq_sourceValue hα _ _ t.property.1 d)]
    exact contDiff_infty.mp (contDiff_value (heatKernel 1 zero_lt_one) _
      (continuous_subtype_val.comp (A (initial hT)).continuous) α β hα
      (fun y => (A (initial hT) y).property) _ (Real.rpow_pos_of_pos t.property.1 _) d.toBCF) 4
  have h1 := contDiff_duhamel_of_holder_gamma A hT hα γ hγ hγ1 L hL hLip j H hH hhold t
  change _ = iteratedFDeriv ℝ 4 (fun x => c0Time hα (A (initial hT)) t.val d x+duhamel hα A j t.val x)
  rw [fun_iteratedFDeriv_add h0 h1,iteratedFDeriv_c0Time hα _ _ t.property.1 d,
    iteratedFDeriv_duhamel_four_gamma hα A hT γ hγ hγ1 L hL hLip j H hH hhold t]
  rfl

lemma continuous_mildBilaplacian_gamma : Continuous (mildBilaplacian hα A hT d j) :=
  (BoundedContinuousFunction.continuous_comp (ClassicalIBP.traceFour (V := V)).lipschitzWith).comp
    (continuous_mildRowFour_gamma hα A hT d j γ hγ hγ1 L H hL hH hLip hhold)

lemma mildBilaplacian_apply_gamma (t : Time T) (x : V) :
    mildBilaplacian hα A hT d j t x = Δ (Δ (fun y => mildTime hα A hT d j t.val y)) x := by
  have h0 : ContDiff ℝ 4 (fun x => c0Time hα (A (initial hT)) t.val d x) := by
    rw [funext (c0Time_eq_sourceValue hα _ _ t.property.1 d)]
    exact contDiff_infty.mp (contDiff_value (heatKernel 1 zero_lt_one) _
      (continuous_subtype_val.comp (A (initial hT)).continuous) α β hα
      (fun y => (A (initial hT) y).property) _ (Real.rpow_pos_of_pos t.property.1 _) d.toBCF) 4
  have h1 := contDiff_duhamel_of_holder_gamma A hT hα γ hγ hγ1 L hL hLip j H hH hhold t
  have hu : ContDiff ℝ 4 (fun y => mildTime hα A hT d j t.val y) := h0.add h1
  rw [ClassicalIBP.bilaplacian_eq_traceFour _ hu x]
  change ClassicalIBP.traceFour ((mildRowFour hα A hT d j t) x) = _
  rw [congrFun (mildRowFour_eq_gamma hα A hT d j γ hγ hγ1 L H hL hH hLip hhold t) x]

end ContinuousMildRowFourGamma

open FrozenParametrix StrongWeightedVolterra
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
variable {T α β : ℝ}
lemma continuous_mildRHS_gamma (hα : 0 < α) (A : C(Slab T,V →ᵇ Icc α β)) (b : C(Slab T,V →ᵇ ℂ))
    (hT : 0 ≤ T) (d : C₀(V,ℂ)) (j : Time T →ᵇ C₀(V,ℂ))
    (γ : ℝ) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (L H : ℝ) (hL : 0≤L) (hH : 0≤H)
    (hLip : ∀ s r : Slab T, ∀ x z : V,
      |(A s x).val-(A r z).val| ≤ L*(‖x-z‖+|s.val-r.val|))
    (hhold : ∀ s : Time T, ∀ x y, ‖unweighted j s.val x-unweighted j s.val y‖ ≤
      H*s.val^(-7/8 : ℝ)*‖x-y‖^γ) :
    Continuous (mildRHS hα A b hT d j) := by
  have hu : Continuous (fun t : Time T => (mildTime hα A hT d j t.val).toBCF) :=
    ZeroAtInftyContinuousMap.isometry_toBCF.continuous.comp
      ((continuousOn_mildTime hα A hT d j).comp_continuous continuous_subtype_val
        (fun t => ⟨t.property.1.le,t.property.2⟩))
  exact ((continuous_coefficient_comp (fun t => A (now t)) (A.continuous.comp continuous_now)).mul
      (continuous_mildBilaplacian_gamma hα A hT d j γ hγ hγ1 L H hL hH hLip hhold)).neg.sub
    ((b.continuous.comp continuous_now).mul hu)

end ParametrixVolterra

end

end OAI
