import OAI.Analysis.AncientFlat.Evolution.GammaRHS
import OAI.Analysis.AncientFlat.Evolution.ActualClassical

namespace OAI
noncomputable section
open Set Filter MeasureTheory
open scoped SchwartzMap Topology ZeroAtInfty BoundedContinuousFunction Laplacian ContDiff
namespace ParametrixVolterra
open FrozenParametrix StrongWeightedVolterra
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
variable {T α β : ℝ}
lemma hasDerivAt_source_mildTime (hα : 0 < α)
    (A : C(Slab T,V →ᵇ Icc α β)) (b : C(Slab T,V →ᵇ ℂ)) (hT : 0 ≤ T)
    (γ : ℝ) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (L : ℝ) (hL : 0 ≤ L)
    (hLip : ∀ s r : Slab T, ∀ x z : V,
      |(A s x).val-(A r z).val| ≤ L*(‖x-z‖+|s.val-r.val|))
    (d : C₀(V,ℂ)) (j l : Time T →ᵇ C₀(V,ℂ)) (H : ℝ) (hH : 0 ≤ H)
    (hhold : ∀ s : Time T, ∀ x y,
      ‖unweighted j s.val x-unweighted j s.val y‖ ≤ H*s.val^(-7/8 : ℝ)*‖x-y‖^γ)
    (hi : ∀ t : Time T, IntervalIntegrable
      (fun r => residualKernel hα A b hT t r (unweighted j r)) volume 0 t.val)
    (hj : ∀ t : Time T, unweighted j t.val+∫ r in 0..t.val,
      residualKernel hα A b hT t r (unweighted j r) = l t-actualResidual hα A b t (initial hT) d)
    (hA : ∀ s, ContDiff ℝ ∞ (fun x => (A s x).val))
    (t : Time T) (ht : t.val < T) :
    HasDerivAt (fun r => (mildTime hα A hT d j r).toBCF)
      ((l t).toBCF+mildRHS hα A b hT d j t) t.val := by
  have hu : ContinuousOn (fun r => (mildTime hα A hT d j r).toBCF) (Icc 0 T) :=
    ZeroAtInftyContinuousMap.isometry_toBCF.continuous.comp_continuousOn
      (continuousOn_mildTime hα A hT d j)
  have hF : Continuous (fun s : Time T => (l s).toBCF+mildRHS hα A b hT d j s) :=
    (ZeroAtInftyContinuousMap.isometry_toBCF.continuous.comp l.continuous).add
      (continuous_mildRHS_gamma hα A b hT d j γ hγ hγ1 L H hL hH hLip hhold)
  apply hasDerivAt_of_weak_on_time _ _ hu hF _ t ht
  intro φ hφ hc s hs
  let φc := realTest φ hφ hc
  have hcφ : HasCompactSupport (φc : V → ℂ) := compactSupport_realTest φ hφ hc
  let ψ := coefficientTest (A (now s)) (hA (now s)) φc hcφ
  have hcψ : HasCompactSupport (ψ : V → ℂ) := by
    change HasCompactSupport (fun x => ((A (now s) x).val : ℂ)*φc x)
    exact hcφ.mul_left
  have hψ : ∀ x, ψ x = ((A (now s) x).val : ℂ)*(φ x : ℂ) := by intro x; rfl
  have hus := contDiff_mildTime_of_holder_gamma hα A hT γ hγ hγ1 L hL hLip d j H hH hhold s
  have hU := mildBilaplacian_apply_gamma hα A hT d j γ hγ hγ1 L H hL hH hLip hhold s
  rw [map_add,mildRHS,pair_rhs_eq_neg_adjoint A b s _ _ hus hU φ hφ hc ψ hcψ hψ,
    pair_realTest_eq φ hφ hc (l s),← sub_eq_add_neg]
  have hd := hasDerivAt_pair_mildTime hα A b hT d j l hi hj s hs φc ψ
    (coefficientTest_apply _ _ _ _)
  apply hd.congr_of_eventuallyEq
  exact Eventually.of_forall (fun r => pair_realTest_eq φ hφ hc (mildTime hα A hT d j r))
end ParametrixVolterra

end

end OAI
