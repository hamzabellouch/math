import OAI.Analysis.AncientFlat.Evolution.PairClassical

namespace OAI
noncomputable section
open Set Filter MeasureTheory
open scoped SchwartzMap Topology ZeroAtInfty BoundedContinuousFunction Laplacian ContDiff
namespace ParametrixVolterra
open FrozenParametrix StrongWeightedVolterra
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
variable {T α β : ℝ}

lemma pair_realTest_eq (φ : V → ℝ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (u : C₀(V,ℂ)) : TestSeparation.pairCLM φ
      (hφ.continuous.integrable_of_hasCompactSupport hc) u.toBCF =
    KernelPairing.pairCLM (realTest φ hφ hc) (realTest φ hφ hc).integrable u := by
  simp only [TestSeparation.pairCLM_apply,KernelPairing.pairCLM_apply,realTest_apply,
    ZeroAtInftyContinuousMap.toBCF_apply,Complex.real_smul]

variable (hα : 0<α) (A : C(Slab T,V →ᵇ Icc α β)) (b : C(Slab T,V →ᵇ ℂ))
    (hT₀ : 0≤T) (hT : T≤1) (L B : ℝ) (hL : 0≤L) (hB : 0≤B) (hb : ∀ s, ‖b s‖≤B)
    (hLip : ∀ s r : Slab T, ∀ x z : V,
      |(A s x).val-(A r z).val| ≤ L*(‖x-z‖+|s.val-r.val|))
    (hLipb : ∀ s : Slab T, ∀ x z : V, ‖b s x-b s z‖ ≤ L*‖x-z‖)
    (d : C₀(V,ℂ)) (j : Time T →ᵇ C₀(V,ℂ))
    (hi : ∀ t : Time T, IntervalIntegrable
      (fun r => residualKernel hα A b hT₀ t r (unweighted j r)) volume 0 t.val)
    (hj : ∀ t : Time T, unweighted j t.val+∫ r in 0..t.val,
      residualKernel hα A b hT₀ t r (unweighted j r) = -actualResidual hα A b t (initial hT₀) d)

include hT hL hB hb hLip hLipb hi hj
lemma homogeneous_correction_holder :
    ∃ H : ℝ, 0≤H ∧ ∀ s : Time T, ∀ x y,
      ‖unweighted j s.val x-unweighted j s.val y‖ ≤ H*s.val^(-7/8 : ℝ)*‖x-y‖^(1/4 : ℝ) := by
  obtain ⟨C,hC,hR⟩ := exists_actualResidual_holder_bound hα A b hT L B hL hB hb hLip hLipb
    (1/4) (by norm_num) (by norm_num)
  have hR' : ∀ (t : Time T) (s : Slab T), s.val<t.val → ∀ (f : C₀(V,ℂ)) (x y : V),
      ‖actualResidual hα A b t s f x-actualResidual hα A b t s f y‖ ≤
        C*‖f‖*(t.val-s.val)^(-7/8 : ℝ)*‖x-y‖^(1/4 : ℝ) := by
    convert hR using 1
    norm_num
  exact correction_holder hα A b hT₀ hT C hC hR' d 0 j 0 le_rfl
    (by intro t x y; simp) hi (by simpa using hj)

lemma hasDerivAt_mildTime_toBCF
    (hA : ∀ s, ContDiff ℝ ∞ (fun x => (A s x).val))
    (t : Time T) (ht : t.val<T) :
    HasDerivAt (fun r => (mildTime hα A hT₀ d j r).toBCF)
      (mildRHS hα A b hT₀ d j t) t.val := by
  obtain ⟨H,hH,hhold⟩ := homogeneous_correction_holder hα A b hT₀ hT L B hL hB hb hLip hLipb d j hi hj
  have hu : ContinuousOn (fun r => (mildTime hα A hT₀ d j r).toBCF) (Icc 0 T) :=
    ZeroAtInftyContinuousMap.isometry_toBCF.continuous.comp_continuousOn
      (continuousOn_mildTime hα A hT₀ d j)
  have hF := continuous_mildRHS hα A b hT₀ d j L H hL hH hLip hhold
  apply hasDerivAt_of_weak_on_time _ _ hu hF _ t ht
  intro φ hφ hc s hs
  let φc := realTest φ hφ hc
  have hcφ : HasCompactSupport (φc : V → ℂ) := compactSupport_realTest φ hφ hc
  let ψ := coefficientTest (A (now s)) (hA (now s)) φc hcφ
  have hcψ : HasCompactSupport (ψ : V → ℂ) := by
    change HasCompactSupport (fun x => ((A (now s) x).val : ℂ)*φc x)
    exact hcφ.mul_left
  have hψ : ∀ x, ψ x = ((A (now s) x).val : ℂ)*(φ x : ℂ) := by intro x; rfl
  have hus := contDiff_mildTime_of_correction hα A b hT₀ hT L B hL hB hb hLip hLipb d j hi hj s
  have hU := mildBilaplacian_apply hα A hT₀ d j L H hL hH hLip hhold s
  rw [mildRHS,pair_rhs_eq_neg_adjoint A b s _ _ hus hU φ hφ hc ψ hcψ hψ]
  have hd := hasDerivAt_pair_mildTime hα A b hT₀ d j 0 hi (by simpa using hj) s hs φc ψ
    (coefficientTest_apply _ _ _ _)
  have hz : (0 : Time T →ᵇ C₀(V,ℂ)) s = 0 := rfl
  rw [hz,map_zero,zero_sub] at hd
  apply hd.congr_of_eventuallyEq
  exact Eventually.of_forall (fun r => pair_realTest_eq φ hφ hc (mildTime hα A hT₀ d j r))

lemma hasDerivAt_mildTime_apply
    (hA : ∀ s, ContDiff ℝ ∞ (fun x => (A s x).val))
    (t : Time T) (ht : t.val<T) (x : V) :
    HasDerivAt (fun r => mildTime hα A hT₀ d j r x)
      (-((A (now t) x).val : ℂ)*(Δ (Δ (fun y => mildTime hα A hT₀ d j t.val y))) x
        -b (now t) x*mildTime hα A hT₀ d j t.val x) t.val := by
  have hd := hasDerivAt_mildTime_toBCF hα A b hT₀ hT L B hL hB hb hLip hLipb d j hi hj hA t ht
  obtain ⟨H,hH,hhold⟩ := homogeneous_correction_holder hα A b hT₀ hT L B hL hB hb hLip hLipb d j hi hj
  let ev : (V →ᵇ ℂ) →L[ℝ] ℂ := BoundedContinuousFunction.evalCLM ℝ x
  have he : HasDerivAt (fun r => mildTime hα A hT₀ d j r x) (mildRHS hα A b hT₀ d j t x) t.val :=
    ev.hasFDerivAt.comp_hasDerivAt t.val hd
  have heq : mildRHS hα A b hT₀ d j t x =
      -((A (now t) x).val : ℂ)*(Δ (Δ (fun y => mildTime hα A hT₀ d j t.val y))) x
        -b (now t) x*mildTime hα A hT₀ d j t.val x := by
    change -(((A (now t) x).val : ℂ)*mildBilaplacian hα A hT₀ d j t x)-_ = _
    rw [mildBilaplacian_apply hα A hT₀ d j L H hL hH hLip hhold t x]
    simp only [BoundedContinuousFunction.mul_apply,ZeroAtInftyContinuousMap.toBCF_apply,neg_mul]
  rw [heq] at he
  exact he
end ParametrixVolterra

end

end OAI
