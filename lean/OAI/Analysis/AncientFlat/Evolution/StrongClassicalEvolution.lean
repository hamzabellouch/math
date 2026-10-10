import OAI.Analysis.AncientFlat.Regularity.UniformCorrection

namespace OAI
noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff ZeroAtInfty BoundedContinuousFunction SchwartzMap Laplacian
namespace ParametrixVolterra
open FrozenParametrix StrongWeightedVolterra
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
lemma exists_uniform_strong_classical_evolution {α β : ℝ} (hα : 0<α)
    (L B : ℝ) (hL : 0≤L) (hB : 0≤B) :
    ∃ K : ℝ, 0≤K ∧ ∀ (T : ℝ) (_ : 0≤T), T≤1 →
      ∀ (A : C(Slab T,V →ᵇ Icc α β)) (b : C(Slab T,V →ᵇ ℂ)),
      (∀ s, ‖b s‖≤B) →
      (∀ s r : Slab T, ∀ x z : V,
        |(A s x).val-(A r z).val|≤L*(‖x-z‖+|s.val-r.val|)) →
      (∀ s : Slab T, ∀ x z : V, ‖b s x-b s z‖≤L*‖x-z‖) →
      (∀ s, ContDiff ℝ ∞ (fun x => (A s x).val)) →
      ∀ d : C₀(V,ℂ), ∃ u : ℝ → C₀(V,ℂ),
        u 0=d ∧ ContinuousOn u (Icc 0 T) ∧
        (∀ t ∈ Icc 0 T, ‖u t‖≤K*‖d‖) ∧
        (∀ t ∈ Ioo 0 T, ContDiff ℝ 4 (fun x => u t x)) ∧
        (∀ t ∈ Ioo 0 T, ∀ n : ℕ, n≤4 → ∃ M : ℝ, ∀ x,
          ‖iteratedFDeriv ℝ n (fun y => u t y) x‖≤M) ∧
        (∀ (t : Time T), t.val<T → ∃ v : V →ᵇ ℂ,
          HasDerivAt (fun r => (u r).toBCF) v t.val ∧ ∀ x,
            v x=-((A (now t) x).val : ℂ)*Δ (Δ (fun y => u t.val y)) x-b (now t) x*u t.val x) := by
  obtain ⟨C,D,hC,hD,hs⟩ := exists_uniform_homogeneous_correction (V := V) (β := β) hα L B hL hB
  let M := frozenBound (V := V) (β := β) hα
  let Q := ∫ v : UnitTime, MildVolterra.massWeight v
  have hM : 0≤M := frozenBound_nonneg hα
  have hQ : 0≤Q := integral_nonneg MildVolterra.massWeight_nonneg
  refine ⟨M+Q*M*D*C,by positivity,fun T hT₀ hT A b hb hLip hLipb hA d => ?_⟩
  obtain ⟨j,hi,hj,hjb⟩ := hs T hT₀ hT A b hb hLip d
  obtain ⟨H,hH,hhold⟩ := homogeneous_correction_holder hα A b hT₀ hT L B hL hB hb hLip hLipb d j hi hj
  refine ⟨mildTime hα A hT₀ d j,mildTime_zero hα A hT₀ d j,
    continuousOn_mildTime hα A hT₀ d j,fun t ht => ?_,fun t ht => ?_,fun t ht n hn => ?_,fun t ht => ?_⟩
  · have ht1 : t^(1/4 : ℝ)≤1 := Real.rpow_le_one ht.1 (ht.2.trans hT) (by positivity)
    have h0 := norm_c0Time_le hα (A (initial hT₀)) t d
    have h1 := norm_duhamel_le hα A hT₀ j t ht
    calc
      ‖mildTime hα A hT₀ d j t‖ ≤ M*‖d‖+t^(1/4 : ℝ)*(Q*M*‖j‖) :=
        (norm_add_le _ _).trans (add_le_add h0 h1)
      _ ≤ M*‖d‖+Q*M*‖j‖ := add_le_add le_rfl
        (mul_le_of_le_one_left (mul_nonneg (mul_nonneg hQ hM) (norm_nonneg j)) ht1)
      _ ≤ M*‖d‖+Q*M*(D*(C*‖d‖)) := add_le_add le_rfl
        (mul_le_mul_of_nonneg_left hjb (mul_nonneg hQ hM))
      _ = _ := by ring
  · exact contDiff_mildTime_of_correction hα A b hT₀ hT L B hL hB hb hLip hLipb d j hi hj ⟨t,ht.1,ht.2.le⟩
  · exact bounded_iteratedFDeriv_mildTime hα A hT₀ L hL hLip j H hH hhold d ⟨t,ht.1,ht.2.le⟩ n hn
  · refine ⟨mildRHS hα A b hT₀ d j t,
      hasDerivAt_mildTime_toBCF hα A b hT₀ hT L B hL hB hb hLip hLipb d j hi hj hA t ht,?_⟩
    intro x
    change -(((A (now t) x).val : ℂ)*mildBilaplacian hα A hT₀ d j t x)-_ = _
    rw [mildBilaplacian_apply hα A hT₀ d j L H hL hH hLip hhold t x]
    simp only [BoundedContinuousFunction.mul_apply,ZeroAtInftyContinuousMap.toBCF_apply,neg_mul]
end ParametrixVolterra

end

end OAI
