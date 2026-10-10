import OAI.Analysis.AncientFlat.Evolution.ActualClassical

namespace OAI
noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff

namespace ParametrixVolterra
open scoped ZeroAtInfty BoundedContinuousFunction SchwartzMap Laplacian
open FrozenParametrix StrongWeightedVolterra
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
variable {T α β : ℝ}

theorem exists_classical_homogeneous_evolution (hα : 0 < α)
    (A : C(Slab T,V →ᵇ Icc α β)) (b : C(Slab T,V →ᵇ ℂ))
    (hT₀ : 0 ≤ T) (hT : T ≤ 1) (L B : ℝ) (hL : 0 ≤ L) (hB : 0 ≤ B)
    (hb : ∀ s, ‖b s‖ ≤ B)
    (hLip : ∀ s r : Slab T, ∀ x z : V,
      |(A s x).val-(A r z).val| ≤ L*(‖x-z‖+|s.val-r.val|))
    (hLipb : ∀ s : Slab T, ∀ x z : V, ‖b s x-b s z‖ ≤ L*‖x-z‖)
    (hA : ∀ s, ContDiff ℝ ∞ (fun x => (A s x).val)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ d : C₀(V,ℂ), ∃ u : ℝ → C₀(V,ℂ),
      u 0=d ∧ ContinuousOn u (Icc 0 T) ∧
      (∀ t ∈ Icc 0 T, ‖u t‖ ≤ K*‖d‖) ∧
      (∀ t ∈ Ioo 0 T, ContDiff ℝ 4 (fun x => u t x)) ∧
      (∀ (t : Time T), t.val < T → ∀ x : V,
        HasDerivAt (fun r => u r x)
          (-((A (now t) x).val : ℂ)*(Δ (Δ (fun y => u t.val y))) x
            -b (now t) x*u t.val x) t.val) := by
  obtain ⟨C,D,hC,hD,hs⟩ := exists_parametrix_correction_full hα A b hT₀ hT L B hL hB hb hLip
  let M := frozenBound (V := V) (β := β) hα
  let Q := ∫ v : UnitTime, MildVolterra.massWeight v
  have hM : 0≤M := frozenBound_nonneg hα
  have hQ : 0≤Q := integral_nonneg MildVolterra.massWeight_nonneg
  refine ⟨M+Q*M*D*C,by positivity,fun d => ?_⟩
  obtain ⟨j,hi,hj,hjb⟩ := hs d 0
  have hj' : ∀ t : Time T, unweighted j t.val+∫ r in 0..t.val,
      residualKernel hα A b hT₀ t r (unweighted j r) =
        -actualResidual hα A b t (initial hT₀) d := by simpa using hj
  let : NormedAddCommGroup (Time T →ᵇ C₀(V,ℂ)) := inferInstance
  have hz : ‖(0 : Time T →ᵇ C₀(V,ℂ))‖ = 0 := norm_zero
  have hjb' : ‖j‖ ≤ D*(C*‖d‖) := by
    rw [hz,zero_add] at hjb
    exact hjb
  refine ⟨mildTime hα A hT₀ d j,mildTime_zero hα A hT₀ d j,
    continuousOn_mildTime hα A hT₀ d j,fun t ht => ?_,fun t ht => ?_,fun t ht x => ?_⟩
  · have ht1 : t^(1/4 : ℝ)≤1 := Real.rpow_le_one ht.1 (ht.2.trans hT) (by positivity)
    have h0 := norm_c0Time_le hα (A (initial hT₀)) t d
    have h1 := norm_duhamel_le hα A hT₀ j t ht
    calc
      ‖mildTime hα A hT₀ d j t‖ ≤ M*‖d‖+t^(1/4 : ℝ)*(Q*M*‖j‖) :=
        (norm_add_le _ _).trans (add_le_add h0 h1)
      _ ≤ M*‖d‖+Q*M*‖j‖ := add_le_add le_rfl
        (mul_le_of_le_one_left (mul_nonneg (mul_nonneg hQ hM) (norm_nonneg j)) ht1)
      _ ≤ M*‖d‖+Q*M*(D*(C*‖d‖)) := add_le_add le_rfl
        (mul_le_mul_of_nonneg_left hjb' (mul_nonneg hQ hM))
      _ = _ := by ring
  · exact contDiff_mildTime_of_correction hα A b hT₀ hT L B hL hB hb hLip hLipb d j hi hj' ⟨t,ht.1,ht.2.le⟩
  · exact hasDerivAt_mildTime_apply hα A b hT₀ hT L B hL hB hb hLip hLipb d j hi hj' hA t ht x
end ParametrixVolterra

end

end OAI
