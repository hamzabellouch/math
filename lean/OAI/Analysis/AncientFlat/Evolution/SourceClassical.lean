import OAI.Analysis.AncientFlat.Evolution.SourceDerivative
import OAI.Analysis.AncientFlat.Regularity.GammaBoundedJets

namespace OAI
noncomputable section
open Set Filter MeasureTheory
open scoped ZeroAtInfty BoundedContinuousFunction ContDiff Laplacian
namespace ParametrixVolterra
open FrozenParametrix StrongWeightedVolterra
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
variable {T α β : ℝ}

theorem exists_classical_source_evolution (hα : 0 < α)
    (A : C(Slab T,V →ᵇ Icc α β)) (b : C(Slab T,V →ᵇ ℂ))
    (hT₀ : 0 ≤ T) (hT : T ≤ 1) (L B : ℝ) (hL : 0 ≤ L) (hB : 0 ≤ B)
    (hb : ∀ s, ‖b s‖ ≤ B)
    (hLip : ∀ s r : Slab T, ∀ x z : V,
      |(A s x).val-(A r z).val| ≤ L*(‖x-z‖+|s.val-r.val|))
    (hLipb : ∀ s : Slab T, ∀ x z : V, ‖b s x-b s z‖ ≤ L*‖x-z‖)
    (hA : ∀ s, ContDiff ℝ ∞ (fun x => (A s x).val)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (γ : ℝ), 0 < γ → γ ≤ 1 →
      ∀ (d : C₀(V,ℂ)) (l : Time T →ᵇ C₀(V,ℂ)),
      (∃ H : ℝ, 0 ≤ H ∧ ∀ t x y, ‖l t x-l t y‖ ≤ H*‖x-y‖^γ) →
      ∃ u : ℝ → C₀(V,ℂ), u 0=d ∧ ContinuousOn u (Icc 0 T) ∧
        (∀ t ∈ Icc 0 T, ‖u t‖ ≤ K*(‖d‖+‖l‖)) ∧
        (∀ t ∈ Ioo 0 T, ContDiff ℝ 4 (fun x => u t x)) ∧
        (∀ t ∈ Ioo 0 T, ∀ n : ℕ, n ≤ 4 → ∃ M : ℝ, ∀ x,
          ‖iteratedFDeriv ℝ n (fun y => u t y) x‖ ≤ M) ∧
        (∀ (t : Time T), t.val < T → ∃ v : V →ᵇ ℂ,
          HasDerivAt (fun r => (u r).toBCF) v t.val ∧ ∀ x,
          v x=l t x-((A (now t) x).val : ℂ)*Δ (Δ (fun y => u t.val y)) x-b (now t) x*u t.val x) := by

  obtain ⟨C,D,hC,hD,hs⟩ := exists_parametrix_correction_full hα A b hT₀ hT L B hL hB hb hLip
  let M := frozenBound (V := V) (β := β) hα
  let Q := ∫ v : UnitTime, MildVolterra.massWeight v
  have hM : 0 ≤ M := frozenBound_nonneg hα
  have hQ : 0 ≤ Q := integral_nonneg MildVolterra.massWeight_nonneg
  refine ⟨M+Q*M*D*(1+C),by positivity,fun γ hγ hγ1 d l hl => ?_⟩
  obtain ⟨H,hH,hl⟩ := hl
  let η := min γ (1/4 : ℝ)
  have hη : 0 < η := lt_min hγ (by norm_num)
  have hηγ : η ≤ γ := min_le_left _ _
  have hηq : η ≤ 1/4 := min_le_right _ _
  have hη1 : η ≤ 1 := by linarith
  have hholdl : ∀ t x y, ‖l t x-l t y‖ ≤ (H+2*‖l‖)*‖x-y‖^η := by
    intro t x y
    by_cases hd : ‖x-y‖ ≤ 1
    · apply (hl t x y).trans
      apply mul_le_mul
      · exact le_add_of_nonneg_right (by positivity)
      · exact Real.rpow_le_rpow_of_exponent_ge' (norm_nonneg _) hd hη.le hηγ
      · exact Real.rpow_nonneg (norm_nonneg _) _
      · positivity
    · have h1 : 1 ≤ ‖x-y‖^η := Real.one_le_rpow (le_of_lt (lt_of_not_ge hd)) hη.le
      have hx : ‖l t x‖ ≤ ‖l‖ := ((l t).toBCF.norm_coe_le_norm x).trans (l.norm_coe_le_norm t)
      have hy : ‖l t y‖ ≤ ‖l‖ := ((l t).toBCF.norm_coe_le_norm y).trans (l.norm_coe_le_norm t)
      calc
        _ ≤ 2*‖l‖ := (norm_sub_le _ _).trans (by linarith)
        _ ≤ H+2*‖l‖ := le_add_of_nonneg_left hH
        _ ≤ _ := le_mul_of_one_le_right (by positivity) h1
  obtain ⟨j,hi,hj,hjb⟩ := hs d l
  obtain ⟨J,hJ,hholder⟩ := source_correction_holder hα A b hT₀ hT L B hL hB hb hLip hLipb
    η hη hηq d l j (H+2*‖l‖) (by positivity) hholdl hi hj
  refine ⟨mildTime hα A hT₀ d j,mildTime_zero hα A hT₀ d j,
    continuousOn_mildTime hα A hT₀ d j,fun t ht => ?_,fun t ht => ?_,fun t ht n hn => ?_,fun t ht => ?_⟩
  · have ht1 : t^(1/4 : ℝ) ≤ 1 := Real.rpow_le_one ht.1 (ht.2.trans hT) (by positivity)
    have h0 := norm_c0Time_le hα (A (initial hT₀)) t d
    have h1 := norm_duhamel_le hα A hT₀ j t ht
    have hjb' : ‖j‖ ≤ D*((1+C)*(‖d‖+‖l‖)) := hjb.trans
      (mul_le_mul_of_nonneg_left (by nlinarith [norm_nonneg l,norm_nonneg d]) hD.le)
    calc
      ‖mildTime hα A hT₀ d j t‖ ≤ M*‖d‖+t^(1/4 : ℝ)*(Q*M*‖j‖) :=
        (norm_add_le _ _).trans (add_le_add h0 h1)
      _ ≤ M*‖d‖+Q*M*‖j‖ := add_le_add le_rfl
        (mul_le_of_le_one_left (mul_nonneg (mul_nonneg hQ hM) (norm_nonneg j)) ht1)
      _ ≤ M*(‖d‖+‖l‖)+Q*M*(D*((1+C)*(‖d‖+‖l‖))) := add_le_add
        (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (norm_nonneg l)) hM)
        (mul_le_mul_of_nonneg_left hjb' (mul_nonneg hQ hM))
      _ = _ := by ring
  · exact contDiff_mildTime_of_holder_gamma hα A hT₀ η hη hη1 L hL hLip d j J hJ hholder ⟨t,ht.1,ht.2.le⟩
  · exact bounded_iteratedFDeriv_mildTime_gamma hα A hT₀ η hη hη1 L hL hLip j J hJ hholder d ⟨t,ht.1,ht.2.le⟩ n hn
  · refine ⟨(l t).toBCF+mildRHS hα A b hT₀ d j t,
      hasDerivAt_source_mildTime hα A b hT₀ η hη hη1 L hL hLip d j l J hJ hholder hi hj hA t ht,?_⟩
    intro x
    change l t x+(-(((A (now t) x).val : ℂ)*mildBilaplacian hα A hT₀ d j t x)-b (now t) x*mildTime hα A hT₀ d j t.val x) = _
    rw [mildBilaplacian_apply_gamma hα A hT₀ d j η hη hη1 L J hL hJ hLip hholder t x]
    ring
end ParametrixVolterra

end

end OAI
