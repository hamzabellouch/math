import OAI.Analysis.AncientFlat.Evolution.TimeRescaling
import OAI.Analysis.AncientFlat.Regularity.ConstantSchauder

namespace OAI
noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff ZeroAtInfty BoundedContinuousFunction Laplacian
namespace ParabolicSchauder
open ParametrixEvolution ParabolicInterior
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
lemma pdist_time_scale_le (c K : ℝ) (hc : 0<c) (hcK : c≤K) (p q : V × ℝ) :
    pdist (p.1,c*p.2) (q.1,c*q.2) ≤ (1+K)*pdist p q := by
  have hK : 0≤K := hc.le.trans hcK
  have hcroot : c^((1:ℝ)/4)≤1+K := by
    by_cases h : c≤1
    · have h1 : c^((1:ℝ)/4)≤1 := Real.rpow_le_one hc.le h (by norm_num)
      linarith
    · have h1 : c^((1:ℝ)/4)≤c := Real.rpow_le_self_of_one_le (le_of_not_ge h) (by norm_num)
      linarith
  unfold pdist
  rw [←mul_sub,abs_mul,abs_of_pos hc,Real.mul_rpow hc.le (abs_nonneg _)]
  nlinarith [mul_nonneg hK (norm_nonneg (p.1-q.1)),Real.rpow_nonneg (abs_nonneg (p.2-q.2)) ((1:ℝ)/4)]
theorem frozen_fourth_estimate (α κ K : ℝ) (hα : 0<α) (hα1 : α<1)
    (hκ : 0<κ) (hK : 0≤K) :
    ∃ C : ℝ, 0<C ∧ ∀ (c T : ℝ), κ≤c → c≤K → 0<T → c*T≤1 →
      ∀ (f : ℝ →ᵇ C₀(V,ℂ)) (F : ℝ), 0≤F →
      (∀ t∈Icc 0 T, ∀ x y, ‖f t x-f t y‖≤F*‖x-y‖^α) →
      ∀ (u : ℝ → C₀(V,ℂ)), SourceEvolves (coefficientLine c) 0 f 0 T 0 u →
      HolderBound α {p : V × ℝ | p.2∈Icc 0 T}
        (fun p => iteratedFDeriv ℝ 4 (fun x => u p.2 x) p.1) (C*F) := by
  obtain ⟨C,hC,hest⟩ := constant_fourth_estimate (V := V) α hα hα1
  refine ⟨C*(1+K)/κ,by positivity,?_⟩
  intro c T hκc hcK hT hcT f F hF hf u hu
  have hc : 0<c := hκ.trans_le hκc
  have hv := rescale_source_evolves hc f u hu
  have he := hest (c*T) (mul_pos hc hT) hcT (rescaledSource c f) (F/c)
    (div_nonneg hF hc.le) (rescaledSource_holder hc f hf) (fun t => u (t/c)) hv
  have hfC : C*(F/c)≤(C*(1+K)/κ)*F := by
    calc
      _≤C*(F/κ) := by gcongr
      _≤(C*(1+K)/κ)*F := by
        have := mul_nonneg (mul_nonneg hC.le hF) hK
        field_simp
        nlinarith
  have hp (p : V × ℝ) (hp : p.2∈Icc 0 T) : (c*p.2)∈Icc 0 (c*T) :=
    ⟨mul_nonneg hc.le hp.1,mul_le_mul_of_nonneg_left hp.2 hc.le⟩
  have hrpow : (1+K)^α≤1+K := Real.rpow_le_self_of_one_le (by linarith) hα1.le
  refine ⟨?_,?_⟩
  · intro p hpp
    have hh := he.1 (p.1,c*p.2) (hp p hpp)
    simpa only [mul_div_cancel_left₀ _ hc.ne'] using hh.trans hfC
  · intro p hpp q hqq
    have hh := he.2 (p.1,c*p.2) (hp p hpp) (q.1,c*q.2) (hp q hqq)
    simp only [mul_div_cancel_left₀ _ hc.ne'] at hh
    apply hh.trans
    have hd := Real.rpow_le_rpow (pdist_nonneg (p.1,c*p.2) (q.1,c*q.2))
      (pdist_time_scale_le c K hc hcK p q) hα.le
    rw [Real.mul_rpow (by linarith : 0≤1+K) (pdist_nonneg p q)] at hd
    have hcoef : C*(F/c)*(1+K)^α≤(C*(1+K)/κ)*F := by
      calc
        _≤C*(F/c)*(1+K) := by gcongr
        _≤C*(F/κ)*(1+K) := by gcongr
        _=_ := by ring
    calc
      _≤C*(F/c)*((1+K)^α*pdist p q^α) := mul_le_mul_of_nonneg_left hd (by positivity)
      _=(C*(F/c)*(1+K)^α)*pdist p q^α := by ring
      _≤_ := mul_le_mul_of_nonneg_right hcoef (Real.rpow_nonneg (pdist_nonneg p q) α)
end ParabolicSchauder

end

end OAI
