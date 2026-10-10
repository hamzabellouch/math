import OAI.Analysis.AncientFlat.Evolution.SpaceRescaling
import OAI.Analysis.AncientFlat.Regularity.FrozenSchauder

namespace OAI
noncomputable section
open Set Filter
open scoped ContDiff ZeroAtInfty BoundedContinuousFunction Laplacian
namespace ParabolicSchauder
open ParametrixEvolution ParametrixDilation ParabolicInterior
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
lemma pdist_space_contract (r : ℝ) (hr : 1≤r) (p q : V × ℝ) :
    pdist (r⁻¹ • p.1,p.2) (r⁻¹ • q.1,q.2)≤pdist p q := by
  have hpos : 0<r := lt_of_lt_of_le zero_lt_one hr
  unfold pdist
  simp only [←smul_sub,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hpos.le)]
  have hi : r⁻¹≤1 := (inv_le_one₀ hpos).mpr hr
  nlinarith [norm_nonneg (p.1-q.1)]
omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
lemma fourth_space_recover (r : ℝ) (hr : 1≤r) (u : ℝ → C₀(V,ℂ))
    (S : Set ℝ) (hs : ∀ t∈S, ContDiff ℝ 4 (fun x => u t x))
    (α B : ℝ) (hα : 0≤α) (hB : 0≤B)
    (he : HolderBound α {p : V × ℝ | p.2∈S}
      (fun p => iteratedFDeriv ℝ 4 (fun x => u p.2 (r • x)) p.1) B) :
    HolderBound α {p : V × ℝ | p.2∈S}
      (fun p => iteratedFDeriv ℝ 4 (fun x => u p.2 x) p.1) B := by
  have hpos : 0<r := lt_of_lt_of_le zero_lt_one hr
  have hr4 : 1≤r^4 := one_le_pow₀ hr
  have hjet (p : V × ℝ) (hp : p.2∈S) :
      iteratedFDeriv ℝ 4 (fun x => u p.2 (r • x)) (r⁻¹ • p.1)=
      r^4 • iteratedFDeriv ℝ 4 (fun x => u p.2 x) p.1 := by
    rw [iteratedFDeriv_scale r _ (hs p.2 hp) 4 le_rfl]
    simp [smul_smul,hpos.ne']
  refine ⟨?_,?_⟩
  · intro p hp
    have hh := he.1 (r⁻¹ • p.1,p.2) hp
    dsimp only at hh
    rw [hjet p hp,norm_smul,Real.norm_of_nonneg (pow_nonneg hpos.le 4)] at hh
    exact (le_mul_of_one_le_left (norm_nonneg _) hr4).trans hh
  · intro p hp q hq
    have hh := he.2 (r⁻¹ • p.1,p.2) hp (r⁻¹ • q.1,q.2) hq
    dsimp only at hh
    rw [hjet p hp,hjet q hq,←smul_sub,norm_smul,Real.norm_of_nonneg (pow_nonneg hpos.le 4)] at hh
    apply (le_mul_of_one_le_left (norm_nonneg _) hr4).trans (hh.trans _)
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (pdist_nonneg _ _) (pdist_space_contract r hr p q) hα) hB

theorem frozen_fourth_estimate_two (α κ K : ℝ) (hα : 0<α) (hα1 : α<1)
    (hκ : 0<κ) (hK : 0≤K) :
    ∃ C : ℝ, 0<C ∧ ∀ (c T : ℝ), κ≤c → c≤K → 0<T → T≤2 →
      ∀ (f : ℝ →ᵇ C₀(V,ℂ)) (F : ℝ), 0≤F →
      (∀ t∈Icc 0 T, ∀ x y, ‖f t x-f t y‖≤F*‖x-y‖^α) →
      ∀ (u : ℝ → C₀(V,ℂ)), (∀ t∈Icc 0 T, ContDiff ℝ 4 (fun x => u t x)) →
      SourceEvolves (coefficientLine c) 0 f 0 T 0 u →
      HolderBound α {p : V × ℝ | p.2∈Icc 0 T}
        (fun p => iteratedFDeriv ℝ 4 (fun x => u p.2 x) p.1) (C*F) := by
  let r : ℝ := 2*(K+1)
  have hr1 : 1≤r := by dsimp [r]; linarith
  have hr : 0<r := lt_of_lt_of_le zero_lt_one hr1
  have hr2 : r≤r^2 := by nlinarith
  have hr4 : r≤r^4 := by nlinarith [sq_nonneg (r^2-1)]
  have hKr4 : 2*K≤r^4 := by dsimp [r] at hr4 ⊢; nlinarith
  obtain ⟨C,hC,hest⟩ := frozen_fourth_estimate (V := V) α (κ/r^4) (K/r^4)
    hα hα1 (by positivity) (by positivity)
  refine ⟨C*r^α,by positivity,?_⟩
  intro c T hκc hcK hT hT2 f F hF hf u hs hu
  have hc : 0<c := hκ.trans_le hκc
  have hct : (c/r^4)*T≤1 := by
    rw [div_mul_eq_mul_div,(div_le_one (by positivity : 0<r^4))]
    calc
      c*T≤K*2 := mul_le_mul hcK hT2 hT.le hK
      _≤r^4 := by simpa only [mul_comm] using hKr4
  have he := hest (c/r^4) T (by gcongr) (by gcongr) hT hct
    (spaceSource r hr.ne' f) (F*r^α) (by positivity) (spaceSource_holder hr f hf)
    (fun t => scaleSpace r hr.ne' (u t)) (space_source_evolves hr.ne' f u hu)
  have he' := fourth_space_recover r hr1 u (Icc 0 T) hs α (C*(F*r^α)) hα.le (by positivity) he
  convert he' using 1; ring
end ParabolicSchauder

end

end OAI
