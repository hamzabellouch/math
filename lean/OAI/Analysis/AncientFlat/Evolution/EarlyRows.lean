import OAI.Analysis.AncientFlat.Evolution.EarlyIntegral

namespace OAI
noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff BoundedContinuousFunction SchwartzMap
namespace SourceFrozenRows
open VariableSchauder
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
lemma early_fourth_holder (K : SchwartzMap V ℂ)
    (A : ℝ → V → ℝ) (hA : Continuous (Function.uncurry A))
    (α β γ L σ p M H T a b : ℝ) (hα : 0<α) (hγ : 0<γ) (hγ1 : γ<1) (hL : 0≤L)
    (hAr : ∀ t y, A t y∈Icc α β) (hAL : ∀ t x y, ‖A t x-A t y‖≤L*‖x-y‖)
    (hσ : σ<1) (hp : p<1) (hM : 0≤M) (hH : 0≤H) (hT : T≤1)
    (f : ℝ → (V →ᵇ ℂ)) (hf : StronglyMeasurable f)
    (hm : ∀ t∈Ioo 0 T, ‖f t‖≤M*t^(-σ))
    (hh : ∀ t∈Ioo 0 T, ∀ x y, ‖f t x-f t y‖≤H*t^(-p)*‖x-y‖^γ)
    (hb : 0<b) (hba : 2*b≤a) (haT : a≤T) :
    ∃ C : ℝ, 0≤C ∧
      (∀ t∈Icc a T, ∀ x, ‖∫ r in Ioo 0 b, jet K (A r) (t-r) (f r) 4 x‖≤C) ∧
      (∀ t∈Icc a T, ∀ s∈Icc a T, ∀ x y,
        ‖(∫ r in Ioo 0 b,jet K (A r) (t-r) (f r) 4 x)-
          (∫ r in Ioo 0 b,jet K (A r) (s-r) (f r) 4 y)‖≤C*(‖x-y‖^γ+|t-s|^(γ/4))) := by
  have ha : 0<a := by linarith
  have hbT : b<T := by linarith
  let w := fun r : ℝ => H*r^(-p)+M*r^(-σ)
  have hw₀ (r) (hr : r∈Ioo 0 b) : 0≤w r := by
    have hr0 := hr.1.le
    dsimp [w]; positivity
  have hiw (q : ℝ) (hq : q<1) : IntegrableOn (fun r : ℝ => r^(-q)) (Ioo 0 b) := by
    have he := (intervalIntegrable_iff_integrableOn_Ioo_of_le hb.le).mp
      (BetaWeights.intervalIntegrable q 0 hq (by norm_num) b hb)
    have heq : BetaWeights.density q 0 b = fun r => r^(-q) := by
      funext r; simp [BetaWeights.density]
    rwa [heq] at he
  have hw : IntegrableOn w (Ioo 0 b) := ((hiw p hp).const_mul H).add ((hiw σ hσ).const_mul M)
  have hi (t) (ht : t∈Icc a T) (x : V) :
      IntegrableOn (fun r => jet K (A r) (t-r) (f r) 4 x) (Ioo 0 b) := by
    have hh' := WeightedSourceFrozenRows.integrableOn_row K A hA α β hα hAr L hL hAL f hf σ p M H γ t hσ hp hM hH (ha.trans_le ht.1) hγ hγ1.le
      (fun r hr => hm r ⟨hr.1,hr.2.trans_le ht.2⟩)
      (fun r hr => hh r ⟨hr.1,hr.2.trans_le ht.2⟩) 4 le_rfl x
    exact hh'.mono_set (fun r hr => ⟨hr.1,by linarith [hr.2,ht.1]⟩)
  obtain ⟨B,hB,hbound⟩ := exists_jet_bound K 4 (by norm_num) α β γ L hα hγ.le hγ1.le hL
  obtain ⟨D,hD,hspace⟩ := exists_jet_lipschitz K 4 α β γ L hα hγ.le hγ1.le hL
  obtain ⟨E₀,hE,htime⟩ := exists_jet_time_increment K 4 (by norm_num) α β γ L hα
    ((hAr 0 0).1.trans (hAr 0 0).2) hγ.le hγ1.le hL
  have hAs (r : ℝ) : Continuous (A r) := hA.comp (continuous_const.prodMk continuous_id)
  have hlag (t) (ht : t∈Icc a T) (r) (hr : r∈Ioo 0 b) : b≤t-r ∧ t-r≤1 := by constructor <;> linarith [ht.1,ht.2,hr.1,hr.2]
  apply EarlyIntegral.holder_of_bounds (fun t r x => jet K (A r) (t-r) (f r) 4 x) a b T γ ha hb hγ hγ1 w hw hw₀
    (B*b^((γ-4)/4)) (D*b^((γ-5)/4)) (E₀*b^((γ-8)/4))
    (by positivity) (by positivity) (by positivity) hi
  · intro t ht r hr x
    have hrT : r∈Ioo 0 T := ⟨hr.1,hr.2.trans hbT⟩
    have hr0 := hr.1.le
    have he := hbound (A r) (hAs r) (hAr r) (hAL r) (f r) (H*r^(-p)) (M*r^(-σ))
      (by positivity) (by positivity) (hm r hrT) (hh r hrT) (t-r) (hb.trans_le (hlag t ht r hr).1) (hlag t ht r hr).2 x
    norm_num only [Nat.cast_ofNat] at he
    calc
      _ ≤ B*w r*(t-r)^((γ-4)/4) := he
      _ ≤ B*w r*b^((γ-4)/4) := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos hb (hlag t ht r hr).1 (by linarith)) (mul_nonneg hB (hw₀ r hr))
      _ = _ := by ring
  · intro t ht r hr x y
    have hrT : r∈Ioo 0 T := ⟨hr.1,hr.2.trans hbT⟩
    have hr0 := hr.1.le
    have he := hspace (A r) (hAs r) (hAr r) (hAL r) (f r) (H*r^(-p)) (M*r^(-σ))
      (by positivity) (by positivity) (hm r hrT) (hh r hrT) (t-r) (hb.trans_le (hlag t ht r hr).1) (hlag t ht r hr).2 x y
    norm_num only [Nat.cast_ofNat] at he
    calc
      _ ≤ D*w r*(t-r)^((γ-5)/4)*‖x-y‖ := by convert he using 1
      _ ≤ D*w r*b^((γ-5)/4)*‖x-y‖ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos hb (hlag t ht r hr).1 (by linarith))
        (mul_nonneg hD (hw₀ r hr))) (norm_nonneg _)
      _ = _ := by ring
  · intro s hs t ht hst he r hr x
    have hrT : r∈Ioo 0 T := ⟨hr.1,hr.2.trans hbT⟩
    have hr0 := hr.1.le
    have hi' := htime (A r) (hAs r) (hAr r) (hAL r) (f r) (H*r^(-p)) (M*r^(-σ))
      (by positivity) (by positivity) (hm r hrT) (hh r hrT) (s-r) (t-s)
      (hb.trans_le (hlag s hs r hr).1) (hlag s hs r hr).2 (sub_nonneg.mpr hst)
      (he.trans (hlag s hs r hr).1) x
    rw [show s-r+(t-s)=t-r by ring] at hi'
    norm_num only [Nat.cast_ofNat] at hi'
    calc
      _ ≤ E₀*w r*(t-s)*(s-r)^((γ-8)/4) := by convert hi' using 1; congr 2; ring
      _ ≤ E₀*w r*(t-s)*b^((γ-8)/4) := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos hb (hlag s hs r hr).1 (by linarith)) (mul_nonneg (mul_nonneg hE (hw₀ r hr)) (sub_nonneg.mpr hst))
      _ = _ := by ring
end SourceFrozenRows

end

end OAI
