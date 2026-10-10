import OAI.Analysis.AncientFlat.Weighted.WeightedScaling

namespace OAI
noncomputable section
open Set Filter
open scoped ContDiff
namespace FlatWeighted
open ParabolicInterior
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
lemma source_unscale (w : ℝ) (p q : V × ℝ) (hp : p.2<0) (f : V × ℝ → ℂ) :
    f q=sigma p^(w-4) • pullback (w-4) p f (unchart p q) := by
  simp only [pullback,chart_unchart p q hp,smul_smul,Real.rpow_neg (sigma_pos p hp).le]
  rw [mul_inv_cancel₀ (Real.rpow_pos_of_pos (sigma_pos p hp) _).ne',one_smul]

lemma YBound.holder_on {α w a M b : ℝ} {f : V × ℝ → ℂ} {Ω : Set (V × ℝ)}
    (h : YBound α w a M f) (hα : 0≤α) (hw : w≤4) (ha : 0<a) (hM : 0≤M) (hb : 0<b)
    (ht : ∀ p∈Ω, p.2<0) (hs : ∀ p∈Ω, b≤ sigma p) :
    HolderBound α Ω f ((b^(w-4)+b^(w-4)*b^(-α)+2*b^(w-4)/(a*b)^α)*M) := by
  let C := b^(w-4)+b^(w-4)*b^(-α)+2*b^(w-4)/(a*b)^α
  have hC0 : 0≤C := by dsimp [C]; positivity
  have hC1 : b^(w-4)≤C := by dsimp [C]; linarith [Real.rpow_nonneg hb.le (w-4),Real.rpow_nonneg hb.le (-α), show 0≤2*b^(w-4)/(a*b)^α by positivity,show 0≤b^(w-4)*b^(-α) by positivity]
  have hC2 : b^(w-4)*b^(-α)≤C := by dsimp [C]; linarith [Real.rpow_nonneg hb.le (w-4),show 0≤2*b^(w-4)/(a*b)^α by positivity]
  have hC3 : 2*b^(w-4)/(a*b)^α≤C := by dsimp [C]; linarith [Real.rpow_nonneg hb.le (w-4),show 0≤b^(w-4)*b^(-α) by positivity]
  have hpoint (p) (hp : p∈Ω) : ‖f p‖≤b^(w-4)*M := by
    exact (h.pointwise ha p (ht p hp)).trans
      ((mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hb (hs p hp) (by linarith)) hM).trans_eq (mul_comm _ _))
  refine ⟨fun p hp => (hpoint p hp).trans (mul_le_mul_of_nonneg_right hC1 hM),?_⟩
  intro p hp q hq
  have hp0 := ht p hp
  have hq0 := ht q hq
  have hr : 0≤pdist p q^α := Real.rpow_nonneg (pdist_nonneg _ _) _
  by_cases hd : pdist p q<a*b
  · have hnear : pdist p q<a*sigma p := hd.trans_le (mul_le_mul_of_nonneg_left (hs p hp) ha.le)
    have hq' := unchart_mem_of_near ha p q hp0 hq0 hnear
    have hpb := (h p hp0).2 0 (zero_localDomain a ha p hp0) (unchart p q) hq'
    rw [pdist_unchart p q hp0] at hpb
    have he : f p=sigma p^(w-4) • pullback (w-4) p f 0 := by
      simpa only [unchart_self] using source_unscale w p p hp0 f
    rw [he,source_unscale w p q hp0 f,←smul_sub,norm_smul,Real.norm_eq_abs,
      abs_of_pos (Real.rpow_pos_of_pos (sigma_pos p hp0) _)]
    have hsig : sigma p^(w-4)≤b^(w-4) := Real.rpow_le_rpow_of_nonpos hb (hs p hp) (by linarith)
    have hinv : (sigma p)^(-α)≤b^(-α) := Real.rpow_le_rpow_of_nonpos hb (hs p hp) (by linarith)
    have hpow : (pdist p q/sigma p)^α=pdist p q^α*(sigma p)^(-α) := by
      rw [Real.div_rpow (pdist_nonneg _ _) (sigma_pos p hp0).le,div_eq_mul_inv,
        Real.rpow_neg (sigma_pos p hp0).le]
    rw [hpow] at hpb
    calc
      _ ≤ sigma p^(w-4)*(M*(pdist p q^α*(sigma p)^(-α))) :=
        mul_le_mul_of_nonneg_left hpb (Real.rpow_pos_of_pos (sigma_pos p hp0) _).le
      _ = (sigma p^(w-4)*(sigma p)^(-α))*M*pdist p q^α := by ring
      _ ≤ (b^(w-4)*b^(-α))*M*pdist p q^α :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (mul_le_mul hsig hinv (Real.rpow_nonneg (sigma_pos p hp0).le _) (Real.rpow_nonneg hb.le _)) hM) hr
      _ ≤ C*M*pdist p q^α := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC2 hM) hr
  · have hab : (a*b)^α≤pdist p q^α := Real.rpow_le_rpow (by positivity) (not_lt.mp hd) hα
    have habp : 0<(a*b)^α := Real.rpow_pos_of_pos (mul_pos ha hb) _
    have hh : 2*b^(w-4)≤(2*b^(w-4)/(a*b)^α)*pdist p q^α := by
      calc
        _ = (2*b^(w-4)/(a*b)^α)*(a*b)^α := (div_mul_cancel₀ _ habp.ne').symm
        _ ≤ _ := mul_le_mul_of_nonneg_left hab (by positivity)
    calc
      _ ≤ ‖f p‖+‖f q‖ := norm_sub_le _ _
      _ ≤ b^(w-4)*M+b^(w-4)*M := add_le_add (hpoint p hp) (hpoint q hq)
      _ = (2*b^(w-4))*M := by ring
      _ ≤ ((2*b^(w-4)/(a*b)^α)*pdist p q^α)*M := mul_le_mul_of_nonneg_right hh hM
      _ ≤ C*M*pdist p q^α := by nlinarith [mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC3 hr) hM]
end FlatWeighted

end

end OAI
