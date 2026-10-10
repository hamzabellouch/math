import OAI.Analysis.AncientFlat.Geometry.InnerExtensionCore
import OAI.Analysis.AncientFlat.Weighted.ExactYNorm
import OAI.Analysis.AncientFlat.Weighted.WeightedSourceHolder

namespace OAI
noncomputable section
open Set Filter
open scoped ContDiff ENNReal
namespace FlatWeighted
open ParabolicInterior
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
def FiniteYBound (α w a T M : ℝ) (f : V × ℝ → ℂ) : Prop :=
  ∀ p : V × ℝ, -T≤p.2 ∧ p.2<0 → HolderBound α (finiteLocalDomain T a p) (pullback (w-4) p f) M
lemma finiteYNorm_bound {α w a T M : ℝ} {f : V × ℝ → ℂ} (hM : 0≤M)
    (h : finiteYNorm α w a T f≤ENNReal.ofReal M) : FiniteYBound α w a T M f := by
  intro p hp
  apply holderNorm_holderBound hM
  exact (le_iSup (fun P : {P : V × ℝ // -T≤P.2 ∧ P.2<0} =>
    holderNorm α (finiteLocalDomain T a P.val) (pullback (w-4) P.val f)) ⟨p,hp⟩).trans h
lemma finiteYNorm_finite_bound {α w a T : ℝ} {f : V × ℝ → ℂ}
    (h : finiteYNorm α w a T f≠⊤) : FiniteYBound α w a T (finiteYNorm α w a T f).toReal f :=
  finiteYNorm_bound ENNReal.toReal_nonneg (by rw [ENNReal.ofReal_toReal h])
lemma zero_finiteLocalDomain (T a : ℝ) (ha : 0<a) (p : V × ℝ) (hp : -T≤p.2 ∧ p.2<0) :
    (0:V × ℝ)∈finiteLocalDomain T a p := by
  simpa [finiteLocalDomain,chart] using And.intro ha (And.intro (show -a^4<0 from neg_neg_of_pos (pow_pos ha _))
    (And.intro (show (0:ℝ)<a^4 by positivity) hp))
variable [FiniteDimensional ℝ V]
lemma FiniteYBound.pointwise {α w a T M : ℝ} {f : V × ℝ → ℂ}
    (h : FiniteYBound α w a T M f) (ha : 0<a) (p : V × ℝ) (hp : -T≤p.2 ∧ p.2<0) :
    ‖f p‖≤M*sigma p^(w-4) := by
  have hs := sigma_pos p hp.2
  have hb := (h p hp).1 0 (zero_finiteLocalDomain T a ha p hp)
  simp only [pullback,chart_zero,norm_smul,Real.norm_eq_abs,
    Real.rpow_neg hs.le,abs_inv,abs_of_pos (Real.rpow_pos_of_pos hs (w-4))] at hb
  exact (inv_mul_le_iff₀ (Real.rpow_pos_of_pos hs _)).mp hb |>.trans_eq (mul_comm _ _)
lemma unchart_mem_finite {a T : ℝ} (ha : 0<a) (p q : V × ℝ)
    (hp : -T≤p.2 ∧ p.2<0) (hq : -T≤q.2 ∧ q.2<0)
    (hd : pdist p q<a*sigma p) : unchart p q∈finiteLocalDomain T a p := by
  obtain ⟨hx,ht1,ht2,ht3⟩ := unchart_mem_of_near ha p q hp.2 hq.2 hd
  exact ⟨hx,ht1,ht2,by simpa only [chart_unchart p q hp.2] using hq.1,ht3⟩

lemma FiniteYBound.holder_on {α w a M b T : ℝ} {f : V × ℝ → ℂ} {Ω : Set (V × ℝ)}
    (h : FiniteYBound α w a T M f) (hα : 0≤α) (hw : w≤4) (ha : 0<a) (hM : 0≤M) (hb : 0<b)
    (ht : ∀ p∈Ω, -T≤p.2 ∧ p.2<0) (hs : ∀ p∈Ω, b≤ sigma p) :
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
  have hp0 := (ht p hp).2
  have hq0 := (ht q hq).2
  have hr : 0≤pdist p q^α := Real.rpow_nonneg (pdist_nonneg _ _) _
  by_cases hd : pdist p q<a*b
  · have hnear : pdist p q<a*sigma p := hd.trans_le (mul_le_mul_of_nonneg_left (hs p hp) ha.le)
    have hq' := unchart_mem_finite ha p q (ht p hp) (ht q hq) hnear
    have hpb := (h p (ht p hp)).2 0 (zero_finiteLocalDomain T a ha p (ht p hp)) (unchart p q) hq'
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
