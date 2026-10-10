import OAI.Analysis.AncientFlat.Weighted.WeightedLocalCore
import OAI.Analysis.AncientFlat.Regularity.HolderContinuity

namespace OAI
noncomputable section
open Set Filter Topology
open scoped ContDiff ZeroAtInfty BoundedContinuousFunction ENNReal
namespace FlatWeighted
open ParabolicInterior
variable {V : Type} [NormedAddCommGroup V]
lemma sigma_pos [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (p : V × ℝ) (hp : p.2<0) : 0<sigma p := by
  unfold sigma
  exact Real.sqrt_pos.2 (add_pos_of_nonneg_of_pos (sq_nonneg _) (Real.sqrt_pos.2 (neg_pos.2 hp)))
variable [InnerProductSpace ℝ V]
lemma chart_zero [FiniteDimensional ℝ V] (p : V × ℝ) : chart p 0=p := by simp [chart]
lemma zero_localDomain [FiniteDimensional ℝ V] (a : ℝ) (ha : 0<a) (p : V × ℝ) (hp : p.2<0) :
    (0:V × ℝ)∈localDomain a p := by
  simpa [localDomain,chart] using And.intro ha (And.intro (show -a^4<0 from neg_neg_of_pos (pow_pos ha _))
    (And.intro (show (0:ℝ)<a^4 by positivity) hp))
lemma continuous_chart [FiniteDimensional ℝ V] (p : V × ℝ) : Continuous (chart p) := by
  unfold chart; fun_prop
section
variable [FiniteDimensional ℝ V]
lemma isOpen_localDomain (a : ℝ) (p : V × ℝ) : IsOpen (localDomain a p) := by
  change IsOpen ({q : V × ℝ | ‖q.1‖<a} ∩ ({q | -a^4<q.2} ∩
    ({q | q.2<a^4} ∩ {q | (chart p q).2<0})))
  exact (isOpen_lt continuous_fst.norm continuous_const).inter
    ((isOpen_lt continuous_const continuous_snd).inter
      ((isOpen_lt continuous_snd continuous_const).inter
        (isOpen_lt (continuous_chart p).snd continuous_const)))
lemma YBound.pointwise {α w a M : ℝ} {f : V × ℝ → ℂ}
    (h : YBound α w a M f) (ha : 0<a) (p : V × ℝ) (hp : p.2<0) :
    ‖f p‖≤M*sigma p^(w-4) := by
  have hs := sigma_pos p hp
  have hb := (h p hp).1 0 (zero_localDomain a ha p hp)
  simp only [pullback,chart_zero,norm_smul,Real.norm_eq_abs,
    Real.rpow_neg hs.le,abs_inv,abs_of_pos (Real.rpow_pos_of_pos hs (w-4))] at hb
  exact (inv_mul_le_iff₀ (Real.rpow_pos_of_pos hs _)).mp hb |>.trans_eq (mul_comm _ _)
def unchart (p q : V × ℝ) : V × ℝ :=
  ((sigma p)⁻¹ • (q.1-p.1),(q.2-p.2)/(sigma p)^4)
end
lemma continuous_unchart [FiniteDimensional ℝ V] (p : V × ℝ) : Continuous (unchart p) := by
  unfold unchart; fun_prop
lemma unchart_self [FiniteDimensional ℝ V] (p : V × ℝ) : unchart p p=0 := by simp [unchart]
variable [FiniteDimensional ℝ V]
lemma chart_unchart (p q : V × ℝ) (hp : p.2<0) : chart p (unchart p q)=q := by
  have hs : sigma p≠0 := (sigma_pos p hp).ne'
  ext <;> simp [chart,unchart,smul_smul,hs,mul_div_cancel₀]
lemma YBound.continuousOn {α w a M : ℝ} {f : V × ℝ → ℂ}
    (h : YBound α w a M f) (hα : 0<α) (ha : 0<a) :
    ContinuousOn f {p | p.2<0} := by
  intro p hp
  have hs := sigma_pos p hp
  have h0 := zero_localDomain a ha p hp
  have hc := (h p hp).continuousOn hα
  have hcont : ContinuousAt (pullback (w-4) p f) 0 := hc.continuousAt
    ((isOpen_localDomain a p).mem_nhds h0)
  have he : f=fun q => sigma p^(w-4) • pullback (w-4) p f (unchart p q) := by
    funext q
    simp only [pullback,chart_unchart p q hp,smul_smul,Real.rpow_neg hs.le]
    simp [(Real.rpow_pos_of_pos hs (w-4)).ne']
  rw [he]
  have hc' : ContinuousAt (pullback (w-4) p f) (unchart p p) := by
    simpa only [unchart_self] using hcont
  exact ((show ContinuousAt (fun _ : V × ℝ => sigma p^(w-4)) p from continuousAt_const).smul
    (hc'.comp (continuous_unchart p).continuousAt)).continuousWithinAt
end FlatWeighted

end

end OAI
