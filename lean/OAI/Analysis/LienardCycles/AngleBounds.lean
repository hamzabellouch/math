import OAI.Analysis.LienardCycles.MonotoneIntegral

namespace OAI

open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open scoped Topology
open Set Filter Metric
open Set Filter
open scoped Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology ENNReal

open Set Filter MeasureTheory
open scoped Topology
namespace QuinticLienard.RealAnalysis
lemma rate_inverse_identity {s a : ℝ} (hs : 0 < s) (ha : |a|<1) :
    1/(1-a)=s*(2*a/(s*(1-a^2)))+1/(1+a) := by
  have ha' := abs_lt.mp ha
  have h₁ : 1-a ≠ 0 := by linarith
  have h₂ : 1+a ≠ 0 := by linarith
  have h₃ : 1-a^2 ≠ 0 := by nlinarith [mul_pos (show 0 < 1-a by linarith) (show 0 < 1+a by linarith)]
  field_simp [ne_of_gt hs,h₁,h₂,h₃]
  ring
lemma bddAbove_angle_of_rate {s : ℝ} (hs : 0 < s) {u : ℕ → ℝ}
    (hu : ∀ n, |u n|<1) (hm : Monotone u)
    (hB : BddAbove (range (fun n => 2*u n/(s*(1-(u n)^2))))) :
    BddAbove (range (fun n => angle (u n))) := by
  obtain ⟨B,hB⟩ := hB
  let C := s*max B 0+1/(1+u 0)+1
  have hlow : 0 < 1+u 0 := by linarith [(abs_lt.mp (hu 0)).1]
  have hC : 1 < C := by
    dsimp only [C]
    have := mul_nonneg hs.le (le_max_right B 0)
    linarith [one_div_pos.mpr hlow]
  have ht : 1-1/C ∈ Ioo (-1:ℝ) 1 := by
    have h₁ := one_div_pos.mpr (show 0 < C by linarith)
    have h₂ := one_div_lt_one_div_of_lt (by norm_num : (0:ℝ)<1) hC
    norm_num only [div_one] at h₂
    constructor <;> linarith
  refine ⟨angle (1-1/C),?_⟩
  rintro y ⟨n,rfl⟩
  apply angle_strictMono.monotoneOn (abs_lt.mp (hu n)) ht
  have hrange := hB (mem_range_self n)
  have hi := one_div_le_one_div_of_le hlow (show 1+u 0 ≤ 1+u n by linarith [hm (Nat.zero_le n)])
  have hc : 1/(1-u n) ≤ C := by
    rw [rate_inverse_identity hs (hu n)]
    have hmul := mul_le_mul_of_nonneg_left (hrange.trans (le_max_left B 0)) hs.le
    dsimp only [C]
    linarith
  have hden : 0 < 1-u n := by linarith [(abs_lt.mp (hu n)).2]
  have hc' : 1/C ≤ 1-u n := by
    have hprod := (div_le_iff₀ hden).mp hc
    apply (div_le_iff₀ (show 0 < C by linarith)).mpr
    nlinarith
  linarith

lemma exists_mem_Ioo_of_ae {l u a b : ℝ} {p : ℝ → Prop}
    (hab : a < b) (hsub : Ioo a b ⊆ Ioc l u)
    (hp : ∀ᵐ s ∂volume.restrict (Ioc l u), p s) : ∃ s ∈ Ioo a b, p s := by
  apply Measure.exists_mem_of_measure_ne_zero_of_ae
    (show volume (Ioo a b) ≠ 0 by rw [Real.volume_Ioo]; exact ne_of_gt (ENNReal.ofReal_pos.mpr (sub_pos.mpr hab)))
  exact hp.filter_mono (ae_mono (Measure.restrict_mono hsub le_rfl))

lemma uniform_integral_pos_of_reciprocal {a b B : ℝ} (hab : a < b) {g : ℕ → ℝ → ℝ}
    (hg : ∀ n, ContinuousOn (g n) (Icc a b))
    (hp : ∀ n x, x ∈ Icc a b → 0 < g n x)
    (hB : ∀ n, (∫ x in a..b, 1/(g n x)) ≤ B) :
    ∃ ε > 0, ∀ n, ε ≤ ∫ x in a..b, g n x := by
  have hi (n : ℕ) : IntervalIntegrable (fun x => 1/(g n x)) volume a b :=
    (continuousOn_const.div (hg n) (fun x hx => ne_of_gt (hp n x hx))).intervalIntegrable_of_Icc hab.le
  have hB0 : 0 ≤ B := (intervalIntegral.integral_nonneg hab.le
    (fun x hx => le_of_lt (one_div_pos.mpr (hp 0 x hx)))).trans (hB 0)
  let δ := (b-a)/(B+1)
  have hδ : 0 < δ := div_pos (sub_pos.mpr hab) (by linarith)
  have hδB : δ*B ≤ b-a := by
    have he : δ*(B+1)=b-a := by dsimp only [δ]; field_simp
    nlinarith
  refine ⟨δ*(b-a),mul_pos hδ (sub_pos.mpr hab),?_⟩
  intro n
  have hpoint (x : ℝ) (hx : x ∈ Icc a b) : 2*δ ≤ g n x+δ^2*(1/g n x) := by
    apply (mul_le_mul_iff_left₀ (hp n x hx)).mp
    have he : (g n x+δ^2*(1/g n x))*g n x=(g n x)^2+δ^2 := by
      field_simp [ne_of_gt (hp n x hx)]
    rw [he]
    nlinarith [sq_nonneg (g n x-δ)]
  have hineq := intervalIntegral.integral_mono_on hab.le intervalIntegrable_const
    (((hg n).intervalIntegrable_of_Icc hab.le).add ((hi n).const_mul (δ^2))) hpoint
  rw [intervalIntegral.integral_const,intervalIntegral.integral_add
    ((hg n).intervalIntegrable_of_Icc hab.le) ((hi n).const_mul (δ^2)),intervalIntegral.integral_const_mul] at hineq
  simp only [smul_eq_mul] at hineq
  have hbound := mul_le_mul_of_nonneg_left (hB n) (sq_nonneg δ)
  have hbound' := mul_le_mul_of_nonneg_left hδB hδ.le
  nlinarith
end QuinticLienard.RealAnalysis

end OAI
