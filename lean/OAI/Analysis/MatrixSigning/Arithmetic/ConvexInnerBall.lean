import Mathlib

namespace OAI

open Matrix

namespace CurrentKS.RationalOptimization
noncomputable section
open Set
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma convex_innerBall (K : Set E) (hK : Convex ℝ K) (z c : E) (hz : z ∈ K)
    {r a : ℝ} (hball : Metric.closedBall c r ⊆ K) (ha : 0 < a) (ha1 : a ≤ 1) :
    Metric.closedBall ((1-a) • z+a • c) (a*r) ⊆ K := by
  intro y hy
  let e := y-((1-a) • z+a • c)
  have he : ‖e‖ ≤ a*r := by simpa only [Metric.mem_closedBall,dist_eq_norm] using hy
  have hu : c+a⁻¹ • e ∈ Metric.closedBall c r := by
    rw [Metric.mem_closedBall,dist_eq_norm]
    have hh : c+a⁻¹ • e-c = a⁻¹ • e := by abel
    rw [hh,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr ha)]
    calc
      _ ≤ a⁻¹*(a*r) := mul_le_mul_of_nonneg_left he (inv_nonneg.mpr ha.le)
      _ = r := by field_simp
  have hc := hK hz (hball hu) (sub_nonneg.mpr ha1) ha.le (by ring : 1-a+a = 1)
  have hcomb : (1-a) • z+a • (c+a⁻¹ • e) = y := by
    dsimp [e]
    rw [smul_add,smul_smul,mul_inv_cancel₀ (ne_of_gt ha),one_smul]
    abel
  rwa [hcomb] at hc

lemma innerBall_objective (f : E →L[ℝ] ℝ) (z c : E) {L R r a : ℝ}
    (hL : ‖f‖ ≤ L) (hz : ‖z‖ ≤ R) (hc : ‖c‖ ≤ R)
    (ha : 0 ≤ a) (y : E)
    (hy : y ∈ Metric.closedBall ((1-a) • z+a • c) (a*r)) :
    f y ≤ f z + a*L*(2*R+r) := by
  have hLp : 0 ≤ L := le_trans (norm_nonneg f) hL
  have he : ‖y-((1-a) • z+a • c)‖ ≤ a*r := by
    simpa only [Metric.mem_closedBall,dist_eq_norm] using hy
  have hdist : ‖y-z‖ ≤ a*(2*R+r) := by
    have hx : y-z = (y-((1-a) • z+a • c))+a • (c-z) := by module
    rw [hx]
    calc
      _ ≤ ‖y-((1-a) • z+a • c)‖+‖a • (c-z)‖ := norm_add_le _ _
      _ ≤ a*r+a*(2*R) := by
        rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg ha]
        have hh := norm_sub_le c z
        gcongr
        linarith
      _ = _ := by ring
  calc
    f y = f z+f (y-z) := by rw [map_sub]; ring
    _ ≤ f z+‖f (y-z)‖ := add_le_add_right (le_abs_self _) _
    _ ≤ f z+‖f‖*‖y-z‖ := add_le_add_right (f.le_opNorm _) _
    _ ≤ f z+L*(a*(2*R+r)) := by
      exact add_le_add_right (mul_le_mul hL hdist (norm_nonneg _) hLp) _
    _ = _ := by ring

theorem nearOptimal_innerBall (K : Set E) (hK : Convex ℝ K) (f : E →L[ℝ] ℝ)
    (z c : E) (hzK : z ∈ K) {L R r δ : ℝ}
    (hL : ‖f‖ ≤ L) (hLp : 0 < L) (hR : 0 ≤ R) (hr : 0 < r)
    (hz : ‖z‖ ≤ R) (hc : ‖c‖ ≤ R) (hball : Metric.closedBall c r ⊆ K)
    (hδ : 0 < δ) (hδsmall : δ ≤ L*(2*R+r)) :
    let a := δ/(L*(2*R+r))
    Metric.closedBall ((1-a) • z+a • c) (a*r) ⊆ K ∩ {y | f y ≤ f z+δ} := by
  dsimp only
  let a := δ/(L*(2*R+r))
  have hden : 0 < L*(2*R+r) := mul_pos hLp (by linarith)
  have ha : 0 < a := div_pos hδ hden
  have ha1 : a ≤ 1 := (div_le_one hden).mpr hδsmall
  intro y hy
  refine ⟨convex_innerBall K hK z c hzK hball ha ha1 hy,?_⟩
  have ho := innerBall_objective f z c hL hz hc ha.le y hy
  have he : a*L*(2*R+r) = δ := by dsimp [a]; field_simp
  simp only [he] at ho
  exact ho

end
end CurrentKS.RationalOptimization

open Matrix

end OAI
