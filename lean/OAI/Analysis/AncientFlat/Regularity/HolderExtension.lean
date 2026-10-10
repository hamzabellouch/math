import OAI.Analysis.AncientFlat.Regularity.HolderContinuity

namespace OAI
noncomputable section
open Set Filter
namespace ParabolicLocalization
open ParabolicInterior
variable {V : Type} {E : Type*} [NormedAddCommGroup V] [NormedAddCommGroup E]
lemma pdist_symm (p q : V × ℝ) : pdist p q=pdist q p := by
  unfold pdist
  rw [norm_sub_rev,abs_sub_comm]
lemma quarter_pow_le {α d : ℝ} (hα : 0≤α) (hα1 : α≤1) (hd : 1/4≤d) :
    1≤4*d^α := by
  have hh := Real.self_le_rpow_of_le_one (by norm_num : (0:ℝ)≤1/4)
    (by norm_num : (1:ℝ)/4≤1) hα1
  have hm := Real.rpow_le_rpow (by norm_num : (0:ℝ)≤1/4) hd hα
  linarith

lemma holder_globalize (α N H : ℝ) (hα : 0≤α) (hα1 : α≤1) (hN : 0≤N) (hH : 0≤H)
    (I : Set ℝ) (f : V × ℝ → E)
    (hz : ∀ p, p.2∈I → 7/4≤‖p.1‖ → f p=0)
    (hn : ∀ p, p.2∈I → ‖p.1‖<2 → ‖f p‖≤N)
    (hh : ∀ p, p.2∈I → ‖p.1‖<2 → ∀ q, q.2∈I → ‖q.1‖<2 →
      ‖f p-f q‖≤H*pdist p q^α) :
    HolderBound α {p : V × ℝ | p.2∈I} f (H+4*N) := by
  have hb (p : V × ℝ) (hp : p.2∈I) : ‖f p‖≤N := by
    by_cases hx : ‖p.1‖<2
    · exact hn p hp hx
    · rw [hz p hp (by linarith [le_of_not_gt hx]),norm_zero]; exact hN
  have hcross (p q : V × ℝ) (hp : p.2∈I) (hq : q.2∈I) (hx : 2≤‖q.1‖) :
      ‖f p-f q‖≤(H+4*N)*pdist p q^α := by
    rw [hz q hq (by linarith),sub_zero]
    by_cases hz' : 7/4≤‖p.1‖
    · rw [hz p hp hz',norm_zero]; exact mul_nonneg (by positivity) (Real.rpow_nonneg (pdist_nonneg p q) α)
    · have hnp : ‖p.1‖<7/4 := lt_of_not_ge hz'
      have hnorm : 1/4≤‖p.1-q.1‖ := by
        have ht := norm_sub_norm_le q.1 p.1
        rw [norm_sub_rev] at ht
        linarith
      have hd : 1/4≤pdist p q := hnorm.trans (le_add_of_nonneg_right (Real.rpow_nonneg (abs_nonneg _) _))
      have hd' := quarter_pow_le hα hα1 hd
      have hn' := hb p hp
      nlinarith [mul_nonneg hH (Real.rpow_nonneg (pdist_nonneg p q) α)]
  refine ⟨fun p hp => (hb p hp).trans (by linarith),?_⟩
  intro p hp q hq
  by_cases hq' : ‖q.1‖<2
  · by_cases hp' : ‖p.1‖<2
    · exact (hh p hp hp' q hq hq').trans
        (mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg (pdist_nonneg p q) α))
    · simpa only [norm_sub_rev,pdist_symm q p] using hcross q p hq hp (le_of_not_gt hp')
  · exact hcross p q hp hq (le_of_not_gt hq')
end ParabolicLocalization

end

end OAI
