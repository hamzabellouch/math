import OAI.MeasureTheory.Falconer.Estimates.TubeUniformization

namespace OAI

/-! Dyadic weight selection preserves regularity with a logarithmic loss.
This is used for coarse tubes weighted by original fine incidences. -/
namespace Falconer
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem weighted_dyadic_regular_subset {δ s K : ℝ} (hδ : 0 ≤ δ) (hK : 0 ≤ K)
    (P : Finset (Space 2)) (w : Space 2 → ℕ) (hP : P.Nonempty) (M : ℕ)
    (hw : ∀ x ∈ P, 0 < w x ∧ w x ≤ M)
    (hball : ∀ z r, δ ≤ r → r ≤ 1 →
      (∑ x ∈ P.filter (fun x => dist x z ≤ r), (w x:ℝ)) ≤
        K*r^s*(∑ x ∈ P, (w x:ℝ))) :
    let J := Nat.log 2 M+1
    ∃ k : ℕ, ∃ S ⊆ P, S.Nonempty ∧
      (∑ x ∈ P, (w x:ℝ)) ≤ (J:ℝ)*(∑ x ∈ S, (w x:ℝ)) ∧
      (∀ x ∈ S, 2^k ≤ w x ∧ w x < 2^(k+1)) ∧
      NormalizedFiniteBallBound δ s (2*K*(J:ℝ)) S := by
  let J := Nat.log 2 M+1
  let f := fun x => Nat.log 2 (w x)
  let W := ∑ x ∈ P, (w x:ℝ)
  have hJ : 0 < (J:ℝ) := by dsimp [J]; positivity
  have hW : 0 < W := Finset.sum_pos (fun x hx => Nat.cast_pos.mpr (hw x hx).1) hP
  have hmap : ∀ x ∈ P, f x ∈ Finset.range J := by
    intro x hx
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.log_mono_right (hw x hx).2))
  have hdiv : (Finset.range J).card • (W/(J:ℝ)) ≤ W := by
    simp only [Finset.card_range,nsmul_eq_mul]
    rw [mul_div_cancel₀ _ hJ.ne']
  obtain ⟨k,_,hk⟩ := Finset.exists_le_sum_fiber_of_maps_to_of_nsmul_le_sum hmap
    (show (Finset.range J).Nonempty from ⟨0,Finset.mem_range.mpr (by dsimp [J]; omega)⟩) hdiv
  let S := P.filter fun x => f x = k
  have hSP : S ⊆ P := Finset.filter_subset _ _
  have hsum : W ≤ (J:ℝ)*(∑ x ∈ S, (w x:ℝ)) := by
    simpa only [mul_comm] using (div_le_iff₀ hJ).mp hk
  have hS : S.Nonempty := by
    by_contra hn
    rw [Finset.not_nonempty_iff_eq_empty.mp hn,Finset.sum_empty,mul_zero] at hsum
    exact hW.not_ge hsum
  have hband (x : Space 2) (hx : x ∈ S) : 2^k ≤ w x ∧ w x < 2^(k+1) := by
    obtain ⟨hxP,hxk⟩ := Finset.mem_filter.mp hx
    dsimp [f] at hxk
    rw [← hxk]
    exact ⟨Nat.pow_log_le_self 2 (hw x hxP).1.ne',Nat.lt_pow_succ_log_self (by norm_num) _⟩
  have ha : (0:ℝ) < (2:ℝ)^k := by positivity
  have hupper : (∑ x ∈ S, (w x:ℝ)) ≤ (2*(2:ℝ)^k)*(S.card:ℝ) := by
    calc
      _ ≤ ∑ _x ∈ S, 2*(2:ℝ)^k := Finset.sum_le_sum fun x hx => by
        have hh : (w x:ℝ) < (2:ℝ)^(k+1) := by exact_mod_cast (hband x hx).2
        simpa only [pow_succ,mul_comm] using hh.le
      _ = _ := by simp; ring
  refine ⟨k,S,hSP,hS,hsum,hband,?_⟩
  intro z r hr hr1
  have hr0 : 0 ≤ r := hδ.trans hr
  let F := S.filter fun x => dist x z ≤ r
  have hlo : (2:ℝ)^k*(F.card:ℝ) ≤ (∑ x ∈ F, (w x:ℝ)) := by
    calc
      _ = ∑ _x ∈ F, (2:ℝ)^k := by simp; ring
      _ ≤ _ := Finset.sum_le_sum fun x hx => by
        exact_mod_cast (hband x (Finset.mem_filter.mp hx).1).1
  have hsub : F ⊆ P.filter (fun x => dist x z ≤ r) := by
    intro x hx
    exact Finset.mem_filter.mpr ⟨hSP (Finset.mem_filter.mp hx).1,(Finset.mem_filter.mp hx).2⟩
  have hh : (2:ℝ)^k*(F.card:ℝ) ≤ (2:ℝ)^k*((2*K*(J:ℝ))*r^s*(S.card:ℝ)) := by
    calc
      _ ≤ ∑ x ∈ F, (w x:ℝ) := hlo
      _ ≤ ∑ x ∈ P.filter (fun x => dist x z ≤ r), (w x:ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun x _ _ => Nat.cast_nonneg _)
      _ ≤ K*r^s*W := hball z r hr hr1
      _ ≤ K*r^s*((J:ℝ)*(∑ x ∈ S, (w x:ℝ))) :=
        mul_le_mul_of_nonneg_left hsum (mul_nonneg hK (Real.rpow_nonneg hr0 _))
      _ ≤ K*r^s*((J:ℝ)*((2*(2:ℝ)^k)*(S.card:ℝ))) := by gcongr
      _ = _ := by ring
  exact (mul_le_mul_iff_right₀ ha).mp hh

end Falconer

end OAI
