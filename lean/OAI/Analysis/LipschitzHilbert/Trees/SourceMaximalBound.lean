import OAI.Analysis.LipschitzHilbert.Trees.SourceThreeGridMaximal
import OAI.Analysis.LipschitzHilbert.Trees.SourceAllStrongMaximal

namespace OAI

/-! Uniform boundedness of the actual maximal representatives on a
bounded source, including on their null-set representatives. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace LipschitzHilbert

theorem monotoneMaximal_le_of_bound {X : Type*} (F : ℕ → X → ℝ)
    (x : X) (B : ℝ) (hB : 0≤B) (hF : ∀ n, |F n x|≤B) :
    monotoneMaximal F x≤B := by
  have hsq : maximalSquare F x≤ENNReal.ofReal (B^2) := by
    apply iSup_le
    intro n
    apply ENNReal.ofReal_le_ofReal
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (F n x)) (hF n) 2
  apply Real.sqrt_le_iff.mpr
  refine ⟨hB,?_⟩
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hsq
  simpa only [ENNReal.toReal_ofReal (sq_nonneg B)] using h

namespace DyadicLineGrid

theorem cellMean_bound (q k : ℤ) (f : ℝ → ℝ) (B : ℝ)
    (hbound : ∀ y, |f y|≤B) (x : ℝ) : |cellMean q k f x|≤B := by
  have h := norm_setIntegral_le_of_norm_le_const (μ:=volume)
    (s:=cell q k (index q k x)) (f:=f) (C:=B)
    (show volume (cell q k (index q k x))<∞ from measure_Ico_lt_top)
    (fun y (_ : y∈cell q k (index q k x)) => by simpa only [Real.norm_eq_abs] using hbound y)
  rw [cellMean,abs_div,abs_of_pos (scale_pos k)]
  apply (div_le_iff₀ (scale_pos k)).mpr
  simpa only [Real.norm_eq_abs,cell_length] using h

theorem dyadicMaximal_bound (q top : ℤ) (N : ℕ) (f : ℝ → ℝ) (B : ℝ)
    (hbound : ∀ y, |f y|≤B) (x : ℝ) : dyadicMaximal q top N f x≤B := by
  change (Finset.range (N+1)).sup' Finset.nonempty_range_add_one
    (fun n : ℕ => |cellMean q (top-(n:ℤ)) f x|)≤B
  apply (Finset.sup'_le_iff _ _).mpr
  intro n _
  exact cellMean_bound q (top-(n:ℤ)) f B hbound x

theorem allDyadicMaximal_bound (q : ℤ) (f : ℝ → ℝ) (B : ℝ)
    (hB : 0≤B) (hbound : ∀ y, |f y|≤B) (x : ℝ) : allDyadicMaximal q f x≤B := by
  apply monotoneMaximal_le_of_bound _ x B hB
  intro n
  rw [abs_of_nonneg (dyadicMaximal_nonneg _ _ _ _ _)]
  exact dyadicMaximal_bound q n (2*n) f B hbound x

theorem threeGridMaximal_bound (f : ℝ → ℝ) (B : ℝ)
    (hB : 0≤B) (hbound : ∀ y, |f y|≤B) (x : ℝ) : threeGridMaximal f x≤3*B := by
  calc
    _ ≤ ∑ q : GridChoice, B := Finset.sum_le_sum (fun q _ => allDyadicMaximal_bound q.val f B hB hbound x)
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,gridChoice_card,nsmul_eq_mul]; norm_num

theorem allHorizontalMaximal_bound (q : ℤ) (f : ℝ×ℝ → ℝ) (B : ℝ)
    (hB : 0≤B) (hbound : ∀ y, |f y|≤B) (z : ℝ×ℝ) : allHorizontalMaximal q f z≤B :=
  allDyadicMaximal_bound q (fun x => f (x,z.2)) B hB (fun x => hbound (x,z.2)) z.1

theorem allVerticalMaximal_bound (q : ℤ) (f : ℝ×ℝ → ℝ) (B : ℝ)
    (hB : 0≤B) (hbound : ∀ y, |f y|≤B) (z : ℝ×ℝ) : allVerticalMaximal q f z≤B :=
  allHorizontalMaximal_bound q (f ∘ Prod.swap) B hB (fun x => hbound x.swap) z.swap

end DyadicLineGrid
end LipschitzHilbert

end

end OAI
