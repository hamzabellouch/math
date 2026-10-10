import OAI.NumberTheory.TotientAsymptotic.PPTRowMargin
import OAI.NumberTheory.TotientAsymptotic.CollisionSlack

namespace OAI

/-!
The comparison simplex after a maximal-prefix choice and cancellation.
The surviving coordinates retain their order, so their smaller renewal
weights preserve the actual inverse-cube row margin.  Grid and normality
errors are charged explicitly to this margin.
-/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

private lemma ppt_fin_embedding_offset {b n : ℕ} (ι : Fin b ↪o Fin n)
    (hb : 0 < b) (r : Fin b) :
    (ι ⟨0,hb⟩).val+r.val ≤ (ι r).val := by
  have hall : ∀ k (hk : k < b),
      (ι ⟨0,hb⟩).val+k ≤ (ι ⟨k,hk⟩).val := by
    intro k
    induction k with
    | zero => intro hk; simp
    | succ k ih =>
      intro hk
      have hk' : k < b := by omega
      have hp := ih hk'
      have hs := ι.strictMono
        (show (⟨k,hk'⟩ : Fin b) < ⟨k+1,hk⟩ from Nat.lt_succ_self k)
      change (ι ⟨k,hk'⟩).val < (ι ⟨k+1,hk⟩).val at hs
      omega
  exact hall r.val r.isLt

private lemma ppt_sum_positive_fin_indices (b : ℕ) (f : ℕ → ℝ) :
    (∑ r ∈ Finset.Icc 1 (b-1), f r) =
      ∑ r : Fin b, if 0 < r.val then f r.val else 0 := by
  classical
  calc
    _ = ∑ r ∈ Finset.univ.filter (fun r : Fin b => 0 < r.val), f r.val := by
      symm
      apply Finset.sum_bij (fun r _ => r.val)
      · intro r hr
        have hpos := (Finset.mem_filter.mp hr).2
        exact Finset.mem_Icc.mpr ⟨hpos, by omega⟩
      · intro r hr s hs hrs
        exact Fin.ext hrs
      · intro k hk
        have hk' := Finset.mem_Icc.mp hk
        have hkb : k < b := by omega
        refine ⟨⟨k,hkb⟩, ?_, rfl⟩
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk'.1⟩
      · intro r hr
        rfl
    _ = _ := by rw [Finset.sum_filter]

/-- Removing ordered coordinates decreases the renewal-weighted row. -/
lemma ppt_surviving_row_sum_le {b n : ℕ} (ι : Fin b ↪o Fin n)
    (hb : 0 < b) (v : Fin n → ℝ) (hv : ∀ j, 0 ≤ v j) :
    (∑ r : Fin b, if 0 < r.val then a r.val*v (ι r) else 0) ≤
      ∑ j : Fin n, if ι ⟨0,hb⟩ < j then
        a (j.val-(ι ⟨0,hb⟩).val)*v j else 0 := by
  classical
  let R : Fin n → ℝ := fun j => if ι ⟨0,hb⟩ < j then
    a (j.val-(ι ⟨0,hb⟩).val)*v j else 0
  have hR (j : Fin n) : 0 ≤ R j := by
    dsimp only [R]
    split_ifs with hj
    · have hidx : 1 ≤ j.val-(ι ⟨0,hb⟩).val := by
        change (ι ⟨0,hb⟩).val < j.val at hj
        omega
      exact mul_nonneg (a_pos hidx).le (hv j)
    · exact le_rfl
  calc
    _ ≤ ∑ r : Fin b, R (ι r) := by
      apply Finset.sum_le_sum
      intro r hr
      by_cases hpos : 0 < r.val
      · have hlt : ι ⟨0,hb⟩ < ι r :=
          ι.strictMono (show (⟨0,hb⟩ : Fin b) < r from hpos)
        simp only [ite_eq_left hpos, R, ite_eq_left hlt]
        apply mul_le_mul_of_nonneg_right _ (hv (ι r))
        apply a_monotone_positive hpos
        have hh := ppt_fin_embedding_offset ι hb r
        omega
      · have hr0 : r = ⟨0,hb⟩ := by
          apply Fin.ext
          change r.val = 0
          omega
        simp [hr0, R]
    _ = ∑ j ∈ Finset.univ.image ι, R j := by
      rw [Finset.sum_image]
      exact fun r _ s _ hrs => ι.injective hrs
    _ ≤ ∑ j : Fin n, R j := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      intro j hj hj'
      exact hR j

/-- The actual order embedding supplies the reindexing, while each grid
coordinate pays only its stated additive error. -/
lemma ppt_gridded_surviving_row {b n : ℕ} (ι : Fin b ↪o Fin n)
    (hb : 0 < b) (v : Fin n → ℝ) (ν : ℕ → ℝ) {T σ e : ℝ}
    (hT : 0 < T) (hv : ∀ j, 0 ≤ v j)
    (hrow : (∑ j : Fin n, if ι ⟨0,hb⟩ < j then
      a (j.val-(ι ⟨0,hb⟩).val)*v j else 0) ≤ (1-σ)*T)
    (hgrid : ∀ r : Fin b, 0 < r.val → ν r.val ≤ v (ι r)/T+e) :
    (∑ r ∈ Finset.Icc 1 (b-1), a r*ν r) ≤
      1-σ+e*(∑ r ∈ Finset.Icc 1 (b-1), a r) := by
  let u : ℕ → ℝ := fun r => if hr : r < b then v (ι ⟨r,hr⟩) else 0
  have hmass : (∑ r ∈ Finset.Icc 1 (b-1), a r*u r) ≤ (1-σ)*T := by
    rw [ppt_sum_positive_fin_indices]
    have hh := (ppt_surviving_row_sum_le ι hb v hv).trans hrow
    simpa only [u, Fin.isLt, dite_true] using hh
  have hgrid' (r : ℕ) (hr : r ∈ Finset.Icc 1 (b-1)) : ν r ≤ u r/T+e := by
    have hr' := Finset.mem_Icc.mp hr
    have hrb : r < b := by omega
    simpa only [u, dite_eq_left hrb] using hgrid ⟨r,hrb⟩ hr'.1
  calc
    _ ≤ ∑ r ∈ Finset.Icc 1 (b-1), a r*(u r/T+e) := by
      apply Finset.sum_le_sum
      intro r hr
      exact mul_le_mul_of_nonneg_left (hgrid' r hr)
        (a_pos (Finset.mem_Icc.mp hr).1).le
    _ = (∑ r ∈ Finset.Icc 1 (b-1), a r*u r)/T+
        e*(∑ r ∈ Finset.Icc 1 (b-1), a r) := by
      simp only [mul_add, Finset.sum_add_distrib]
      congr 1
      · rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro r hr
        ring
      · rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro r hr
        ring
    _ ≤ _ := by
      have hh := (div_le_iff₀ hT).mpr hmass
      linarith only [hh]

/-- The inverse-cube margin comes from membership in the constructed
geometric family, before matching coordinates are removed. -/
theorem ppt_relaxed_surviving_slack {m n b : ℕ} {B c T headError e : ℝ}
    {v : Fin n → ℝ} (hv : v ∈ relaxedGeometricFamily m n B c)
    (ι : Fin b ↪o Fin n) (hb : 0 < b) (ν : ℕ → ℝ)
    (hT : 0 < T) (hhead : v (ι ⟨0,hb⟩) ≤ T+headError)
    (herr : 4*headError ≤
      (rowContractionError (m-((ι ⟨0,hb⟩).val+1))/2)*T)
    (hgrid : ∀ r : Fin b, 0 < r.val → ν r.val ≤ v (ι r)/T+e) :
    (∑ r ∈ Finset.Icc 1 (b-1), a r*ν r) ≤
      1-rowContractionError (m-((ι ⟨0,hb⟩).val+1))/8+
        e*(∑ r ∈ Finset.Icc 1 (b-1), a r) := by
  exact ppt_gridded_surviving_row ι hb v ν hT hv.1.1
    (ppt_relaxed_row_budget hv (ι ⟨0,hb⟩) hT hhead herr) hgrid

/-- After charging the grid widths and normality discrepancy, the
published comparison exponent retains half the concrete row margin. -/
theorem ppt_relaxed_surviving_exponent {m n b : ℕ} {budget c T headError e w S z : ℝ}
    {v : Fin n → ℝ} (hv : v ∈ relaxedGeometricFamily m n budget c)
    (ι : Fin b ↪o Fin n) (hb : 0 < b) (ν μ : ℕ → ℝ)
    (hT : 0 < T) (hBz : B z ≠ 0)
    (hhead : v (ι ⟨0,hb⟩) ≤ T+headError)
    (herr : 4*headError ≤
      (rowContractionError (m-((ι ⟨0,hb⟩).val+1))/2)*T)
    (hgrid : ∀ r : Fin b, 0 < r.val → ν r.val ≤ v (ι r)/T+e)
    (hwidth : ∀ r ∈ Finset.Icc 1 (b-1), ν r-μ r ≤ w)
    (herror : e*(∑ r ∈ Finset.Icc 1 (b-1), a r)+2*(b-1 : ℕ)*w+
      Real.sqrt (B S/B z)*(∑ i ∈ Finset.Icc 2 b, ((i : ℝ)*Real.log i+i)) ≤
        rowContractionError (m-((ι ⟨0,hb⟩).val+1))/16) :
    -2+(∑ r ∈ Finset.Icc 1 (b-1),
      a r*(B (comparisonCutoffs z ν r)/B z))+
      comparisonError b z S (comparisonCutoffs z ν) (comparisonCutoffs z μ) ≤
        -1-rowContractionError (m-((ι ⟨0,hb⟩).val+1))/16 := by
  have hslack := ppt_relaxed_surviving_slack hv ι hb ν hT hhead herr hgrid
  have hh := comparisonExponent_le b z S (comparisonCutoffs z ν) (comparisonCutoffs z μ)
    (rowContractionError (m-((ι ⟨0,hb⟩).val+1))/8) e w
    (by simpa only [comparisonCutoffs_doubleLog hBz] using hslack)
    (by simpa only [comparisonCutoffs_doubleLog hBz] using hwidth)
    (by
      convert herror using 1
      ring)
  convert hh using 1
  ring

end TotientAsymptotic

end

end OAI
