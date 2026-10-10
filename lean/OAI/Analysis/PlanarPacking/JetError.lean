import OAI.Analysis.PlanarPacking.InterpolationError
import OAI.Analysis.PlanarPacking.FullMomentBridge
import OAI.Analysis.PlanarPacking.DirectBounds

namespace OAI

namespace SharpPlanar
open IntegerBasis
open scoped BigOperators
noncomputable def exactData (a : Bool) : CardinalData := if a then exactData₂ else exactData₁
noncomputable def exactJet (a : Bool) (ell : ℕ) (s : ℝ) : ℝ :=
  cardinalSeries (exactData a) ell s+K (exactData (!a)) ell s
lemma exactJet_deriv (a : Bool) (ell : ℕ) (s : ℝ) :
    HasDerivAt (exactJet a ell) (exactJet a (ell+1) s) s :=
  (cardinalSeries_hasDerivAt _ _ _).add (K_hasDerivAt _ _ _)
lemma exactData_x (a : Bool) : (exactData a).x=exactList a := by cases a <;> rfl
lemma table_exact_fixed (a : Bool) :
    (tableData a).C=(exactData a).C ∧ (tableData a).c₀=(exactData a).c₀ ∧
      (tableData a).d₀=(exactData a).d₀ := by
  cases a
  · rw [tableData_false]; exact ⟨rfl,rfl,rfl⟩
  · rw [tableData_true]; exact ⟨rfl,rfl,rfl⟩
lemma cardinalSeries_sub {p q : CardinalData}
    (hC : p.C=q.C) (hc : p.c₀=q.c₀) (hd : p.d₀=q.d₀) (ell : ℕ) (s : ℝ) :
    cardinalSeries p ell s-cardinalSeries q ell s=cardinalSeries (positiveData (p.x-q.x)) ell s := by
  have he := (cardinalSeries_summable p ell s).tsum_sub (cardinalSeries_summable q ell s)
  simp only [cardinalSeries,positiveData,hC,hc,hd,zero_mul,zero_add]
  rw [add_sub_add_left_eq_sub]
  rw [← he]
  apply tsum_congr
  intro n
  simp only [lp.coeFn_sub,Pi.sub_apply]
  ring
lemma K_positive_neg (x : X) (ell : ℕ) (s : ℝ) :
    K (positiveData (-x)) ell s= -K (positiveData x) ell s := by
  simpa only [neg_one_smul,neg_one_mul] using K_positive_smul (-1) x ell s
lemma K_positive_sub (x y : X) (ell : ℕ) (s : ℝ) :
    K (positiveData (x-y)) ell s=K (positiveData x) ell s-K (positiveData y) ell s := by
  rw [sub_eq_add_neg,K_positive_add,K_positive_neg,sub_eq_add_neg]
lemma K_table_exact (a : Bool) (ell : ℕ) (s : ℝ) :
    K (tableData a) ell s-K (exactData a) ell s=K (positiveData (coefficientError a)) ell s := by
  cases a
  · change K (tableData false) ell s-K (fixed₁ exactList₁) ell s=_
    rw [tableData_false,K_fixed₁ (tableList false),K_fixed₁ exactList₁]
    change _=K (positiveData (tableList false-exactList₁)) ell s
    rw [K_positive_sub]
    ring
  · change K (tableData true) ell s-K (fixed₂ exactList₂) ell s=_
    rw [tableData_true,K_fixed₂ (tableList true),K_fixed₂ exactList₂]
    change _=K (positiveData (tableList true-exactList₂)) ell s
    rw [K_positive_sub]
    ring
lemma table_exactJet_diff (a : Bool) (ell : ℕ) (s : ℝ) :
    tableHJet a ell s-exactJet a ell s=
      cardinalSeries (positiveData (coefficientError a)) ell s+
      K (positiveData (coefficientError (!a))) ell s := by
  have hs:=cardinalSeries_sub (table_exact_fixed a).1 (table_exact_fixed a).2.1
    (table_exact_fixed a).2.2 ell s
  have hk:=K_table_exact (!a) ell s
  rw [exactData_x] at hs
  change _ = cardinalSeries (positiveData (coefficientError a)) ell s at hs
  unfold tableHJet exactJet
  linarith
lemma jet_error_bound (a : Bool) (ell : ℕ) {s : ℝ} (hs : 0 ≤ s) :
    |tableHJet a ell s-exactJet a ell s| ≤
      ‖coefficientError a‖*(∑ j : Fin 6,densityCap j/6*(Real.pi*((j.val:ℝ)+1)/6)^ell)+
      ‖coefficientError (!a)‖*(∑ j : Fin 6,densityCap j*pieceL j s*(Real.pi*zCap ⟨j.val,by omega⟩)^ell) := by
  rw [table_exactJet_diff]
  refine (abs_add_le _ _).trans (add_le_add (direct_positive_bound _ _ _) ?_)
  simpa only [positiveData,abs_zero,zero_add,zero_mul,add_zero] using
    sharp_moment_bound (positiveData (coefficientError (!a))) ell hs
end SharpPlanar

end OAI
