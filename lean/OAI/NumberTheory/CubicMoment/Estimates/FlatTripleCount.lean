import OAI.NumberTheory.CubicMoment.Estimates.TripleScaleLogRange

namespace OAI

/-! The actual finite set of flat three-prime norm boxes has only a
fixed power of log log X elements. The large common index offset does
not enter this count. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def flatTripleIndexSet (M G : ℕ) (X : ℝ) : Finset (Fin 3 → Fin M) :=
  Finset.univ.filter (fun f =>
    X/16 ≤ ∏ i, tripleNormScale (fun j => (f j).val) i ∧
    (∏ i, tripleNormScale (fun j => (f j).val) i) ≤ 3*X ∧
    ∃ B : ℝ, (∀ i, tripleNormScale (fun j => (f j).val) i ≤ B) ∧
      B^3 ≤ (∏ i, tripleNormScale (fun j => (f j).val) i)*(1+Real.log X)^G)

lemma flatTripleIndexSet_card_nat (M G : ℕ) {X : ℝ} (hX : 1 ≤ X) :
    (flatTripleIndexSet M G X).card ≤
      (2*tripleIndexEnvelopeWidth+1+
        2*⌈(G:ℝ)*Real.log (1+Real.log X)/Real.log (4/3:ℝ)⌉₊+2)^3 := by
  let N := tripleIndexEnvelopeStart X
  let C := 2*tripleIndexEnvelopeWidth+1
  let D := ⌈(G:ℝ)*Real.log (1+Real.log X)/Real.log (4/3:ℝ)⌉₊
  have hsub : flatTripleIndexSet M G X ⊆ tripleIndexCluster M N C D := by
    intro f hf
    obtain ⟨_,hlo,hhi,B,hB,hflat⟩ := Finset.mem_filter.mp hf
    have hrange := tripleNormScale_index_sum_range hX (fun i => (f i).val) hlo hhi
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ f,hrange.1,hrange.2,?_⟩
    intro i j
    exact tripleNormScale_index_spread (fun i => (f i).val) G
      (by linarith [Real.log_nonneg hX]) hB hflat i j
  exact (Finset.card_le_card hsub).trans (tripleIndexCluster_card M N C D)

theorem flatTripleIndexSet_loglog_count (G : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (M : ℕ) (X : ℝ), 1 ≤ X →
      ((flatTripleIndexSet M G X).card:ℝ) ≤ K*(1+Real.log (1+Real.log X))^3 := by
  let r := Real.log (4/3:ℝ)
  have hr : 0 < r := Real.log_pos (by norm_num)
  let A : ℝ := 2*tripleIndexEnvelopeWidth+5+2*(G:ℝ)/r
  have hA : 0 < A := by dsimp [A]; positivity
  refine ⟨A^3,pow_pos hA _,?_⟩
  intro M X hX
  have hL : 1 ≤ 1+Real.log X := by linarith [Real.log_nonneg hX]
  have hlogL : 0 ≤ Real.log (1+Real.log X) := Real.log_nonneg hL
  have hceil := (Nat.ceil_lt_add_one
    (div_nonneg (mul_nonneg (Nat.cast_nonneg G) hlogL) hr.le)).le
  have hcore : ((2*tripleIndexEnvelopeWidth+1+
      2*⌈(G:ℝ)*Real.log (1+Real.log X)/r⌉₊+2:ℕ):ℝ) ≤
      A*(1+Real.log (1+Real.log X)) := by
    push_cast
    dsimp only [A]
    have hpos : 0 ≤ 2*(G:ℝ)/r := by positivity
    have hcross : 0 ≤ (2*(tripleIndexEnvelopeWidth:ℝ)+5)*Real.log (1+Real.log X) := by positivity
    have hdist : (2*(G:ℝ)/r)*Real.log (1+Real.log X) =
        2*((G:ℝ)*Real.log (1+Real.log X)/r) := by ring
    nlinarith
  have hcount : ((flatTripleIndexSet M G X).card:ℝ) ≤
      ((2*tripleIndexEnvelopeWidth+1+
        2*⌈(G:ℝ)*Real.log (1+Real.log X)/r⌉₊+2:ℕ):ℝ)^3 := by
    exact_mod_cast flatTripleIndexSet_card_nat M G hX
  apply hcount.trans
  exact (pow_le_pow_left₀ (by positivity) hcore 3).trans_eq (mul_pow _ _ _)

end CubicFirstMoment

end

end OAI
