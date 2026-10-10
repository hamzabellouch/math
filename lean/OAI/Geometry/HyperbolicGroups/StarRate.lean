import Mathlib
import OAI.Geometry.HyperbolicGroups.StarError

namespace OAI

section
section


noncomputable section
open scoped BigOperators
open Filter Topology
namespace HyperbolicObstruction
namespace IncidenceTemplate
variable {B A : Type*} [Fintype B] [Fintype A] [DecidableEq B] [DecidableEq A]
  [Nonempty B] [Nonempty A]

abbrev actualProbability (α β δ : ℝ) (A : Type*) [Fintype A] (r : Row) : ℝ :=
  (Fintype.card A : ℝ) ^ (-actualRowCost α β δ r)

omit [DecidableEq A] in
lemma actualProbability_mem {α β δ : ℝ} (ha : 0 ≤ α) (hb : 7*α ≤ β) (hd : 0 ≤ δ) (r : Row) :
    actualProbability α β δ A r ∈ Set.Icc (0:ℝ) 1 :=
  TableModel.powerProbability_mem
    (by exact_mod_cast Fintype.card_pos (α := A)) (actualRowCost_nonneg ha hb hd r)

omit [DecidableEq A] in
lemma actualProbability_pos (α β δ : ℝ) (r : Row) : 0 < actualProbability α β δ A r :=
  Real.rpow_pos_of_pos (by exact_mod_cast Fintype.card_pos (α := A)) _

def extensionRate (U : Finset Field) (j : B) (N : ℕ) : ℝ :=
  Fintype.card (BernoulliCandidates.OverlapType (StarModel.ExtPos rowSupport U j)) *
    2 ^ Fintype.card (PinnedAssignments.Free (StarModel.branchPins U j)) * (N : ℝ) ^ (-(1/2:ℝ))

def leafRate (U : Finset Field) (e : Field) (N : ℕ) : ℝ :=
  Fintype.card (BernoulliCandidates.OverlapType (StarModel.Pos (B := B) rowSupport U)) *
    2 ^ Fintype.card (PinnedAssignments.Free (StarModel.leafPins (B := B) U e)) * (N : ℝ) ^ (-(1/2:ℝ))

def errorRate (U : Finset Field) (e : Field) (N : ℕ) : ℝ :=
  (∑ j : B, Real.sqrt (extensionRate U j N)) + Real.sqrt (leafRate (B := B) U e N)

omit [Nonempty B] in
lemma errorRate_tendsto (U : Finset Field) (e : Field) :
    Tendsto (errorRate (B := B) U e) atTop (𝓝 0) := by
  have hn : Tendsto (fun N : ℕ => (N : ℝ)^(-(1/2:ℝ))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ) < 1/2)).comp tendsto_natCast_atTop_atTop
  have he (j : B) : Tendsto (fun N => Real.sqrt (extensionRate U j N)) atTop (𝓝 0) := by
    have hh := Real.continuous_sqrt.continuousAt.tendsto.comp (hn.const_mul
      ((Fintype.card (BernoulliCandidates.OverlapType (StarModel.ExtPos rowSupport U j)) : ℝ) *
        2 ^ Fintype.card (PinnedAssignments.Free (StarModel.branchPins U j))))
    simpa only [mul_zero,Real.sqrt_zero,Function.comp_def,extensionRate] using hh
  have hl : Tendsto (fun N => Real.sqrt (leafRate (B := B) U e N)) atTop (𝓝 0) := by
    have hh := Real.continuous_sqrt.continuousAt.tendsto.comp (hn.const_mul
      ((Fintype.card (BernoulliCandidates.OverlapType (StarModel.Pos (B := B) rowSupport U)) : ℝ) *
        2 ^ Fintype.card (PinnedAssignments.Free (StarModel.leafPins (B := B) U e))))
    simpa only [mul_zero,Real.sqrt_zero,Function.comp_def,leafRate] using hh
  unfold errorRate
  simpa only [Finset.sum_const_zero,zero_add] using
    (tendsto_finsetSum Finset.univ (fun j _ => he j)).add hl

/-- All constants in the error estimate are independent of the alphabet,
parameters and the pinned values. Only the fixed finite star template remains. -/
theorem expectedError_le {α β δ : ℝ} (ha : 0 ≤ α) (hb : 7*α ≤ β) (hd : 0 ≤ δ)
    (hsmall : (Fintype.card B : ℝ) * (β+90*δ) ≤ 1/2)
    (U : Finset Field) (e : Field) (he : e ∉ U)
    (gap : ∀ W, W.Nonempty → Disjoint U W → 1 ≤ pattern.exponent (U ∪ W) - pattern.exponent U)
    (a₀ : A) (b₀ : B ↪ A) (hN : 4 * Fintype.card (StarModel.Var (B := B) U) ≤ Fintype.card A) :
    let p := actualProbability α β δ A
    let hp := actualProbability_mem (A := A) ha hb hd
    (TableModel.law rowSupport p hp).expect (StarModel.normalizedError rowSupport U e p hp a₀ b₀) ≤
      errorRate (B := B) U e (Fintype.card A) := by
  apply StarModel.expect_normalizedError_le rowSupport U e he
    (actualProbability α β δ A) (actualProbability_mem (A := A) ha hb hd) a₀ b₀
    (fun j => extensionRate U j (Fintype.card A)) (leafRate (B := B) U e (Fintype.card A))
  · intro j; unfold extensionRate; positivity
  · unfold leafRate; positivity
  · exact StarModel.starMean_pos rowSupport U (Classical.choice inferInstance) _ _
      (actualProbability_pos α β δ) (fun _ => a₀) hN
  · intro j σ
    exact extension_variance_bound ha hb hd hsmall U j gap (StarModel.branchValues U σ) hN
  · intro b
    exact leaf_variance_bound ha hb hd hsmall U e he gap (StarModel.leafValues U b a₀)
      (StarModel.leaf_pin_fieldwise U e b a₀) hN

end IncidenceTemplate
end HyperbolicObstruction
end
end

section

end
end

end OAI
