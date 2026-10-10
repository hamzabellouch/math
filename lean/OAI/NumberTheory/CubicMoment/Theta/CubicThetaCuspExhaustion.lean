import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCompactCuspEnergy
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaC1Cutoff

namespace OAI

/-! A fixed finite cusp family gives an explicit smooth exhaustion
which is eventually identically one in each quotient neighborhood. -/
noncomputable section
open Set Filter Topology
open scoped MatrixGroups ContDiff
namespace CubicFirstMoment

def cubicThetaCuspExhaustion (T : Finset SL(2,Eisenstein)) (n : ℕ) : C(CubicThetaQuotient,ℂ) :=
  ⟨cubicThetaCompactCuspCutoff T ((n:ℝ)+2),
    cubicThetaCompactCuspCutoff_continuous T (by linarith [Nat.cast_nonneg (α:=ℝ) n])⟩

lemma cubicThetaCuspExhaustion_smooth (T : Finset SL(2,Eisenstein)) (n : ℕ) :
    ContDiffOn ℝ ∞ (fun y => cubicThetaCuspExhaustion T n
      (cubicThetaQuotientMap (cubicThetaPointInclusion.symm y))) {y : ℂ × ℝ | 0<y.2} :=
  cubicThetaCompactCuspCutoff_smooth T (by linarith [Nat.cast_nonneg (α:=ℝ) n])

lemma cubicThetaCuspExhaustion_compact (S T : Finset SL(2,Eisenstein))
    (hc : ∀ V, cubicThetaQuotientCore S V ∪ ⋃ δ∈T,cubicThetaCuspNeighborhood δ V=univ)
    (hd : (T : Set SL(2,Eisenstein)).PairwiseDisjoint (fun δ => cubicThetaCuspNeighborhood δ 1))
    (n : ℕ) : HasCompactSupport (cubicThetaCuspExhaustion T n) :=
  cubicThetaCompactCuspCutoff_compact S T hc hd (by linarith [Nat.cast_nonneg (α:=ℝ) n])

lemma cubicThetaCuspExhaustion_local_one (T : Finset SL(2,Eisenstein)) (q : CubicThetaQuotient) :
    ∀ᶠ n : ℕ in atTop, (cubicThetaCuspExhaustion T n : CubicThetaQuotient → ℂ)=ᶠ[𝓝 q] (fun _ => 1) := by
  obtain ⟨C,_,hC⟩ := cubicThetaCompactCuspCutoff_local_one T q
  have hn : ∀ᶠ n : ℕ in atTop, C<(n:ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_gt_atTop C)
  filter_upwards [hn] with n hn
  exact hC _ (by linarith)

lemma cubicThetaCuspExhaustion_value_one (T : Finset SL(2,Eisenstein)) (q : CubicThetaQuotient) :
    ∀ᶠ n : ℕ in atTop, cubicThetaCuspExhaustion T n q=1 :=
  (cubicThetaCuspExhaustion_local_one T q).mono (fun _ h => h.eq_of_nhds)

lemma cubicThetaCuspExhaustion_gradient_agrees (T : Finset SL(2,Eisenstein))
    (F : CubicThetaSection) (q : CubicThetaQuotient) :
    ∀ᶠ n : ℕ in atTop, cubicThetaGradientRepresentative
      (cubicThetaSectionCutoff (cubicThetaCuspExhaustion T n) F) q=cubicThetaGradientRepresentative F q := by
  filter_upwards [cubicThetaCuspExhaustion_local_one T q] with n hn
  unfold cubicThetaGradientRepresentative
  apply cubicThetaSectionCutoff_local_gradient
  rwa [cubicThetaBorelSection_rightInverse]

lemma cubicThetaCuspExhaustion_value_agrees (T : Finset SL(2,Eisenstein))
    (F : CubicThetaSection) (q : CubicThetaQuotient) :
    ∀ᶠ n : ℕ in atTop, cubicThetaSectionRepresentative
      (cubicThetaSectionCutoff (cubicThetaCuspExhaustion T n) F) q=cubicThetaSectionRepresentative F q := by
  filter_upwards [cubicThetaCuspExhaustion_value_one T q] with n hn
  change cubicThetaCuspExhaustion T n (cubicThetaQuotientMap (cubicThetaBorelSection q))*
    cubicThetaSectionRepresentative F q=cubicThetaSectionRepresentative F q
  rw [cubicThetaBorelSection_rightInverse,hn,one_mul]

lemma cubicThetaCuspExhaustion_norm (T : Finset SL(2,Eisenstein)) (n : ℕ) (q : CubicThetaQuotient) :
    ‖cubicThetaCuspExhaustion T n q‖≤1+(T.card:ℝ) :=
  cubicThetaCompactCuspCutoff_norm T (by linarith [Nat.cast_nonneg (α:=ℝ) n]) q

lemma cubicThetaCuspExhaustion_energy (T : Finset SL(2,Eisenstein)) :
    ∃ B≥0, ∀ (n : ℕ) (p : ℂ × ℝ), 0<p.2 →
      p.2^2*cubicThetaFunctionEnergy (fun y => cubicThetaCuspExhaustion T n
        (cubicThetaQuotientMap (cubicThetaPointInclusion.symm y))) p≤B := by
  obtain ⟨B,hB,h⟩ := cubicThetaCompactCuspCutoff_energy_bound T
  exact ⟨B,hB,fun n p hp => h _ (by linarith [Nat.cast_nonneg (α:=ℝ) n]) p hp⟩

end CubicFirstMoment

end

end OAI
