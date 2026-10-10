import OAI.Geometry.Relativity.CKS.CollarShiftJet

namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

def packExpansion (q : MatrixThreeJet) (Q : MatrixScalarJet) (S : I → ScalarThreeJet) : ExpansionInput :=
  (fun i k => (q i k).1,fun a i k => (q i k).2 a,Q,
    fun a => (S a).1,fun a b => (S b).2 a)

lemma actualExpansionInput_pack (q Q : Point → Mat) (S : Point → Point) (x : Point) :
    actualExpansionInput q Q S x = packExpansion (matrixThreeJets q x) (matrixScalarJets Q x)
      (fun a => actualThreeJet (fun y => S y a) x) := rfl

lemma packExpansion_reference (q : MatrixThreeJet) : packExpansion q 0 0 =
    expansionReference (fun i k => (q i k).1) (fun a i k => (q i k).2 a) := rfl

lemma packExpansion_sub (q q' : MatrixThreeJet) (Q Q' : MatrixScalarJet)
    (S S' : I → ScalarThreeJet) :
    packExpansion q Q S-packExpansion q' Q' S' = packExpansion (q-q') (Q-Q') (S-S') := rfl

lemma packExpansion_norm {q : MatrixThreeJet} {Q : MatrixScalarJet} {S : I → ScalarThreeJet}
    {D : ℝ} (hD : 0 ≤ D) (hq : ‖q‖ ≤ D) (hQ : ‖Q‖ ≤ D) (hS : ‖S‖ ≤ D) :
    ‖packExpansion q Q S‖ ≤ D := by
  have hqi (i k : I) : ‖q i k‖ ≤ D := (Matrix.norm_entry_le_entrywise_sup_norm q).trans hq
  have hSi (a : I) : ‖S a‖ ≤ D := (norm_le_pi_norm S a).trans hS
  apply norm_prod_le_iff.mpr
  constructor
  · exact (Matrix.norm_le_iff hD).mpr (fun i k => (norm_fst_le (q i k)).trans (hqi i k))
  apply norm_prod_le_iff.mpr
  constructor
  · apply (pi_norm_le_iff_of_nonneg hD).mpr
    intro a
    apply (Matrix.norm_le_iff hD).mpr
    intro i k
    exact (norm_le_pi_norm (q i k).2 a).trans ((norm_snd_le (q i k)).trans (hqi i k))
  apply norm_prod_le_iff.mpr
  refine ⟨hQ,?_⟩
  apply norm_prod_le_iff.mpr
  constructor
  · exact (pi_norm_le_iff_of_nonneg hD).mpr (fun a => (norm_fst_le (S a)).trans (hSi a))
  · apply (pi_norm_le_iff_of_nonneg hD).mpr
    intro a
    apply (pi_norm_le_iff_of_nonneg hD).mpr
    intro b
    exact (norm_le_pi_norm (S b).2 a).trans ((norm_snd_le (S b)).trans (hSi b))

theorem actualExpansionInput_norm {q σ Q : Point → Mat} {S : Point → Point} {x : Point} {D : ℝ}
    (hD : 0 ≤ D) (hq : ‖matrixThreeJets q x-matrixThreeJets σ x‖ ≤ D)
    (hQ : ‖matrixScalarJets Q x‖ ≤ D)
    (hS : ‖fun a => actualThreeJet (fun y => S y a) x‖ ≤ D) :
    ‖actualExpansionInput q Q S x-expansionReference (matrixScalarJets σ x)
      (fun a => matrixScalarJets (fun y i k => CKSCalculus.D (basis a) (fun z => σ z i k) y) x)‖ ≤ D := by
  change ‖actualExpansionInput q Q S x-packExpansion (matrixThreeJets σ x) 0 0‖ ≤ D
  rw [actualExpansionInput_pack,packExpansion_sub,sub_zero,sub_zero]
  exact packExpansion_norm hD hq hQ hS

def normalizedShift (r : ℝ) (q : Point → Mat) (mixed : Point → Point) : Point → Point :=
  fun x a => (1/r)*∑ b, inverse (q x) a b*mixed x b

lemma normalizedShift_realized (r : ℝ) {q : Point → Mat} {mixed : Point → Point} {x : Point}
    (hq : ContDiffAt ℝ 3 q x) (hmixed : ContDiffAt ℝ 3 mixed x) (h0 : determinant (q x) ≠ 0) :
    (fun a => actualThreeJet (fun y => normalizedShift r q mixed y a) x) =
      (1/r) • raisedMixedJet (matrixThreeJets q x,fun a => actualThreeJet (fun y => mixed y a) x) := by
  rw [← actual_raisedMixedJet hq hmixed h0]
  funext a
  apply actualThreeJet_smul
  apply ContDiffAt.sum
  intro b hb
  apply ContDiffAt.mul _ (contDiffAt_pi.mp hmixed b)
  unfold inverse
  apply ContDiffAt.div
  · fin_cases a <;> fin_cases b <;> dsimp <;> first | exact component_three hq _ _ | exact (component_three hq _ _).neg
  · exact (determinant_smooth.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 3)).contDiffAt.comp x hq
  · exact h0

end
end CKSAngularGeometry

end

end OAI
