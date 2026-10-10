import OAI.Analysis.KadisonKastler.CenteredTestCentralVectors
import OAI.Analysis.KadisonKastler.CenteredTestEnergy

namespace OAI

/-! # The commutator inequalities furnished by the centered test

This gives the quantitative premise used by the Haagerup criterion in
AHHM, arXiv:1804.05706v2, Theorem 7.2, with the uniform constant six.
The implication from that criterion to scalar bicentralizers is separate.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H} {Ω : H}

private theorem energy_gap {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t)
    (h : (1/2 : ℝ) < s^2-t^2) : (1/2 : ℝ) < s ∧ t < s := by
  constructor
  · nlinarith [sq_nonneg t]
  · nlinarith

theorem centeredTest_commutator_witness
    (d : ModularConjugationData M Ω) (a : Algebra M)
    (ha : a.val Ω=d.rightAction (star a) Ω)
    (hdetect : ∀ ε : ℝ, 0 < ε → ∃ b : Algebra M,
      ‖b.val Ω-d.rightAction b Ω‖ < ε ∧
      ((‖b.val Ω‖ < 2 ∧ (1/2 : ℝ) <
        (inner ℂ (b.val Ω) (modularCenteredTest d a (b.val Ω))).re) ∨
       (‖d.rightAction b Ω‖ < 2 ∧ (1/2 : ℝ) <
        (inner ℂ (d.rightAction b Ω) (modularCenteredTest d a (d.rightAction b Ω))).re)))
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ b : Algebra M,
      ‖b.val Ω‖+‖(b*a).val Ω‖ < 6*‖(a*b-b*a).val Ω‖ ∧
      ‖b.val Ω-d.rightAction b Ω‖ < δ*‖(a*b-b*a).val Ω‖ := by
  obtain ⟨b,hdef,hcase⟩ := hdetect (δ/2) (by positivity)
  rcases hcase with ⟨hbn,henergy⟩ | ⟨hbn,henergy⟩
  · rw [modularCenteredTest_left_energy d a b ha] at henergy
    obtain ⟨hgap,he⟩ := energy_gap (norm_nonneg _) (norm_nonneg _) henergy
    refine ⟨b,?_,?_⟩
    · nlinarith
    · exact hdef.trans (by nlinarith)
  · rw [modularCenteredTest_right_energy d a b ha] at henergy
    obtain ⟨hgap,he⟩ := energy_gap (norm_nonneg _) (norm_nonneg _) henergy
    have hbn' : ‖(star b).val Ω‖ < 2 := by
      change ‖star b.val Ω‖ < 2
      have hr : d.rightAction b Ω=d.conjugation (star b.val Ω) := by
        change d.conjugation (star b.val (d.conjugation Ω))=_
        rw [d.fixes_vector]
      rwa [hr,d.conjugation.norm_map] at hbn
    have hprod : ‖(star b*a).val Ω‖ ≤ ‖(a*star b).val Ω‖+
        ‖(a*star b-star b*a).val Ω‖ := by
      have hid : (star b*a).val Ω=(a*star b).val Ω-(a*star b-star b*a).val Ω := by
        simp only [AddSubgroupClass.coe_sub,sub_apply]
        abel
      rw [hid]
      exact norm_sub_le _ _
    have hdef' : ‖(star b).val Ω-d.rightAction (star b) Ω‖=
        ‖b.val Ω-d.rightAction b Ω‖ := by
      have hh := d.rightAction_adjoint_defect b 1
      simp only [Complex.ofReal_one,one_smul] at hh
      rw [hh,norm_neg,d.conjugation.norm_map]
    refine ⟨star b,?_,?_⟩
    · nlinarith
    · rw [hdef']
      exact hdef.trans (by nlinarith)

end

end KadisonKastler

end OAI
