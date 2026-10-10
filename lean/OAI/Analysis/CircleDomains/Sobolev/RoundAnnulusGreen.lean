import OAI.Analysis.CircleDomains.Topology.RoundDiskGreen

namespace OAI

/-! The existing signed Green input on a round annulus. The outer sign
is fixed by its zero-hole radial-form specialization. -/
open Set Filter Function MeasureTheory Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma round_annulus_green (hgreen : UnorientedFiniteCircleGreenFormula)
    {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (O : Set ℂ) (hO : IsOpen O)
    (hsub : closedBall (0 : ℂ) b \ ball 0 a ⊆ O)
    (P Q : ℂ → ℝ) (hP : ContDiffOn ℝ (⊤ : ℕ∞) P O)
    (hQ : ContDiffOn ℝ (⊤ : ℕ∞) Q O) :
    planarFormIntegral P Q (unitCircleParam 0 b) -
      planarFormIntegral P Q (unitCircleParam 0 a) =
      ∫ z in ball (0 : ℂ) b \ closedBall 0 a,
        (fderiv ℝ Q z) 1 - (fderiv ℝ P z) Complex.I := by
  have hb : 0 < b := ha.trans hab
  obtain ⟨e, _, hg⟩ := hgreen (roundDiskChart b hb) (unitCircleParam 0 b)
    (unitCircleParam_regular b hb)
  have hzero := hg 0 Fin.elim0 Fin.elim0 (by intro i; exact Fin.elim0 i)
    (by intro i; exact Fin.elim0 i) (by intro i; exact Fin.elim0 i)
    univ isOpen_univ (subset_univ _) (fun z => -z.im) (fun z => z.re)
    Complex.imCLM.contDiff.neg.contDiffOn Complex.reCLM.contDiff.contDiffOn
  simp only [Finset.univ_eq_empty, Finset.sum_empty, sub_zero,
    iUnion_of_empty, sdiff_empty, roundDiskChart_interior] at hzero
  rw [← round_disk_green hgreen b hb univ isOpen_univ (subset_univ _)
    (fun z : ℂ => -z.im) (fun z : ℂ => z.re)
      Complex.imCLM.contDiff.neg.contDiffOn Complex.reCLM.contDiff.contDiffOn,
    radial_form_unitCircleParam] at hzero
  have he : e = 1 := by
    have hp : 0 < 2*Real.pi*b^2 := by positivity
    nlinarith
  have h := hg 1 (fun _ => 0) (fun _ => a) (fun _ => ha)
    (by intro i j hij; exact (hij (Subsingleton.elim i j)).elim)
    (by intro i; rw [roundDiskChart_interior]; exact closedBall_subset_ball hab)
    O hO (by simpa only [roundDiskChart_interior, iUnion_const,
      closure_ball _ hb.ne'] using hsub) P Q hP hQ
  simpa only [he, one_mul, Fin.sum_univ_one, roundDiskChart_interior, iUnion_const] using h

end CircleDomainRigidity

end

end OAI
