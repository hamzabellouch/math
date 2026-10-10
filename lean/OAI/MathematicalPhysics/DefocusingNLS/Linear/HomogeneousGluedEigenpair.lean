import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousGluedRegularity

namespace OAI

/-! A matching zero supplies a nonzero classical eigenpair, including at the join. -/

open Set Filter Topology
open scoped ContDiff
namespace DefocusingNLS
local notation "E₄" => (ℂ × ℂ) × (ℂ × ℂ)

theorem homogeneousGlued_nonzero_values (νp νm eta : ℂ) (m : ℕ)
    (Q : ℝ → ℂ) (U : ℝ → E₄) (R : ℝ) (hR : 0 < R) (hne : U R ≠ 0)
    (hU : ∀ r, 0 < r → HasDerivAt U
      (spectralPhysicalCircularField νp νm eta m (Q r) r (U r)) r) :
    ∃ r : ℝ, 0 < r ∧ ((U r).1.1 ≠ 0 ∨ (U r).2.1 ≠ 0) := by
  by_contra hn
  push Not at hn
  have hp : (fun r => (U r).1.1) =ᶠ[𝓝 R] (fun _ => (0 : ℂ)) := by
    filter_upwards [Ioi_mem_nhds hR] with r hr
    exact (hn r hr).1
  have hm : (fun r => (U r).2.1) =ᶠ[𝓝 R] (fun _ => (0 : ℂ)) := by
    filter_upwards [Ioi_mem_nhds hR] with r hr
    exact (hn r hr).2
  obtain ⟨hvp, hvm⟩ := homogeneousRegular_state_velocity νp νm eta m Q U R (hU R hR)
  have hdp : (U R).1.2 = 0 := by
    rw [← hvp, hp.deriv_eq]
    exact deriv_const R 0
  have hdm : (U R).2.2 = 0 := by
    rw [← hvm, hm.deriv_eq]
    exact deriv_const R 0
  apply hne
  apply Prod.ext <;> apply Prod.ext
  · exact (hn R hR).1
  · exact hdp
  · exact (hn R hR).2
  · exact hdm

theorem homogeneousGlued_matching_state (νp νm eta : ℂ) (m : ℕ)
    (Q : ℝ → ℂ) (hQ : ContDiffOn ℝ ∞ Q (Ioi 0))
    (R : ℝ) (hR : 0 < R) (Rp Rm Op Om : ℝ → E₄)
    (hpc : ContDiff ℝ 2 (fun r => (Rp r).1.1) ∧
      ContDiff ℝ 2 (fun r => (Rp r).2.1))
    (hmc : ContDiff ℝ 2 (fun r => (Rm r).1.1) ∧
      ContDiff ℝ 2 (fun r => (Rm r).2.1))
    (hRp : ∀ r ∈ Ioc 0 R, HasDerivAt Rp
      (spectralPhysicalCircularField νp νm eta m (Q r) r (Rp r)) r)
    (hRm : ∀ r ∈ Ioc 0 R, HasDerivAt Rm
      (spectralPhysicalCircularField νp νm eta m (Q r) r (Rm r)) r)
    (hOp : ∀ r, R ≤ r → HasDerivAt Op
      (spectralPhysicalCircularField νp νm eta m (Q r) r (Op r)) r)
    (hOm : ∀ r, R ≤ r → HasDerivAt Om
      (spectralPhysicalCircularField νp νm eta m (Q r) r (Om r)) r)
    (hrank : LinearIndependent ℂ ![Rp R, Rm R])
    (horank : LinearIndependent ℂ ![Op R, Om R])
    (hzero : spectralMatchingDeterminant (Rp R) (Rm R) (Op R) (Om R) = 0) :
    ∃ (U : ℝ → E₄) (a b c d : ℂ),
      (∀ r, r ≤ R → U r = a • Rp r + b • Rm r) ∧
      (∀ r, R ≤ r → U r = c • Op r + d • Om r) ∧
      U R ≠ 0 ∧
      ContDiff ℝ 2 (fun r => (U r).1.1) ∧
      ContDiff ℝ 2 (fun r => (U r).2.1) ∧
      ContDiffOn ℝ ∞ U (Ioi 0) ∧
      (∀ r, 0 < r → HasDerivAt U
        (spectralPhysicalCircularField νp νm eta m (Q r) r (U r)) r) := by
  obtain ⟨U, a, b, c, d, hi, ho, hn, hd⟩ :=
    (spectralMatching_zero_iff_glued νp νm eta m Q R hR Rp Rm Op Om
      hRp hRm hOp hOm hrank horank).mp hzero
  have hc : ContDiff ℝ 2 (fun r => (a • Rp r + b • Rm r).1.1) ∧
      ContDiff ℝ 2 (fun r => (a • Rp r + b • Rm r).2.1) :=
    ⟨(hpc.1.const_smul a).add (hmc.1.const_smul b),
      (hpc.2.const_smul a).add (hmc.2.const_smul b)⟩
  obtain ⟨hf, hg⟩ := homogeneousGlued_positions_c2 νp νm eta m Q hQ U
    (fun r => a • Rp r + b • Rm r) R hR hc (fun r hr => hi r hr.le) hd
  exact ⟨U, a, b, c, d, hi, ho, hn, hf, hg,
    homogeneousGlued_state_smooth νp νm eta m Q hQ U hd, hd⟩

end DefocusingNLS

end OAI
