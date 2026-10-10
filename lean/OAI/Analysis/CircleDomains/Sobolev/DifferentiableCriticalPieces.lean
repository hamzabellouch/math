import OAI.Analysis.CircleDomains.Selection.RegularMapPieces

namespace OAI

/-! At critical differentiability points the linear-approximation partition
has arbitrarily small Lipschitz constant on each measurable piece. -/
open Set Function Filter MeasureTheory
open scoped Topology NNReal
noncomputable section
namespace CircleDomainRigidity

lemma differentiable_critical_pieces {f : ℂ → ℝ} {S : Set ℂ}
    (hS : MeasurableSet S) (hne : S.Nonempty)
    (hd : ∀ x ∈ S, DifferentiableAt ℝ f x)
    (hz : ∀ x ∈ S, fderiv ℝ f x = 0) (ε : ℝ≥0) (hε : 0 < ε) :
    ∃ B : ℕ → Set ℂ, (∀ n, MeasurableSet (B n)) ∧
      Pairwise (Disjoint on B) ∧ (⋃ n, B n) = S ∧
      ∀ n, LipschitzOnWith ε f (B n) := by
  obtain ⟨t,A,hdj,ht,hcover,happrox,hA⟩ :=
    exists_partition_approximatesLinearOn_of_hasFDerivWithinAt f S (fderiv ℝ f)
      (fun x hx => (hd x hx).hasFDerivAt.hasFDerivWithinAt) (fun _ => ε)
      (fun _ => hε.ne')
  have hAz (n : ℕ) : A n = 0 := by
    obtain ⟨x,hx,he⟩ := hA hne n
    rw [he, hz x hx]
  refine ⟨fun n => S ∩ t n, (fun n => hS.inter (ht n)), ?_, ?_, ?_⟩
  · exact fun i j hij => (hdj hij).mono inter_subset_right inter_subset_right
  · rw [← inter_iUnion, inter_eq_left.mpr hcover]
  · intro n
    have hh := (happrox n).lipschitz
    rw [hAz n] at hh
    simpa only [norm_zero, nnnorm_zero, zero_add] using lipschitzOnWith_iff_restrict.mpr hh

end CircleDomainRigidity

end

end OAI
