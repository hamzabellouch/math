import OAI.NumberTheory.Jacobsthal.Sieve.HypotheticalCofactorHit

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace ErdosVarianceEffective
open ErdosInverseCells ErdosInverseHits ErdosHypotheticalTag ErdosInverseCounts ErdosInverseAlignment
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

noncomputable def effectiveBase (a : ℕ → ℕ) (r : ℚ) (qf p : ℕ) [NeZero p]
    (hHp : (effectiveModulus a r qf).Coprime p) : ℕ :=
  cofactorHit qf a+qf*intervalK p (effectiveModulus a r qf) hHp (effectiveIntercept a r qf)

noncomputable def effectiveSurvivors (Y : ℕ) (small : Finset ℕ) (a : ℕ → ℕ) (r : ℚ)
    (qf p : ℕ) [NeZero p] (hHp : (effectiveModulus a r qf).Coprime p) : Finset ℕ :=
  (Finset.range (hitLength Y (p*qf) (effectiveBase a r qf p hHp))).filter
    (fun j => ∀ t ∈ small,(effectiveBase a r qf p hHp+p*qf*j)%t ≠ a t%t)

theorem effectiveBase_eq_sourceParentBase (a : ℕ → ℕ) (r : ℚ) (qf : ℕ) (hq : Squarefree qf)
    (p : ℕ) [NeZero p] (hp : p.Prime) (hqp : qf.Coprime p)
    (hHp : (effectiveModulus a r qf).Coprime p) :
    effectiveBase a r qf p hHp = sourceParentBase p qf hqp hq (hypotheticalClass a r p) := by
  unfold sourceParentBase
  rw [← cofactorHit_eq qf hq (hypotheticalClass a r p),cofactorHit_hypothetical a r qf p hq hqp,
    ← effective_k_eq_parentSlope a r qf hq p hp hqp hHp]
  rfl

theorem effectiveSurvivors_eq_parent (Y : ℕ) (small : Finset ℕ) (a : ℕ → ℕ) (r : ℚ)
    (qf : ℕ) (hq : Squarefree qf) (p : ℕ) [NeZero p] (hp : p.Prime)
    (hqp : qf.Coprime p) (hHp : (effectiveModulus a r qf).Coprime p) (hps : p ∉ small) :
    effectiveSurvivors Y small a r qf p hHp =
      parentSurvivorCoordinates Y small (hypotheticalClass a r p) p qf hqp hq := by
  unfold effectiveSurvivors parentSurvivorCoordinates
  rw [effectiveBase_eq_sourceParentBase a r qf hq p hp hqp hHp]
  ext j
  simp only [Finset.mem_filter,Finset.mem_range]
  apply and_congr_right
  intro _hj
  apply forall_congr'
  intro t
  apply forall_congr'
  intro ht
  rw [hypothetical_other a r p t (by intro he;subst t;exact hps ht)]

theorem hypothetical_candidates_eq_effective_image (Y : ℕ) (small : Finset ℕ) (a : ℕ → ℕ) (r : ℚ)
    (qf : ℕ) (hq : Squarefree qf) (p : ℕ) [NeZero p] (hp : p.Prime)
    (hqp : qf.Coprime p) (hHp : (effectiveModulus a r qf).Coprime p) (hps : p ∉ small) :
    modulusCandidates Y small (hypotheticalClass a r p) (p*qf) =
      (effectiveSurvivors Y small a r qf p hHp).image (fun j => effectiveBase a r qf p hHp+p*qf*j) := by
  rw [modulusCandidates_eq_parent_image Y small (hypotheticalClass a r p) p qf hp hqp hq,
    effectiveSurvivors_eq_parent Y small a r qf hq p hp hqp hHp hps,
    effectiveBase_eq_sourceParentBase a r qf hq p hp hqp hHp]

theorem hypothetical_count_eq_effective_card (Y : ℕ) (small : Finset ℕ) (a : ℕ → ℕ) (r : ℚ)
    (qf : ℕ) (hq : Squarefree qf) (p : ℕ) [NeZero p] (hp : p.Prime)
    (hqp : qf.Coprime p) (hHp : (effectiveModulus a r qf).Coprime p) (hps : p ∉ small) :
    modulusCount Y small (hypotheticalClass a r p) (p*qf) =
      ((effectiveSurvivors Y small a r qf p hHp).card : ℤ) := by
  rw [modulusCount_eq_parent_card Y small (hypotheticalClass a r p) p qf hp hqp hq,
    effectiveSurvivors_eq_parent Y small a r qf hq p hp hqp hHp hps]

theorem actual_aligned_count_eq_effective_card (Y : ℕ) (small : Finset ℕ) (a : ℕ → ℕ) (r : ℚ)
    (qf : ℕ) (hq : Squarefree qf) (p : ℕ) [NeZero p] (hp : p.Prime)
    (hqp : qf.Coprime p) (hHp : (effectiveModulus a r qf).Coprime p) (hps : p ∉ small)
    (halign : aligns (fun t => (a t : ℤ)) r p) :
    modulusCount Y small a (p*qf) = ((effectiveSurvivors Y small a r qf p hHp).card : ℤ) := by
  rw [← hypothetical_count_agrees Y small a r (p*qf) p hp halign]
  exact hypothetical_count_eq_effective_card Y small a r qf hq p hp hqp hHp hps

theorem effective_length_error (Y : ℕ) (a : ℕ → ℕ) (r : ℚ) (qf : ℕ) (hq : Squarefree qf)
    (p : ℕ) [NeZero p] (hHp : (effectiveModulus a r qf).Coprime p) :
    |(hitLength Y (p*qf) (effectiveBase a r qf p hHp) : ℝ)-(Y : ℝ)/((p : ℝ)*qf)| ≤ 1 := by
  have hb := effective_initial_bounds a r qf hq p hHp
  simpa only [Nat.cast_mul] using hitLength_error Y (p*qf) (effectiveBase a r qf p hHp)
    (Nat.mul_pos (Nat.pos_of_ne_zero (NeZero.ne p)) (Nat.pos_of_ne_zero hq.ne_zero)) hb.1 hb.2

end ErdosVarianceEffective

end

end Erdos970

end OAI
