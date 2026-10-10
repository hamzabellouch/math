import OAI.Analysis.IrrationalRotation.Model.OperatorProperties
import Mathlib.Algebra.Star.UnitaryStarAlgAut
import Mathlib.Algebra.Star.StarProjection
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Tactic

namespace OAI

noncomputable section
open scoped InnerProductSpace ComplexOrder
namespace Invariant233.ProjectionAtomOrbit

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

theorem mul_eq_zero_of_atoms
    (hab : ∀ A ∈ M, ∀ B ∈ M, Commute A B)
    {p q : H →L[ℂ] H} (hp : IsProjectionAtom M p) (hq : IsProjectionAtom M q)
    (hne : p ≠ q) : p * q = 0 := by
  have hc := hab p hp.1 q hq.1
  have hproj : IsStarProjection (p * q) := hp.2.1.mul hq.2.1 hc
  have hmem : p * q ∈ M := mul_mem hp.1 hq.1
  have hpp : (p * q) * p = p * q := by
    calc
      (p * q) * p = p * (q * p) := mul_assoc _ _ _
      _ = p * (p * q) := by rw [hc.eq]
      _ = p * q := by rw [← mul_assoc, hp.2.1.isIdempotentElem.eq]
  have hpq : (p * q) * q = p * q := by
    rw [mul_assoc, hq.2.1.isIdempotentElem.eq]
  rcases hp.2.2.2 (p * q) hmem hproj hpp with hz | hp'
  · exact hz
  rcases hq.2.2.2 (p * q) hmem hproj hpq with hz | hq'
  · exact hz
  exact (hne (hp'.symm.trans hq')).elim

theorem sum_atoms_isStarProjection
    (hab : ∀ A ∈ M, ∀ B ∈ M, Commute A B)
    (s : Finset (H →L[ℂ] H)) (hs : ∀ p ∈ s, IsProjectionAtom M p) :
    IsStarProjection (∑ p ∈ s, p) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert p s hp ih =>
    rw [Finset.sum_insert hp]
    apply (hs p (Finset.mem_insert_self p s)).2.1.add
      (ih fun q hq => hs q (Finset.mem_insert_of_mem hq))
    rw [Finset.mul_sum]
    apply Finset.sum_eq_zero
    intro q hq
    exact mul_eq_zero_of_atoms hab (hs p (Finset.mem_insert_self p s))
      (hs q (Finset.mem_insert_of_mem hq)) (fun he => hp (he ▸ hq))

theorem vectorTrace_le_norm_sq (ξ : H) {p : H →L[ℂ] H} (hp : IsStarProjection p) :
    (vectorTrace ξ p).re ≤ ‖ξ‖ ^ 2 := by
  have h := (ContinuousLinearMap.IsPositive.of_isStarProjection hp.one_sub).re_inner_nonneg_right ξ
  change 0 ≤ (inner ℂ ξ ((1 - p) ξ)).re at h
  simp only [sub_apply, one_apply_eq_self, inner_sub_right,
    inner_self_eq_norm_sq_to_K] at h
  norm_num at h
  simpa only [← Complex.ofReal_pow, Complex.ofReal_re, vectorTrace] using h

theorem sum_vectorTrace_atoms_le (ξ : H)
    (hab : ∀ A ∈ M, ∀ B ∈ M, Commute A B)
    (s : Finset (H →L[ℂ] H)) (hs : ∀ p ∈ s, IsProjectionAtom M p) :
    (∑ p ∈ s, (vectorTrace ξ p).re) ≤ ‖ξ‖ ^ 2 := by
  have h := vectorTrace_le_norm_sq ξ (sum_atoms_isStarProjection hab s hs)
  simpa [vectorTrace, sum_apply, inner_sum] using h

theorem finite_atoms_vectorTrace_ge (ξ : H)
    (hab : ∀ A ∈ M, ∀ B ∈ M, Commute A B)
    {δ : ℝ} (hδ : 0 < δ) :
    {p : H →L[ℂ] H | IsProjectionAtom M p ∧ δ ≤ (vectorTrace ξ p).re}.Finite := by
  classical
  by_contra hfin
  have hinf : Set.Infinite {p : H →L[ℂ] H |
      IsProjectionAtom M p ∧ δ ≤ (vectorTrace ξ p).re} := hfin
  obtain ⟨n, hn⟩ := exists_nat_gt (‖ξ‖ ^ 2 / δ)
  obtain ⟨s, hs, hcard⟩ := hinf.exists_subset_card_eq n
  have hlo : (n : ℝ) * δ ≤ ∑ p ∈ s, (vectorTrace ξ p).re := by
    calc
      (n : ℝ) * δ = ∑ _p ∈ s, δ := by simp [hcard]
      _ ≤ _ := Finset.sum_le_sum fun p hp => (hs hp).2
  have hhi := sum_vectorTrace_atoms_le ξ hab s (fun p hp => (hs hp).1)
  have hlarge : ‖ξ‖ ^ 2 < (n : ℝ) * δ := (div_lt_iff₀ hδ).mp hn
  linarith

theorem atom_map (Φ : (H →L[ℂ] H) ≃⋆ₐ[ℂ] (H →L[ℂ] H))
    (hM : ∀ A, Φ A ∈ M ↔ A ∈ M)
    {p : H →L[ℂ] H} (hp : IsProjectionAtom M p) :
    IsProjectionAtom M (Φ p) := by
  refine ⟨(hM p).mpr hp.1, hp.2.1.map Φ, ?_, ?_⟩
  · intro hz
    apply hp.2.2.1
    apply Φ.injective
    simpa using hz
  · intro q hq hproj hqp
    have hqm : Φ.symm q ∈ M := (hM _).mp (by simpa using hq)
    have hle : Φ.symm q * p = Φ.symm q := by
      apply Φ.injective
      change Φ (Φ.symm q * p) = Φ (Φ.symm q)
      rw [map_mul]
      simpa only [StarAlgEquiv.apply_symm_apply] using hqp
    rcases hp.2.2.2 (Φ.symm q) hqm (hproj.map Φ.symm) hle with hz | he
    · left
      simpa using congrArg Φ hz
    · right
      simpa using congrArg Φ he

theorem atom_iterate (Φ : (H →L[ℂ] H) ≃⋆ₐ[ℂ] (H →L[ℂ] H))
    (hM : ∀ A, Φ A ∈ M ↔ A ∈ M)
    {p : H →L[ℂ] H} (hp : IsProjectionAtom M p) (n : ℕ) :
    IsProjectionAtom M ((Φ : (H →L[ℂ] H) → (H →L[ℂ] H))^[n] p) := by
  induction n with
  | zero => exact hp
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact atom_map Φ hM ih

theorem finite_atom_orbit (ξ : H)
    (hab : ∀ A ∈ M, ∀ B ∈ M, Commute A B)
    (Φ : (H →L[ℂ] H) ≃⋆ₐ[ℂ] (H →L[ℂ] H))
    (hM : ∀ A, Φ A ∈ M ↔ A ∈ M)
    (htrace : ∀ A ∈ M, vectorTrace ξ (Φ A) = vectorTrace ξ A)
    {p : H →L[ℂ] H} (hp : IsProjectionAtom M p)
    (hpos : 0 < (vectorTrace ξ p).re) :
    (Set.range fun n : ℕ => (Φ : (H →L[ℂ] H) → (H →L[ℂ] H))^[n] p).Finite := by
  have hm : ∀ n : ℕ,
      vectorTrace ξ ((Φ : (H →L[ℂ] H) → (H →L[ℂ] H))^[n] p) = vectorTrace ξ p := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [Function.iterate_succ_apply', htrace _ (atom_iterate Φ hM hp n).1, ih]
  apply (finite_atoms_vectorTrace_ge ξ hab hpos).subset
  rintro A ⟨n, rfl⟩
  exact ⟨atom_iterate Φ hM hp n, (congrArg Complex.re (hm n)).ge⟩

theorem exists_positive_atom_period (ξ : H)
    (hab : ∀ A ∈ M, ∀ B ∈ M, Commute A B)
    (Φ : (H →L[ℂ] H) ≃⋆ₐ[ℂ] (H →L[ℂ] H))
    (hM : ∀ A, Φ A ∈ M ↔ A ∈ M)
    (htrace : ∀ A ∈ M, vectorTrace ξ (Φ A) = vectorTrace ξ A)
    {p : H →L[ℂ] H} (hp : IsProjectionAtom M p)
    (hpos : 0 < (vectorTrace ξ p).re) :
    ∃ n : ℕ, 0 < n ∧ (Φ : (H →L[ℂ] H) → (H →L[ℂ] H))^[n] p = p := by
  have hfin := finite_atom_orbit ξ hab Φ hM htrace hp hpos
  have hnot : ¬ Function.Injective
      (fun n : ℕ => (Φ : (H →L[ℂ] H) → (H →L[ℂ] H))^[n] p) := by
    intro hinj
    exact (Set.infinite_range_of_injective hinj) hfin
  simp only [Function.Injective, not_forall] at hnot
  obtain ⟨m, n, heq, hne⟩ := hnot
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact ⟨n - m, Nat.sub_pos_of_lt hlt, Function.iterate_cancel Φ.injective heq.symm⟩
  · exact ⟨m - n, Nat.sub_pos_of_lt hlt, Function.iterate_cancel Φ.injective heq⟩

theorem vectorTrace_pos_of_faithful (ξ : H)
    (hξ : IsFaithfulTracialVector M ξ)
    {p : H →L[ℂ] H} (hp : p ∈ M) (hproj : IsStarProjection p) (hne : p ≠ 0) :
    0 < (vectorTrace ξ p).re := by
  have hpositive := ContinuousLinearMap.IsPositive.of_isStarProjection hproj
  have hnonneg : 0 ≤ vectorTrace ξ p := hpositive.inner_nonneg_right ξ
  have hparts := Complex.nonneg_iff.mp hnonneg
  by_contra h
  apply hne
  apply hξ.2.2 p hp hpositive
  apply Complex.ext
  · exact le_antisymm (not_lt.mp h) hparts.1
  · exact hparts.2.symm

theorem isDiffuse_of_total_ergodicity (ξ : H)
    (hab : ∀ A ∈ M, ∀ B ∈ M, Commute A B)
    (hξ : IsFaithfulTracialVector M ξ)
    (Φ : (H →L[ℂ] H) ≃⋆ₐ[ℂ] (H →L[ℂ] H))
    (hM : ∀ A, Φ A ∈ M ↔ A ∈ M)
    (htrace : ∀ A ∈ M, vectorTrace ξ (Φ A) = vectorTrace ξ A)
    (htotal : ∀ n : ℕ, 0 < n → ∀ p : H →L[ℂ] H,
      p ∈ M → IsStarProjection p →
      (Φ : (H →L[ℂ] H) → (H →L[ℂ] H))^[n] p = p → p = 0 ∨ p = 1)
    (hnontrivial : ∃ q : H →L[ℂ] H,
      q ∈ M ∧ IsStarProjection q ∧ q ≠ 0 ∧ q ≠ 1) :
    IsDiffuseVonNeumannAlgebra M := by
  intro p hp
  have hpos := vectorTrace_pos_of_faithful ξ hξ hp.1 hp.2.1 hp.2.2.1
  obtain ⟨n, hn, hperiod⟩ := exists_positive_atom_period ξ hab Φ hM htrace hp hpos
  have hp1 : p = 1 := (htotal n hn p hp.1 hp.2.1 hperiod).resolve_left hp.2.2.1
  obtain ⟨q, hq, hqproj, hq0, hq1⟩ := hnontrivial
  rcases hp.2.2.2 q hq hqproj (by rw [hp1, mul_one]) with hz | he
  · exact hq0 hz
  · exact hq1 (he.trans hp1)

theorem faithfulTracialVector_restrict {N : VonNeumannAlgebra H}
    (hMN : M ≤ N) (ξ : H) (hξ : IsFaithfulTracialVector N ξ) :
    IsFaithfulTracialVector M ξ := by
  exact ⟨hξ.1, fun A B hA hB => hξ.2.1 A B (hMN hA) (hMN hB),
    fun A hA hpos hz => hξ.2.2 A (hMN hA) hpos hz⟩

theorem vectorTrace_unitary_conjugation {N : VonNeumannAlgebra H}
    (ξ : H) (hξ : IsFaithfulTracialVector N ξ)
    (U : unitary (H →L[ℂ] H)) (hU : (U : H →L[ℂ] H) ∈ N)
    {A : H →L[ℂ] H} (hA : A ∈ N) :
    vectorTrace ξ (Unitary.conjStarAlgAut ℂ (H →L[ℂ] H) U A) = vectorTrace ξ A := by
  rw [Unitary.conjStarAlgAut_apply]
  rw [hξ.2.1 ((U : H →L[ℂ] H) * A) (star (U : H →L[ℂ] H))
    (mul_mem hU hA) (star_mem hU)]
  rw [← mul_assoc, (Unitary.mem_iff.mp U.property).1, one_mul]

end Invariant233.ProjectionAtomOrbit

end

end OAI
