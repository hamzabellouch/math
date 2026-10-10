import OAI.Computability.PerfectCompleteness.Decoding.RepresentativeBucketCollisionLemmas
import OAI.Computability.PerfectCompleteness.Foundations.PartitionsLemmas
import OAI.Computability.PerfectCompleteness.Sampling.FiniteListSampling
import OAI.Computability.UniqueGames.Foundations.SamplingLemmas

namespace OAI


namespace PerfectCompleteness.LeftDecoder

open scoped BigOperators Classical
open UniqueGamesTheorem.Foundations.Games
open ClauseSupport MixedSupport

abbrev F2 := ZMod 2

noncomputable section

section Affine

variable {V : Type*} [AddCommGroup V] [Module F2 V] [FiniteDimensional F2 V]

local instance dualFintype : Fintype (Module.Dual F2 V) :=
  Fintype.ofEquiv (Fin (Module.finrank F2 (Module.Dual F2 V)) → F2)
    (Module.finBasis F2 (Module.Dual F2 V)).equivFun.toEquiv.symm

def affineLaw (W : Submodule F2 V)
    (C : Submodule F2 (Module.Dual F2 (V ⧸ W))) (center : Module.Dual F2 V) :
    FiniteDistribution (Module.Dual F2 V) :=
  (FiniteDistribution.uniform (PulledColumnSpace.Candidates W C center)).pushforward Subtype.val

theorem affineLaw_probability (W : Submodule F2 V)
    (C : Submodule F2 (Module.Dual F2 (V ⧸ W))) (center : Module.Dual F2 V)
    (event : Module.Dual F2 V → Bool) :
    (affineLaw W C center).probability event =
      (FiniteDistribution.uniform (PulledColumnSpace.Candidates W C center)).probability
        (fun q => event q.val) :=
  FiniteDistribution.probability_pushforward _ _ _

theorem affineLaw_probability_eq_one (W : Submodule F2 V)
    (C : Submodule F2 (Module.Dual F2 (V ⧸ W))) (center : Module.Dual F2 V)
    (event : Module.Dual F2 V → Bool)
    (hevent : ∀ q : PulledColumnSpace.Candidates W C center, event q.val = true) :
    (affineLaw W C center).probability event = 1 := by
  rw [affineLaw_probability]
  have heq : (fun q : PulledColumnSpace.Candidates W C center => event q.val) =
      fun _ => true := funext hevent
  rw [heq, FiniteDistribution.probability_true]

theorem affineLaw_weight (W : Submodule F2 V)
    (C : Submodule F2 (Module.Dual F2 (V ⧸ W))) (center q : Module.Dual F2 V) :
    (affineLaw W C center).weight q =
      if q - center ∈ PulledColumnSpace.pulled W C then
        1 / (2 : ℝ) ^ Module.finrank F2 C else 0 := by
  have hweight : (affineLaw W C center).weight q =
      if q - center ∈ PulledColumnSpace.pulled W C then
        1 / (Fintype.card (PulledColumnSpace.Candidates W C center) : ℝ) else 0 := by
    let : Fintype {p : Module.Dual F2 V // p - center ∈ PulledColumnSpace.pulled W C} :=
      PulledColumnSpace.candidatesFintype W C center
    change (∑ p : {p : Module.Dual F2 V // p - center ∈ PulledColumnSpace.pulled W C},
      if p.val = q then
        1 / (Fintype.card (PulledColumnSpace.Candidates W C center) : ℝ) else 0) = _
    by_cases hq : q - center ∈ PulledColumnSpace.pulled W C
    · rw [ite_eq_left hq, Finset.sum_eq_single
        (⟨q, hq⟩ : {p : Module.Dual F2 V // p - center ∈ PulledColumnSpace.pulled W C})]
      · simp
      · intro p _ hp
        have hne : p.val ≠ q := fun heq => hp (Subtype.ext heq)
        simp [hne]
      · simp
    · rw [ite_eq_right hq]
      apply Finset.sum_eq_zero
      intro p _
      have hne : p.val ≠ q := fun heq => hq (heq ▸ p.property)
      simp [hne]
  simpa only [PulledColumnSpace.fintype_card_candidates, Nat.cast_pow, Nat.cast_ofNat]
    using hweight

theorem affineLaw_support (W : Submodule F2 V)
    (C : Submodule F2 (Module.Dual F2 (V ⧸ W))) (center : Module.Dual F2 V) :
    (affineLaw W C center).probability
      (fun q => decide (q - center ∈ PulledColumnSpace.pulled W C)) = 1 := by
  rw [affineLaw_probability]
  have hevent : (fun q : PulledColumnSpace.Candidates W C center =>
      decide (q.val - center ∈ PulledColumnSpace.pulled W C)) = fun _ => true := by
    funext q
    exact decide_eq_true q.property
  rw [hevent, FiniteDistribution.probability_true]

theorem affineLaw_success_lower (W : Submodule F2 V)
    (C : Submodule F2 (Module.Dual F2 (V ⧸ W))) (center : Module.Dual F2 V)
    {r : Nat} (hC : Module.finrank F2 C ≤ r) (event : Module.Dual F2 V → Bool)
    (witness : ∃ q : PulledColumnSpace.Candidates W C center, event q.val = true) :
    1 / (2 : ℝ) ^ r ≤ (affineLaw W C center).probability event := by
  obtain ⟨q, hq⟩ := witness
  have hweight := FiniteListSampling.probability_ge_weight
    (affineLaw W C center) event q.val hq
  rw [affineLaw_weight, ite_eq_left q.property] at hweight
  exact (one_div_le_one_div_of_le (pow_pos (by norm_num : (0 : ℝ) < 2) _)
    (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hC)).trans hweight

end Affine


attribute [local instance] UniqueGamesTheorem.Appendix.RankLevelFilter.linearMapFintype

variable {n : Nat} {K Z : Type*} [AddCommGroup K] [Module F2 K]
  (slots : Fin n → Slot) (H : Submodule F2 (Assignment slots → F2))
  (other : Assignment slots → Z) (labeling : KeyStrategy.Strategy n)
  (W : Submodule F2 H) (s : (H ⧸ W) →ₗ[F2] H)
  (hs : W.mkQ.comp s = LinearMap.id)
  [FiniteDimensional F2 H] [FiniteDimensional F2 K]
  [Fintype H] [Fintype K] [Fintype Z]
  (useful : (Module.Dual F2 (H ⧸ W) →ₗ[F2] K) → Prop)
  {r : Nat} {ρ : ℝ} {A : ManyGoodRows.RowMap K r}
  {U : Module.Dual F2 (H ⧸ W) →ₗ[F2] (Fin r → F2)}

local instance representativeDualFintype : Fintype (Module.Dual F2 H) :=
  dualFintype (V := H)

def center (w : DenseWitnessRealization.RepresentativeWitness
    slots H other labeling W s useful (r := r) (ρ := ρ) (A := A) (U := U)) :
    Module.Dual F2 H :=
  RepresentativeMatrixTable.correctionFunctional slots H other W s hs w.value.2

def law (w : DenseWitnessRealization.RepresentativeWitness
    slots H other labeling W s useful (r := r) (ρ := ρ) (A := A) (U := U)) :
    FiniteDistribution (Module.Dual F2 H) :=
  affineLaw W w.columnSpace (center slots H other labeling W s hs useful w)

omit [FiniteDimensional F2 K] [Fintype Z]

theorem law_weight (w : DenseWitnessRealization.RepresentativeWitness
    slots H other labeling W s useful (r := r) (ρ := ρ) (A := A) (U := U))
    (q : Module.Dual F2 H) :
    (law slots H other labeling W s hs useful w).weight q =
      if q - center slots H other labeling W s hs useful w ∈
          PulledColumnSpace.pulled W w.columnSpace then
        1 / (2 : ℝ) ^ Module.finrank F2 w.columnSpace else 0 :=
  affineLaw_weight W w.columnSpace _ q

theorem law_support (w : DenseWitnessRealization.RepresentativeWitness
    slots H other labeling W s useful (r := r) (ρ := ρ) (A := A) (U := U)) :
    (law slots H other labeling W s hs useful w).probability
      (fun q => decide (q - center slots H other labeling W s hs useful w ∈
        PulledColumnSpace.pulled W w.columnSpace)) = 1 :=
  affineLaw_support W w.columnSpace _

omit [FiniteDimensional F2 H] in
theorem exists_candidate_realizer
    (hW : RepresentativeMatrixTable.Determined slots H other W)
    (w : DenseWitnessRealization.RepresentativeWitness
      slots H other labeling W s useful (r := r) (ρ := ρ) (A := A) (U := U))
    (hρ : 0 < ρ) :
    ∃ x : Assignment slots, other x = w.value.2 ∧
      ∀ q : PulledColumnSpace.Candidates W w.columnSpace
        (center slots H other labeling W s hs useful w),
      ∀ b : W, q.val (b : H) = b.val.val x := by
  obtain ⟨X, _, x, hx, hknown⟩ := DenseWitnessRealization.exists_coset_realizer
    slots H other labeling W s useful hs hW w hρ
    (PulledColumnSpace.pulled W w.columnSpace)
    (PulledColumnSpace.pulled_le_annihilator W w.columnSpace)
  refine ⟨x, congrArg Prod.snd hx, ?_⟩
  intro q b
  rw [PulledColumnSpace.candidate_apply_known]
  simpa only [center, Submodule.coe_zero, add_zero] using hknown 0 b

omit [FiniteDimensional F2 H] in
theorem candidate_one (hW : RepresentativeMatrixTable.Determined slots H other W)
    (w : DenseWitnessRealization.RepresentativeWitness
      slots H other labeling W s useful (r := r) (ρ := ρ) (A := A) (U := U))
    (hρ : 0 < ρ) (b : W) (hb : b.val.val = (1 : Assignment slots → F2))
    (q : PulledColumnSpace.Candidates W w.columnSpace
      (center slots H other labeling W s hs useful w)) : q.val (b : H) = 1 := by
  obtain ⟨x, _, hknown⟩ :=
    exists_candidate_realizer slots H other labeling W s hs useful hW w hρ
  rw [hknown q b, hb]
  rfl

theorem law_normalized_on_one
    (hW : RepresentativeMatrixTable.Determined slots H other W)
    (w : DenseWitnessRealization.RepresentativeWitness
      slots H other labeling W s useful (r := r) (ρ := ρ) (A := A) (U := U))
    (hρ : 0 < ρ) (b : W) (hb : b.val.val = (1 : Assignment slots → F2)) :
    (law slots H other labeling W s hs useful w).probability
      (fun q => decide (q (b : H) = 1)) = 1 := by
  rw [law, affineLaw_probability]
  have hevent : (fun q : PulledColumnSpace.Candidates W w.columnSpace
      (center slots H other labeling W s hs useful w) => decide (q.val (b : H) = 1)) =
      fun _ => true := by
    funext q
    exact decide_eq_true (candidate_one slots H other labeling W s hs useful hW w hρ b hb q)
  rw [hevent, FiniteDistribution.probability_true]

theorem success_lower (w : DenseWitnessRealization.RepresentativeWitness
    slots H other labeling W s useful (r := r) (ρ := ρ) (A := A) (U := U))
    (event : Module.Dual F2 H → Bool)
    (witness : ∃ q : PulledColumnSpace.Candidates W w.columnSpace
      (center slots H other labeling W s hs useful w), event q.val = true) :
    1 / (2 : ℝ) ^ r ≤
      (law slots H other labeling W s hs useful w).probability event :=
  affineLaw_success_lower W w.columnSpace _ w.column_count event witness

def adviceLaw (r : Nat) (ρ : ℝ) (A : ManyGoodRows.RowMap K r)
    (U : Module.Dual F2 (H ⧸ W) →ₗ[F2] (Fin r → F2)) :
    FiniteDistribution (Module.Dual F2 H) :=
  if hgood : ManyGoodRows.GoodRow
      (RepresentativeMatrixTable.partialTable slots H other labeling W s useful) r ρ A U then
    law slots H other labeling W s hs useful
      (ManyGoodRows.selectWitness
        (RepresentativeMatrixTable.partialTable slots H other labeling W s useful) r ρ A U hgood)
  else
    affineLaw W ⊥ (RepresentativeMatrixTable.correctionFunctional slots H other W s hs
      (CanonicalMatrixTable.response slots H other labeling (0 : CanonicalMatrixTable.Matrix
        (K := K) slots H)).2)

theorem adviceLaw_of_good (r : Nat) (ρ : ℝ) (A : ManyGoodRows.RowMap K r)
    (U : Module.Dual F2 (H ⧸ W) →ₗ[F2] (Fin r → F2))
    (hgood : ManyGoodRows.GoodRow
      (RepresentativeMatrixTable.partialTable slots H other labeling W s useful) r ρ A U) :
    adviceLaw slots H other labeling W s hs useful r ρ A U =
      law slots H other labeling W s hs useful
        (ManyGoodRows.selectWitness
          (RepresentativeMatrixTable.partialTable slots H other labeling W s useful)
          r ρ A U hgood) := by
  simp only [adviceLaw, dite_eq_left hgood]

theorem adviceLaw_normalized_on_one
    (hW : RepresentativeMatrixTable.Determined slots H other W)
    (r : Nat) (ρ : ℝ) (hρ : 0 < ρ) (A : ManyGoodRows.RowMap K r)
    (U : Module.Dual F2 (H ⧸ W) →ₗ[F2] (Fin r → F2))
    (b : W) (hb : b.val.val = (1 : Assignment slots → F2)) :
    (adviceLaw slots H other labeling W s hs useful r ρ A U).probability
      (fun q => decide (q (b : H) = 1)) = 1 := by
  by_cases hgood : ManyGoodRows.GoodRow
      (RepresentativeMatrixTable.partialTable slots H other labeling W s useful) r ρ A U
  · rw [adviceLaw_of_good slots H other labeling W s hs useful r ρ A U hgood]
    exact law_normalized_on_one slots H other labeling W s hs useful hW _ hρ b hb
  · simp only [adviceLaw, dite_eq_right hgood]
    apply affineLaw_probability_eq_one
    intro q
    apply decide_eq_true
    rw [PulledColumnSpace.candidate_apply_known]
    obtain ⟨x, _, hx⟩ := CanonicalMatrixTable.response_realized slots H other labeling
      (0 : CanonicalMatrixTable.Matrix (K := K) slots H)
    rw [← hx]
    simpa only [add_zero] using RepresentativeDecoder.coset_one_at_image
      slots H other W s hs hW x 0 W.dualAnnihilator.zero_mem b hb


end

end PerfectCompleteness.LeftDecoder

end OAI
