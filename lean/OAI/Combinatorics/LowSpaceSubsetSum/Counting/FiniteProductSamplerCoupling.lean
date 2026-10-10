import OAI.Combinatorics.LowSpaceSubsetSum.Storage.PermutationSamplerCoupling
import OAI.Combinatorics.LowSpaceSubsetSum.Counting.BalancedPartitions

namespace OAI

/-! # Finite arrays of bounded calls and permutation-generated partitions -/

noncomputable section

namespace LowSpaceSubsetSum

open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace SamplerCoupling

/-- Independent fresh seeds for a finite array of calls. Each coordinate may
have a different output type and a different number of internal attempts. -/
def pi : (k : ℕ) → (A : Fin k → Type) → [∀ i, Fintype (A i)] →
    (∀ i, SamplerCoupling (A i)) → SamplerCoupling (∀ i, A i)
  | 0, _, _, _ => SamplerCoupling.pure (fun i => Fin.elim0 i)
  | k + 1, A, _, S =>
      ((S 0).prod (pi k (fun i => A i.succ) (fun i => S i.succ))).map (Fin.consEquiv A)

theorem pi_uniform : ∀ (k : ℕ) (A : Fin k → Type) [∀ i, Fintype (A i)]
    [∀ i, Nonempty (A i)] (S : ∀ i, SamplerCoupling (A i)),
    (∀ i, (S i).idealLaw = FiniteLaw.uniform) →
    (pi k A S).idealLaw = FiniteLaw.uniform := by
  intro k
  induction k with
  | zero =>
    intro A _ _ S _
    exact pure_uniform _
  | succ k ih =>
    intro A _ _ S hS
    rw [pi, map_idealLaw, prod_uniform _ _ (hS 0)
      (ih (fun i => A i.succ) (fun i => S i.succ) (fun i => hS i.succ))]
    exact FiniteLaw.map_equiv_uniform (Fin.consEquiv A)

theorem pi_failure_le : ∀ (k : ℕ) (A : Fin k → Type) [∀ i, Fintype (A i)]
    (S : ∀ i, SamplerCoupling (A i)) (δ : Fin k → ℝ),
    (∀ i, (S i).failure ≤ δ i) → (pi k A S).failure ≤ ∑ i, δ i := by
  intro k
  induction k with
  | zero => intro A _ S δ _; simp [pi, pure_failure]
  | succ k ih =>
    intro A _ S δ hS
    rw [pi, map_failure, Fin.sum_univ_succ]
    exact (prod_failure_le _ _).trans (add_le_add (hS 0)
      (ih (fun i => A i.succ) (fun i => S i.succ) (fun i => δ i.succ)
        (fun i => hS i.succ)))

end SamplerCoupling

/-- A bounded choice from an explicitly enumerated finite set. This is used
only for the polynomial-size interval guesses and residue ranges. -/
def finiteChoiceCoupling (n : ℕ) (A : Type) [Fintype A] [Nonempty A] :
    SamplerCoupling A :=
  (finCoupling n (Fintype.card A)).map (Fintype.equivFin A).symm

theorem finiteChoiceCoupling_uniform (n : ℕ) (A : Type) [Fintype A] [Nonempty A] :
    (finiteChoiceCoupling n A).idealLaw = FiniteLaw.uniform := by
  rw [finiteChoiceCoupling, SamplerCoupling.map_idealLaw, finCoupling_uniform]
  exact FiniteLaw.map_equiv_uniform (Fintype.equivFin A).symm

theorem finiteChoiceCoupling_failure (n : ℕ) (A : Type) [Fintype A] [Nonempty A] :
    (finiteChoiceCoupling n A).failure ≤ 1 / (2 : ℝ) ^ (n ^ 3) := by
  rw [finiteChoiceCoupling, SamplerCoupling.map_failure]
  exact finCoupling_failure _ _

def finitePermutationCoupling (n : ℕ) (A : Type) [Fintype A] [DecidableEq A] :
    SamplerCoupling (Equiv.Perm A) :=
  (permutationCoupling n (Fintype.card A)).map
    (Equiv.permCongr (Fintype.equivFin A).symm)

theorem finitePermutationCoupling_uniform (n : ℕ) (A : Type)
    [Fintype A] [DecidableEq A] :
    (finitePermutationCoupling n A).idealLaw = FiniteLaw.uniform := by
  rw [finitePermutationCoupling, SamplerCoupling.map_idealLaw, permutationCoupling_uniform]
  exact FiniteLaw.map_equiv_uniform (Equiv.permCongr (Fintype.equivFin A).symm)

theorem finitePermutationCoupling_failure (n : ℕ) (A : Type)
    [Fintype A] [DecidableEq A] :
    (finitePermutationCoupling n A).failure ≤ Fintype.card A / (2 : ℝ) ^ (n ^ 3) := by
  rw [finitePermutationCoupling, SamplerCoupling.map_failure]
  exact permutationCoupling_failure _ _

/-- Fix one block labeling; a uniformly permuted labeling has the exact
uniform law on all labelings with these block sizes. -/
def coloringOfPermutation {A K : Type} [Fintype A] [Fintype K] [DecidableEq K]
    {t : K → ℕ} (f : MatchingSmoothing.Colorings A K t) (e : Equiv.Perm A) :
    MatchingSmoothing.Colorings A K t :=
  ⟨f.val ∘ e, (MatchingSmoothing.histogram_comp_perm _ _).trans f.property⟩

theorem coloringOfPermutation_uniform {A K : Type} [Fintype A] [DecidableEq A]
    [Fintype K] [DecidableEq K] {t : K → ℕ} (f : MatchingSmoothing.Colorings A K t) :
    (FiniteLaw.uniform : FiniteLaw (Equiv.Perm A)).map (coloringOfPermutation f) =
      @FiniteLaw.uniform (MatchingSmoothing.Colorings A K t) inferInstance ⟨f⟩ := by
  let : Nonempty (MatchingSmoothing.Colorings A K t) := ⟨f⟩
  have hf (g : MatchingSmoothing.Colorings A K t) :
      Fintype.card {e : Equiv.Perm A // coloringOfPermutation f e = g} =
        ∏ b, (t b).factorial := by
    let equiv : {e : Equiv.Perm A // coloringOfPermutation f e = g} ≃
        {e : Equiv.Perm A // f.val ∘ e = g.val} :=
      Equiv.subtypeEquivRight (fun _ => Subtype.ext_iff)
    rw [Fintype.card_congr equiv]
    have h := MatchingSmoothing.card_perm_color_fiber f.val
      (⟨g.val, g.property.trans f.property.symm⟩ :
        MatchingSmoothing.Colorings A K (MatchingSmoothing.histogram f.val))
    simpa only [f.property] using h
  apply FiniteLaw.eq_of_mass
  intro g
  change (FiniteLaw.uniform : FiniteLaw (Equiv.Perm A)).probability
    (fun e => coloringOfPermutation f e = g) = _
  rw [FiniteLaw.uniform_probability,
    finiteUniformProbability_map_of_constant_fibers (coloringOfPermutation f) hf (fun x => x = g)]
  rw [← FiniteLaw.uniform_probability, FiniteLaw.probability_eq]

def coloringCoupling (n : ℕ) {A K : Type} [Fintype A] [DecidableEq A]
    [Fintype K] [DecidableEq K] {t : K → ℕ} (f : MatchingSmoothing.Colorings A K t) :
    SamplerCoupling (MatchingSmoothing.Colorings A K t) :=
  (finitePermutationCoupling n A).map (coloringOfPermutation f)

theorem coloringCoupling_uniform (n : ℕ) {A K : Type} [Fintype A] [DecidableEq A]
    [Fintype K] [DecidableEq K] {t : K → ℕ} (f : MatchingSmoothing.Colorings A K t) :
    (coloringCoupling n f).idealLaw =
      @FiniteLaw.uniform (MatchingSmoothing.Colorings A K t) inferInstance ⟨f⟩ := by
  rw [coloringCoupling, SamplerCoupling.map_idealLaw, finitePermutationCoupling_uniform]
  exact coloringOfPermutation_uniform f

theorem coloringCoupling_failure (n : ℕ) {A K : Type} [Fintype A] [DecidableEq A]
    [Fintype K] [DecidableEq K] {t : K → ℕ} (f : MatchingSmoothing.Colorings A K t) :
    (coloringCoupling n f).failure ≤ Fintype.card A / (2 : ℝ) ^ (n ^ 3) := by
  rw [coloringCoupling, SamplerCoupling.map_failure]
  exact finitePermutationCoupling_failure _ _

end LowSpaceSubsetSum

end

end OAI
