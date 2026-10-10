import OAI.Combinatorics.LowSpaceSubsetSum.Counting.RejectionSamplerCoupling
import OAI.Combinatorics.LowSpaceSubsetSum.Storage.PermutationSampling
import Mathlib.GroupTheory.Perm.Fin

namespace OAI

/-! # Successive bounded uniform choices for permutations and fixed-size subsets -/

noncomputable section

namespace LowSpaceSubsetSum

open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace FiniteLaw

theorem uniform_bind_const {α β : Type} [Fintype α] [Fintype β]
    [Nonempty α] [Nonempty β] :
    (FiniteLaw.uniform : FiniteLaw α).bind (fun _ => β)
      (fun _ => FiniteLaw.uniform) =
      @FiniteLaw.uniform (Σ _ : α, β) inferInstance
        ⟨⟨Classical.choice inferInstance, Classical.choice inferInstance⟩⟩ := by
  apply eq_of_mass
  intro x
  simp [bind, uniform, Fintype.card_sigma, mul_comm]

end FiniteLaw

namespace SamplerCoupling

variable {α β : Type} [Fintype α] [Fintype β]

theorem pure_failure (a : α) : (SamplerCoupling.pure a).failure = 0 := by
  simp [failure, pure, FiniteLaw.probability]

theorem pure_uniform [Unique α] (a : α) :
    (SamplerCoupling.pure a).idealLaw = FiniteLaw.uniform := by
  apply FiniteLaw.eq_of_mass
  intro b
  have h : a = b := Subsingleton.elim _ _
  simp [idealLaw, FiniteLaw.map, pure, FiniteLaw.probability, FiniteLaw.uniform, h]
  exact Fintype.card_unique

theorem bind_idealLaw (S : SamplerCoupling α) (β : α → Type)
    [∀ a, Fintype (β a)] (T : ∀ a, SamplerCoupling (β a)) :
    (S.bind β T).idealLaw = S.idealLaw.bind β (fun a => (T a).idealLaw) := by
  apply FiniteLaw.eq_of_mass
  intro x
  rw [← FiniteLaw.probability_eq, ← FiniteLaw.probability_eq]
  exact bind_ideal_probability S β T (fun a => a = x)

def prod (S : SamplerCoupling α) (T : SamplerCoupling β) : SamplerCoupling (α × β) :=
  (S.bind (fun _ => β) (fun _ => T)).map (Equiv.sigmaEquivProd α β)

theorem prod_uniform [Nonempty α] [Nonempty β]
    (S : SamplerCoupling α) (T : SamplerCoupling β)
    (hS : S.idealLaw = FiniteLaw.uniform) (hT : T.idealLaw = FiniteLaw.uniform) :
    (S.prod T).idealLaw = FiniteLaw.uniform := by
  let : Nonempty (Σ _ : α, β) :=
    ⟨⟨Classical.choice inferInstance, Classical.choice inferInstance⟩⟩
  rw [prod, map_idealLaw, bind_idealLaw, hS, hT, FiniteLaw.uniform_bind_const]
  exact FiniteLaw.map_equiv_uniform (Equiv.sigmaEquivProd α β)

theorem prod_failure_le (S : SamplerCoupling α) (T : SamplerCoupling β) :
    (S.prod T).failure ≤ S.failure + T.failure := by
  rw [prod, map_failure]
  exact bind_failure_le S (fun _ => β) (fun _ => T) T.failure (fun _ => le_rfl)

end SamplerCoupling

/-- Range one is returned directly. Every other range uses exactly the
fresh low-bit candidate sampler with at most `n³` attempts. -/
def finCoupling (n D : ℕ) [NeZero D] : SamplerCoupling (Fin D) :=
  if h : 1 < D then rangeCoupling h n
  else SamplerCoupling.pure ⟨0, Nat.pos_of_ne_zero (NeZero.ne D)⟩

theorem finCoupling_uniform (n D : ℕ) [NeZero D] :
    (finCoupling n D).idealLaw = FiniteLaw.uniform := by
  by_cases h : 1 < D
  · simpa only [finCoupling, dite_eq_left h] using rangeCoupling_uniform h n
  · have hD : D = 1 := by have := NeZero.ne D; omega
    subst D
    simp only [finCoupling, dite_eq_right (by omega : ¬1 < 1)]
    exact SamplerCoupling.pure_uniform _

theorem finCoupling_failure (n D : ℕ) [NeZero D] :
    (finCoupling n D).failure ≤ 1 / (2 : ℝ) ^ (n ^ 3) := by
  by_cases h : 1 < D
  · simpa only [finCoupling, dite_eq_left h] using rangeCoupling_failure h n
  · simp only [finCoupling, dite_eq_right h, SamplerCoupling.pure_failure]
    positivity

/-- Insert one uniformly chosen location, then permute the remaining locations.
The insertion bijection is Mathlib's explicit swap-based permutation code. -/
def permutationCoupling (n : ℕ) : (k : ℕ) → SamplerCoupling (Equiv.Perm (Fin k))
  | 0 => SamplerCoupling.pure (Equiv.refl _)
  | k + 1 => ((finCoupling n (k + 1)).prod (permutationCoupling n k)).map
      Equiv.Perm.decomposeFin.symm

theorem permutationCoupling_uniform (n k : ℕ) :
    (permutationCoupling n k).idealLaw = FiniteLaw.uniform := by
  induction k with
  | zero => exact SamplerCoupling.pure_uniform _
  | succ k ih =>
    rw [permutationCoupling, SamplerCoupling.map_idealLaw,
      SamplerCoupling.prod_uniform _ _ (finCoupling_uniform n (k + 1)) ih]
    exact FiniteLaw.map_equiv_uniform Equiv.Perm.decomposeFin.symm

theorem permutationCoupling_failure (n k : ℕ) :
    (permutationCoupling n k).failure ≤ k / (2 : ℝ) ^ (n ^ 3) := by
  induction k with
  | zero => simp [permutationCoupling, SamplerCoupling.pure_failure]
  | succ k ih =>
    rw [permutationCoupling, SamplerCoupling.map_failure]
    calc
      _ ≤ (finCoupling n (k + 1)).failure + (permutationCoupling n k).failure :=
        SamplerCoupling.prod_failure_le _ _
      _ ≤ 1 / (2 : ℝ) ^ (n ^ 3) + k / (2 : ℝ) ^ (n ^ 3) :=
        add_le_add (finCoupling_failure n (k + 1)) ih
      _ = (k + 1 : ℕ) / (2 : ℝ) ^ (n ^ 3) := by push_cast; ring

def subsetCoupling (n k : ℕ) (K : Finset (Fin k)) :
    SamplerCoupling ↥((Finset.univ : Finset (Fin k)).powersetCard K.card) :=
  (permutationCoupling n k).map (permutationBlock K)

theorem subsetCoupling_uniform (n k : ℕ) (K : Finset (Fin k)) :
    (subsetCoupling n k K).idealLaw =
      @FiniteLaw.uniform _ inferInstance
        ⟨⟨K, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, rfl⟩⟩⟩ := by
  apply FiniteLaw.eq_of_mass
  intro T
  rw [subsetCoupling, SamplerCoupling.map_idealLaw, permutationCoupling_uniform]
  change (FiniteLaw.uniform : FiniteLaw (Equiv.Perm (Fin k))).probability
    (fun e => permutationBlock K e = T) = _
  rw [FiniteLaw.uniform_probability]
  have h := permutationBlock_uniform K (fun S => S = T.val)
  have hv : (fun S : ↥((Finset.univ : Finset (Fin k)).powersetCard K.card) =>
      S.val = T.val) = (fun S => S = T) := by
    funext S
    exact propext Subtype.ext_iff.symm
  rw [hv] at h
  have hr : finiteUniformProbability
      (fun S : ↥((Finset.univ : Finset (Fin k)).powersetCard K.card) => S = T) =
      1 / Fintype.card ↥((Finset.univ : Finset (Fin k)).powersetCard K.card) := by
    let : Nonempty ↥((Finset.univ : Finset (Fin k)).powersetCard K.card) := ⟨T⟩
    rw [← FiniteLaw.uniform_probability, FiniteLaw.probability_eq]
    rfl
  rw [hr] at h
  simpa only [permutationBlock, Subtype.ext_iff, FiniteLaw.uniform] using h

theorem subsetCoupling_failure (n k : ℕ) (K : Finset (Fin k)) :
    (subsetCoupling n k K).failure ≤ k / (2 : ℝ) ^ (n ^ 3) := by
  rw [subsetCoupling, SamplerCoupling.map_failure]
  exact permutationCoupling_failure n k

end LowSpaceSubsetSum

end

end OAI
