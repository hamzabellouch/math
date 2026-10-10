import OAI.Combinatorics.LowSpaceSubsetSum.Separators.SeparatorFamilies
import Mathlib.Logic.Equiv.Basic
import Mathlib.Logic.Equiv.Set
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Perm

namespace OAI

/-!
# Actual permutation sampling has uniform fixed-size block marginals

The seven compressed blocks and the mixer blocks need only marginal
uniformity; they need not be independent. The proof counts fibers of the
permutation action, using an explicit bijection between any two fibers.
-/

namespace LowSpaceSubsetSum

open scoped BigOperators

theorem finiteUniformProbability_mono {Ω : Type*} [Fintype Ω]
    {P Q : Ω → Prop} (h : ∀ ω, P ω → Q ω) :
    finiteUniformProbability P ≤ finiteUniformProbability Q := by
  classical
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg (Fintype.card Ω))
  exact_mod_cast Fintype.card_le_of_injective
    (fun x : {ω // P ω} => (⟨x.1, h x.1 x.2⟩ : {ω // Q ω}))
    (fun x y hxy => Subtype.ext (congrArg (fun z : {ω // Q ω} => z.val) hxy))

/-- A finite map with constant fiber cardinality preserves the uniform law. -/
theorem finiteUniformProbability_map_of_constant_fibers {Ω Ψ : Type*}
    [Fintype Ω] [Nonempty Ω] [Fintype Ψ] [Nonempty Ψ] [DecidableEq Ψ]
    (f : Ω → Ψ) {c : ℕ} (hf : ∀ y, Fintype.card {x // f x = y} = c)
    (P : Ψ → Prop) :
    finiteUniformProbability (fun x => P (f x)) = finiteUniformProbability P := by
  classical
  have htotal : Fintype.card Ω = Fintype.card Ψ * c := by
    rw [← Fintype.card_congr (Equiv.sigmaFiberEquiv f)]
    simp only [Fintype.card_sigma, hf, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.cast_id]
  have hevent : Fintype.card {x // P (f x)} = Fintype.card {y // P y} * c := by
    rw [← Fintype.card_congr
      (Equiv.sigmaSubtypeFiberEquivSubtype f (p := fun x => P (f x)) (q := P)
        (fun _ => Iff.rfl))]
    simp only [Fintype.card_sigma, hf, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.cast_id]
  have hc : c ≠ 0 := by
    intro hc
    have hp : 0 < Fintype.card Ω := Fintype.card_pos
    rw [hc, mul_zero] at htotal
    omega
  unfold finiteUniformProbability
  rw [hevent, htotal, Nat.cast_mul, Nat.cast_mul]
  have hcR : (c : ℝ) ≠ 0 := by exact_mod_cast hc
  exact mul_div_mul_right _ _ hcR

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def permuteSubset (e : Equiv.Perm ι) (S : Finset ι) : Finset ι := S.map e.toEmbedding

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem permuteSubset_card (e : Equiv.Perm ι) (S : Finset ι) :
    (permuteSubset e S).card = S.card := Finset.card_map _

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem permuteSubset_trans (e f : Equiv.Perm ι) (S : Finset ι) :
    permuteSubset (e.trans f) S = permuteSubset f (permuteSubset e S) := by
  simp only [permuteSubset, Finset.map_map]
  rfl

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem permuteSubset_refl (S : Finset ι) :
    permuteSubset (Equiv.refl ι) S = S := by simp [permuteSubset]

theorem exists_permutation_of_card_eq (S T : Finset ι) (hcard : S.card = T.card) :
    ∃ e : Equiv.Perm ι, permuteSubset e S = T := by
  classical
  let es : {x // x ∈ S} ≃ {x // x ∈ T} := Finset.equivOfCardEq hcard
  have hc : Fintype.card {x // x ∉ S} = Fintype.card {x // x ∉ T} := by
    simp only [Fintype.card_subtype_compl, Fintype.card_coe, hcard]
  let ec : {x // x ∉ S} ≃ {x // x ∉ T} := Fintype.equivOfCardEq hc
  let e : Equiv.Perm ι := Equiv.subtypeCongr es ec
  refine ⟨e, Finset.eq_of_subset_of_card_le ?_ ?_⟩
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp hy
    have he : e x = (es ⟨x, hx⟩).val := by
      simp [e, Equiv.subtypeCongr, Equiv.sumCompl_symm_apply_of_pos hx]
    change e x ∈ T
    rw [he]
    exact (es ⟨x, hx⟩).property
  · simpa only [permuteSubset_card] using hcard.ge

def permutationBlock (K : Finset ι) (e : Equiv.Perm ι) :
    ↥((Finset.univ : Finset ι).powersetCard K.card) :=
  ⟨permuteSubset e K, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, permuteSubset_card e K⟩⟩

theorem permutationBlock_fiber_card_eq (K : Finset ι)
    (S T : ↥((Finset.univ : Finset ι).powersetCard K.card)) :
    Fintype.card {e : Equiv.Perm ι // permutationBlock K e = S} =
      Fintype.card {e : Equiv.Perm ι // permutationBlock K e = T} := by
  classical
  have hS := (Finset.mem_powersetCard.mp S.property).2
  have hT := (Finset.mem_powersetCard.mp T.property).2
  obtain ⟨τ, hτ⟩ := exists_permutation_of_card_eq S.val T.val (hS.trans hT.symm)
  have hτinv : permuteSubset τ.symm T.val = S.val := by
    rw [← hτ, ← permuteSubset_trans]
    simp
  let equiv : {e : Equiv.Perm ι // permutationBlock K e = S} ≃
      {e : Equiv.Perm ι // permutationBlock K e = T} :=
    { toFun := fun e => ⟨e.val.trans τ, by
        apply Subtype.ext
        change permuteSubset (e.val.trans τ) K = T.val
        have he : permuteSubset e.val K = S.val := congrArg Subtype.val e.property
        rw [permuteSubset_trans, he, hτ]⟩
      invFun := fun e => ⟨e.val.trans τ.symm, by
        apply Subtype.ext
        change permuteSubset (e.val.trans τ.symm) K = S.val
        have he : permuteSubset e.val K = T.val := congrArg Subtype.val e.property
        rw [permuteSubset_trans, he, hτinv]⟩
      left_inv := fun e => by apply Subtype.ext; ext x; simp
      right_inv := fun e => by apply Subtype.ext; ext x; simp }
  exact Fintype.card_congr equiv

/-- The image of any fixed block under a uniform permutation is a uniform
subset of the same cardinality, including empty and full blocks. -/
theorem permutationBlock_uniform (K : Finset ι) (P : Finset ι → Prop) :
    finiteUniformProbability (fun e : Equiv.Perm ι => P (permuteSubset e K)) =
      finiteUniformProbability (fun S : ↥((Finset.univ : Finset ι).powersetCard K.card) => P S.val) := by
  classical
  let : Nonempty ↥((Finset.univ : Finset ι).powersetCard K.card) :=
    ⟨⟨K, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, rfl⟩⟩⟩
  let c := Fintype.card {e : Equiv.Perm ι //
    permutationBlock K e = permutationBlock K (Equiv.refl ι)}
  have hf : ∀ S, Fintype.card {e : Equiv.Perm ι // permutationBlock K e = S} = c := by
    intro S
    exact permutationBlock_fiber_card_eq K S (permutationBlock K (Equiv.refl ι))
  have h := finiteUniformProbability_map_of_constant_fibers
    (Ω := Equiv.Perm ι) (Ψ := ↥((Finset.univ : Finset ι).powersetCard K.card))
    (permutationBlock K) hf (fun S => P S.val)
  simpa only [permutationBlock] using h

theorem finiteUniformProbability_finset {α : Type*} [DecidableEq α]
    (X : Finset α) (P : α → Prop) [DecidablePred P] :
    finiteUniformProbability (fun x : X => P x.val) =
      ((X.filter P).card : ℝ) / X.card := by
  classical
  let : DecidablePred (fun x : X => P x.val) := fun _ => Classical.propDecidable _
  let equiv : {x : X // P x.val} ≃ ↥(X.filter P) :=
    { toFun := fun x => ⟨x.val.val, Finset.mem_filter.mpr ⟨x.val.property, x.property⟩⟩
      invFun := fun x => ⟨⟨x.val, (Finset.mem_filter.mp x.property).1⟩,
        (Finset.mem_filter.mp x.property).2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  unfold finiteUniformProbability
  calc
    _ = (Fintype.card ↥(X.filter P) : ℝ) / Fintype.card X := by
      congr 1
      exact_mod_cast @Fintype.card_congr _ _ _ _ equiv
    _ = ((X.filter P).card : ℝ) / X.card := by
      rw [Fintype.card_coe, Fintype.card_coe]

theorem permutationBlock_uniform_ratio (K : Finset ι) (P : Finset ι → Prop)
    [DecidablePred P] :
    finiteUniformProbability (fun e : Equiv.Perm ι => P (permuteSubset e K)) =
      ((((Finset.univ : Finset ι).powersetCard K.card).filter P).card : ℝ) /
        ((Finset.univ : Finset ι).powersetCard K.card).card := by
  rw [permutationBlock_uniform, finiteUniformProbability_finset]

end LowSpaceSubsetSum

end OAI
