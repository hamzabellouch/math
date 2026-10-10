import OAI.Analysis.KadisonSimilarity.Tensor.InvariantTensors
import OAI.Analysis.KadisonSimilarity.Tracial.TracialMatrixTower
import Mathlib.GroupTheory.Perm.Option
import Mathlib.Data.Fintype.Option

namespace OAI

/-! Naturality of normalized permutation contractions under trace-preserving
matrix algebra maps, proved by deleting one permutation vertex at a time. -/

noncomputable section
namespace KadisonSimilarity

open Finset

universe u
variable {ι : Type u} {α β : Type*} [Fintype ι] [decι : DecidableEq ι]

/-- Insert one new vertex after `b` in its permutation cycle. -/
def insertPermutationVertex (p : Equiv.Perm ι) (b : ι) : Equiv.Perm (Option ι) :=
  Equiv.swap none (some (p b)) * p.optionCongr

omit [Fintype ι] in
@[simp] theorem insertPermutationVertex_none (p : Equiv.Perm ι) (b : ι) :
    insertPermutationVertex p b none = some (p b) := by
  simp [insertPermutationVertex, Equiv.Perm.mul_apply]

omit [Fintype ι] in
@[simp] theorem insertPermutationVertex_self (p : Equiv.Perm ι) (b : ι) :
    insertPermutationVertex p b (some b) = none := by
  simp [insertPermutationVertex, Equiv.Perm.mul_apply]

omit [Fintype ι] in
theorem insertPermutationVertex_other (p : Equiv.Perm ι) (b i : ι) (hi : i ≠ b) :
    insertPermutationVertex p b (some i) = some (p i) := by
  simp [insertPermutationVertex, Equiv.Perm.mul_apply, Equiv.swap_apply_def,
    p.injective.ne hi]

/-- Removing an inserted vertex preserves the set of cycle-constant labels. -/
def insertedCycleLabelingsEquiv (p : Equiv.Perm ι) (b : ι) (β : Type*) :
    CycleConstantLabelings (insertPermutationVertex p b) β ≃ CycleConstantLabelings p β where
  toFun f := ⟨fun i => f.1 (some i), by
    intro i
    by_cases hi : i = b
    · subst i
      have h₀ := f.2 none
      have hb := f.2 (some b)
      simp only [insertPermutationVertex_none] at h₀
      simp only [insertPermutationVertex_self] at hb
      exact h₀.trans hb
    · simpa only [insertPermutationVertex_other p b i hi] using f.2 (some i)⟩
  invFun f := ⟨fun i => i.elim (f.1 b) f.1, by
    intro i
    cases i with
    | none => simpa only [insertPermutationVertex_none, Option.elim_some, Option.elim_none] using f.2 b
    | some i =>
      by_cases hi : i = b
      · subst i
        simp
      · simp only [insertPermutationVertex_other p b i hi, Option.elim_some]
        exact f.2 i⟩
  left_inv f := by
    apply Subtype.ext
    funext i
    cases i with
    | none =>
      have h := f.2 (some b)
      simpa only [insertPermutationVertex_self, Option.elim_none] using h.symm
    | some i => rfl
  right_inv f := rfl

/-- A new fixed point contributes an independent constant label. -/
def fixedCycleLabelingsEquiv (p : Equiv.Perm ι) (β : Type*) :
    CycleConstantLabelings p.optionCongr β ≃ β × CycleConstantLabelings p β where
  toFun f := (f.1 none, ⟨fun i => f.1 (some i), fun i => f.2 (some i)⟩)
  invFun f := ⟨fun i => i.elim f.1 f.2.1, by
    intro i
    cases i with
    | none => rfl
    | some i => exact f.2.2 i⟩
  left_inv f := by
    apply Subtype.ext
    funext i
    cases i <;> rfl
  right_inv f := rfl

theorem permutationCycleCount_insert (p : Equiv.Perm ι) (b : ι) :
    permutationCycleCount (insertPermutationVertex p b) = permutationCycleCount p := by
  apply Nat.pow_right_injective (a := 2) (by decide)
  have h := Fintype.card_congr (insertedCycleLabelingsEquiv p b (Fin 2))
  simpa only [card_cycleConstantLabelings, Fintype.card_fin] using h

theorem permutationCycleCount_optionCongr (p : Equiv.Perm ι) :
    permutationCycleCount p.optionCongr = permutationCycleCount p + 1 := by
  apply Nat.pow_right_injective (a := 2) (by decide)
  have h := Fintype.card_congr (fixedCycleLabelingsEquiv p (Fin 2))
  simpa only [card_cycleConstantLabelings, Fintype.card_prod, Fintype.card_fin,
    pow_succ, Nat.mul_comm] using h

variable [Fintype α] [DecidableEq α]

/-- Splicing two adjacent slots multiplies their matrix arguments in cycle order. -/
def splicePermutationWord (v : Option ι → Matrix α α ℂ) (b : ι) : ι → Matrix α α ℂ :=
  Function.update (fun i => v (some i)) b (v (some b) * v none)

omit [DecidableEq α] in
/-- A fixed vertex contributes the ordinary matrix trace. -/
theorem permutationContraction_optionCongr (p : Equiv.Perm ι)
    (v : Option ι → Matrix α α ℂ) :
    permutationContraction p.optionCongr v =
      Matrix.trace (v none) * permutationContraction p (fun i => v (some i)) := by
  unfold permutationContraction
  rw [Fintype.sum_equiv (Equiv.piOptionEquivProd :
    (Option ι → α) ≃ α × (ι → α)) _
    (fun ag => v none ag.1 ag.1 * ∏ i, v (some i) (ag.2 i) (ag.2 (p i)))]
  · rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum]
    rw [← Finset.sum_mul]
    rfl
  · intro f
    simp [Fintype.prod_option]

omit [DecidableEq α] in
/-- Summing the label at an inserted nonfixed vertex is matrix multiplication. -/
theorem permutationContraction_insert (p : Equiv.Perm ι) (b : ι)
    (v : Option ι → Matrix α α ℂ) :
    permutationContraction (insertPermutationVertex p b) v =
      permutationContraction p (splicePermutationWord v b) := by
  unfold permutationContraction
  rw [Fintype.sum_equiv (Equiv.piOptionEquivProd :
    (Option ι → α) ≃ α × (ι → α)) _
    (fun ag => v none ag.1 (ag.2 (p b)) *
      (v (some b) (ag.2 b) ag.1 *
        ∏ i : {i : ι // i ≠ b}, v (some i) (ag.2 i) (ag.2 (p i))))]
  · rw [Fintype.sum_prod_type, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro g _
    have hreorder (a : α) :
        v none a (g (p b)) * (v (some b) (g b) a *
            ∏ i : {i : ι // i ≠ b}, v (some i) (g i) (g (p i))) =
          (v (some b) (g b) a * v none a (g (p b))) *
            ∏ i : {i : ι // i ≠ b}, v (some i) (g i) (g (p i)) := by ring
    simp_rw [hreorder]
    rw [← Finset.sum_mul]
    rw [Fintype.prod_eq_mul_prod_subtype_ne _ b]
    change ((v (some b) * v none) (g b) (g (p b))) * _ = _
    simp only [splicePermutationWord, Function.update_self]
    congr 1
    apply Finset.prod_congr rfl
    intro i _
    simp only [Function.update_of_ne i.2]
  · intro f
    rw [Fintype.prod_option, Fintype.prod_eq_mul_prod_subtype_ne _ b]
    simp only [insertPermutationVertex_none, insertPermutationVertex_self,
      Equiv.piOptionEquivProd]
    congr 2
    apply Finset.prod_congr rfl
    intro i _
    rw [insertPermutationVertex_other p b i i.2]
    rfl

omit [DecidableEq α] in
/-- Normalized fixed-point deletion carries precisely one normalized trace. -/
theorem normalizedPermutationContraction_optionCongr (p : Equiv.Perm ι)
    (v : Option ι → Matrix α α ℂ) :
    normalizedPermutationContraction p.optionCongr v =
      ((Fintype.card α : ℂ)⁻¹ * Matrix.trace (v none)) *
        normalizedPermutationContraction p (fun i => v (some i)) := by
  rw [normalizedPermutationContraction, permutationCycleCount_optionCongr,
    permutationContraction_optionCongr, normalizedPermutationContraction, pow_succ]
  ring

omit [DecidableEq α] in
/-- Insertion into an existing cycle adds no trace-normalization factor. -/
theorem normalizedPermutationContraction_insert (p : Equiv.Perm ι) (b : ι)
    (v : Option ι → Matrix α α ℂ) :
    normalizedPermutationContraction (insertPermutationVertex p b) v =
      normalizedPermutationContraction p (splicePermutationWord v b) := by
  rw [normalizedPermutationContraction, permutationCycleCount_insert,
    permutationContraction_insert, normalizedPermutationContraction]

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- Vertex reindexing does not change cycle-constant labels. -/
def reindexedCycleLabelingsEquiv (e : ι ≃ κ) (p : Equiv.Perm ι) (β : Type*) :
    CycleConstantLabelings (e.permCongr p) β ≃ CycleConstantLabelings p β where
  toFun f := ⟨fun i => f.1 (e i), by
    intro i
    simpa only [Equiv.permCongr_apply, e.symm_apply_apply] using f.2 (e i)⟩
  invFun f := ⟨fun i => f.1 (e.symm i), by
    intro i
    simpa only [Equiv.permCongr_apply, e.symm_apply_apply] using f.2 (e.symm i)⟩
  left_inv f := by
    apply Subtype.ext
    funext i
    exact congrArg f.1 (e.apply_symm_apply i)
  right_inv f := by
    apply Subtype.ext
    funext i
    exact congrArg f.1 (e.symm_apply_apply i)

theorem permutationCycleCount_permCongr (e : ι ≃ κ) (p : Equiv.Perm ι) :
    permutationCycleCount (e.permCongr p) = permutationCycleCount p := by
  apply Nat.pow_right_injective (a := 2) (by decide)
  have h := Fintype.card_congr (reindexedCycleLabelingsEquiv e p (Fin 2))
  simpa only [card_cycleConstantLabelings, Fintype.card_fin] using h

omit [DecidableEq α] in
theorem permutationContraction_permCongr (e : ι ≃ κ) (p : Equiv.Perm ι)
    (v : κ → Matrix α α ℂ) :
    permutationContraction (e.permCongr p) v =
      permutationContraction p (fun i => v (e i)) := by
  unfold permutationContraction
  apply Fintype.sum_equiv (Equiv.arrowCongr e.symm (Equiv.refl α))
  intro f
  apply Fintype.prod_equiv e.symm
  intro i
  simp [Equiv.permCongr_apply, Equiv.arrowCongr]

omit [DecidableEq α] in
theorem normalizedPermutationContraction_permCongr (e : ι ≃ κ) (p : Equiv.Perm ι)
    (v : κ → Matrix α α ℂ) :
    normalizedPermutationContraction (e.permCongr p) v =
      normalizedPermutationContraction p (fun i => v (e i)) := by
  rw [normalizedPermutationContraction, permutationCycleCount_permCongr,
    permutationContraction_permCongr, normalizedPermutationContraction]

/-- Normalized permutation contractions are natural for every trace-preserving
unital matrix algebra map; no normal-form hypothesis on that map is needed. -/
theorem normalizedPermutationContraction_map
    [Fintype β] [DecidableEq β]
    (φ : Matrix α α ℂ →ₐ[ℂ] Matrix β β ℂ)
    (htrace : ∀ a, (Fintype.card β : ℂ)⁻¹ * Matrix.trace (φ a) =
      (Fintype.card α : ℂ)⁻¹ * Matrix.trace a)
    (p : Equiv.Perm ι) (v : ι → Matrix α α ℂ) :
      normalizedPermutationContraction p (fun i => φ (v i)) =
      normalizedPermutationContraction p v := by
  classical
  let Q (I : Type u) [hI : Fintype I] : Prop :=
    ∀ (d : DecidableEq I) (p : Equiv.Perm I) (v : I → Matrix α α ℂ),
      @normalizedPermutationContraction I β hI d _ p (fun i => φ (v i)) =
        @normalizedPermutationContraction I α hI d _ p v
  suffices hQ : Q ι from hQ decι p v
  refine Fintype.induction_empty_option (P := Q) ?_ ?_ ?_ ι
  · intro I J _ e ih
    let : Fintype I := Fintype.ofEquiv J e.symm
    dsimp only [Q] at ih ⊢
    intro d p v
    let : DecidableEq J := d
    let : DecidableEq I := Classical.decEq I
    have hp : e.permCongr (e.symm.permCongr p) = p := e.permCongr.apply_symm_apply p
    have hleft := normalizedPermutationContraction_permCongr e (e.symm.permCongr p)
      (fun i => φ (v i))
    have hright := normalizedPermutationContraction_permCongr e (e.symm.permCongr p) v
    rw [hp] at hleft hright
    exact hleft.trans ((ih (Classical.decEq I) (e.symm.permCongr p)
      (fun i => v (e i))).trans hright.symm)
  · dsimp only [Q]
    intro d p v
    cases Subsingleton.elim d (inferInstance : DecidableEq PEmpty)
    simp [normalizedPermutationContraction, permutationContraction, permutationCycleCount]
  · intro I _ ih
    dsimp only [Q] at ih ⊢
    intro d p v
    let : DecidableEq I := Classical.decEq I
    cases Subsingleton.elim d (@Option.instDecidableEq I (Classical.decEq I))
    obtain ⟨⟨a, q⟩, rfl⟩ := Equiv.Perm.decomposeOption.symm.surjective p
    cases a with
    | none =>
      have hp : Equiv.Perm.decomposeOption.symm (none, q) = q.optionCongr := by
        simp [Equiv.Perm.decomposeOption]
        rfl
      rw [hp]
      rw [normalizedPermutationContraction_optionCongr,
        normalizedPermutationContraction_optionCongr, htrace,
        ih (Classical.decEq I) q (fun i => v (some i))]
    | some a =>
      have hp : Equiv.Perm.decomposeOption.symm (some a, q) =
          insertPermutationVertex q (q.symm a) := by
        simp [Equiv.Perm.decomposeOption, insertPermutationVertex]
      rw [hp]
      rw [normalizedPermutationContraction_insert q (q.symm a) (fun i => φ (v i)),
        normalizedPermutationContraction_insert q (q.symm a) v]
      have hw : splicePermutationWord (fun i => φ (v i)) (q.symm a) =
          fun i => φ (splicePermutationWord v (q.symm a) i) := by
        funext i
        simp only [splicePermutationWord, Function.update_apply]
        split_ifs <;> simp only [map_mul]
      rw [hw]
      exact ih (Classical.decEq I) q (splicePermutationWord v (q.symm a))

section TracialTower

variable {R E : Type*} [Ring R] [StarRing R] [Algebra ℂ R]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  {A : ℕ → Type*} [∀ s, Fintype (A s)] [∀ s, DecidableEq (A s)]
  {τ : R →ₗ[ℂ] ℂ} {V : R →ₗ[ℂ] E}

/-- The stable-stage contraction compatibility follows from the raw tracial
matrix inclusions and is not an additional tensor-classification hypothesis. -/
theorem NestedTracialMatrices.normalizedPermutationContraction_inclusion
    (M : NestedTracialMatrices (A := A) τ V) (s t : ℕ) (h : s ≤ t)
    (p : Equiv.Perm ι) (v : ι → Matrix (A s) (A s) ℂ) :
    normalizedPermutationContraction p (fun i => M.inclusion s t h (v i)) =
      normalizedPermutationContraction p v := by
  apply normalizedPermutationContraction_map (M.inclusion s t h).toAlgHom ?_ p v
  intro a
  calc
    _ = τ (M.embedding t (M.inclusion s t h a)) := (M.trace_embedding t _).symm
    _ = τ (M.embedding s a) := congrArg τ (M.compatible s t h a)
    _ = _ := M.trace_embedding s a

end TracialTower

end KadisonSimilarity

end

end OAI
