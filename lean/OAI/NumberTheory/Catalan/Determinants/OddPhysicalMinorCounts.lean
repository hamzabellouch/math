import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Card
import OAI.NumberTheory.Catalan.Determinants.RealColumnDeterminant

namespace OAI


noncomputable section

namespace InternalCatalan

open Classical
open scoped BigOperators

abbrev oddPhysicalIndex (R B C : ℕ) := Fin R ⊕ (Fin B ⊕ Fin C)

def oddPhysicalChoice {R B C : ℕ} (e : ℕ) : oddPhysicalIndex R B C → Type
  | Sum.inl _ => Unit
  | Sum.inr (Sum.inl _) => Unit
  | Sum.inr (Sum.inr _) => Option (Fin e)

instance oddPhysicalChoice_fintype {R B C e : ℕ} (j : oddPhysicalIndex R B C) :
    Fintype (oddPhysicalChoice e j) := by
  rcases j with j | (j | j) <;> dsimp [oddPhysicalChoice] <;> infer_instance

def oddPhysicalExceptionalTag {R B C e : ℕ} (j : oddPhysicalIndex R B C)
    (u : oddPhysicalChoice e j) : Option (Fin e) :=
  match j with
  | Sum.inl _ => none
  | Sum.inr (Sum.inl _) => none
  | Sum.inr (Sum.inr _) => u

def oddPhysicalVector {n R B C e : ℕ}
    (U : Fin R → Fin n → ℚ) (W : Fin B → Fin n → ℚ)
    (I : Fin C → Fin n → ℚ) (V : Fin e → Fin n → ℚ)
    (j : oddPhysicalIndex R B C) (u : oddPhysicalChoice e j) : Fin n → ℚ :=
  match j with
  | Sum.inl r => U r
  | Sum.inr (Sum.inl b) => W b
  | Sum.inr (Sum.inr c) => match u with | none => I c | some l => V l

def oddPhysicalScalar {R B C e : ℕ} (p : ℕ) (a : Fin C → Fin e → ℚ)
    (j : oddPhysicalIndex R B C) (u : oddPhysicalChoice e j) : ℚ :=
  match j with
  | Sum.inl _ => ((p : ℚ) ^ 2)⁻¹
  | Sum.inr (Sum.inl _) => (p : ℚ)⁻¹
  | Sum.inr (Sum.inr c) => match u with | none => 1 | some l => (p : ℚ)⁻¹ * a c l

def oddPhysicalColumn {n R B C e : ℕ} (p : ℕ)
    (U : Fin R → Fin n → ℚ) (W : Fin B → Fin n → ℚ)
    (I : Fin C → Fin n → ℚ) (V : Fin e → Fin n → ℚ)
    (a : Fin C → Fin e → ℚ) (j : oddPhysicalIndex R B C) (r : Fin n) : ℚ :=
  match j with
  | Sum.inl l => ((p : ℚ) ^ 2)⁻¹ * U l r
  | Sum.inr (Sum.inl l) => (p : ℚ)⁻¹ * W l r
  | Sum.inr (Sum.inr l) => I l r + (p : ℚ)⁻¹ * ∑ v, a l v * V v r

theorem oddPhysicalColumn_expansion {n R B C e : ℕ} (p : ℕ)
    (U : Fin R → Fin n → ℚ) (W : Fin B → Fin n → ℚ)
    (I : Fin C → Fin n → ℚ) (V : Fin e → Fin n → ℚ)
    (a : Fin C → Fin e → ℚ) (j : oddPhysicalIndex R B C) (r : Fin n) :
    oddPhysicalColumn p U W I V a j r =
      ∑ u : oddPhysicalChoice e j,
        oddPhysicalVector U W I V j u r * oddPhysicalScalar p a j u := by
  rcases j with j | (j | j)
  · change ((p : ℚ) ^ 2)⁻¹ * U j r = ∑ _u : Unit, U j r * ((p : ℚ) ^ 2)⁻¹
    have hunit : (Finset.univ : Finset Unit) = {()} := by ext u; simp
    rw [hunit, Finset.sum_singleton]
    ring
  · change (p : ℚ)⁻¹ * W j r = ∑ _u : Unit, W j r * (p : ℚ)⁻¹
    have hunit : (Finset.univ : Finset Unit) = {()} := by ext u; simp
    rw [hunit, Finset.sum_singleton]
    ring
  · simp only [oddPhysicalColumn, oddPhysicalChoice, Fintype.sum_option,
      oddPhysicalVector, oddPhysicalScalar, mul_one]
    rw [Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro l hl
    ring

def oddPhysicalVectorMinor {n R B C e : ℕ}
    (U : Fin R → Fin n → ℚ) (W : Fin B → Fin n → ℚ)
    (I : Fin C → Fin n → ℚ) (V : Fin e → Fin n → ℚ)
    (c : Fin n → oddPhysicalIndex R B C)
    (u : ∀ k, oddPhysicalChoice e (c k)) : ℚ :=
  Matrix.det (Matrix.of fun r k => oddPhysicalVector U W I V (c k) (u k) r)

theorem oddPhysicalMinor_expansion {n R B C e : ℕ} (p : ℕ)
    (U : Fin R → Fin n → ℚ) (W : Fin B → Fin n → ℚ)
    (I : Fin C → Fin n → ℚ) (V : Fin e → Fin n → ℚ)
    (a : Fin C → Fin e → ℚ) (c : Fin n → oddPhysicalIndex R B C) :
    Matrix.det (Matrix.of fun r k => oddPhysicalColumn p U W I V a (c k) r) =
      ∑ u : ∀ k, oddPhysicalChoice e (c k),
        (∏ k, oddPhysicalScalar p a (c k) (u k)) * oddPhysicalVectorMinor U W I V c u := by
  have hmatrix :
      (Matrix.of fun r k => oddPhysicalColumn p U W I V a (c k) r) =
        (Matrix.of fun r k => ∑ u : oddPhysicalChoice e (c k),
          oddPhysicalVector U W I V (c k) u r * oddPhysicalScalar p a (c k) u) := by
    ext r k
    exact oddPhysicalColumn_expansion p U W I V a (c k) r
  rw [hmatrix]
  calc
    _ = ∑ u : ∀ k, oddPhysicalChoice e (c k),
        ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℚ) *
          ∏ k, oddPhysicalVector U W I V (c k) (u k) (σ k) *
            oddPhysicalScalar p a (c k) (u k) := by
      simp only [Matrix.det_apply', Matrix.of_apply, Fintype.prod_sum, Finset.mul_sum]
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro u hu
      simp only [oddPhysicalVectorMinor, Matrix.det_apply', Matrix.of_apply, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro σ hσ
      rw [Finset.prod_mul_distrib]
      ring

theorem oddPhysicalVector_of_exceptional {n R B C e : ℕ}
    (U : Fin R → Fin n → ℚ) (W : Fin B → Fin n → ℚ)
    (I : Fin C → Fin n → ℚ) (V : Fin e → Fin n → ℚ)
    (j : oddPhysicalIndex R B C) (u : oddPhysicalChoice e j) (l : Fin e)
    (h : oddPhysicalExceptionalTag j u = some l) :
    oddPhysicalVector U W I V j u = V l := by
  rcases j with j | (j | j)
  · simp [oddPhysicalExceptionalTag] at h
  · simp [oddPhysicalExceptionalTag] at h
  · change u = some l at h
    subst u
    rfl

theorem oddPhysicalVectorMinor_eq_zero_of_repeat {n R B C e : ℕ}
    (U : Fin R → Fin n → ℚ) (W : Fin B → Fin n → ℚ)
    (I : Fin C → Fin n → ℚ) (V : Fin e → Fin n → ℚ)
    (c : Fin n → oddPhysicalIndex R B C)
    (u : ∀ k, oddPhysicalChoice e (c k)) {i j : Fin n} (hij : i ≠ j)
    (l : Fin e) (hi : oddPhysicalExceptionalTag (c i) (u i) = some l)
    (hj : oddPhysicalExceptionalTag (c j) (u j) = some l) :
    oddPhysicalVectorMinor U W I V c u = 0 := by
  apply Matrix.det_zero_of_column_eq hij
  intro r
  change oddPhysicalVector U W I V (c i) (u i) r =
    oddPhysicalVector U W I V (c j) (u j) r
  rw [oddPhysicalVector_of_exceptional U W I V (c i) (u i) l hi,
    oddPhysicalVector_of_exceptional U W I V (c j) (u j) l hj]

end InternalCatalan

end



noncomputable section

namespace InternalCatalan

open Classical
open scoped BigOperators

def oddPhysicalIsRetained {R B C : ℕ} : oddPhysicalIndex R B C → Bool
  | Sum.inl _ => true
  | _ => false

def oddPhysicalIsPaired {R B C : ℕ} : oddPhysicalIndex R B C → Bool
  | Sum.inr (Sum.inl _) => true
  | _ => false

def oddPhysicalRetainedSet {n R B C : ℕ} (c : Fin n → oddPhysicalIndex R B C) :=
  Finset.univ.filter (fun k => oddPhysicalIsRetained (c k) = true)

def oddPhysicalPairedSet {n R B C : ℕ} (c : Fin n → oddPhysicalIndex R B C) :=
  Finset.univ.filter (fun k => oddPhysicalIsPaired (c k) = true)

def oddPhysicalExceptionalSet {n R B C e : ℕ} (c : Fin n → oddPhysicalIndex R B C)
    (u : ∀ k, oddPhysicalChoice e (c k)) :=
  Finset.univ.filter (fun k => (oddPhysicalExceptionalTag (c k) (u k)).isSome = true)

def oddPhysicalLoss {R B C e : ℕ} (j : oddPhysicalIndex R B C)
    (u : oddPhysicalChoice e j) : ℕ :=
  (if oddPhysicalIsRetained j = true then 2 else 0) +
    (if oddPhysicalIsPaired j = true then 1 else 0) +
      (if (oddPhysicalExceptionalTag j u).isSome = true then 1 else 0)

theorem oddPhysical_one_tag {R B C e : ℕ} (j : oddPhysicalIndex R B C)
    (u : oddPhysicalChoice e j) :
    (if oddPhysicalIsRetained j = true then 1 else 0) +
      (if oddPhysicalIsPaired j = true then 1 else 0) +
        (if (oddPhysicalExceptionalTag j u).isSome = true then 1 else 0) ≤ (1 : ℕ) := by
  rcases j with j | (j | j)
  · simp [oddPhysicalIsRetained, oddPhysicalIsPaired, oddPhysicalExceptionalTag]
  · simp [oddPhysicalIsRetained, oddPhysicalIsPaired, oddPhysicalExceptionalTag]
  · cases u <;> simp [oddPhysicalIsRetained, oddPhysicalIsPaired, oddPhysicalExceptionalTag]

theorem oddPhysical_counts_le_size {n R B C e : ℕ}
    (c : Fin n → oddPhysicalIndex R B C) (u : ∀ k, oddPhysicalChoice e (c k)) :
    (oddPhysicalRetainedSet c).card + (oddPhysicalPairedSet c).card +
      (oddPhysicalExceptionalSet c u).card ≤ n := by
  have hs := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin n)))
    (fun k _ => oddPhysical_one_tag (c k) (u k))
  simpa only [Finset.sum_add_distrib, Finset.sum_boole, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one, Nat.cast_id,
    oddPhysicalRetainedSet, oddPhysicalPairedSet, oddPhysicalExceptionalSet] using hs

theorem oddPhysical_retained_count_le {n R B C : ℕ}
    (c : Fin n → oddPhysicalIndex R B C) (hc : Function.Injective c) :
    (oddPhysicalRetainedSet c).card ≤ R := by
  have h := Finset.card_le_card_of_injOn c
    (s := oddPhysicalRetainedSet c)
    (t := Finset.univ.image (Sum.inl : Fin R → oddPhysicalIndex R B C))
    (by
      intro k hk
      have hk' : oddPhysicalIsRetained (c k) = true := (Finset.mem_filter.mp hk).2
      cases hck : c k with
      | inl r => exact Finset.mem_image.mpr ⟨r, Finset.mem_univ _, rfl⟩
      | inr j => simp [hck, oddPhysicalIsRetained] at hk')
    (fun i _ j _ h => hc h)
  simpa only [Finset.card_image_of_injective _ Sum.inl_injective,
    Finset.card_univ, Fintype.card_fin] using h

theorem oddPhysical_paired_count_le {n R B C : ℕ}
    (c : Fin n → oddPhysicalIndex R B C) (hc : Function.Injective c) :
    (oddPhysicalPairedSet c).card ≤ B := by
  let f : Fin B → oddPhysicalIndex R B C := fun b => Sum.inr (Sum.inl b)
  have hf : Function.Injective f := by intro i j h; exact Sum.inl.inj (Sum.inr.inj h)
  have h := Finset.card_le_card_of_injOn c
    (s := oddPhysicalPairedSet c) (t := Finset.univ.image f)
    (by
      intro k hk
      have hk' : oddPhysicalIsPaired (c k) = true := (Finset.mem_filter.mp hk).2
      rcases hck : c k with j | (j | j)
      · simp [hck, oddPhysicalIsPaired] at hk'
      · exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
      · simp [hck, oddPhysicalIsPaired] at hk')
    (fun i _ j _ h => hc h)
  simpa only [Finset.card_image_of_injective _ hf,
    Finset.card_univ, Fintype.card_fin] using h

theorem oddPhysical_exceptional_count_le {n R B C e : ℕ}
    (U : Fin R → Fin n → ℚ) (W : Fin B → Fin n → ℚ)
    (I : Fin C → Fin n → ℚ) (V : Fin e → Fin n → ℚ)
    (c : Fin n → oddPhysicalIndex R B C) (u : ∀ k, oddPhysicalChoice e (c k))
    (hdet : oddPhysicalVectorMinor U W I V c u ≠ 0) :
    (oddPhysicalExceptionalSet c u).card ≤ e := by
  let f : Fin n → Option (Fin e) := fun k => oddPhysicalExceptionalTag (c k) (u k)
  have h := Finset.card_le_card_of_injOn f
    (s := oddPhysicalExceptionalSet c u)
    (t := Finset.univ.image (some : Fin e → Option (Fin e)))
    (by
      intro k hk
      have hk' : (f k).isSome = true := (Finset.mem_filter.mp hk).2
      cases hfk : f k with
      | none => simp [hfk] at hk'
      | some l => exact Finset.mem_image.mpr ⟨l, Finset.mem_univ _, rfl⟩)
    (by
      intro i hi j hj hij
      have hi' : (f i).isSome = true := (Finset.mem_filter.mp hi).2
      cases hfi : f i with
      | none => simp [hfi] at hi'
      | some l =>
        by_contra hne
        exact hdet (oddPhysicalVectorMinor_eq_zero_of_repeat U W I V c u
          hne l hfi (hij.symm.trans hfi)))
  simpa only [Finset.card_image_of_injective _ (Option.some_injective (Fin e)),
    Finset.card_univ, Fintype.card_fin] using h

theorem oddPhysical_total_loss_eq {n R B C e : ℕ}
    (c : Fin n → oddPhysicalIndex R B C) (u : ∀ k, oddPhysicalChoice e (c k)) :
    ∑ k, oddPhysicalLoss (c k) (u k) =
      2 * (oddPhysicalRetainedSet c).card + (oddPhysicalPairedSet c).card +
        (oddPhysicalExceptionalSet c u).card := by
  simp only [oddPhysicalLoss, Finset.sum_add_distrib,
    oddPhysicalRetainedSet, oddPhysicalPairedSet, oddPhysicalExceptionalSet]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
  simp
  omega

theorem oddPhysical_total_loss_le_min {n R B C e : ℕ}
    (U : Fin R → Fin n → ℚ) (W : Fin B → Fin n → ℚ)
    (I : Fin C → Fin n → ℚ) (V : Fin e → Fin n → ℚ)
    (c : Fin n → oddPhysicalIndex R B C) (hc : Function.Injective c)
    (u : ∀ k, oddPhysicalChoice e (c k))
    (hdet : oddPhysicalVectorMinor U W I V c u ≠ 0) :
    ∑ k, oddPhysicalLoss (c k) (u k) ≤ min (2 * n) (min (n + R) (2 * R + B + e)) := by
  rw [oddPhysical_total_loss_eq]
  have hs := oddPhysical_counts_le_size c u
  have hr := oddPhysical_retained_count_le c hc
  have hb := oddPhysical_paired_count_le c hc
  have he := oddPhysical_exceptional_count_le U W I V c u hdet
  omega

end InternalCatalan

end

end OAI
