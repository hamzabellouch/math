import OAI.Geometry.HeilbronnTriangle.AuxiliaryCap

namespace OAI


noncomputable section

namespace Problem355.WeightedZeroPartition

open scoped BigOperators
attribute [local instance] Classical.propDecidable

def columnPair : Fin 3 → Fin 3 × Fin 3 := ![(0, 1), (0, 2), (1, 2)]

def EqualPair {F : Type*} (v : Fin 3 → (Fin 3 → F)) (p : Fin 3) : Prop :=
  v (columnPair p).1 = v (columnPair p).2

theorem affine_or_equalPair_of_cap {F : Type*} [Field F]
    (v : Fin 3 → (Fin 3 → F)) (T : Set (Fin 3 → F))
    (hT : AuxiliaryCap.IsCap T) (hv : ∀ i, v i ∈ T) :
    AffineIndependent F v ∨ ∃ p : Fin 3, EqualPair v p := by
  by_cases h01 : v 0 = v 1
  · exact Or.inr ⟨0, h01⟩
  by_cases h02 : v 0 = v 2
  · exact Or.inr ⟨1, h02⟩
  by_cases h12 : v 1 = v 2
  · exact Or.inr ⟨2, h12⟩
  left
  have h := (affineIndependent_iff_not_collinear_set).mpr
    (hT (v 0) (hv 0) (v 1) (hv 1) (v 2) (hv 2) h01 h02 h12)
  convert h using 1
  funext i
  fin_cases i <;> rfl

theorem sum_le_four_case_sums {α : Type*}
    (S : Finset α) (W : α → ℝ)
    (affine : α → Prop) (equalPair : Fin 3 → α → Prop)
    (exceptional : Fin 3 → Prop) (lowRank : α → Prop)
    (hW : ∀ a ∈ S, 0 ≤ W a)
    (hsupport : ∀ a ∈ S, 0 < W a → affine a ∨ ∃ p, equalPair p a) :
    (∑ a ∈ S, W a) ≤
      (∑ a ∈ S.filter affine, W a) +
      ∑ p : Fin 3,
        ((∑ a ∈ S.filter (fun a => equalPair p a ∧ ¬ exceptional p), W a) +
         (∑ a ∈ S.filter (fun a => equalPair p a ∧ exceptional p ∧ ¬ lowRank a), W a) +
         (∑ a ∈ S.filter (fun a => equalPair p a ∧ exceptional p ∧ lowRank a), W a)) := by
  classical
  have hpoint (a : α) (ha : a ∈ S) :
      W a ≤ (if affine a then W a else 0) +
        ∑ p : Fin 3, if equalPair p a then W a else 0 := by
    have hnonneg (p : Fin 3) : 0 ≤ if equalPair p a then W a else 0 := by
      split_ifs <;> first | exact hW a ha | rfl
    by_cases hw : 0 < W a
    · rcases hsupport a ha hw with haf | ⟨p, hp⟩
      · simp only [ite_eq_left haf]
        exact le_add_of_nonneg_right (Finset.sum_nonneg fun p _ => hnonneg p)
      · have hs := Finset.single_le_sum
          (s := Finset.univ) (f := fun p => if equalPair p a then W a else 0)
          (fun p _ => hnonneg p) (Finset.mem_univ p)
        have hs' : W a ≤ ∑ p : Fin 3, if equalPair p a then W a else 0 := by
          simpa only [ite_eq_left hp] using hs
        exact hs'.trans (le_add_of_nonneg_left (by split_ifs <;> positivity))
    · have hz : W a = 0 := le_antisymm (not_lt.mp hw) (hW a ha)
      simp [hz]
  have hsplit (p : Fin 3) (a : α) :
      (if equalPair p a then W a else 0) =
        (if equalPair p a ∧ ¬ exceptional p then W a else 0) +
        (if equalPair p a ∧ exceptional p ∧ ¬ lowRank a then W a else 0) +
        (if equalPair p a ∧ exceptional p ∧ lowRank a then W a else 0) := by
    by_cases he : equalPair p a <;> by_cases hx : exceptional p <;>
      by_cases hl : lowRank a <;> simp [he, hx, hl]
  calc
    (∑ a ∈ S, W a) ≤ ∑ a ∈ S,
        ((if affine a then W a else 0) +
          ∑ p : Fin 3, if equalPair p a then W a else 0) :=
      Finset.sum_le_sum hpoint
    _ = _ := by
      simp_rw [hsplit]
      rw [Finset.sum_add_distrib, Finset.sum_comm]
      simp only [Finset.sum_add_distrib, ← Finset.sum_filter]

theorem shell_sum_le_of_four_case_bounds {α β : Type*}
    (X : Finset β) (S : β → Finset α) (W : α → ℝ)
    (affine : α → Prop) (equalPair : Fin 3 → α → Prop)
    (exceptional : β → Fin 3 → Prop) (lowRank : α → Prop)
    (hW : ∀ x ∈ X, ∀ a ∈ S x, 0 ≤ W a)
    (hsupport : ∀ x ∈ X, ∀ a ∈ S x, 0 < W a →
      affine a ∨ ∃ p, equalPair p a)
    (Caff Cadd Chigh Clow : ℝ)
    (haff : (∑ x ∈ X, ∑ a ∈ (S x).filter affine, W a) ≤ Caff)
    (hadd : ∀ p : Fin 3,
      (∑ x ∈ X, ∑ a ∈ (S x).filter
        (fun a => equalPair p a ∧ ¬ exceptional x p), W a) ≤ Cadd)
    (hhigh : ∀ p : Fin 3,
      (∑ x ∈ X, ∑ a ∈ (S x).filter
        (fun a => equalPair p a ∧ exceptional x p ∧ ¬ lowRank a), W a) ≤ Chigh)
    (hlow : ∀ p : Fin 3,
      (∑ x ∈ X, ∑ a ∈ (S x).filter
        (fun a => equalPair p a ∧ exceptional x p ∧ lowRank a), W a) ≤ Clow) :
    (∑ x ∈ X, ∑ a ∈ S x, W a) ≤ Caff + 3 * (Cadd + Chigh + Clow) := by
  classical
  calc
    (∑ x ∈ X, ∑ a ∈ S x, W a) ≤
        ∑ x ∈ X, ((∑ a ∈ (S x).filter affine, W a) +
          ∑ p : Fin 3,
            ((∑ a ∈ (S x).filter (fun a => equalPair p a ∧ ¬ exceptional x p), W a) +
             (∑ a ∈ (S x).filter (fun a => equalPair p a ∧ exceptional x p ∧ ¬ lowRank a), W a) +
             (∑ a ∈ (S x).filter (fun a => equalPair p a ∧ exceptional x p ∧ lowRank a), W a))) := by
      exact Finset.sum_le_sum fun x hx =>
        sum_le_four_case_sums (S x) W affine equalPair (exceptional x) lowRank
          (hW x hx) (hsupport x hx)
    _ = (∑ x ∈ X, ∑ a ∈ (S x).filter affine, W a) +
        ∑ p : Fin 3,
          ((∑ x ∈ X, ∑ a ∈ (S x).filter (fun a => equalPair p a ∧ ¬ exceptional x p), W a) +
           (∑ x ∈ X, ∑ a ∈ (S x).filter (fun a => equalPair p a ∧ exceptional x p ∧ ¬ lowRank a), W a) +
           (∑ x ∈ X, ∑ a ∈ (S x).filter (fun a => equalPair p a ∧ exceptional x p ∧ lowRank a), W a)) := by
      rw [Finset.sum_add_distrib]
      congr 1
      rw [Finset.sum_comm]
      simp only [Finset.sum_add_distrib]
    _ ≤ Caff + ∑ _p : Fin 3, (Cadd + Chigh + Clow) := by
      apply add_le_add haff
      exact Finset.sum_le_sum fun p _ => add_le_add (add_le_add (hadd p) (hhigh p)) (hlow p)
    _ = Caff + 3 * (Cadd + Chigh + Clow) := by simp; ring

abbrev IntMatrix := Matrix (Fin 3) (Fin 3) ℤ

def residueColumns (q : ℕ) (A : IntMatrix) : Fin 3 → (Fin 3 → ZMod q) :=
  fun j i => (A i j : ZMod q)

def Exceptional (q : ℕ) (x : Fin 3 → ℤ) (p : Fin 3) : Prop :=
  (fun i => (x i : ZMod q)) ∈ Submodule.span (ZMod q)
    {Pi.single (columnPair p).1 (1 : ZMod q) - Pi.single (columnPair p).2 1}

def LowRowRank (q : ℕ) [Fact q.Prime] (A : IntMatrix) : Prop :=
  Module.finrank (ZMod q)
    (Submodule.span (ZMod q) (Set.range (A.map fun z : ℤ => (z : ZMod q)))) ≤ 1

theorem matrix_sum_le_four_case_sums
    (q : ℕ) [Fact q.Prime] (x : Fin 3 → ℤ)
    (S : Finset IntMatrix) (W : IntMatrix → ℝ)
    (hW : ∀ A ∈ S, 0 ≤ W A)
    (hcap : ∀ A ∈ S, 0 < W A → ∃ T : Set (Fin 3 → ZMod q),
      AuxiliaryCap.IsCap T ∧ ∀ i, residueColumns q A i ∈ T) :
    (∑ A ∈ S, W A) ≤
      (∑ A ∈ S.filter (fun A => AffineIndependent (ZMod q) (residueColumns q A)), W A) +
      ∑ p : Fin 3,
        ((∑ A ∈ S.filter (fun A => EqualPair (residueColumns q A) p ∧ ¬ Exceptional q x p), W A) +
         (∑ A ∈ S.filter (fun A => EqualPair (residueColumns q A) p ∧ Exceptional q x p ∧ ¬ LowRowRank q A), W A) +
         (∑ A ∈ S.filter (fun A => EqualPair (residueColumns q A) p ∧ Exceptional q x p ∧ LowRowRank q A), W A)) := by
  apply sum_le_four_case_sums S W
    (fun A => AffineIndependent (ZMod q) (residueColumns q A))
    (fun p A => EqualPair (residueColumns q A) p)
    (Exceptional q x) (LowRowRank q) hW
  intro A hA hpos
  obtain ⟨T, hT, hcols⟩ := hcap A hA hpos
  exact affine_or_equalPair_of_cap (residueColumns q A) T hT hcols

end Problem355.WeightedZeroPartition

end

end OAI
