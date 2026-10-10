import OAI.Geometry.HeilbronnTriangle.WeightedZeroPartition
import OAI.Geometry.HeilbronnTriangle.AuxiliaryAffineWeights
import OAI.Geometry.HeilbronnTriangle.PrimitiveNormal
import OAI.Geometry.HeilbronnTriangle.PlaneReduction

namespace OAI


noncomputable section

namespace Problem355.AuxiliaryThreeCase

open WeightedZeroPartition
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def ExceptionalVector {F : Type*} [Field F] (x : Fin 3 → F) (p : Fin 3) : Prop :=
  x ∈ Submodule.span F
    {Pi.single (columnPair p).1 (1 : F) - Pi.single (columnPair p).2 1}

theorem not_exceptional_zero_one {F : Type*} [Field F]
    (x : Fin 3 → F) (hx : x ≠ 0) :
    ¬ (ExceptionalVector x 0 ∧ ExceptionalVector x 1) := by
  rintro ⟨h0, h1⟩
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp h0
  obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.mp h1
  have ha2 := congrFun ha 2
  have hb2 := congrFun hb 2
  simp [columnPair] at ha2 hb2
  have hb0 : b = 0 := by simpa [← ha2] using hb2
  apply hx
  rw [← hb, hb0, zero_smul]

theorem exists_nonexceptional {F : Type*} [Field F]
    (x : Fin 3 → F) (hx : x ≠ 0) :
    ∃ p : Fin 3, ¬ ExceptionalVector x p := by
  by_cases h0 : ExceptionalVector x 0
  · exact ⟨1, fun h1 => not_exceptional_zero_one x hx ⟨h0, h1⟩⟩
  · exact ⟨0, h0⟩

theorem three_case_cover {F : Type*} [Field F]
    (x : Fin 3 → F) (hx : x ≠ 0) (v : Fin 3 → (Fin 3 → F))
    (hsupport : AffineIndependent F v ∨ ∃ p : Fin 3, EqualPair v p) :
    AffineIndependent F v ∨
      (∃ p : Fin 3, EqualPair v p ∧ ¬ ExceptionalVector x p) ∨
      (∃ p : Fin 3, EqualPair v p ∧ ExceptionalVector x p ∧
        ∃ i j : Fin 3, v i ≠ v j) := by
  rcases hsupport with ha | ⟨p, hp⟩
  · exact Or.inl ha
  right
  by_cases he : ExceptionalVector x p
  · by_cases hn : ∃ i j : Fin 3, v i ≠ v j
    · exact Or.inr ⟨p, hp, he, hn⟩
    · obtain ⟨p', hp'⟩ := exists_nonexceptional x hx
      left
      refine ⟨p', ?_, hp'⟩
      exact not_not.mp (fun h => hn ⟨(columnPair p').1, (columnPair p').2, h⟩)
  · exact Or.inl ⟨p, hp, he⟩

theorem three_case_cover_of_cap {F : Type*} [Field F]
    (x : Fin 3 → F) (hx : x ≠ 0) (v : Fin 3 → (Fin 3 → F))
    (T : Set (Fin 3 → F)) (hT : AuxiliaryCap.IsCap T) (hv : ∀ i, v i ∈ T) :
    AffineIndependent F v ∨
      (∃ p : Fin 3, EqualPair v p ∧ ¬ ExceptionalVector x p) ∨
      (∃ p : Fin 3, EqualPair v p ∧ ExceptionalVector x p ∧
        ∃ i j : Fin 3, v i ≠ v j) :=
  three_case_cover x hx v (affine_or_equalPair_of_cap v T hT hv)

theorem sum_le_three_case_sums {F α : Type*} [Field F]
    (x : Fin 3 → F) (hx : x ≠ 0) (S : Finset α) (W : α → ℝ)
    (v : α → Fin 3 → (Fin 3 → F))
    (hW : ∀ a ∈ S, 0 ≤ W a)
    (hsupport : ∀ a ∈ S, 0 < W a →
      AffineIndependent F (v a) ∨ ∃ p : Fin 3, EqualPair (v a) p) :
    (∑ a ∈ S, W a) ≤
      (∑ a ∈ S.filter (fun a => AffineIndependent F (v a)), W a) +
      ∑ p : Fin 3,
        ((∑ a ∈ S.filter (fun a => EqualPair (v a) p ∧
          ¬ ExceptionalVector x p), W a) +
         (∑ a ∈ S.filter (fun a => EqualPair (v a) p ∧
          ExceptionalVector x p ∧ ∃ i j : Fin 3, v a i ≠ v a j), W a)) := by
  classical
  let eq' := fun p a => EqualPair (v a) p ∧
    (¬ ExceptionalVector x p ∨ ∃ i j : Fin 3, v a i ≠ v a j)
  have hcover : ∀ a ∈ S, 0 < W a →
      AffineIndependent F (v a) ∨ ∃ p : Fin 3, eq' p a := by
    intro a ha hw
    rcases three_case_cover x hx (v a) (hsupport a ha hw) with
      h | ⟨p, he, hp⟩ | ⟨p, he, hp, hn⟩
    · exact Or.inl h
    · exact Or.inr ⟨p, he, Or.inl hp⟩
    · exact Or.inr ⟨p, he, Or.inr hn⟩
  have H := sum_le_four_case_sums S W
    (fun a => AffineIndependent F (v a)) eq' (ExceptionalVector x)
    (fun _ => False) hW hcover
  have heq (p : Fin 3) (a : α) :
      (eq' p a ∧ ¬ ExceptionalVector x p) ↔
        (EqualPair (v a) p ∧ ¬ ExceptionalVector x p) := by
    simp only [eq']
    tauto
  have hne (p : Fin 3) (a : α) :
      (eq' p a ∧ ExceptionalVector x p ∧ ¬ False) ↔
        (EqualPair (v a) p ∧ ExceptionalVector x p ∧
          ∃ i j : Fin 3, v a i ≠ v a j) := by
    simp only [eq']
    tauto
  simp_rw [heq, hne] at H
  simpa only [and_false, Finset.filter_false, Finset.sum_empty, add_zero] using H

theorem special_weight_le_four {F : Type*} [Field F] [Fintype F]
    [Fintype ((Fin 3 → F) ≃ᵃ[F] (Fin 3 → F))]
    (S : Finset (Fin 3 → F)) (hS : S.Nonempty)
    (T : Finset ((Fin 3 → F) ≃ᵃ[F] (Fin 3 → F))) (hT : T.Nonempty)
    (hsize : Fintype.card ((Fin 3 → F) ≃ᵃ[F] (Fin 3 → F)) ≤ 2 * T.card)
    (v : Fin 3 → (Fin 3 → F)) (hne : ∃ i j : Fin 3, v i ≠ v j) :
    AuxiliaryWeights.affineInclusionWeight S T v ≤
      4 * ((Fintype.card F : ℝ) ^ 3 / S.card) := by
  obtain ⟨i, j, hij⟩ := hne
  exact AuxiliaryWeights.affineInclusionWeight_le_four_of_ne S hS T hT hsize v i j hij

theorem shell_sum_le_of_three_case_bounds {F α β : Type*} [Field F]
    (X : Finset β) (normal : β → Fin 3 → F)
    (hnormal : ∀ x ∈ X, normal x ≠ 0)
    (S : β → Finset α) (W : α → ℝ) (v : α → Fin 3 → (Fin 3 → F))
    (hW : ∀ x ∈ X, ∀ a ∈ S x, 0 ≤ W a)
    (hsupport : ∀ x ∈ X, ∀ a ∈ S x, 0 < W a →
      AffineIndependent F (v a) ∨ ∃ p : Fin 3, EqualPair (v a) p)
    (Caff Cadd Cspecial : ℝ)
    (haff : (∑ x ∈ X, ∑ a ∈ (S x).filter
      (fun a => AffineIndependent F (v a)), W a) ≤ Caff)
    (hadd : ∀ p : Fin 3, (∑ x ∈ X, ∑ a ∈ (S x).filter
      (fun a => EqualPair (v a) p ∧ ¬ ExceptionalVector (normal x) p), W a) ≤ Cadd)
    (hspecial : ∀ p : Fin 3, (∑ x ∈ X, ∑ a ∈ (S x).filter
      (fun a => EqualPair (v a) p ∧ ExceptionalVector (normal x) p ∧
        ∃ i j : Fin 3, v a i ≠ v a j), W a) ≤ Cspecial) :
    (∑ x ∈ X, ∑ a ∈ S x, W a) ≤ Caff + 3 * (Cadd + Cspecial) := by
  classical
  calc
    (∑ x ∈ X, ∑ a ∈ S x, W a) ≤
        ∑ x ∈ X, ((∑ a ∈ (S x).filter
          (fun a => AffineIndependent F (v a)), W a) +
        ∑ p : Fin 3,
          ((∑ a ∈ (S x).filter (fun a => EqualPair (v a) p ∧
            ¬ ExceptionalVector (normal x) p), W a) +
           (∑ a ∈ (S x).filter (fun a => EqualPair (v a) p ∧
            ExceptionalVector (normal x) p ∧ ∃ i j : Fin 3, v a i ≠ v a j), W a))) := by
      exact Finset.sum_le_sum fun x hx =>
        sum_le_three_case_sums (normal x) (hnormal x hx) (S x) W v
          (hW x hx) (hsupport x hx)
    _ = (∑ x ∈ X, ∑ a ∈ (S x).filter
          (fun a => AffineIndependent F (v a)), W a) +
        ∑ p : Fin 3,
          ((∑ x ∈ X, ∑ a ∈ (S x).filter (fun a => EqualPair (v a) p ∧
            ¬ ExceptionalVector (normal x) p), W a) +
           (∑ x ∈ X, ∑ a ∈ (S x).filter (fun a => EqualPair (v a) p ∧
            ExceptionalVector (normal x) p ∧ ∃ i j : Fin 3, v a i ≠ v a j), W a)) := by
      rw [Finset.sum_add_distrib]
      congr 1
      rw [Finset.sum_comm]
      simp only [Finset.sum_add_distrib]
    _ ≤ Caff + ∑ _p : Fin 3, (Cadd + Cspecial) := by
      apply add_le_add haff
      exact Finset.sum_le_sum fun p _ => add_le_add (hadd p) (hspecial p)
    _ = Caff + 3 * (Cadd + Cspecial) := by simp; ring

@[simp] theorem exceptionalVector_reduction (q : ℕ) [Fact q.Prime]
    (x : Fin 3 → ℤ) (p : Fin 3) :
    ExceptionalVector (fun i => (x i : ZMod q)) p ↔ Exceptional q x p := Iff.rfl

theorem matrix_sum_le_three_case_sums
    (q : ℕ) [Fact q.Prime] (x : Fin 3 → ℤ) (hx : PrimitiveNormal.IsPrimitive x)
    (S : Finset IntMatrix) (W : IntMatrix → ℝ)
    (hW : ∀ A ∈ S, 0 ≤ W A)
    (hcap : ∀ A ∈ S, 0 < W A → ∃ T : Set (Fin 3 → ZMod q),
      AuxiliaryCap.IsCap T ∧ ∀ i, residueColumns q A i ∈ T) :
    (∑ A ∈ S, W A) ≤
      (∑ A ∈ S.filter (fun A => AffineIndependent (ZMod q) (residueColumns q A)), W A) +
      ∑ p : Fin 3,
        ((∑ A ∈ S.filter (fun A => EqualPair (residueColumns q A) p ∧
          ¬ Exceptional q x p), W A) +
         (∑ A ∈ S.filter (fun A => EqualPair (residueColumns q A) p ∧
          Exceptional q x p ∧ ∃ i j : Fin 3, residueColumns q A i ≠ residueColumns q A j), W A)) := by
  obtain ⟨z, hz⟩ := (PrimitiveNormal.isPrimitive_iff_exists_dot_eq_one x).mp hx
  have hnormal := PlaneReduction.normal_reduction_ne_zero q x z hz
  have hs : ∀ A ∈ S, 0 < W A → AffineIndependent (ZMod q) (residueColumns q A) ∨
      ∃ p : Fin 3, EqualPair (residueColumns q A) p := by
    intro A hA hp
    obtain ⟨T, hT, hcols⟩ := hcap A hA hp
    exact affine_or_equalPair_of_cap (residueColumns q A) T hT hcols
  have H := sum_le_three_case_sums (fun i => (x i : ZMod q)) hnormal S W
    (residueColumns q) hW hs
  simpa only [exceptionalVector_reduction] using H

end Problem355.AuxiliaryThreeCase

end

end OAI
