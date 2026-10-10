import Mathlib
import OAI.Computability.MinUncut.Games.JointCoefficient
import OAI.Computability.MinUncut.Analysis.Hermite

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory Polynomial Filter
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory WithLp
open scoped BigOperators RealInnerProductSpace
namespace MinUncut.Inner
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {V A : Type*} [AddCommGroup V] [Module F₂ V] [AddTorsor V A] [Fintype A]
variable {m n : ℕ}

def singleRow (r : Row m n) : Row m n → F₂ := Pi.single r 1

lemma rowCode_singleRow (r : Row m n) (u : Point m n) :
    (rowCode (singleRow r)).val u = if face u r.1=r.2 then 1 else 0 := by
  change (∑ i : Fin m, (Pi.single r (1:F₂) : Row m n → F₂) ⟨i,face u i⟩) = _
  rw [Finset.sum_eq_single r.1]
  · by_cases hh : face u r.1=r.2
    · simp [hh]
    · have he : (⟨r.1,face u r.1⟩ : Row m n) ≠ r := by
        intro he; cases r; simp_all
      simp [hh, Pi.single_eq_of_ne he]
  · intro i _ hi
    apply Pi.single_eq_of_ne
    intro he
    exact hi (congrArg Sigma.fst he)
  · simp

omit [Fintype A] in
lemma constantArray_singleRow (r : Row m n) :
    constantArray (singleRow r) = Pi.single r (AffineMap.const F₂ A 1) := by
  funext t
  by_cases ht : t=r
  · subst t; simp [constantArray, singleRow]
  · simp only [constantArray, singleRow, Pi.single_eq_of_ne ht]
    rfl

theorem joint_local_odd (f : FoldedProof A) {σ : ℝ} (hσ : σ ≠ 0) (η : ℝ)
    (x : Point m n) (α : Module.Dual F₂ (FaceArray A m n)) (I : Point m n → ℕ)
    (hne : jointCoefficient f σ η x α I ≠ 0) (i : Fin m)
    (hi : ∀ u, 0 < I u → face u i ≠ face x i) :
    RowNoise.frequency α ⟨i,face x i⟩ (AffineMap.const F₂ A 1) = 1 := by
  have hh := joint_row_gauge f hσ η x α I hne (singleRow ⟨i,face x i⟩)
  rw [constantArray_singleRow, rowCode_singleRow, ite_eq_left rfl] at hh
  have hp : GaussianHermite.parity (rowCode (singleRow ⟨i,face x i⟩)).val I = 0 := by
    unfold GaussianHermite.parity
    apply Finset.sum_eq_zero
    intro u _
    by_cases hu : I u=0
    · simp [hu]
    · rw [rowCode_singleRow, ite_eq_right (hi u (Nat.pos_of_ne_zero hu)), zero_mul]
  rw [hp, add_zero] at hh
  exact hh

lemma frequency_cylinder (α : Module.Dual F₂ (FaceArray A m n))
    (x : Point m n) (i j : Fin m) (hij : i ≠ j)
    (hi : ∀ y, RowNoise.frequency α ⟨i,y⟩ ≠ 0 →
      doubleMatch i j x (rowFill x ⟨i,y⟩) → y=face x i)
    (hj : ∀ y, RowNoise.frequency α ⟨j,y⟩ ≠ 0 →
      doubleMatch j i x (rowFill x ⟨j,y⟩) → y=face x j) (a : Forms A) :
    α (cylinderArray i j x a) =
      RowNoise.frequency α ⟨i,face x i⟩ a + RowNoise.frequency α ⟨j,face x j⟩ a := by
  rw [RowNoise.dual_apply]
  have he (r : Row m n) : RowNoise.frequency α r (cylinderArray i j x a r) =
      (if r=⟨i,face x i⟩ then RowNoise.frequency α ⟨i,face x i⟩ a else 0) +
      (if r=⟨j,face x j⟩ then RowNoise.frequency α ⟨j,face x j⟩ a else 0) := by
    by_cases hr : r=⟨i,face x i⟩
    · subst r
      have hne : (⟨i,face x i⟩ : Row m n) ≠ ⟨j,face x j⟩ := by
        intro he; exact hij (congrArg Sigma.fst he)
      simp [hne, cylinderArray_local, doubleMatch]
    by_cases hr' : r=⟨j,face x j⟩
    · subst r
      simp [hr, cylinderArray_local, doubleMatch]
    simp only [ite_eq_right hr, ite_eq_right hr', zero_add]
    by_cases ha : RowNoise.frequency α r=0
    · simp [ha]
    · unfold cylinderArray
      split_ifs with hc
      · rcases r with ⟨t,y⟩
        rcases hc.1 with ht | ht
        · change t=i at ht
          subst t
          exact False.elim (hr (by rw [hi y ha hc.2]))
        · change t=j at ht
          subst t
          have hc' : doubleMatch j i x (rowFill x ⟨j,y⟩) :=
            fun u huj hui => hc.2 u hui huj
          exact False.elim (hr' (by rw [hj y ha hc']))
      · simp
  simp_rw [he]
  rw [Finset.sum_add_distrib]
  simp

theorem joint_matching_odd (f : FoldedProof A) {σ : ℝ} (hσ : σ ≠ 0) (η : ℝ)
    (x : Point m n) (α : Module.Dual F₂ (FaceArray A m n)) (I : Point m n → ℕ)
    (hne : jointCoefficient f σ η x α I ≠ 0) (hx : I x=0)
    (hsize : (RowNoise.mask α).card < (m-(∑ u, I u)).choose 2) :
    ∃ i j : Fin m, i ≠ j ∧
      RowNoise.frequency α ⟨i,face x i⟩ = RowNoise.frequency α ⟨j,face x j⟩ ∧
      RowNoise.frequency α ⟨i,face x i⟩ (AffineMap.const F₂ A 1) = 1 := by
  obtain ⟨i,j,hij,hs,hi,hj⟩ := admissible_pair x I (RowNoise.mask α) hx hsize
  refine ⟨i,j,hij,?_,joint_local_odd f hσ η x α I hne i (fun u hu => (hs u hu).1)⟩
  apply LinearMap.ext
  intro a
  have hh := joint_cylinder_gauge f σ η x α I hne i j hij x a
  rw [frequency_cylinder α x i j hij
    (fun y hy => hi y (by simpa [RowNoise.mask] using hy))
    (fun y hy => hj y (by simpa [RowNoise.mask] using hy))] at hh
  exact (BinaryFourier.add_eq_zero_iff _ _).mp hh
end MinUncut.Inner

end

end OAI
