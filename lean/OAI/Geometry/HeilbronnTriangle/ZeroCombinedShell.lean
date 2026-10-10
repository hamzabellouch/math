import OAI.Geometry.HeilbronnTriangle.ZeroDeterminantCount
import OAI.Geometry.HeilbronnTriangle.AuxiliaryThreeCase

namespace OAI


noncomputable section

namespace Problem355.ZeroDeterminantCount

open Matrix PrimitiveNormal WeightedZeroPartition AuxiliaryThreeCase
open scoped BigOperators Matrix
attribute [local instance] Classical.propDecidable

private lemma sum_filter_normal {α β : Type*} (T : Finset β)
    (F : β → Finset α) (W : α → ℝ) (P : β → Prop) (Q : β → α → Prop) :
    (∑ x ∈ T, ∑ a ∈ (F x).filter (fun a => Q x a ∧ P x), W a) =
      ∑ x ∈ T.filter P, ∑ a ∈ (F x).filter (Q x), W a := by
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x hx
  by_cases hp : P x <;> simp [hp]

private theorem additional_case_bound (D : RowData) (q R : ℕ) [Fact q.Prime]
    (hEq : IsUnit (D.E : ZMod q)) (hparam : D.h ^ 26 ≤ (q : ℝ))
    (T : Finset IntVector) (hR : 0 < R)
    (hprimitive : ∀ x ∈ T, IsPrimitive x)
    (_ : ∀ x ∈ T, ∀ i, x i ≠ 0)
    (hnorm : ∀ x ∈ T, (R : ℝ) ≤ ‖toEuclidean x‖ ∧
      ‖toEuclidean x‖ < 2 * (R : ℝ))
    (F : IntVector → Finset IntMatrix)
    (hF : ∀ x, ∀ A ∈ F x, A *ᵥ x = 0 ∧ ∀ i, A i ∈ D.L)
    (W : IntMatrix → ℝ) (N Ca Cg Cd : ℝ)
    (hN : 0 ≤ N) (_ : 0 ≤ Ca) (hCg : 0 ≤ Cg) (_ : 0 ≤ Cd)
    (hcoord : ∀ x ∈ T, ∀ A ∈ F x, ∀ i j, |(A i j : ℝ)| ≤ 2 * N)
    (hproj : ∀ x ∈ T, ∀ A ∈ F x, ∃ s t : Fin 3,
      A 2 s ≠ 0 ∧ A 2 t ≠ 0 ∧
      PlaneRowTransport.projectedColumn A s ≠ PlaneRowTransport.projectedColumn A t)
    (_ : ∀ x ∈ T, ∀ A ∈ F x, 0 ≤ W A)
    (_ : ∀ x ∈ T, ∀ A ∈ F x, 0 < W A →
      ∃ C : Set (Fin 3 → ZMod q), AuxiliaryCap.IsCap C ∧
        ∀ i, residueColumns q A i ∈ C)
    (_ : ∀ x ∈ T, ∀ A ∈ F x,
      AffineIndependent (ZMod q) (residueColumns q A) → W A ≤ Ca)
    (_ : ∀ x ∈ T, ∀ A ∈ F x,
      AffineIndependent (ZMod q) (residueColumns q A) →
      0 < W A → D.h ^ 2 < ‖toEuclidean x‖)
    (hwall : ∀ x ∈ T, ∀ A ∈ F x, W A ≤ Cg * (q : ℝ) ^ 2 * D.h ^ 24)
    (_ : ∀ x ∈ T, ∀ A ∈ F x,
      (∃ i j : Fin 3, residueColumns q A i ≠ residueColumns q A j) →
      W A ≤ Cd * (q : ℝ) * D.h ^ 12) (p : Fin 3) :
    (∑ x ∈ T, ∑ A ∈ (F x).filter (fun A =>
      EqualPair (residueColumns q A) p ∧
        ¬ ExceptionalVector (fun i => (x i : ZMod q)) p), W A) ≤
    125 * planeConstant * Cg * N ^ 6 / (D.I : ℝ) ^ 2 := by
  let T' := T.filter (fun x => ¬ ExceptionalVector (fun i => (x i : ZMod q)) p)
  let F' := fun x => (F x).filter (fun A => EqualPair (residueColumns q A) p)
  have hij : (columnPair p).1 ≠ (columnPair p).2 := by
    fin_cases p <;> decide
  have hspan : ∀ x ∈ T', ¬ ∃ a : ZMod q,
      (fun s => (x s : ZMod q)) =
        a • PlaneFunctional.coordinateDifference (columnPair p).1 (columnPair p).2 := by
    intro x hx he
    apply (Finset.mem_filter.mp hx).2
    obtain ⟨a, ha⟩ := he
    apply Submodule.mem_span_singleton.mpr
    refine ⟨a, ?_⟩
    rw [ha]
    congr 1
    ext t
    simp only [PlaneFunctional.coordinateDifference, Pi.single_apply, Pi.sub_apply]
    split_ifs <;> rfl
  have hb := additional_shell_le D q hEq hparam (columnPair p).1 (columnPair p).2
    hij T' (fun x hx => hprimitive x (Finset.mem_filter.mp hx).1) hspan F'
    (fun x hx A hA => hF x A (Finset.mem_filter.mp hA).1) W (R : ℝ) N Cg
    (by exact_mod_cast hR) hN hCg
    (fun x hx => ⟨(hnorm x (Finset.mem_filter.mp hx).1).1,
      (hnorm x (Finset.mem_filter.mp hx).1).2.le⟩)
    (fun x hx A hA s => congrFun (Finset.mem_filter.mp hA).2 s)
    (fun x hx A hA => hcoord x (Finset.mem_filter.mp hx).1 A (Finset.mem_filter.mp hA).1)
    (fun x hx A hA => hproj x (Finset.mem_filter.mp hx).1 A (Finset.mem_filter.mp hA).1)
    (fun x hx A hA => hwall x (Finset.mem_filter.mp hx).1 A (Finset.mem_filter.mp hA).1)
  calc
    _ = ∑ x ∈ T', ∑ A ∈ F' x, W A := by
      simp only [T', F', Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro x hx
      by_cases hp : ExceptionalVector (fun i => (x i : ZMod q)) p
      · simp [hp]
      · simp [hp]
    _ ≤ _ := hb

private theorem special_case_bound (D : RowData) (q R : ℕ) [Fact q.Prime]
    (_ : IsUnit (D.E : ZMod q)) (hparam : D.h ^ 26 ≤ (q : ℝ))
    (T : Finset IntVector) (hR : 0 < R)
    (hprimitive : ∀ x ∈ T, IsPrimitive x)
    (hnonzero : ∀ x ∈ T, ∀ i, x i ≠ 0)
    (hnorm : ∀ x ∈ T, (R : ℝ) ≤ ‖toEuclidean x‖ ∧
      ‖toEuclidean x‖ < 2 * (R : ℝ))
    (F : IntVector → Finset IntMatrix)
    (hF : ∀ x, ∀ A ∈ F x, A *ᵥ x = 0 ∧ ∀ i, A i ∈ D.L)
    (W : IntMatrix → ℝ) (N Ca Cg Cd : ℝ)
    (hN : 0 ≤ N) (_ : 0 ≤ Ca) (_ : 0 ≤ Cg) (hCd : 0 ≤ Cd)
    (hcoord : ∀ x ∈ T, ∀ A ∈ F x, ∀ i j, |(A i j : ℝ)| ≤ 2 * N)
    (hproj : ∀ x ∈ T, ∀ A ∈ F x, ∃ s t : Fin 3,
      A 2 s ≠ 0 ∧ A 2 t ≠ 0 ∧
      PlaneRowTransport.projectedColumn A s ≠ PlaneRowTransport.projectedColumn A t)
    (_ : ∀ x ∈ T, ∀ A ∈ F x, 0 ≤ W A)
    (_ : ∀ x ∈ T, ∀ A ∈ F x, 0 < W A →
      ∃ C : Set (Fin 3 → ZMod q), AuxiliaryCap.IsCap C ∧
        ∀ i, residueColumns q A i ∈ C)
    (_ : ∀ x ∈ T, ∀ A ∈ F x,
      AffineIndependent (ZMod q) (residueColumns q A) → W A ≤ Ca)
    (_ : ∀ x ∈ T, ∀ A ∈ F x,
      AffineIndependent (ZMod q) (residueColumns q A) →
      0 < W A → D.h ^ 2 < ‖toEuclidean x‖)
    (_ : ∀ x ∈ T, ∀ A ∈ F x, W A ≤ Cg * (q : ℝ) ^ 2 * D.h ^ 24)
    (hwdist : ∀ x ∈ T, ∀ A ∈ F x,
      (∃ i j : Fin 3, residueColumns q A i ≠ residueColumns q A j) →
      W A ≤ Cd * (q : ℝ) * D.h ^ 12) (p : Fin 3) :
    (∑ x ∈ T, ∑ A ∈ (F x).filter (fun A =>
      EqualPair (residueColumns q A) p ∧
        ExceptionalVector (fun i => (x i : ZMod q)) p ∧
        ∃ i j : Fin 3, residueColumns q A i ≠ residueColumns q A j), W A) ≤
    512 * planeConstant * Cd * N ^ 6 / (D.I : ℝ) ^ 2 := by
  let T' := T.filter (fun x => ExceptionalVector (fun i => (x i : ZMod q)) p)
  let F' := fun x => (F x).filter (fun A => EqualPair (residueColumns q A) p ∧
    ∃ i j : Fin 3, residueColumns q A i ≠ residueColumns q A j)
  let l : Fin 3 := ![2, 1, 0] p
  have hli : l ≠ (columnPair p).1 := by fin_cases p <;> decide
  have hlj : l ≠ (columnPair p).2 := by fin_cases p <;> decide
  have h14 : D.h ^ 14 ≤ (q : ℝ) :=
    (pow_le_pow_right₀ D.h_one (by norm_num : 14 ≤ 26)).trans hparam
  have hb := special_shell_le D q R (Fact.out : q.Prime).pos hR T'
    (fun x hx => hprimitive x (Finset.mem_filter.mp hx).1)
    (fun x hx => hnorm x (Finset.mem_filter.mp hx).1)
    (columnPair p).1 (columnPair p).2 l hli hlj
    (fun x hx => hnonzero x (Finset.mem_filter.mp hx).1 l)
    (fun x hx => (Finset.mem_filter.mp hx).2) F'
    (fun x A hA => hF x A (Finset.mem_filter.mp hA).1) W N Cd hN hCd h14
    (fun x hx A hA => hcoord x (Finset.mem_filter.mp hx).1 A (Finset.mem_filter.mp hA).1)
    (fun x hx A hA => hproj x (Finset.mem_filter.mp hx).1 A (Finset.mem_filter.mp hA).1)
    (fun x hx A hA => hwdist x (Finset.mem_filter.mp hx).1 A
      (Finset.mem_filter.mp hA).1 (Finset.mem_filter.mp hA).2.2)
  have heq : (∑ x ∈ T, ∑ A ∈ (F x).filter (fun A =>
      EqualPair (residueColumns q A) p ∧
        ExceptionalVector (fun i => (x i : ZMod q)) p ∧
        ∃ i j : Fin 3, residueColumns q A i ≠ residueColumns q A j), W A) =
      ∑ x ∈ T', ∑ A ∈ F' x, W A := by
    simp only [T', F', Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro x hx
    by_cases hp : ExceptionalVector (fun i => (x i : ZMod q)) p
    · simp [hp]
    · simp [hp]
  rw [heq]
  exact hb

private theorem combine_case_bounds (D : RowData) (q : ℕ) [Fact q.Prime]
    (T : Finset IntVector) (hprimitive : ∀ x ∈ T, IsPrimitive x)
    (F : IntVector → Finset IntMatrix) (W : IntMatrix → ℝ) (N Ca Cg Cd : ℝ)
    (hW : ∀ x ∈ T, ∀ A ∈ F x, 0 ≤ W A)
    (hcap : ∀ x ∈ T, ∀ A ∈ F x, 0 < W A →
      ∃ C : Set (Fin 3 → ZMod q), AuxiliaryCap.IsCap C ∧
        ∀ i, residueColumns q A i ∈ C)
    (haff : (∑ x ∈ T, ∑ A ∈ (F x).filter (fun A => AffineIndependent (ZMod q)
      (A.map (Int.castRingHom (ZMod q))).col), W A) ≤
      1024 * planeConstant * Ca * N ^ 6 / (D.I : ℝ) ^ 2)
    (hadd : ∀ p : Fin 3,
      (∑ x ∈ T, ∑ A ∈ (F x).filter (fun A => EqualPair (residueColumns q A) p ∧
        ¬ ExceptionalVector (fun i => (x i : ZMod q)) p), W A) ≤
      125 * planeConstant * Cg * N ^ 6 / (D.I : ℝ) ^ 2)
    (hspecial : ∀ p : Fin 3,
      (∑ x ∈ T, ∑ A ∈ (F x).filter (fun A => EqualPair (residueColumns q A) p ∧
        ExceptionalVector (fun i => (x i : ZMod q)) p ∧
        ∃ i j : Fin 3, residueColumns q A i ≠ residueColumns q A j), W A) ≤
      512 * planeConstant * Cd * N ^ 6 / (D.I : ℝ) ^ 2) :
    (∑ x ∈ T, ∑ A ∈ F x, W A) ≤
      (1024 * Ca + 3 * (125 * Cg + 512 * Cd)) * planeConstant * N ^ 6 /
        (D.I : ℝ) ^ 2 := by
  let faff := fun x => ∑ A ∈ (F x).filter
    (fun A => AffineIndependent (ZMod q) (residueColumns q A)), W A
  let fadd := fun p x => ∑ A ∈ (F x).filter (fun A =>
    EqualPair (residueColumns q A) p ∧
      ¬ ExceptionalVector (fun i => (x i : ZMod q)) p), W A
  let fspecial := fun p x => ∑ A ∈ (F x).filter (fun A =>
    EqualPair (residueColumns q A) p ∧
      ExceptionalVector (fun i => (x i : ZMod q)) p ∧
      ∃ i j : Fin 3, residueColumns q A i ≠ residueColumns q A j), W A
  have hpoint (x : IntVector) (hx : x ∈ T) :
      (∑ A ∈ F x, W A) ≤ faff x + ∑ p : Fin 3, (fadd p x + fspecial p x) := by
    have hh := matrix_sum_le_three_case_sums q x (hprimitive x hx) (F x) W
      (hW x hx) (hcap x hx)
    simpa only [faff, fadd, fspecial, exceptionalVector_reduction] using hh
  have haff' : (∑ x ∈ T, faff x) ≤
      1024 * planeConstant * Ca * N ^ 6 / (D.I : ℝ) ^ 2 := by
    calc
      _ = ∑ x ∈ T, ∑ A ∈ (F x).filter (fun A => AffineIndependent (ZMod q)
          (A.map (Int.castRingHom (ZMod q))).col), W A := by
        apply Finset.sum_congr rfl
        intro x hx
        apply Finset.sum_congr
        · apply Finset.filter_congr
          intro A hA
          rfl
        · intro A hA
          rfl
      _ ≤ _ := haff
  calc
    (∑ x ∈ T, ∑ A ∈ F x, W A) ≤
        ∑ x ∈ T, (faff x + ∑ p : Fin 3, (fadd p x + fspecial p x)) :=
      Finset.sum_le_sum hpoint
    _ = (∑ x ∈ T, faff x) + ∑ p : Fin 3,
        ((∑ x ∈ T, fadd p x) + (∑ x ∈ T, fspecial p x)) := by
      rw [Finset.sum_add_distrib]
      congr 1
      rw [Finset.sum_comm]
      simp only [Finset.sum_add_distrib]
    _ ≤ (1024 * planeConstant * Ca * N ^ 6 / (D.I : ℝ) ^ 2) +
        ∑ _p : Fin 3, ((125 * planeConstant * Cg * N ^ 6 / (D.I : ℝ) ^ 2) +
          (512 * planeConstant * Cd * N ^ 6 / (D.I : ℝ) ^ 2)) := by
      apply add_le_add haff'
      exact Finset.sum_le_sum fun p _ => add_le_add (hadd p) (hspecial p)
    _ = _ := by simp; ring

theorem combined_shell_le (D : RowData) (q R : ℕ) [Fact q.Prime]
    (hEq : IsUnit (D.E : ZMod q)) (hparam : D.h ^ 26 ≤ (q : ℝ))
    (T : Finset IntVector) (hR : 0 < R)
    (hprimitive : ∀ x ∈ T, IsPrimitive x)
    (hnonzero : ∀ x ∈ T, ∀ i, x i ≠ 0)
    (hnorm : ∀ x ∈ T, (R : ℝ) ≤ ‖toEuclidean x‖ ∧
      ‖toEuclidean x‖ < 2 * (R : ℝ))
    (F : IntVector → Finset IntMatrix)
    (hF : ∀ x, ∀ A ∈ F x, A *ᵥ x = 0 ∧ ∀ i, A i ∈ D.L)
    (W : IntMatrix → ℝ) (N Ca Cg Cd : ℝ)
    (hN : 0 ≤ N) (hCa : 0 ≤ Ca) (hCg : 0 ≤ Cg) (hCd : 0 ≤ Cd)
    (hcoord : ∀ x ∈ T, ∀ A ∈ F x, ∀ i j, |(A i j : ℝ)| ≤ 2 * N)
    (hproj : ∀ x ∈ T, ∀ A ∈ F x, ∃ s t : Fin 3,
      A 2 s ≠ 0 ∧ A 2 t ≠ 0 ∧
      PlaneRowTransport.projectedColumn A s ≠ PlaneRowTransport.projectedColumn A t)
    (hW : ∀ x ∈ T, ∀ A ∈ F x, 0 ≤ W A)
    (hcap : ∀ x ∈ T, ∀ A ∈ F x, 0 < W A →
      ∃ C : Set (Fin 3 → ZMod q), AuxiliaryCap.IsCap C ∧
        ∀ i, residueColumns q A i ∈ C)
    (hwaff : ∀ x ∈ T, ∀ A ∈ F x,
      AffineIndependent (ZMod q) (residueColumns q A) → W A ≤ Ca)
    (hexclude : ∀ x ∈ T, ∀ A ∈ F x,
      AffineIndependent (ZMod q) (residueColumns q A) →
      0 < W A → D.h ^ 2 < ‖toEuclidean x‖)
    (hwall : ∀ x ∈ T, ∀ A ∈ F x, W A ≤ Cg * (q : ℝ) ^ 2 * D.h ^ 24)
    (hwdist : ∀ x ∈ T, ∀ A ∈ F x,
      (∃ i j : Fin 3, residueColumns q A i ≠ residueColumns q A j) →
      W A ≤ Cd * (q : ℝ) * D.h ^ 12) :
    (∑ x ∈ T, ∑ A ∈ F x, W A) ≤
      (1024 * Ca + 3 * (125 * Cg + 512 * Cd)) * planeConstant * N ^ 6 /
        (D.I : ℝ) ^ 2 := by
  have haff := affine_shell_le D q R T hR hprimitive hnorm F hF W N Ca hN hCa
    hcoord hproj hwaff hexclude
  have hadd := additional_case_bound D q R hEq hparam T hR hprimitive hnonzero hnorm F hF W N Ca Cg Cd hN hCa hCg hCd hcoord hproj hW hcap hwaff hexclude hwall hwdist
  have hspecial := special_case_bound D q R hEq hparam T hR hprimitive hnonzero hnorm F hF W N Ca Cg Cd hN hCa hCg hCd hcoord hproj hW hcap hwaff hexclude hwall hwdist
  exact combine_case_bounds D q T hprimitive F W N Ca Cg Cd hW hcap haff hadd hspecial

end Problem355.ZeroDeterminantCount

end

end OAI
