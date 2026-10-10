import Mathlib
import Mathlib.LinearAlgebra.Projectivization.Basic
import OAI.Combinatorics.BalancedRyser.Incidence.Projective2

namespace OAI

namespace Balanced
open scoped _root_.Balanced

variable {F : Type*} [Field F]

def homogeneousPoint : ProjectivePoint F → Fin 3 → F
  | Sum.inl p => ![p.1, p.2, 1]
  | Sum.inr none => ![0, 1, 0]
  | Sum.inr (some m) => ![1, m, 0]

def homogeneousLine : ProjectiveLine F → Fin 3 → F
  | none => ![0, 0, 1]
  | some (none, b) => ![1, 0, -b]
  | some (some m, b) => ![-m, 1, -b]

theorem homogeneousPoint_ne_zero (P : ProjectivePoint F) : homogeneousPoint P ≠ 0 := by
  cases P with
  | inl p =>
    intro h
    have h2 := congrFun h 2
    simp [homogeneousPoint] at h2
  | inr d =>
    cases d with
    | none =>
      intro h
      have h1 := congrFun h 1
      simp [homogeneousPoint] at h1
    | some m =>
      intro h
      have h0 := congrFun h 0
      simp [homogeneousPoint] at h0

def toProjectivization (P : ProjectivePoint F) : Projectivization F (Fin 3 → F) :=
  Projectivization.mk F (homogeneousPoint P) (homogeneousPoint_ne_zero P)

noncomputable def normalizeProjective (v : Fin 3 → F) : ProjectivePoint F := by
  classical
  exact if v 2 ≠ 0 then Sum.inl (v 0 / v 2, v 1 / v 2)
    else if v 0 ≠ 0 then Sum.inr (some (v 1 / v 0)) else Sum.inr none

@[simp] theorem normalize_homogeneousPoint (P : ProjectivePoint F) :
    normalizeProjective (homogeneousPoint P) = P := by
  cases P with
  | inl p => rcases p with ⟨x,y⟩; simp [normalizeProjective, homogeneousPoint]
  | inr d => cases d <;> simp [normalizeProjective, homogeneousPoint]

theorem normalizeProjective_smul (a : F) (ha : a ≠ 0) (v : Fin 3 → F) :
    normalizeProjective (a • v) = normalizeProjective v := by
  classical
  simp [normalizeProjective, Pi.smul_apply, smul_eq_mul, ha, mul_div_mul_left]

theorem exists_smul_homogeneous_normalize (v : Fin 3 → F) (hv : v ≠ 0) :
    ∃ a : F, a ≠ 0 ∧ a • homogeneousPoint (normalizeProjective v) = v := by
  classical
  by_cases h2 : v 2 ≠ 0
  · refine ⟨v 2, h2, ?_⟩
    ext i
    fin_cases i <;> simp [normalizeProjective, h2, homogeneousPoint, Pi.smul_apply,
      smul_eq_mul, mul_div_cancel₀]
  · have hz2 : v 2 = 0 := not_not.mp h2
    by_cases h0 : v 0 ≠ 0
    · refine ⟨v 0, h0, ?_⟩
      ext i
      fin_cases i <;> simp [normalizeProjective, hz2, h0, homogeneousPoint,
        Pi.smul_apply, smul_eq_mul, mul_div_cancel₀]
    · have hz0 : v 0 = 0 := not_not.mp h0
      have h1 : v 1 ≠ 0 := by
        intro h1
        apply hv
        ext i
        fin_cases i <;> simp_all
      refine ⟨v 1, h1, ?_⟩
      ext i
      fin_cases i <;> simp [normalizeProjective, hz2, hz0, homogeneousPoint,
        Pi.smul_apply, smul_eq_mul]

theorem toProjectivization_injective : Function.Injective (toProjectivization (F := F)) := by
  intro P Q h
  obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff' F _ _
    (homogeneousPoint_ne_zero P) (homogeneousPoint_ne_zero Q)).mp h
  have hane : a ≠ 0 := by
    intro hzero
    apply homogeneousPoint_ne_zero P
    simpa [hzero] using ha.symm
  have hn := congrArg normalizeProjective ha
  simpa only [normalizeProjective_smul a hane, normalize_homogeneousPoint] using hn.symm

theorem toProjectivization_surjective : Function.Surjective (toProjectivization (F := F)) := by
  intro P
  induction P using Projectivization.ind with
  | h v hv =>
    obtain ⟨a, ha, hs⟩ := exists_smul_homogeneous_normalize v hv
    refine ⟨normalizeProjective v, ?_⟩
    symm
    exact (Projectivization.mk_eq_mk_iff' F _ _ hv
      (homogeneousPoint_ne_zero (normalizeProjective v))).mpr ⟨a, hs⟩

noncomputable def projectiveModelEquiv :
    ProjectivePoint F ≃ Projectivization F (Fin 3 → F) :=
  Equiv.ofBijective toProjectivization
    ⟨toProjectivization_injective, toProjectivization_surjective⟩

theorem projective_incident_iff_homogeneous (P : ProjectivePoint F) (l : ProjectiveLine F) :
    ProjectiveIncident P l ↔
      (∑ i : Fin 3, homogeneousLine l i * homogeneousPoint P i) = 0 := by
  cases P with
  | inl p =>
    rcases p with ⟨x,y⟩
    cases l with
    | none => simp [ProjectiveIncident, homogeneousLine, homogeneousPoint, Fin.sum_univ_succ]
    | some l =>
      rcases l with ⟨d,b⟩
      cases d with
      | none =>
        simp only [ProjectiveIncident, homogeneousLine, homogeneousPoint,
          ThroughProjective, OnLine, lineEval]
        simp [Fin.sum_univ_succ]
        constructor <;> intro h <;> linear_combination h
      | some m =>
        simp [ProjectiveIncident, homogeneousLine, homogeneousPoint,
          ThroughProjective, OnLine, lineEval, Fin.sum_univ_succ]
        constructor <;> intro h <;> linear_combination h
  | inr d =>
    cases d with
    | none =>
      cases l with
      | none => simp [ProjectiveIncident, homogeneousLine, homogeneousPoint, Fin.sum_univ_succ]
      | some l =>
        rcases l with ⟨d,b⟩
        cases d <;> simp [ProjectiveIncident, homogeneousLine, homogeneousPoint,
          ThroughProjective, Fin.sum_univ_succ]
    | some m =>
      cases l with
      | none => simp [ProjectiveIncident, homogeneousLine, homogeneousPoint, Fin.sum_univ_succ]
      | some l =>
        rcases l with ⟨d,b⟩
        cases d with
        | none => simp [ProjectiveIncident, homogeneousLine, homogeneousPoint,
            ThroughProjective, Fin.sum_univ_succ]
        | some a =>
          simp [ProjectiveIncident, homogeneousLine, homogeneousPoint,
            ThroughProjective, Fin.sum_univ_succ]
          constructor <;> intro h <;> linear_combination -h

theorem homogeneousLine_ne_zero (l : ProjectiveLine F) : homogeneousLine l ≠ 0 := by
  cases l with
  | none =>
    intro h
    have hh := congrFun h 2
    simp [homogeneousLine] at hh
  | some l =>
    rcases l with ⟨d,b⟩
    cases d with
    | none =>
      intro h
      have hh := congrFun h 0
      simp [homogeneousLine] at hh
    | some m =>
      intro h
      have hh := congrFun h 1
      simp [homogeneousLine] at hh

noncomputable def projectiveLineModelEquiv :
    ProjectiveLine F ≃ Projectivization F (Fin 3 → F) :=
  projectiveDuality.symm.trans projectiveModelEquiv

variable [Fintype F]

omit [Field F] in
theorem card_projectivePoint :
    Fintype.card (ProjectivePoint F) = Fintype.card F ^ 2 + Fintype.card F + 1 := by
  simp only [ProjectivePoint, Point, Direction, Fintype.card_sum,
    Fintype.card_prod, Fintype.card_option]
  ring

omit [Field F] in
theorem card_projectiveLine :
    Fintype.card (ProjectiveLine F) = Fintype.card F ^ 2 + Fintype.card F + 1 := by
  simp only [ProjectiveLine, Line, Direction, Fintype.card_prod, Fintype.card_option]
  ring

end Balanced

end OAI
