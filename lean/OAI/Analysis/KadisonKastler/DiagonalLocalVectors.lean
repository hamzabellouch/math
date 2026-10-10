import OAI.Analysis.KadisonKastler.DiagonalLocality
import Mathlib.MeasureTheory.Function.Floor

namespace OAI

/-! # Local vector representatives for a diagonal operator

Apply the operator to constant vectors cut off on `[-n,n]`. Locality
makes these representatives agree on overlaps. Selecting the interval
of radius `ceil |t|` gives measurable vector values on the whole line.
-/

namespace KadisonKastler

open MeasureTheory Filter

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

def diagonalTestVector (n : ℕ) (ξ : H) : RegularCoreHilbert H :=
  indicatorConstLp 2 (measurableSet_Icc (a := -(n : ℝ)) (b := n)) (by simp) ξ

omit [InnerProductSpace ℂ H] [CompleteSpace H] in
theorem diagonalTestVector_ae (n : ℕ) (ξ : H) :
    diagonalTestVector n ξ =ᵐ[volume]
      (Set.Icc (-(n : ℝ)) (n : ℝ)).indicator (fun _ => ξ) :=
  indicatorConstLp_coeFn

omit [InnerProductSpace ℂ H] [CompleteSpace H] in
theorem diagonalTestVector_add (n : ℕ) (ξ η : H) :
    diagonalTestVector n (ξ + η) = diagonalTestVector n ξ + diagonalTestVector n η :=
  indicatorConstLp_add.symm

omit [CompleteSpace H] in
theorem diagonalTestVector_smul (n : ℕ) (c : ℂ) (ξ : H) :
    diagonalTestVector n (c • ξ) = c • diagonalTestVector n ξ := by
  apply Lp.ext
  filter_upwards [diagonalTestVector_ae n (c • ξ), diagonalTestVector_ae n ξ,
    Lp.coeFn_smul c (diagonalTestVector n ξ)] with t hc hξ hs
  rw [hc, hs]
  simp only [Pi.smul_apply, hξ]
  by_cases ht : t ∈ Set.Icc (-(n : ℝ)) (n : ℝ) <;> simp [ht]

def diagonalRawVector
    (T : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) (ξ : H) (t : ℝ) : H :=
  T (diagonalTestVector (Nat.ceil |t|) ξ) t

theorem diagonalRawVector_measurable [TopologicalSpace.SeparableSpace H]
    (T : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) (ξ : H) :
    AEStronglyMeasurable (diagonalRawVector T ξ) volume := by
  let : MeasurableSpace H := borel H
  let : BorelSpace H := ⟨rfl⟩
  have hev : Measurable (fun p : ℕ × (ℕ → H) => p.2 p.1) :=
    measurable_from_prod_countable_right fun n => measurable_pi_apply n
  have hseq : AEMeasurable (fun t : ℝ => fun n : ℕ => T (diagonalTestVector n ξ) t)
      volume := AEMeasurable.of_eval fun n => (Lp.aestronglyMeasurable _).aemeasurable
  exact (hev.comp_aemeasurable
    ((Nat.measurable_ceil.comp measurable_abs).aemeasurable.prodMk hseq)).aestronglyMeasurable

omit [CompleteSpace H] in
theorem diagonalRawVector_add_ae
    (T : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) (ξ η : H) :
    diagonalRawVector T (ξ + η) =ᵐ[volume]
      fun t => diagonalRawVector T ξ t + diagonalRawVector T η t := by
  have hall : ∀ᵐ t : ℝ, ∀ n : ℕ,
      T (diagonalTestVector n (ξ + η)) t =
        T (diagonalTestVector n ξ) t + T (diagonalTestVector n η) t := by
    apply ae_all_iff.mpr
    intro n
    rw [diagonalTestVector_add, map_add]
    exact Lp.coeFn_add _ _
  exact hall.mono fun t ht => ht (Nat.ceil |t|)

omit [CompleteSpace H] in
theorem diagonalRawVector_smul_ae
    (T : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) (c : ℂ) (ξ : H) :
    diagonalRawVector T (c • ξ) =ᵐ[volume] fun t => c • diagonalRawVector T ξ t := by
  have hall : ∀ᵐ t : ℝ, ∀ n : ℕ,
      T (diagonalTestVector n (c • ξ)) t = c • T (diagonalTestVector n ξ) t := by
    apply ae_all_iff.mpr
    intro n
    rw [diagonalTestVector_smul, map_smul]
    exact Lp.coeFn_smul _ _
  exact hall.mono fun t ht => ht (Nat.ceil |t|)

variable (T : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
  (hT : ∀ (s : Set ℝ) (hs : MeasurableSet s),
    Commute T (regularIndicatorProjection s hs))

include hT

theorem diagonalRawVector_norm_ae (ξ : H) :
    ∀ᵐ t : ℝ, ‖diagonalRawVector T ξ t‖ ≤ ‖T‖ * ‖ξ‖ := by
  have hall : ∀ᵐ t : ℝ, ∀ n : ℕ,
      ‖T (diagonalTestVector n ξ) t‖ ≤ ‖T‖ * ‖diagonalTestVector n ξ t‖ :=
    ae_all_iff.mpr fun n => ae_norm_apply_le_of_commute_indicators T hT _
  have hvec : ∀ᵐ t : ℝ, ∀ n : ℕ,
      diagonalTestVector n ξ t = (Set.Icc (-(n : ℝ)) (n : ℝ)).indicator (fun _ => ξ) t :=
    ae_all_iff.mpr fun n => diagonalTestVector_ae n ξ
  filter_upwards [hall, hvec] with t ht hξ
  have hmem : t ∈ Set.Icc (-(Nat.ceil |t| : ℝ)) (Nat.ceil |t| : ℝ) :=
    Set.mem_Icc.mpr (abs_le.mp (Nat.le_ceil |t|))
  simpa only [diagonalRawVector, hξ, Set.indicator_of_mem hmem] using ht (Nat.ceil |t|)

theorem diagonalRawVector_eq_local_ae (ξ : H) (n : ℕ) :
    ∀ᵐ t : ℝ, t ∈ Set.Icc (-(n : ℝ)) (n : ℝ) →
      diagonalRawVector T ξ t = T (diagonalTestVector n ξ) t := by
  have hall : ∀ᵐ t : ℝ, ∀ m : ℕ,
      diagonalTestVector m ξ t = diagonalTestVector n ξ t →
      T (diagonalTestVector m ξ) t = T (diagonalTestVector n ξ) t :=
    ae_all_iff.mpr fun m => ae_apply_eq_of_eq_of_commute_indicators T hT _ _
  have hvec : ∀ᵐ t : ℝ, ∀ m : ℕ,
      diagonalTestVector m ξ t = (Set.Icc (-(m : ℝ)) (m : ℝ)).indicator (fun _ => ξ) t :=
    ae_all_iff.mpr fun m => diagonalTestVector_ae m ξ
  filter_upwards [hall, hvec] with t ht hξ
  intro hn
  apply ht (Nat.ceil |t|)
  rw [hξ, hξ, Set.indicator_of_mem hn]
  exact Set.indicator_of_mem (Set.mem_Icc.mpr (abs_le.mp (Nat.le_ceil |t|))) _

end

end KadisonKastler

end OAI
