import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Data.List.FinRange
import OAI.NumberTheory.Ostmann.Arithmetic.BulkIntegrands

namespace OAI

/-! # The joint bulk integral in ordinary finite product coordinates -/

namespace Ostmann
open MeasureTheory
open scoped Classical BigOperators

noncomputable def BulkIntegrand.headSlice {n : ℕ}
    (f : BulkIntegrand (Fin (n + 1))) (a : ℝ) : BulkIntegrand (Fin n) where
  toFun x := f (Fin.cons a x)
  measurable := f.measurable.comp (Measurable.of_eval (fun i => by
    refine Fin.cases ?_ (fun j => ?_) i
    · exact measurable_const
    · exact measurable_pi_apply j))
  bounded := by
    obtain ⟨C, hC, hf⟩ := f.bounded
    exact ⟨C, hC, fun x => hf _⟩

theorem fin_cons_update {n : ℕ} (a b : ℝ) (x : Fin n → ℝ) (i : Fin n) :
    (show Fin (n + 1) → ℝ from Fin.cons a
      (@Function.update (Fin n) (fun _ => ℝ) (Classical.decEq _) x i b)) =
      @Function.update (Fin (n + 1)) (fun _ => ℝ) (Classical.decEq _)
        (Fin.cons a x) i.succ b := by
  funext j
  refine Fin.cases ?_ (fun j => ?_) j
  · simp [Function.update, Ne.symm (Fin.succ_ne_zero i)]
  · by_cases hj : j = i
    · subst j; simp [Function.update]
    · simp [Function.update, hj]

theorem BulkIntegrand.headSlice_average {n : ℕ} (f : BulkIntegrand (Fin (n + 1)))
    (μ : Measure ℝ) [IsFiniteMeasure μ] (i : Fin n) (a : ℝ) :
    (f.average μ i.succ).headSlice a = (f.headSlice a).average μ i := by
  ext x
  dsimp only [headSlice, average]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun b => congrArg f (fin_cons_update a b x i).symm

theorem BulkIntegrand.headSlice_averages {n : ℕ} (f : BulkIntegrand (Fin (n + 1)))
    (μ : Fin (n + 1) → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)]
    (l : List (Fin n)) (a : ℝ) :
    (f.averages μ (l.map Fin.succ)).headSlice a =
      (f.headSlice a).averages (fun i => μ i.succ) l := by
  induction l with
  | nil => rfl
  | cons i l ih => simp only [List.map_cons, averages, headSlice_average, ih]

/-- Finite-measure Fubini, with the first coordinate displayed explicitly. -/
theorem BulkIntegrand.integral_headSlice {n : ℕ} (f : BulkIntegrand (Fin (n + 1)))
    (μ : Fin (n + 1) → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] :
    (∫ x, f x ∂Measure.pi μ) =
      ∫ a, ∫ x, f.headSlice a x ∂Measure.pi (fun i => μ i.succ) ∂μ 0 := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0
  have he := (measurePreserving_piFinSuccAbove μ 0).symm
  have hi := (he.integrable_comp_emb e.symm.measurableEmbedding).mpr (f.integrable (Measure.pi μ))
  rw [← he.integral_comp' (fun x => f x)]
  change (∫ z, (f ∘ e.symm) z ∂(μ 0).prod (Measure.pi (fun j => μ (Fin.succAbove 0 j)))) = _
  rw [integral_prod (f ∘ e.symm) hi]
  congr 1
  funext a
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    simp only [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
      Fin.insertNth_zero, headSlice, Function.comp_apply, Equiv.coe_fn_mk, cast_eq]

theorem BulkIntegrand.averages_finRange {n : ℕ} (f : BulkIntegrand (Fin n))
    (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] (x : Fin n → ℝ) :
    f.averages μ (List.finRange n) x = ∫ y, f y ∂Measure.pi μ := by
  induction n with
  | zero =>
    have hf (y : Fin 0 → ℝ) : f y = f x := congrArg f (Subsingleton.elim _ _)
    simp only [List.finRange_zero, averages]
    simp_rw [hf]
    have hm : (Measure.pi μ).real Set.univ = 1 := by
      rw [Measure.real, Measure.pi_univ]
      simp
    simp only [integral_const, Complex.real_smul, hm, Complex.ofReal_one, one_mul]
  | succ n ih =>
    rw [f.integral_headSlice μ, List.finRange_succ]
    dsimp only [averages, average]
    apply integral_congr_ae
    refine Filter.Eventually.of_forall fun a => ?_
    have hx : @Function.update (Fin (n + 1)) (fun _ => ℝ) (Classical.decEq _)
        x 0 a = Fin.cons a (fun i => x i.succ) := by
      funext j
      refine Fin.cases ?_ (fun j => ?_) j <;> simp
    dsimp only
    calc
      _ = (f.averages μ ((List.finRange n).map Fin.succ)) (Fin.cons a (fun i => x i.succ)) :=
        congrArg (fun z => (f.averages μ ((List.finRange n).map Fin.succ)) z) hx
      _ = _ := by
        change ((f.averages μ ((List.finRange n).map Fin.succ)).headSlice a) (fun i => x i.succ) = _
        rw [f.headSlice_averages]
        exact ih _ _ _

end Ostmann

end OAI
