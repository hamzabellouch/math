import OAI.NumberTheory.JointDickman.Arithmetic.PrimeProductBoundary

namespace OAI

/-! # Repeated-prime tuples have vanishing reciprocal weight -/
namespace JointDickman
open Finset Filter MeasureTheory
open scoped Topology NNReal ENNReal

theorem pi_coordinate_diagonal_null (μ : Measure ℝ) [IsFiniteMeasure μ] [NullSingletonClass μ]
    {n : ℕ} (i j : Fin (n+1)) (hij : i ≠ j) :
    (Measure.pi (fun _ : Fin (n+1) => μ)) {t | t i = t j} = 0 := by
  obtain ⟨k,rfl⟩ := Fin.exists_succAbove_eq hij.symm
  let E : Set (ℝ × (Fin n → ℝ)) := {t | t.1 = t.2 k}
  have hE : MeasurableSet E := by
    have h1 : Continuous (fun t : ℝ × (Fin n → ℝ) => t.1) := continuous_fst
    have h2 : Continuous (fun t : ℝ × (Fin n → ℝ) => t.2 k) :=
      (continuous_apply k).comp continuous_snd
    exact (isClosed_eq h1 h2).measurableSet
  have he : (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) i) ⁻¹' E =
      {t | t i = t (i.succAbove k)} := by
    ext t
    rfl
  rw [← he, (measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => μ) i).measure_preimage hE.nullMeasurableSet,
    Measure.prod_apply_symm hE]
  have hf (t : Fin n → ℝ) : (fun x : ℝ => (x,t)) ⁻¹' E = {t k} := rfl
  simp only [hf, measure_singleton, lintegral_zero]

noncomputable def tupleDiagonal (n : ℕ) : Set (Fin n → ℝ) :=
  {t | ¬Function.Injective t}

theorem tupleDiagonal_eq_union (n : ℕ) :
    tupleDiagonal n = ⋃ i : Fin n, ⋃ j : Fin n,
      if i = j then ∅ else {t | t i = t j} := by
  classical
  ext t
  simp only [tupleDiagonal, Set.mem_ofPred_eq, Set.mem_iUnion]
  constructor
  · intro ht
    obtain ⟨i,j,hij,hne⟩ := Function.not_injective_iff.mp ht
    exact ⟨i,j,by simp [hne,hij]⟩
  · rintro ⟨i,j,ht⟩
    by_cases hij : i = j
    · simp [hij] at ht
    · simp only [hij, ite_false, Set.mem_ofPred_eq] at ht
      exact fun hinj => hij (hinj ht)

theorem tupleDiagonal_isClosed (n : ℕ) : IsClosed (tupleDiagonal n) := by
  classical
  rw [tupleDiagonal_eq_union]
  apply isClosed_iUnion_of_finite
  intro i
  apply isClosed_iUnion_of_finite
  intro j
  split_ifs
  · exact isClosed_empty
  · exact isClosed_eq (continuous_apply i) (continuous_apply j)

theorem pi_tupleDiagonal_null (μ : Measure ℝ) [IsFiniteMeasure μ] [NullSingletonClass μ]
    (n : ℕ) : (Measure.pi (fun _ : Fin (n+1) => μ)) (tupleDiagonal (n+1)) = 0 := by
  classical
  rw [tupleDiagonal_eq_union]
  apply measure_iUnion_null
  intro i
  apply measure_iUnion_null
  intro j
  split_ifs with hij
  · exact measure_empty
  · exact pi_coordinate_diagonal_null μ i j hij

theorem primeLogProduct_diagonal_tendsto_zero {c : ℝ} (hc : 0 < c) (hc1 : c < 1)
    (n : ℕ) :
    Tendsto (fun x => ((FiniteMeasure.pi (fun _ : Fin (n+1) => primeLogMeasure c x))
      (tupleDiagonal (n+1)) : ℝ)) atTop (𝓝 0) := by
  have hm0 : (logarithmicPrimeMeasure c).mass ≠ 0 := by
    intro h
    have he := congrArg ((↑) : ℝ≥0 → ℝ) h
    rw [logarithmicPrimeMeasure_mass hc hc1.le, NNReal.coe_zero] at he
    linarith [Real.log_neg hc hc1]
  have hne : (FiniteMeasure.pi (fun _ : Fin (n+1) => logarithmicPrimeMeasure c)) ≠ 0 := by
    apply (FiniteMeasure.mass_nonzero_iff _).mp
    rw [FiniteMeasure.mass_pi]
    exact prod_ne_zero_iff.mpr (fun _ _ => hm0)
  have hnull : (FiniteMeasure.pi (fun _ : Fin (n+1) => logarithmicPrimeMeasure c))
      (tupleDiagonal (n+1)) = 0 := by
    apply (FiniteMeasure.null_iff_toMeasure_null _ _).mpr
    exact pi_tupleDiagonal_null _ n
  have hfront : (FiniteMeasure.pi (fun _ : Fin (n+1) => logarithmicPrimeMeasure c))
      (frontier (tupleDiagonal (n+1))) = 0 := by
    apply le_antisymm _ bot_le
    exact (FiniteMeasure.apply_mono _ (frontier_subset_iff_isClosed.mpr (tupleDiagonal_isClosed _))).trans_eq hnull
  have ht := NNReal.tendsto_coe.mpr (finiteMeasure_set_tendsto
    (primeLogProduct_tendsto hc hc1 (n+1)) hne hfront)
  simpa only [hnull,NNReal.coe_zero] using ht

end JointDickman

end OAI
