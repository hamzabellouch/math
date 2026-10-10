import OAI.NumberTheory.DukePrimeDegree.Dynamics.ExponentialReturnRefinement
import OAI.NumberTheory.DukePrimeDegree.Dynamics.ErgodicReturnLevels

namespace OAI

/-! # A finite-entropy observation with arbitrarily fine recurrent fibers

For an ergodic map and a section with unbounded positive return levels,
the transverse refinement forces future fibers to agree arbitrarily
closely in the chosen transverse coordinates.
-/

noncomputable section
open MeasureTheory Set
namespace DukePrimeDegree

theorem exists_fine_return_observation
    {Y : Type*} [MeasurableSpace Y] (μ : Measure Y) [IsProbabilityMeasure μ]
    {T : Y → Y} (hT : Ergodic T μ) (hE : MeasurableEmbedding T)
    {S : Set Y} (hS : MeasurableSet S)
    (htail : ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ μ (firstReturnLevel T S n) ≠ 0)
    {d : ℕ} (f : Y → Fin d → ℝ) (hf : Measurable f)
    {R : ℝ} (hR : 0 ≤ R) (hbound : ∀ x ∈ S, ∀ i, |f x i| ≤ R) :
    ∃ (K : ℕ → ℕ) (B : ∀ n, Y → Fin (K n)),
      (∀ n, Measurable (B n)) ∧
      Summable (fun z : Option (Σ n : ℕ, Fin (K n)) =>
        Real.negMulLog (μ.real {x | returnRefinement T S B x=z})) ∧
      ∀ᵐ x ∂μ, ∀ y, (∀ k : ℕ,
        returnRefinement T S B (T^[k] y)=returnRefinement T S B (T^[k] x)) →
        ∀ ε : ℝ, 0 < ε → ∃ k : ℕ, T^[k] x ∈ S ∧ T^[k] y ∈ S ∧
          ∀ i, |f (T^[k] y) i-f (T^[k] x) i| < ε := by
  obtain ⟨K,B,hB,hent,hclose⟩ := exists_exponential_return_refinement
    μ hT.toMeasurePreserving hE hS f hf hR hbound
  refine ⟨K,B,hB,hent,?_⟩
  filter_upwards [ae_visits_unbounded_return_levels μ hT hS htail] with x hx
  intro y hy ε hε
  obtain ⟨N,hN⟩ := exists_nat_gt (-Real.log (ε/2))
  obtain ⟨k,n,hn,hret⟩ := hx N
  have hxcode : returnRefinement T S B (T^[k] x)=some ⟨n,B n (T^[k] x)⟩ := by
    have hm : T^[k] x ∈ returnRefinementAtom T S B (some ⟨n,B n (T^[k] x)⟩) :=
      ⟨hret,rfl⟩
    rwa [←returnRefinement_fiber] at hm
  have hyret : T^[k] y ∈ firstReturnLevel T S n := by
    have hm : T^[k] y ∈ returnRefinementAtom T S B (some ⟨n,B n (T^[k] x)⟩) := by
      rw [←returnRefinement_fiber]
      exact (hy k).trans hxcode
    exact hm.1
  refine ⟨k,hret.1,hyret.1,
    fun i => (hclose n (T^[k] x) (T^[k] y) hret (hy k) i).trans ?_⟩
  have hNn : (N:ℝ) ≤ n := by exact_mod_cast hn
  have he : Real.exp (-(n+1:ℝ)) < ε/2 := by
    rw [←Real.exp_log (by positivity : 0 < ε/2)]
    apply Real.exp_lt_exp.mpr
    linarith
  linarith

end DukePrimeDegree

end

end OAI
