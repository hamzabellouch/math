import OAI.NumberTheory.DukePrimeDegree.Dynamics.SmallReturnRefinement
import OAI.NumberTheory.DukePrimeDegree.Dynamics.ExponentialReturnRefinement

namespace OAI

/-! # Arbitrarily small entropy with exponentially fine transverse cells -/

noncomputable section
open MeasureTheory Set
namespace DukePrimeDegree

lemma log_scaled_exponential_grid_bound {d K n : ℕ} {R α : ℝ}
    (hR : 0 ≤ R) (hα : 0 ≤ α)
    (hK : (K:ℝ) ≤ 1+(2*R+2)^d/(Real.exp (-α*(n+1:ℝ)))^d) :
    Real.log K ≤ Real.log (1+(2*R+2)^d)+(d:ℝ)*α*(n+1) := by
  let A := (2*R+2)^d
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hlog : 0 ≤ Real.log (1+A) := Real.log_nonneg (by linarith)
  by_cases hz : K=0
  · subst K
    simp only [Nat.cast_zero,Real.log_zero]
    exact add_nonneg hlog (by positivity)
  have hKpos : (0:ℝ) < K := by exact_mod_cast Nat.pos_of_ne_zero hz
  have he : 1 ≤ Real.exp ((d:ℝ)*α*(n+1)) := Real.one_le_exp_iff.mpr (by positivity)
  have hpow : (Real.exp (-α*(n+1:ℝ)))^d=Real.exp (-((d:ℝ)*α*(n+1))) := by
    rw [←Real.exp_nat_mul]
    congr 1
    ring
  have hbound : (K:ℝ) ≤ (1+A)*Real.exp ((d:ℝ)*α*(n+1)) := by
    rw [hpow,Real.exp_neg,div_inv_eq_mul] at hK
    dsimp only [A]
    nlinarith
  calc
    Real.log K ≤ Real.log ((1+A)*Real.exp ((d:ℝ)*α*(n+1))) :=
      Real.log_le_log hKpos hbound
    _ = _ := by
      rw [Real.log_mul (by positivity) (Real.exp_ne_zero _),Real.log_exp]

/-- The section mass threshold is chosen before its transverse geometry.
The positive exponential rate can be arbitrarily small and still forces
arbitrarily fine cells on unbounded return levels. -/
theorem exists_small_entropy_return_refinement
    {Y : Type*} [MeasurableSpace Y] {d : ℕ} {R ε : ℝ}
    (hR : 0 ≤ R) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (μ : Measure Y) [IsProbabilityMeasure μ]
      {T : Y → Y} (_hT : MeasurePreserving T μ μ) (_hE : MeasurableEmbedding T)
      {S : Set Y} (_hS : MeasurableSet S), μ.real S ≤ δ →
      ∀ (f : Y → Fin d → ℝ), Measurable f →
        (∀ x ∈ S, ∀ i, |f x i| ≤ R) →
      ∃ (α : ℝ) (K : ℕ → ℕ) (B : ∀ n, Y → Fin (K n)), 0 < α ∧
        (∀ n, Measurable (B n)) ∧
        Summable (fun z : Option (Σ n : ℕ, Fin (K n)) =>
          Real.negMulLog (μ.real {x | returnRefinement T S B x=z})) ∧
        (∑' z : Option (Σ n : ℕ, Fin (K n)),
          Real.negMulLog (μ.real {x | returnRefinement T S B x=z})) < ε ∧
        ∀ n x y, x ∈ firstReturnLevel T S n →
          returnRefinement T S B y=returnRefinement T S B x →
          ∀ i, |f y i-f x i| < 2*Real.exp (-α*(n+1:ℝ)) := by
  let a := Real.log (1+(2*R+2)^d)
  have ha : 0 ≤ a := Real.log_nonneg (by
    have hpow : 0 ≤ (2*R+2)^d := by positivity
    linarith)
  obtain ⟨δ₀,hδ₀,hbase⟩ := exists_small_section_return_entropy (Y := Y)
    (by positivity : 0 < ε/2)
  let δ := min δ₀ (ε/(4*(a+1)))
  have hδ : 0 < δ := lt_min hδ₀ (div_pos hε (by positivity))
  refine ⟨δ,hδ,?_⟩
  intro μ _ T hT hE S hS hsmall f hf hbound
  let α := ε/(4*((d:ℝ)+1))
  have hα : 0 < α := div_pos hε (by positivity)
  have hδbase : μ.real S ≤ δ₀ := hsmall.trans (min_le_left _ _)
  have hbaseEntropy := hbase μ hT hE hS hδbase
  have hcost : a*μ.real S ≤ ε/4 := by
    have h := hsmall.trans (min_le_right _ _)
    have hp : 0 < 4*(a+1) := by positivity
    have hh := (le_div_iff₀ hp).mp h
    nlinarith [measureReal_nonneg (μ := μ) (s := S)]
  have hrate : (d:ℝ)*α ≤ ε/4 := by
    have hp : 0 < 4*((d:ℝ)+1) := by positivity
    have he : α*(4*((d:ℝ)+1))=ε := div_mul_cancel₀ ε hp.ne'
    nlinarith
  have hδn (n : ℕ) : Real.exp (-α*(n+1:ℝ)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith [Nat.cast_nonneg (α := ℝ) n])
  choose K B hB hcard hclose using fun n : ℕ =>
    exists_bounded_vector_code f hf hR (Real.exp_pos (-α*(n+1:ℝ))) (hδn n)
  have hlog n : Real.log (K n) ≤ a+(d:ℝ)*α*(n+1) :=
    log_scaled_exponential_grid_bound hR hα.le (hcard n)
  have hlog' n : Real.log (K n) ≤ (a+(d:ℝ)*α)*(n+1) := by
    nlinarith [hlog n,mul_nonneg ha (Nat.cast_nonneg (α := ℝ) n)]
  have hs := returnRefinement_information_summable μ hT hE hS K B hB
    (a+(d:ℝ)*α) hlog'
  have hi := returnRefinement_information_le μ hT hE hS K B hB ha
    (mul_nonneg (Nat.cast_nonneg d) hα.le) hlog
  refine ⟨α,K,B,hα,hB,hs,by linarith,?_⟩
  intro n x y hx hxy i
  have hxcode : returnRefinement T S B x=some ⟨n,B n x⟩ := by
    have hm : x ∈ returnRefinementAtom T S B (some ⟨n,B n x⟩) := ⟨hx,rfl⟩
    rwa [←returnRefinement_fiber] at hm
  have hy : y ∈ returnRefinementAtom T S B (some ⟨n,B n x⟩) := by
    rw [←returnRefinement_fiber]
    exact hxy.trans hxcode
  exact hclose n x y (hbound x hx.1) hy.2 i

end DukePrimeDegree

end

end OAI
