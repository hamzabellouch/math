import OAI.MeasureTheory.Falconer.Geometry.SamplingGrid
import Mathlib.Analysis.Normed.Lp.MeasurableSpace

namespace OAI

/-!
# Uniform ball bounds for the original sampled labels

The finite query estimate is transferred to every ball, without identifying
labels that happen to have the same spatial coordinate.
-/

namespace Falconer
open Set Metric MeasureTheory Real
attribute [local instance] Classical.propDecidable

theorem iidCount_mono {X : Type*} {A B : Set X} (hAB : A ⊆ B)
    {n : ℕ} (ω : Fin n → X) : iidCount A ω ≤ iidCount B ω := by
  apply Finset.sum_le_sum
  intro i _
  by_cases h : ω i ∈ A
  · simp [h, hAB h]
  · simp only [Set.indicator_of_notMem h]
    by_cases h' : ω i ∈ B <;> simp [h']

theorem iidCount_le_card {X : Type*} (A : Set X) {n : ℕ} (ω : Fin n → X) :
    iidCount A ω ≤ n := by
  have hh : iidCount A ω ≤ iidCount Set.univ ω := iidCount_mono (subset_univ A) ω
  simpa [iidCount] using hh

theorem iidCount_eq_card_filter {X : Type*} (A : Set X) {n : ℕ} (ω : Fin n → X) :
    iidCount A ω = ((Finset.univ.filter (fun i => ω i ∈ A)).card : ℝ) := by
  simp [iidCount, Set.indicator_apply]

theorem uniform_ball_count_of_queries {X : Type*} {n L H : ℕ}
    (ω : Fin n → X) (p : X → Space 2) (hp : ∀ x i, |p x i| ≤ 1)
    {δ s T : ℝ} (hδ : 0 < δ) (hs : 0 ≤ s) (hT : 1 ≤ T)
    (hL : δ⁻¹+1 ≤ L) (hH : δ⁻¹ ≤ H)
    (hq : ∀ j ∈ planarQueries L H,
      iidCount {x | dist (p x) (planarMesh δ j.1) ≤ 4*(j.2 : ℝ)*δ} ω ≤
        T * (n : ℝ) * (4*(j.2 : ℝ)*δ)^s) :
    ∀ c r, δ ≤ r → iidCount {x | dist (p x) c ≤ r} ω ≤
      (T * 8^s) * (n : ℝ) * r^s := by
  intro c r hδr
  have hr0 : 0 < r := hδ.trans_le hδr
  have h8 : (1 : ℝ) ≤ 8^s := Real.one_le_rpow (by norm_num) hs
  by_cases hr : r ≤ 1
  · by_cases hex : ∃ i : Fin n, dist (p (ω i)) c ≤ r
    · obtain ⟨i, hi⟩ := hex
      obtain ⟨j, hj, hsub, hjpos, hjrad⟩ := planar_ball_query hδ hδr hr hL hH p hp c (ω i) hi
      have hh := (iidCount_mono hsub ω).trans (hq j hj)
      have hrpow := Real.rpow_le_rpow (hδ.le.trans hjpos) hjrad hs
      have he : (8*r)^s = (8 : ℝ)^s * r^s := Real.mul_rpow (by norm_num) hr0.le
      calc
        _ ≤ T * (n : ℝ) * (4*(j.2 : ℝ)*δ)^s := hh
        _ ≤ T * (n : ℝ) * (8*r)^s :=
          mul_le_mul_of_nonneg_left hrpow (by positivity)
        _ = _ := by rw [he]; ring
    · have hz : iidCount {x | dist (p x) c ≤ r} ω = 0 := by
        apply Finset.sum_eq_zero
        intro i _
        apply Set.indicator_of_notMem
        exact fun hi => hex ⟨i,hi⟩
      rw [hz]
      positivity
  · have hr1 : 1 ≤ r := le_of_not_ge hr
    have hrpow : 1 ≤ r^s := Real.one_le_rpow hr1 hs
    have hcoef : 1 ≤ (T * 8^s) * r^s := by
      have hh : (1 : ℝ) ≤ T * 8^s := one_le_mul_of_one_le_of_one_le hT h8
      exact one_le_mul_of_one_le_of_one_le hh hrpow
    calc
      _ ≤ (n : ℝ) := iidCount_le_card _ ω
      _ ≤ (n : ℝ) * ((T * 8^s) * r^s) := by
        exact le_mul_of_one_le_right (Nat.cast_nonneg n) hcoef
      _ = _ := by ring

/-- Simultaneous ball control and retained empirical incidence. The explicit
failure budget depends only on the polynomial number of grid queries. -/
theorem exists_uniform_ball_sample {X : Type*} [MeasurableSpace X]
    (ν : ProbabilityMeasure X) (p : X → Space 2) (hp : Measurable p)
    (hpbound : ∀ x i, |p x i| ≤ 1)
    {n L H : ℕ} (hn : 0 < n) {δ s K B I : ℝ}
    (hδ : 0 < δ) (hs : 0 ≤ s) (hK : 0 ≤ K) (hB : 1 ≤ B)
    (hL : δ⁻¹+1 ≤ L) (hH : δ⁻¹ ≤ H)
    (hsize : 1 ≤ (n : ℝ) * δ^s)
    (hprob : ∀ c r, δ ≤ r →
      (ν : Measure X).real {x | dist (p x) c ≤ r} ≤ K * r^s)
    (f : X → ℝ) (hf : Integrable f (ν : Measure X)) (hf1 : ∀ x, f x ≤ 1)
    (hI : 0 < I) (hmean : I ≤ ∫ x, f x ∂(ν : Measure X))
    (hsmall : (((2*L+1)^2 * H : ℕ) : ℝ) * exp (-B) ≤ I/4) :
    ∃ ω : Fin n → X,
      (∀ c r, δ ≤ r → iidCount {x | dist (p x) c ≤ r} ω ≤
        (((exp 1 - 1)*K+B) * 8^s) * (n : ℝ) * r^s) ∧
      I/2 ≤ iidAverage f ω := by
  let radius := fun j : (Fin 2 → ℤ) × ℤ => 4*(j.2 : ℝ)*δ
  let A := fun j => {x | dist (p x) (planarMesh δ j.1) ≤ radius j}
  have hrad (j) (hj : j ∈ planarQueries L H) : δ ≤ radius j := by
    have hm : (1 : ℤ) ≤ j.2 := (Finset.mem_Icc.mp (Finset.mem_product.mp hj).2).1
    have hm' : (1 : ℝ) ≤ j.2 := by exact_mod_cast hm
    dsimp [radius]
    nlinarith
  have hA (j) : MeasurableSet (A j) :=
    measurableSet_le (hp.dist measurable_const) measurable_const
  obtain ⟨ω, hω, hinc⟩ := exists_iid_sample_scale_counts ν hn
    (planarQueries L H) A hA (fun j => radius j ^ s) hK (zero_le_one.trans hB)
    (fun j hj => hsize.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow hδ.le (hrad j hj) hs) (Nat.cast_nonneg n)))
    (fun j hj => hprob _ _ (hrad j hj)) f hf hf1 hI hmean
    (by simpa only [planarQueries_card] using hsmall)
  refine ⟨ω, ?_, hinc⟩
  have he : 0 ≤ exp 1 - 1 := sub_nonneg.mpr (Real.one_le_exp_iff.mpr (by norm_num))
  have hT : 1 ≤ (exp 1 - 1)*K+B := le_add_of_nonneg_left (mul_nonneg he hK) |>.trans' hB
  exact uniform_ball_count_of_queries ω p hpbound hδ hs hT hL hH
    (fun j hj => (hω j hj).le)

end Falconer

end OAI
