import Mathlib
import OAI.Analysis.HardSphere.Geometry.AnimalFamily

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical ENNReal
namespace HardSphere.Lattice

def torusNear (K R : ℕ) (x y : DiscreteTorus K) : Prop :=
  ∃ d : Vertex, (∀ i, |d i|≤R) ∧ ∀ i, y i=x i+(d i : ZMod K)

lemma torusNear_refl (K R : ℕ) (x : DiscreteTorus K) : torusNear K R x x := by
  exact ⟨0,fun i ↦ by simp,fun i ↦ by simp⟩

lemma torusNear_symm {K R : ℕ} {x y : DiscreteTorus K} (h : torusNear K R x y) :
    torusNear K R y x := by
  obtain ⟨d,hd,he⟩ := h
  refine ⟨-d,fun i ↦ by simpa using hd i,fun i ↦ ?_⟩
  simp only [Pi.neg_apply,Int.cast_neg,he i]
  abel

lemma torusNear_mono {K R S : ℕ} {x y : DiscreteTorus K} (hRS : R≤S) (h : torusNear K R x y) :
    torusNear K S x y := by
  obtain ⟨d,hd,he⟩ := h
  exact ⟨d,fun i ↦ (hd i).trans (by exact_mod_cast hRS),he⟩

lemma torusNear_add {K R S : ℕ} {x y z : DiscreteTorus K}
    (hxy : torusNear K R x y) (hyz : torusNear K S y z) : torusNear K (R+S) x z := by
  obtain ⟨d,hd,he⟩ := hxy
  obtain ⟨e,he',hf⟩ := hyz
  refine ⟨d+e,fun i ↦ ?_,fun i ↦ ?_⟩
  · exact (abs_add_le (d i) (e i)).trans (by simpa only [Nat.cast_add] using add_le_add (hd i) (he' i))
  · simp only [Pi.add_apply,Int.cast_add,hf i,he i,add_assoc]

def torusOffsets (R : ℕ) : Finset Vertex :=
  Fintype.piFinset fun _ : Fin 3 ↦ Finset.Icc (-(R:ℤ)) R

lemma torusOffsets_card (R : ℕ) : (torusOffsets R).card=(2*R+1)^3 := by
  have hcard : (Finset.Icc (-(R:ℤ)) R).card=2*R+1 := by rw [Int.card_Icc]; omega
  simp only [torusOffsets,Fintype.card_piFinset,hcard,Finset.prod_const,Finset.card_univ,Fintype.card_fin]

lemma torusNear_mem_image {K R : ℕ} (x y : DiscreteTorus K) :
    torusNear K R x y ↔ y∈(torusOffsets R).image (fun d ↦ x+torusProjection K d) := by
  constructor
  · rintro ⟨d,hd,he⟩
    refine Finset.mem_image.mpr ⟨d,?_,?_⟩
    · simpa only [torusOffsets,Fintype.mem_piFinset,Finset.mem_Icc,← abs_le] using hd
    · ext i; exact (he i).symm
  · intro hy
    obtain ⟨d,hd,rfl⟩ := Finset.mem_image.mp hy
    refine ⟨d,?_,fun i ↦ rfl⟩
    simpa only [torusOffsets,Fintype.mem_piFinset,Finset.mem_Icc,← abs_le] using hd

lemma torusNear_ball_card {K : ℕ} [NeZero K] (R : ℕ) (x : DiscreteTorus K) :
    (Finset.univ.filter (torusNear K R x)).card≤(2*R+1)^3 := by
  have he : Finset.univ.filter (torusNear K R x)=(torusOffsets R).image (fun d ↦ x+torusProjection K d) := by
    ext y
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,torusNear_mem_image]
  rw [he]
  exact Finset.card_image_le.trans (torusOffsets_card R).le

lemma torusRange_degree {K : ℕ} [NeZero K] (a : ℕ) (x : DiscreteTorus K) :
    (torusRangeGraph K a).degree x≤(2*a+1)^3 := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  apply (Finset.card_le_card (t := Finset.univ.filter (torusNear K a x)) ?_).trans (torusNear_ball_card a x)
  intro y hy
  have hxy : (torusRangeGraph K a).Adj x y := by simpa using hy
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hxy.2⟩

open MeasureTheory
variable {W V : Type*} [MeasurableSpace W] [Fintype V] [DecidableEq V]

theorem largeBadComponent_measure (G : SimpleGraph V) (Δ : ℕ)
    (hΔ : ∀ x, G.degree x≤Δ) (μ : Measure W) (B : W → Finset V) (p : ℝ≥0∞)
    (hbad : ∀ A : Finset V, μ {ω | A⊆B ω} ≤ p^A.card) (m : ℕ) (hm : 1 ≤ m) :
    μ {ω | LargeBadComponent G (B ω) m} ≤
      (Fintype.card V : ℝ≥0∞) * (((2^Δ:ℕ):ℝ≥0∞)*p)^m := by
  classical
  have hsub : {ω | LargeBadComponent G (B ω) m} ⊆
      ⋃ A∈animalFamily G m, {ω | A⊆B ω} := by
    intro ω hω
    obtain ⟨A,hA,hAB⟩ := largeBadComponent_contains_animal G (B ω) m hm hω
    exact Set.mem_iUnion₂.mpr ⟨A,hA,hAB⟩
  calc
    _ ≤ μ (⋃ A∈animalFamily G m, {ω | A⊆B ω}) := measure_mono hsub
    _ ≤ ∑ A∈animalFamily G m, μ {ω | A⊆B ω} := measure_biUnion_finset_le _ _
    _ ≤ ∑ _A∈animalFamily G m, p^m := by
      apply Finset.sum_le_sum
      intro A hA
      simpa only [mem_animalFamily_card G m hA] using hbad A
    _ = ((animalFamily G m).card:ℝ≥0∞)*p^m := by simp
    _ ≤ ((Fintype.card V*(2^Δ)^m:ℕ):ℝ≥0∞)*p^m := by
      apply mul_le_mul' _ le_rfl
      exact_mod_cast animalFamily_card_le G Δ hΔ m
    _ = _ := by simp only [Nat.cast_mul,Nat.cast_pow,mul_pow]; ring

def animalCost (G : SimpleGraph V) (B : Finset V) (w : ℕ → ℝ≥0∞) : ℝ≥0∞ :=
  ∑' m : ℕ, ∑ v : V, ∑ A∈rootedAnimals G v (m+1), if A⊆B then w (m+1) else 0

lemma measurable_animalCost (G : SimpleGraph V) (B : W → Finset V)
    (hB : Measurable B) (w : ℕ → ℝ≥0∞) : Measurable (fun ω ↦ animalCost G (B ω) w) := by
  apply Measurable.tsum
  intro m
  apply Finset.measurable_sum
  intro v _
  apply Finset.measurable_sum
  intro A _
  apply Measurable.ite _ measurable_const measurable_const
  have hm : MeasurableSet {C : Finset V | A⊆C} := (Set.to_countable _).measurableSet
  exact hm.preimage hB

theorem animalCost_mean_le (G : SimpleGraph V) (Δ : ℕ)
    (hΔ : ∀ x, G.degree x≤Δ) (μ : Measure W) (B : W → Finset V)
    (hB : Measurable B) (p : ℝ≥0∞)
    (hbad : ∀ A : Finset V, μ {ω | A⊆B ω} ≤ p^A.card) (w : ℕ → ℝ≥0∞) :
    (∫⁻ ω, animalCost G (B ω) w ∂μ) ≤
      (Fintype.card V:ℝ≥0∞) * ∑' m : ℕ, w (m+1) * (((2^Δ:ℕ):ℝ≥0∞)*p)^(m+1) := by
  classical
  have hm (A : Finset V) : MeasurableSet {ω | A⊆B ω} :=
    (Set.to_countable {C : Finset V | A⊆C}).measurableSet.preimage hB
  have hi (A : Finset V) (t : ℝ≥0∞) : Measurable (fun ω ↦ if A⊆B ω then t else 0) :=
    Measurable.ite (hm A) measurable_const measurable_const
  unfold animalCost
  rw [lintegral_tsum (fun m ↦ (Finset.measurable_sum _ fun v _ ↦
    Finset.measurable_sum _ fun A _ ↦ hi A _).aemeasurable)]
  rw [←ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro m
  rw [lintegral_finsetSum _ (fun v _ ↦ Finset.measurable_sum _ fun A _ ↦ hi A _)]
  calc
    _ ≤ ∑ _v : V, (((2^Δ:ℕ):ℝ≥0∞)^(m+1)) * (w (m+1)*p^(m+1)) := by
      apply Finset.sum_le_sum
      intro v _
      rw [lintegral_finsetSum _ (fun A _ ↦ hi A _)]
      calc
        _ ≤ ∑ _A∈rootedAnimals G v (m+1), w (m+1)*p^(m+1) := by
          apply Finset.sum_le_sum
          intro A hA
          have hc : A.card=m+1 := (Finset.mem_filter.mp hA).2.2.1
          have heq : (fun ω ↦ if A⊆B ω then w (m+1) else 0) =
              {ω | A⊆B ω}.indicator (fun _ ↦ w (m+1)) := by
            ext ω
            simp only [Set.indicator_apply, Set.mem_ofPred_eq]
          rw [heq,lintegral_indicator_const (hm A)]
          exact mul_le_mul' le_rfl (by simpa only [hc] using hbad A)
        _ = ((rootedAnimals G v (m+1)).card:ℝ≥0∞)*(w (m+1)*p^(m+1)) := by simp
        _ ≤ _ := by
          apply mul_le_mul' _ le_rfl
          exact_mod_cast rootedAnimals_card_le G Δ hΔ v (m+1)
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_pow]; ring

end HardSphere.Lattice

end

end OAI
