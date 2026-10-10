import Mathlib
import OAI.Geometry.CAT0Fillings.Mass.Approximation

namespace OAI

section

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal BigOperators

namespace CAT0Fillings
namespace BorelCoefficients
variable {X : Type*}

lemma exists_measurable_max_selector [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [CompactSpace X] (ρ : ℕ → X → ℝ) (hρ : ∀ j, Measurable (ρ j)) (N : ℕ) :
    ∃ σ : X → ℕ, Measurable σ ∧ (∀ x, σ x ≤ N) ∧
      ∀ x j, j ≤ N → |ρ j x| ≤ |ρ (σ x) x| := by
  classical
  let p x i := i ≤ N ∧ ∀ j, j ≤ N → |ρ j x| ≤ |ρ i x|
  have hp : ∀ x, ∃ i, p x i := by
    intro x
    obtain ⟨i,hi,hh⟩ := Finset.exists_max_image (Finset.range (N+1))
      (fun i => |ρ i x|) (by simp)
    refine ⟨i,Nat.le_of_lt_succ (Finset.mem_range.mp hi),fun j hj => hh j ?_⟩
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le hj)
  refine ⟨fun x => Nat.find (hp x),measurable_find hp ?_,fun x => (Nat.find_spec (hp x)).1,
    fun x => (Nat.find_spec (hp x)).2⟩
  intro i
  have hm : MeasurableSet {x : X | ∀ j, j ≤ N → |ρ j x| ≤ |ρ i x|} := by
    simp only [ofPred_forall]
    exact MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ =>
      measurableSet_le (hρ j).abs (hρ i).abs
  exact (MeasurableSet.const (i ≤ N)).inter hm

variable [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X]

lemma exists_measurable_max_coefficients (ρ : ℕ → X → ℝ) (hρ : ∀ j, Measurable (ρ j)) (N : ℕ) :
    ∃ b : Fin (N+1) → X → ℝ, (∀ i, Measurable (b i)) ∧
      (∀ x, ∑ i, |b i x| ≤ 1) ∧
      ∀ x, (∑ i, b i x * ρ i x) = ⨆ i : Fin (N+1), |ρ i x| := by
  classical
  obtain ⟨σ,hσm,hσN,hσ⟩ := exists_measurable_max_selector ρ hρ N
  let b (i : Fin (N+1)) (x : X) : ℝ := if σ x = i then (if 0 ≤ ρ i x then 1 else -1) else 0
  have hb i : Measurable (b i) :=
    Measurable.ite (measurableSet_eq_fun hσm measurable_const)
      (Measurable.ite (measurableSet_le measurable_const (hρ i)) measurable_const measurable_const)
      measurable_const
  have hid (x : X) : (⟨σ x,Nat.lt_succ_of_le (hσN x)⟩ : Fin (N+1)).val = σ x := rfl
  have hsum x (F : Fin (N+1) → ℝ) :
      (∑ i : Fin (N+1), if σ x = i then F i else 0) = F ⟨σ x,Nat.lt_succ_of_le (hσN x)⟩ := by
    rw [Finset.sum_eq_single (⟨σ x,Nat.lt_succ_of_le (hσN x)⟩ : Fin (N+1))]
    · simp
    · intro i hi hneq
      have hh : ¬σ x = i := by intro he; apply hneq; apply Fin.ext; exact he.symm
      simp [hh]
    · simp
  refine ⟨b,hb,?_,?_⟩
  · intro x
    have he : (∑ i, |b i x|) = ∑ i : Fin (N+1), if σ x = i then (1:ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      dsimp [b]
      split_ifs <;> norm_num
    rw [he,hsum]
  · intro x
    have he : (∑ i, b i x*ρ i x) = ∑ i : Fin (N+1), if σ x = i then |ρ i x| else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      dsimp [b]
      split_ifs <;> simp_all [abs_of_nonneg,abs_of_neg]
    rw [he,hsum]
    apply le_antisymm
    · exact le_ciSup (Finite.bddAbove_range (fun i : Fin (N+1) => |ρ i x|)) _
    · exact ciSup_le fun i => hσ x i (Nat.le_of_lt_succ i.isLt)

theorem mass_le_of_finite_tests {k : ℕ} {T : Functional X k} (hT : IsMetricCurrent T)
    (π : ℕ → Fin k → X → ℝ) (hπ : ∀ j i, LipschitzWith 1 (π j i))
    (ρ : ℕ → X → ℝ) (hρm : ∀ j, Measurable (ρ j)) (hρ1 : ∀ j x, |ρ j x| ≤ 1)
    (hρ : ∀ j b, BoundedLip b → T b (π j) =
      ∫ x, b x*ρ j x ∂MassMeasure.currentMassMeasure hT)
    (hmass : mass T = ∫ x, ⨆ j, |ρ j x| ∂MassMeasure.currentMassMeasure hT)
    {C : ℝ} (hC : ∀ N (b : Fin (N+1) → X → ℝ), (∀ i, BoundedLip (b i)) →
      (∀ x, ∑ i, |b i x| ≤ 1) → (∑ i, T (b i) (π i)) ≤ C) : mass T ≤ C := by
  classical
  let μ := MassMeasure.currentMassMeasure hT
  let R (N : ℕ) (x : X) : ℝ := ⨆ i : Fin (N+1), |ρ i x|
  have hR0 N x : 0 ≤ R N x := (abs_nonneg (ρ 0 x)).trans (le_ciSup (Finite.bddAbove_range (fun i : Fin (N+1) => |ρ i x|)) (0:Fin (N+1)))
  have hR1 N x : R N x ≤ 1 := ciSup_le fun i => hρ1 i x
  have hRN N : (∫ x, R N x ∂μ) ≤ C := by
    apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨b,hbm,hb1,hbmax⟩ := exists_measurable_max_coefficients ρ hρm N
    obtain ⟨f,hf,hf1,happrox⟩ := exists_admissible_coefficient_approx μ b hbm hb1 hε
    have hfAdm (index : Fin (N+1)) : Admissible (f index) (π index) :=
      ⟨hf index,fun coordinate => ⟨1,hπ index coordinate⟩⟩
    have hbi i : Integrable (b i) μ := Integrable.mono' (integrable_const (1:ℝ)) (hbm i).aestronglyMeasurable
      (Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs]
        exact (Finset.single_le_sum (fun j _ => abs_nonneg (b j x)) (Finset.mem_univ i)).trans (hb1 x))
    have hri (g : X → ℝ) (hg : Integrable g μ) (i : ℕ) : Integrable (fun x => g x*ρ i x) μ :=
      hg.mul_bdd (hρm i).aestronglyMeasurable (Eventually.of_forall fun x => by
        simpa only [Real.norm_eq_abs] using hρ1 i x)
    have hdiff i : (∫ x, b i x*ρ i x ∂μ) ≤ T (f i) (π i)+(∫ x, |f i x-b i x| ∂μ) := by
      rw [hρ i (f i) (hfAdm i).1]
      have he : (∫ x, b i x*ρ i x ∂μ)-(∫ x, f i x*ρ i x ∂μ) =
          ∫ x, (b i x-f i x)*ρ i x ∂μ := by
        rw [←integral_sub (hri _ (hbi i) _) (hri _ (integrable_boundedLip μ (hf i)) _)]
        congr 1; funext x; ring
      apply sub_le_iff_le_add'.mp
      rw [he]
      apply ((le_abs_self _).trans (abs_integral_le_integral_abs)).trans
      apply integral_mono ((hri _ ((hbi i).sub (integrable_boundedLip μ (hf i))) _).abs)
        (((integrable_boundedLip μ (hf i)).sub (hbi i)).abs)
      intro x
      change |(b i x-f i x)*ρ i x| ≤ |f i x-b i x|
      rw [abs_mul,abs_sub_comm (b i x)]
      exact mul_le_of_le_one_right (abs_nonneg _) (hρ1 i x)
    calc (∫ x, R N x ∂μ) = ∑ i, ∫ x, b i x*ρ i x ∂μ := by
          rw [←integral_finsetSum _ (fun i _ => hri _ (hbi i) _)]
          apply integral_congr_ae (Eventually.of_forall fun x => (hbmax x).symm)
         _ ≤ ∑ i, (T (f i) (π i)+(∫ x, |f i x-b i x| ∂μ)) := Finset.sum_le_sum fun i _ => hdiff i
         _ ≤ C+ε := by
          rw [Finset.sum_add_distrib]
          exact add_le_add (hC N f hf hf1) happrox.le
  have hlim : Tendsto (fun N => ∫ x, R N x ∂μ) atTop (𝓝 (mass T)) := by
    rw [hmass]
    apply tendsto_integral_of_dominated_convergence (fun _ => (1:ℝ))
    · intro N
      exact (Measurable.iSup fun i : Fin (N+1) => (hρm i).abs).aestronglyMeasurable
    · exact integrable_const _
    · intro N
      exact Eventually.of_forall fun x => by rw [Real.norm_of_nonneg (hR0 N x)]; exact hR1 N x
    · apply Eventually.of_forall
      intro x
      have hmono : Monotone (fun N => R N x) := by
        intro N M hNM
        apply ciSup_le
        intro i
        exact le_ciSup (Finite.bddAbove_range (fun i : Fin (M+1) => |ρ i x|)) (⟨i,Nat.lt_of_lt_of_le i.isLt (Nat.succ_le_succ hNM)⟩:Fin (M+1))
      have hbd : BddAbove (range (fun N => R N x)) := ⟨1,by rintro _ ⟨N,rfl⟩; exact hR1 N x⟩
      have he : (⨆ N, R N x) = ⨆ j, |ρ j x| := by
        have hb : BddAbove (range (fun j => |ρ j x|)) := ⟨1,by rintro _ ⟨j,rfl⟩; exact hρ1 j x⟩
        apply le_antisymm
        · apply ciSup_le
          intro N
          exact ciSup_le fun i => le_ciSup hb i
        · apply ciSup_le
          intro j
          exact (le_ciSup (Finite.bddAbove_range (fun i : Fin (j+1) => |ρ i x|)) (⟨j,Nat.lt_succ_self j⟩:Fin (j+1))).trans (le_ciSup hbd j)
      simpa only [he] using tendsto_atTop_ciSup hmono hbd
  exact le_of_tendsto hlim (Eventually.of_forall hRN)

end BorelCoefficients
end CAT0Fillings
end

end OAI
