import Mathlib
import OAI.Probability.ThreeStateClauses.PosteriorLaw

namespace OAI

/-! Branch Moments. -/

open scoped BigOperators ENNReal NNReal Topology
open Filter
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace ThreeState.TreeClauses.Experiment
open ThreeState.TreeClauses.Radial ThreeState.TreeClauses.Positive

variable {ι : Type*} [Fintype ι]

def branchProduct (a : ι → Vec) : Vec := fun i ↦ ∏ j, a j i

def normalizer (a : ι → Vec) : ℝ := avg (branchProduct a)

def normalizedProduct (a : ι → Vec) : Vec := fun i ↦ branchProduct a i / normalizer a

lemma avg_sum (f : ι → Vec) : avg (fun i ↦ ∑ j, f j i) = ∑ j, avg (f j) := by
  dsimp only [avg]
  rw [← Finset.sum_div]
  congr 1
  simp only [Finset.sum_add_distrib]

lemma avg_div (f : Vec) (c : ℝ) : avg (fun i ↦ f i/c) = avg f/c := by
  simp only [avg]; ring

lemma normalizer_positive {a : ι → Vec} (ha : ∀ j i, 0 < a j i) : 0 < normalizer a := by
  have h (i) : 0 < branchProduct a i := Finset.prod_pos (fun j _ ↦ ha j i)
  dsimp only [normalizer, avg]
  exact div_pos (add_pos (add_pos (h 0) (h 1)) (h 2)) (by norm_num)

lemma normalizedProduct_positive {a : ι → Vec} (ha : ∀ j i, 0 < a j i) :
    PositiveMessage (normalizedProduct a) := by
  refine ⟨fun i ↦ div_pos (Finset.prod_pos (fun j _ ↦ ha j i)) (normalizer_positive ha), ?_⟩
  change avg (fun i ↦ branchProduct a i/normalizer a) = 1
  rw [avg_div]
  exact div_self (ne_of_gt (normalizer_positive ha))

lemma log_normalizedProduct {a : ι → Vec} (ha : ∀ j i, 0 < a j i) (i : Fin 3) :
    Real.log (normalizedProduct a i) = (∑ j, Real.log (a j i))-Real.log (normalizer a) := by
  rw [normalizedProduct, branchProduct, Real.log_div (ne_of_gt (Finset.prod_pos (fun j _ ↦ ha j i)))
    (ne_of_gt (normalizer_positive ha))]
  congr 1
  exact Real.log_prod (fun j _ ↦ ne_of_gt (ha j i))

lemma logCentered_normalizedProduct {a : ι → Vec} (ha : ∀ j i, 0 < a j i) (i : Fin 3) :
    logCentered (normalizedProduct a) i = ∑ j, logCentered (a j) i := by
  simp only [logCentered, logAverage, log_normalizedProduct ha]
  rw [avg_sub, avg_sum, avg_const, Finset.sum_sub_distrib]
  ring

lemma symEntropy_centeredLog {m : Vec} (hm : avg m = 1) :
    symEntropy m = avg (fun i ↦ m i*logCentered m i)/2 := by
  have h : avg (fun i ↦ m i*logAverage m) = logAverage m := by
    calc
      _ = logAverage m*avg m := by simp only [avg]; ring
      _ = _ := by rw [hm]; ring
  unfold symEntropy logCentered
  simp_rw [mul_sub, sub_mul, one_mul]
  rw [avg_sub, avg_sub, h]
  rfl

lemma weighted_symEntropy {a : ι → Vec} (ha : ∀ j i, 0 < a j i) :
    normalizer a*symEntropy (normalizedProduct a) =
      avg (fun i ↦ branchProduct a i*(∑ j, logCentered (a j) i))/2 := by
  rw [symEntropy_centeredLog (normalizedProduct_positive ha).2]
  simp_rw [logCentered_normalizedProduct ha]
  change normalizer a*(avg (fun i ↦ (branchProduct a i/normalizer a)*(∑ j, logCentered (a j) i))/2) = _
  dsimp only [avg]
  field_simp [ne_of_gt (normalizer_positive ha)]

lemma weighted_correction {a : ι → Vec} (ha : ∀ j i, 0 < a j i) :
    normalizer a*correction (normalizedProduct a) =
      avg (fun i ↦ branchProduct a i*(∑ j, logCentered (a j) i)^2)/2 := by
  simp only [correction, logCentered_normalizedProduct ha, normalizedProduct, avg]
  field_simp [ne_of_gt (normalizer_positive ha)]

lemma weighted_info {a : ι → Vec} (ha : ∀ j i, 0 < a j i) :
    normalizer a*info (normalizedProduct a) =
      avg (fun i ↦ branchProduct a i*(∑ j, Real.log (a j i))) -
      normalizer a*Real.log (normalizer a) := by
  unfold info
  simp_rw [log_normalizedProduct ha]
  simp only [normalizedProduct, avg]
  field_simp [ne_of_gt (normalizer_positive ha)]
  dsimp only [normalizer, avg]
  ring

end ThreeState.TreeClauses.Experiment

end 

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ThreeState.TreeClauses.Experiment

variable {ι X : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace X]
  {μ : Measure X} [SigmaFinite μ] {a u : X → ℝ}

def weightProduct (a : X → ℝ) (x : ι → X) : ℝ := ∏ i, a (x i)

omit [MeasurableSpace X] in
lemma select_product (a u : X → ℝ) (x : ι → X) (j : ι) :
    weightProduct a x*u (x j) = ∏ i, a (x i)*(if i=j then u (x i) else 1) := by
  rw [Finset.prod_mul_distrib]
  simp only [weightProduct, Fintype.prod_ite_eq']

lemma integrable_weighted_single (ha : Integrable a μ) (hau : Integrable (fun x ↦ a x*u x) μ)
    (j : ι) : Integrable (fun x : ι → X ↦ weightProduct a x*u (x j)) (Measure.pi fun _ ↦ μ) := by
  have hi : ∀ i : ι, Integrable (fun x ↦ a x*(if i=j then u x else 1)) μ := by
    intro i
    by_cases h : i=j
    · simpa [h] using hau
    · simpa [h] using ha
  simpa only [← select_product] using Integrable.fintype_prod hi

lemma integral_weighted_single (ha : ∫ x, a x ∂μ = 1) (j : ι) :
    (∫ x : ι → X, weightProduct a x*u (x j) ∂(Measure.pi fun _ ↦ μ)) = ∫ x, a x*u x ∂μ := by
  simp_rw [select_product]
  rw [integral_fintype_prod_eq_prod (fun i x ↦ a x*(if i=j then u x else 1))]
  have he (i : ι) : (∫ x, a x*(if i=j then u x else 1) ∂μ) =
      if i=j then (∫ x, a x*u x ∂μ) else 1 := by
    by_cases h : i=j <;> simp [h, ha]
  simp_rw [he]
  simp

omit [MeasurableSpace X] in
lemma select_pair_product (a u : X → ℝ) (x : ι → X) (j k : ι) :
    weightProduct a x*(u (x j)*u (x k)) =
      ∏ i, a (x i)*(if i=j then u (x i) else 1)*(if i=k then u (x i) else 1) := by
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  simp only [weightProduct, Fintype.prod_ite_eq']
  ring

lemma integrable_weighted_pair (ha : Integrable a μ) (hau : Integrable (fun x ↦ a x*u x) μ)
    (hau₂ : Integrable (fun x ↦ a x*u x^2) μ) (j k : ι) :
    Integrable (fun x : ι → X ↦ weightProduct a x*(u (x j)*u (x k))) (Measure.pi fun _ ↦ μ) := by
  have hi : ∀ i : ι, Integrable (fun x ↦ a x*(if i=j then u x else 1)*(if i=k then u x else 1)) μ := by
    intro i
    by_cases h : i=j <;> by_cases h' : i=k
    · simpa only [ite_eq_left h, ite_eq_left h', pow_two, mul_assoc] using hau₂
    · simpa only [ite_eq_left h, ite_eq_right h', mul_one] using hau
    · simpa only [ite_eq_right h, ite_eq_left h', mul_one] using hau
    · simpa [h, h'] using ha
  simpa only [← select_pair_product] using Integrable.fintype_prod hi

lemma integral_weighted_pair (ha : ∫ x, a x ∂μ = 1) (j k : ι) :
    (∫ x : ι → X, weightProduct a x*(u (x j)*u (x k)) ∂(Measure.pi fun _ ↦ μ)) =
      if j=k then (∫ x, a x*u x^2 ∂μ) else (∫ x, a x*u x ∂μ)^2 := by
  by_cases hjk : j=k
  · subst k
    simp only [ite_true, pow_two]
    exact integral_weighted_single (u := fun x ↦ u x*u x) ha j
  · simp_rw [select_pair_product]
    rw [integral_fintype_prod_eq_prod (fun i x ↦ a x*(if i=j then u x else 1)*(if i=k then u x else 1)), ite_eq_right hjk]
    have he (i : ι) : (∫ x, a x*(if i=j then u x else 1)*(if i=k then u x else 1) ∂μ) =
        (if i=j then (∫ x, a x*u x ∂μ) else 1)*(if i=k then (∫ x, a x*u x ∂μ) else 1) := by
      by_cases h : i=j <;> by_cases h' : i=k
      · exact (hjk (h.symm.trans h')).elim
      · simp only [ite_eq_left h, ite_eq_right h', mul_one]
      · simp only [ite_eq_right h, ite_eq_left h', mul_one, one_mul]
      · simp only [ite_eq_right h, ite_eq_right h', mul_one, ha]
    simp_rw [he]
    rw [Finset.prod_mul_distrib]
    simp [sq]

lemma integrable_weighted_sum (ha : Integrable a μ) (hau : Integrable (fun x ↦ a x*u x) μ) :
    Integrable (fun x : ι → X ↦ weightProduct a x*(∑ j, u (x j))) (Measure.pi fun _ ↦ μ) := by
  simp_rw [Finset.mul_sum]
  exact integrable_finsetSum _ (fun j _ ↦ integrable_weighted_single ha hau j)

lemma integral_weighted_sum (ha : Integrable a μ) (hau : Integrable (fun x ↦ a x*u x) μ)
    (hbal : ∫ x, a x ∂μ = 1) :
    (∫ x : ι → X, weightProduct a x*(∑ j, u (x j)) ∂(Measure.pi fun _ ↦ μ)) =
      (Fintype.card ι : ℝ)*(∫ x, a x*u x ∂μ) := by
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum _ (fun j _ ↦ integrable_weighted_single ha hau j)]
  simp only [integral_weighted_single hbal, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

lemma integrable_weighted_sq_sum (ha : Integrable a μ) (hau : Integrable (fun x ↦ a x*u x) μ)
    (hau₂ : Integrable (fun x ↦ a x*u x^2) μ) :
    Integrable (fun x : ι → X ↦ weightProduct a x*(∑ j, u (x j))^2) (Measure.pi fun _ ↦ μ) := by
  have he (x : ι → X) : weightProduct a x*(∑ j, u (x j))^2 =
      ∑ j, ∑ k, weightProduct a x*(u (x j)*u (x k)) := by
    rw [sq, Finset.sum_mul_sum]
    simp_rw [Finset.mul_sum]
  simp_rw [he]
  exact integrable_finsetSum _ (fun j _ ↦ integrable_finsetSum _ (fun k _ ↦ integrable_weighted_pair ha hau hau₂ j k))

theorem integral_weighted_sq_sum (ha : Integrable a μ) (hau : Integrable (fun x ↦ a x*u x) μ)
    (hau₂ : Integrable (fun x ↦ a x*u x^2) μ) (hbal : ∫ x, a x ∂μ = 1) :
    (∫ x : ι → X, weightProduct a x*(∑ j, u (x j))^2 ∂(Measure.pi fun _ ↦ μ)) =
      (Fintype.card ι : ℝ)*(∫ x, a x*u x^2 ∂μ)+
      ((Fintype.card ι : ℝ)^2-(Fintype.card ι : ℝ))*(∫ x, a x*u x ∂μ)^2 := by
  have he (x : ι → X) : weightProduct a x*(∑ j, u (x j))^2 =
      ∑ j, ∑ k, weightProduct a x*(u (x j)*u (x k)) := by
    rw [sq, Finset.sum_mul_sum]
    simp_rw [Finset.mul_sum]
  simp_rw [he]
  rw [integral_finsetSum _ (fun j _ ↦ integrable_finsetSum _ (fun k _ ↦ integrable_weighted_pair ha hau hau₂ j k))]
  simp_rw [integral_finsetSum _ (fun k _ ↦ integrable_weighted_pair ha hau hau₂ _ k), integral_weighted_pair hbal]
  have he' (j k : ι) : (if j=k then (∫ x, a x*u x^2 ∂μ) else (∫ x, a x*u x ∂μ)^2) =
      (if j=k then (∫ x, a x*u x^2 ∂μ)-(∫ x, a x*u x ∂μ)^2 else 0)+(∫ x, a x*u x ∂μ)^2 := by
    split_ifs <;> ring
  simp_rw [he', Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

end ThreeState.TreeClauses.Experiment

end 

noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace ThreeState.TreeClauses.Experiment
open ThreeState.TreeClauses.Radial ThreeState.TreeClauses.Positive

abbrev branchEdges {n : ℕ} (lam : ℝ) (m : Fin n → Message) : Fin n → Vec := fun j ↦ edgeMessage lam (m j)

def finiteBranchExpectation (Q : Law) (lam : ℝ) (n : ℕ) (f : Vec → ℝ) : ℝ :=
  ∫ m : Fin n → Message, normalizer (branchEdges lam m)*f (normalizedProduct (branchEdges lam m))
    ∂(Measure.pi fun _ ↦ Q.probability.toMeasure)

def correlationEntropy (Q : Law) (lam : ℝ) (n : ℕ) : ℝ :=
  ∫ m : Fin n → Message, normalizer (branchEdges lam m)*Real.log (normalizer (branchEdges lam m))
    ∂(Measure.pi fun _ ↦ Q.probability.toMeasure)

lemma branchEdges_positive {lam : ℝ} (hl₀ : 0 ≤ lam) (hl₁ : lam < 1) {n : ℕ} (m : Fin n → Message) :
    ∀ j i, 0 < branchEdges lam m j i := fun j i ↦ (edge_positive hl₀ hl₁ (m j)).1 i

lemma continuous_branchProduct {n : ℕ} (lam : ℝ) (i : Fin 3) :
    Continuous (fun m : Fin n → Message ↦ branchProduct (branchEdges lam m) i) := by
  unfold branchProduct branchEdges
  exact continuous_finsetProd _ (fun j _ ↦ ((continuous_apply i).comp (continuous_edgeMessage lam)).comp (continuous_apply j))

lemma continuous_normalizer (n : ℕ) (lam : ℝ) :
    Continuous (fun m : Fin n → Message ↦ normalizer (branchEdges lam m)) :=
  continuous_avg.comp (continuous_pi (continuous_branchProduct lam))

lemma continuous_correlationIntegrand {lam : ℝ} (hl₀ : 0 ≤ lam) (hl₁ : lam < 1) (n : ℕ) :
    Continuous (fun m : Fin n → Message ↦ normalizer (branchEdges lam m)*Real.log (normalizer (branchEdges lam m))) :=
  (continuous_normalizer n lam).mul ((continuous_normalizer n lam).log
    (fun m ↦ ne_of_gt (normalizer_positive (branchEdges_positive hl₀ hl₁ m))))

lemma integral_normalizer (Q : Law) (lam : ℝ) (n : ℕ) :
    (∫ m : Fin n → Message, normalizer (branchEdges lam m) ∂(Measure.pi fun _ ↦ Q.probability.toMeasure)) = 1 := by
  unfold normalizer
  rw [integral_avg_measure (fun i ↦ compact_integrable (continuous_branchProduct lam i))]
  have he (i : Fin 3) : (∫ m : Fin n → Message, branchProduct (branchEdges lam m) i
      ∂(Measure.pi fun _ ↦ Q.probability.toMeasure)) = 1 := by
    change (∫ m : Fin n → Message, ∏ j, edgeMessage lam (m j) i ∂(Measure.pi fun _ ↦ Q.probability.toMeasure)) = 1
    rw [integral_fintype_prod_eq_pow (fun m ↦ edgeMessage lam m i), Q.edge_balanced]
    simp
  simp_rw [he]
  exact avg_const 1

lemma correlationEntropy_nonneg (Q : Law) {lam : ℝ} (hl₀ : 0 ≤ lam) (hl₁ : lam < 1) (n : ℕ) :
    0 ≤ correlationEntropy Q lam n := by
  have he (m : Fin n → Message) : normalizer (branchEdges lam m)-1 ≤
      normalizer (branchEdges lam m)*Real.log (normalizer (branchEdges lam m)) := by
    have hp := normalizer_positive (branchEdges_positive hl₀ hl₁ m)
    have h := mul_le_mul_of_nonneg_left (Real.one_sub_inv_le_log_of_pos hp) hp.le
    simpa [mul_sub, ne_of_gt hp] using h
  have h := integral_mono (μ := Measure.pi fun _ : Fin n ↦ Q.probability.toMeasure)
    (f := fun m ↦ normalizer (branchEdges lam m)-1)
    (g := fun m ↦ normalizer (branchEdges lam m)*Real.log (normalizer (branchEdges lam m)))
    ((compact_integrable (continuous_normalizer n lam)).sub (integrable_const 1))
    (compact_integrable (continuous_correlationIntegrand hl₀ hl₁ n)) he
  rw [integral_sub (f := fun m : Fin n → Message ↦ normalizer (branchEdges lam m))
    (g := fun _ ↦ (1:ℝ)) (compact_integrable (continuous_normalizer n lam)) (integrable_const _),
    integral_normalizer] at h
  simpa [correlationEntropy] using h

theorem finite_symEntropy (Q : Law) {lam : ℝ} (hl₀ : 0 ≤ lam) (hl₁ : lam < 1) (n : ℕ) :
    finiteBranchExpectation Q lam n symEntropy =
      n*(∫ m, symEntropy (edgeMessage lam m) ∂Q.probability.toMeasure) := by
  have ha (i : Fin 3) : Integrable (fun m ↦ edgeMessage lam m i) Q.probability.toMeasure :=
    compact_integrable ((continuous_apply i).comp (continuous_edgeMessage lam))
  have hau (i : Fin 3) : Integrable (fun m ↦ edgeMessage lam m i*logCentered (edgeMessage lam m) i) Q.probability.toMeasure :=
    compact_integrable (((continuous_apply i).comp (continuous_edgeMessage lam)).mul
      (continuous_edge_centeredLog hl₀ hl₁ i))
  unfold finiteBranchExpectation
  simp_rw [weighted_symEntropy (branchEdges_positive hl₀ hl₁ _)]
  rw [integral_div]
  rw [integral_avg_measure (f := fun m : Fin n → Message ↦ fun i ↦ branchProduct (branchEdges lam m) i*(∑ j, logCentered (branchEdges lam m j) i))
    (fun i ↦ integrable_weighted_sum (ι := Fin n) (ha i) (hau i))]
  have he (i : Fin 3) : (∫ m : Fin n → Message, branchProduct (branchEdges lam m) i*(∑ j, logCentered (branchEdges lam m j) i)
      ∂(Measure.pi fun _ ↦ Q.probability.toMeasure)) =
      n*(2*∫ m, symEntropy (edgeMessage lam m) ∂Q.probability.toMeasure) := by
    have h := integral_weighted_sum (ι := Fin n) (ha i) (hau i) (Q.edge_balanced lam i)
    rw [Q.edge_centeredLog_mean hl₀ hl₁] at h
    simpa only [Fintype.card_fin, weightProduct, branchProduct, branchEdges] using h
  simp_rw [he]
  rw [avg_const]
  ring

theorem finite_correction (Q : Law) {lam : ℝ} (hl₀ : 0 ≤ lam) (hl₁ : lam < 1) (n : ℕ) :
    finiteBranchExpectation Q lam n correction =
      n*(∫ m, correction (edgeMessage lam m) ∂Q.probability.toMeasure)+
      2*((n:ℝ)^2-n)*(∫ m, symEntropy (edgeMessage lam m) ∂Q.probability.toMeasure)^2 := by
  have ha (i : Fin 3) : Integrable (fun m ↦ edgeMessage lam m i) Q.probability.toMeasure :=
    compact_integrable ((continuous_apply i).comp (continuous_edgeMessage lam))
  have hau (i : Fin 3) : Integrable (fun m ↦ edgeMessage lam m i*logCentered (edgeMessage lam m) i) Q.probability.toMeasure :=
    compact_integrable (((continuous_apply i).comp (continuous_edgeMessage lam)).mul
      (continuous_edge_centeredLog hl₀ hl₁ i))
  have hau₂ (i : Fin 3) : Integrable (fun m ↦ edgeMessage lam m i*logCentered (edgeMessage lam m) i^2) Q.probability.toMeasure :=
    compact_integrable (((continuous_apply i).comp (continuous_edgeMessage lam)).mul
      ((continuous_edge_centeredLog hl₀ hl₁ i).pow 2))
  unfold finiteBranchExpectation
  simp_rw [weighted_correction (branchEdges_positive hl₀ hl₁ _)]
  rw [integral_div]
  rw [integral_avg_measure (f := fun m : Fin n → Message ↦ fun i ↦ branchProduct (branchEdges lam m) i*(∑ j, logCentered (branchEdges lam m j) i)^2)
    (fun i ↦ integrable_weighted_sq_sum (ι := Fin n) (ha i) (hau i) (hau₂ i))]
  have he (i : Fin 3) : (∫ m : Fin n → Message, branchProduct (branchEdges lam m) i*(∑ j, logCentered (branchEdges lam m j) i)^2
      ∂(Measure.pi fun _ ↦ Q.probability.toMeasure)) =
      n*(2*∫ m, correction (edgeMessage lam m) ∂Q.probability.toMeasure)+
      ((n:ℝ)^2-n)*(2*∫ m, symEntropy (edgeMessage lam m) ∂Q.probability.toMeasure)^2 := by
    have h := integral_weighted_sq_sum (ι := Fin n) (ha i) (hau i) (hau₂ i) (Q.edge_balanced lam i)
    rw [Q.edge_centeredLog_mean hl₀ hl₁, Q.edge_centeredLog_sq hl₀ hl₁] at h
    simpa only [Fintype.card_fin, weightProduct, branchProduct, branchEdges] using h
  simp_rw [he]
  rw [avg_const]
  ring

theorem finite_info (Q : Law) {lam : ℝ} (hl₀ : 0 ≤ lam) (hl₁ : lam < 1) (n : ℕ) :
    finiteBranchExpectation Q lam n info =
      n*(∫ m, info (edgeMessage lam m) ∂Q.probability.toMeasure)-correlationEntropy Q lam n := by
  have ha (i : Fin 3) : Integrable (fun m ↦ edgeMessage lam m i) Q.probability.toMeasure :=
    compact_integrable ((continuous_apply i).comp (continuous_edgeMessage lam))
  have hau (i : Fin 3) : Integrable (fun m ↦ edgeMessage lam m i*Real.log (edgeMessage lam m i)) Q.probability.toMeasure :=
    compact_integrable (((continuous_apply i).comp (continuous_edgeMessage lam)).mul
      (continuous_edge_log hl₀ hl₁ i))
  unfold finiteBranchExpectation
  simp_rw [weighted_info (branchEdges_positive hl₀ hl₁ _)]
  rw [integral_sub (f := fun m : Fin n → Message ↦ avg (fun i ↦ branchProduct (branchEdges lam m) i*(∑ j, Real.log (branchEdges lam m j i))))
    (g := fun m ↦ normalizer (branchEdges lam m)*Real.log (normalizer (branchEdges lam m)))
    (integrable_avg (fun i ↦ integrable_weighted_sum (ι := Fin n) (ha i) (hau i)))
    (compact_integrable (continuous_correlationIntegrand hl₀ hl₁ n))]
  congr 1
  rw [integral_avg_measure (f := fun m : Fin n → Message ↦ fun i ↦ branchProduct (branchEdges lam m) i*(∑ j, Real.log (branchEdges lam m j i)))
    (fun i ↦ integrable_weighted_sum (ι := Fin n) (ha i) (hau i))]
  have he (i : Fin 3) : (∫ m : Fin n → Message, branchProduct (branchEdges lam m) i*(∑ j, Real.log (branchEdges lam m j i))
      ∂(Measure.pi fun _ ↦ Q.probability.toMeasure)) =
      n*(∫ m, edgeMessage lam m i*Real.log (edgeMessage lam m i) ∂Q.probability.toMeasure) := by
    simpa only [Fintype.card_fin, weightProduct, branchProduct, branchEdges] using integral_weighted_sum (ι := Fin n) (ha i) (hau i) (Q.edge_balanced lam i)
  simp_rw [he]
  rw [avg_mul, ← integral_avg_measure hau]
  rfl

end ThreeState.TreeClauses.Experiment

end

end OAI
