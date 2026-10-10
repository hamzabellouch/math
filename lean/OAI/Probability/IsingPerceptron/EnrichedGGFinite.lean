import Mathlib
import OAI.Probability.IsingPerceptron.JointGGClosure

namespace OAI

/-! Enriched G G Finite. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

def enrichedMonomialResidual {N : ℕ} {A : Type*} [MeasurableSpace A]
    (P : Measure A) (r : ℝ≥0) (n : ℕ) (b h : ℕ → ℝ)
    (u : Fin N → ℝ) (ν : Measure (Spin N)) (φ : A → Spin N → ℝ)
    (p d : ℕ) {m : ℕ} (D : (Fin (m+1) → Spin N × LabeledLeaf n) → ℝ) : ℝ :=
  let κ := fun x y : Spin N × LabeledLeaf n => spinOverlap x.1 y.1 ^ p * treeOverlap n x.2 y.2 ^ d
  (m+1 : ℕ)*enrichedReplicaAverage P r n b h u ν φ
        (fun τ : Fin (m+1+1) → Spin N × LabeledLeaf n => D (Fin.tail τ)*κ ((Fin.tail τ) 0) (τ 0)) -
      enrichedReplicaAverage P r n b h u ν φ D * enrichedReplicaAverage P r n b h u ν φ
        (fun τ : Fin 2 → Spin N × LabeledLeaf n => κ (τ 1) (τ 0)) -
      enrichedReplicaAverage P r n b h u ν φ
        (fun σ => D σ*(∑ l : Fin m, κ (σ 0) (σ l.succ)))

lemma enrichedMonomialResidual_bound {N : ℕ} (hN : 0 < N) (n : ℕ) (b : ℕ → ℝ)
    (hb : CascadeExponents n b) {h : ℕ → ℝ} (hh : Monotone h) (h0 : 0 ≤ h 0)
    {H : ℝ} (hH : h n ≤ H) (u : Fin N → ℝ) (hu : ∀ j, u j ∈ Icc (1:ℝ) 2) (j : Fin N)
    (ν : Measure (Spin N)) [IsProbabilityMeasure ν]
    {A : Type*} [MeasurableSpace A] (P : Measure A) [IsProbabilityMeasure P]
    {φ : A → Spin N → ℝ} (hm : Measurable φ) {K : ℝ} (hK : 0 ≤ K)
    (hφ : ∀ y x, |φ y x| ≤ K) (r : ℝ≥0) {α : ℝ} (hr : (r:ℝ) ≤ α*N)
    (hmin : ∀ v ∈ Icc (1:ℝ) 2, enrichedCoordinateObjective P r n b h u j ν φ (u j) ≤
      enrichedCoordinateObjective P r n b h u j ν φ v)
    (he : perturbationScale N ≤ 1/8) (hs : contactStep N ≤ 1/4)
    {m : ℕ} (D : (Fin (m+1) → Spin N × LabeledLeaf n) → ℝ)
    {B : ℝ} (hB : 0 ≤ B) (hD : ∀ σ, |D σ| ≤ B) :
    |enrichedMonomialResidual P r n b h u ν φ (monomialIndex j).1 (monomialIndex j).2 D| ≤
      contactGGRate N j
        (4*(∫ T, (Real.log (rawTreeTotal n T).toReal)^2 ∂(rawCascadeLaw n b : Measure (RawTree n)))+
          H+4+5*K^2*α) B := by
  have hua : ∀ i, |u i| ≤ 2 := fun i => abs_le.mpr ⟨by linarith [(hu i).1],(hu i).2⟩
  have hint := enriched_coordinate_minimum_interior hN n b hb hh h0 u hua j ν P hm hK hφ r hmin he hs
  have hn : (0:ℝ) < N := by exact_mod_cast hN
  have hstep : 0 < contactStep N := Real.rpow_pos_of_pos hn _
  have hepos : 0 < perturbationScale N := Real.rpow_pos_of_pos hn _
  have ha := perturbationAmplitude_pos hN j
  have hg := enriched_gg_at_coordinate_minimum hN n b hb hh h0 hH u hua j ν P hm hK hφ r hr
    hstep (one_div_pos.mpr hepos) hint.1 hint.2 hmin D hB hD
  change |perturbationAmplitude N j*u j| *
    |enrichedMonomialResidual P r n b h u ν φ (monomialIndex j).1 (monomialIndex j).2 D| ≤ _ at hg
  have hau : perturbationAmplitude N j ≤ |perturbationAmplitude N j*u j| := by
    rw [abs_of_pos (mul_pos ha (lt_of_lt_of_le zero_lt_one (hu j).1))]
    nlinarith [(hu j).1]
  apply (le_div_iff₀ ha).2
  calc
    _ = perturbationAmplitude N j*
      |enrichedMonomialResidual P r n b h u ν φ (monomialIndex j).1 (monomialIndex j).2 D| := by ring
    _ ≤ |perturbationAmplitude N j*u j| *
      |enrichedMonomialResidual P r n b h u ν φ (monomialIndex j).1 (monomialIndex j).2 D| :=
        mul_le_mul_of_nonneg_right hau (abs_nonneg _)
    _ ≤ _ := hg

 
def enrichedPerturbationObjective {N : ℕ} {A : Type*} [MeasurableSpace A]
    (P : Measure A) (r : ℝ≥0) (n : ℕ) (b h : ℕ → ℝ)
    (ν : Measure (Spin N)) (φ : A → Spin N → ℝ) (u : Fin N → ℝ) : ℝ :=
  -enrichedMeanPressure P r n b h u ν φ +
    ∑ j : Fin N, perturbationWeight j*(u j-3/2)^2

lemma enriched_minimum_coordinate {N : ℕ} {A : Type*} [MeasurableSpace A]
    (P : Measure A) (r : ℝ≥0) (n : ℕ) (b h : ℕ → ℝ)
    (ν : Measure (Spin N)) (φ : A → Spin N → ℝ) (u : Fin N → ℝ)
    (hu : ∀ j, u j ∈ Icc (1:ℝ) 2)
    (hmin : ∀ v : Fin N → ℝ, (∀ j, v j ∈ Icc (1:ℝ) 2) →
      enrichedPerturbationObjective P r n b h ν φ u ≤ enrichedPerturbationObjective P r n b h ν φ v)
    (j : Fin N) (v : ℝ) (hv : v ∈ Icc (1:ℝ) 2) :
    enrichedCoordinateObjective P r n b h u j ν φ (u j) ≤
      enrichedCoordinateObjective P r n b h u j ν φ v := by
  classical
  have huv : ∀ i, Function.update u j v i ∈ Icc (1:ℝ) 2 := by
    intro i
    by_cases hi : i = j
    · subst i; simpa only [Function.update_self] using hv
    · simpa only [Function.update_of_ne hi] using hu i
  have hc := hmin (Function.update u j v) huv
  unfold enrichedPerturbationObjective at hc
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j),
    ← Finset.add_sum_erase _ _ (Finset.mem_univ j)] at hc
  have he : (∑ i ∈ Finset.univ.erase j, perturbationWeight i*(Function.update u j v i-3/2)^2) =
      ∑ i ∈ Finset.univ.erase j, perturbationWeight i*(u i-3/2)^2 := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [Function.update_of_ne (Finset.mem_erase.mp hi).1]
  rw [he,Function.update_self] at hc
  unfold enrichedCoordinateObjective
  rw [Function.update_eq_self]
  linarith

end IsingPerceptron

 

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction
namespace IsingPerceptron

def newReplicaEmbedding (k : ℕ) (e : Equiv.Perm (Fin k)) : Fin (k+1) → ℕ :=
  Fin.cases k (fun j => (e j).val)

lemma newReplicaEmbedding_injective (k : ℕ) (e : Equiv.Perm (Fin k)) :
    Function.Injective (newReplicaEmbedding k e) := by
  intro a
  refine Fin.cases ?_ (fun a => ?_) a
  · intro b
    refine Fin.cases ?_ (fun b => ?_) b
    · exact fun _ => rfl
    · intro hab
      have hlt := (e b).isLt
      simp only [newReplicaEmbedding,Fin.cases_zero,Fin.cases_succ] at hab
      omega
  · intro b
    refine Fin.cases ?_ (fun b => ?_) b
    · intro hab
      have hlt := (e a).isLt
      simp only [newReplicaEmbedding,Fin.cases_zero,Fin.cases_succ] at hab
      omega
    · intro hab
      apply congrArg Fin.succ
      apply e.injective
      apply Fin.val_injective
      exact hab

lemma sum_nonzero_permutation {m : ℕ} (e : Equiv.Perm (Fin (m+1))) (f : Fin (m+1) → ℝ) :
    (∑ l : Fin m, f (e l.succ)) = ∑ j ∈ Finset.univ.erase (e 0), f j := by
  classical
  have he := Equiv.sum_comp e f
  rw [Fin.sum_univ_succ,← Finset.add_sum_erase _ _ (Finset.mem_univ (e 0))] at he
  exact add_left_cancel he

lemma jointEntry_monomial_le (x : JointEntry) (p d : ℕ) : |x.1.1^p*x.2.1^d| ≤ 1 := by
  rw [abs_mul,abs_pow,abs_pow]
  have h1 : |x.1.1| ≤ 1 := abs_le.mpr x.1.2
  have h2 : |x.2.1| ≤ 1 := abs_le.mpr ⟨by linarith [x.2.2.1],x.2.2.2⟩
  exact (mul_le_mul (pow_le_one₀ (abs_nonneg _) h1)
    (pow_le_one₀ (abs_nonneg _) h2) (pow_nonneg (abs_nonneg _) _) zero_le_one).trans_eq
    (one_mul 1)

def monomialPair (n p d : ℕ) {N : ℕ} (x y : Spin N × LabeledLeaf n) : ℝ :=
  spinOverlap x.1 y.1^p*treeOverlap n x.2 y.2^d

lemma abs_monomialPair_le_one (n p d : ℕ) {N : ℕ} (x y : Spin N × LabeledLeaf n) :
    |monomialPair n p d x y| ≤ 1 := jointEntry_monomial_le (enrichedJointEntry n x y) p d

def finiteJointBlock {N m : ℕ} (n : ℕ) (σ : Fin m → Spin N × LabeledLeaf n) : JointBlock m :=
  fun i j => enrichedJointEntry n (σ i) (σ j)

def permutedBlockTest {N m : ℕ} (n : ℕ) (e : Equiv.Perm (Fin m))
    (D : JointBlock m → ℝ) (σ : Fin m → Spin N × LabeledLeaf n) : ℝ :=
  D (finiteJointBlock n (σ ∘ e.symm))

lemma enrichedArrayLawTest_integral {N : ℕ} (hN : 0 < N) (n : ℕ) (b : ℕ → ℝ)
    {h : ℕ → ℝ} (hh : Monotone h) (h0 : 0 ≤ h 0)
    (u : Fin N → ℝ) (hu : ∀ j, |u j| ≤ 2)
    (ν : Measure (Spin N)) [IsProbabilityMeasure ν]
    {A : Type*} [MeasurableSpace A] (P : Measure A) [IsProbabilityMeasure P]
    {φ : A → Spin N → ℝ} (hm : Measurable φ) {K : ℝ} (hK : 0 ≤ K)
    (hφ : ∀ y x, |φ y x| ≤ K) (r : ℝ≥0)
    (F : JointArray → ℝ) (hF : Measurable F)
    {m : ℕ} (D : (Fin m → Spin N × LabeledLeaf n) → ℝ) {C : ℝ} (hD : ∀ σ, |D σ| ≤ C)
    (ι : Fin m → ℕ) (hi : Function.Injective ι)
    (he : ∀ σ, F (sampledOverlapArray (enrichedJointEntry n) σ) = D (fun i => σ (ι i))) :
    (∫ x, F x ∂(enrichedArrayLaw P r n b h u ν hm : Measure JointArray)) =
      enrichedReplicaAverage P r n b h u ν φ D := by
  rw [enrichedArrayLaw_integral _ _ _ _ _ _ _ _ _ hF]
  simp_rw [he]
  exact enrichedReplicaLaw_integral hN n b hh h0 u hu ν P hm hK hφ r D hD ι hi

lemma permutedBlockTest_embedding {N m : ℕ} (n : ℕ) (e : Equiv.Perm (Fin m))
    (D : JointBlock m → ℝ) (σ : ℕ → Spin N × LabeledLeaf n) :
    permutedBlockTest n e D (fun j => σ (e j)) =
      D (jointBlockView m (sampledOverlapArray (enrichedJointEntry n) σ)) := by
  unfold permutedBlockTest
  apply congrArg D
  funext i j
  simp [finiteJointBlock,jointBlockView,sampledOverlapArray]

lemma enrichedArrayLaw_residual {N : ℕ} (hN : 0 < N) (n : ℕ) (b : ℕ → ℝ)
    {h : ℕ → ℝ} (hh : Monotone h) (h0 : 0 ≤ h 0)
    (u : Fin N → ℝ) (hu : ∀ j, |u j| ≤ 2)
    (ν : Measure (Spin N)) [IsProbabilityMeasure ν]
    {A : Type*} [MeasurableSpace A] (P : Measure A) [IsProbabilityMeasure P]
    {φ : A → Spin N → ℝ} (hm : Measurable φ) {K : ℝ} (hK : 0 ≤ K)
    (hφ : ∀ y x, |φ y x| ≤ K) (r : ℝ≥0)
    {m : ℕ} (e : Equiv.Perm (Fin (m+1))) (D : JointBlock (m+1) → ℝ)
    (hDc : Continuous D) {B : ℝ} (hB : 0 ≤ B) (hD : ∀ x, |D x| ≤ B) (p d : ℕ) :
    jointMonomialResidual (enrichedArrayLaw P r n b h u ν hm) (m+1) (e 0) D p d =
      enrichedMonomialResidual P r n b h u ν φ p d (permutedBlockTest n e D) := by
  classical
  let μ : Measure JointArray := enrichedArrayLaw P r n b h u ν hm
  let D' := permutedBlockTest (N := N) n e D
  have hD' : ∀ σ, |D' σ| ≤ B := fun σ => hD _
  have hcD : Continuous (fun x => D (jointBlockView (m+1) x)) :=
    hDc.comp (continuous_jointBlockView _)
  have hmono (x y : Spin N × LabeledLeaf n) := abs_monomialPair_le_one n p d x y
  have hnew : (∫ x, D (jointBlockView (m+1) x)*(x (e 0,m+1)).1.1^p*(x (e 0,m+1)).2.1^d ∂μ) =
      enrichedReplicaAverage P r n b h u ν φ
        (fun τ : Fin (m+1+1) → Spin N × LabeledLeaf n =>
          D' (Fin.tail τ)*monomialPair n p d ((Fin.tail τ) 0) (τ 0)) := by
    refine enrichedArrayLawTest_integral hN n b hh h0 u hu ν P hm hK hφ r _
      (hcD.mul (by fun_prop) |>.mul (by fun_prop) |>.measurable) _ (C := B)
      (fun τ => ?_) (newReplicaEmbedding (m+1) e) (newReplicaEmbedding_injective _ e) ?_
    · rw [abs_mul]
      exact (mul_le_mul (hD' _) (hmono _ _) (abs_nonneg _) hB).trans_eq (mul_one B)
    · intro σ
      change D (jointBlockView (m+1) (sampledOverlapArray (enrichedJointEntry n) σ)) *
        (enrichedJointEntry n (σ (e 0)) (σ (m+1))).1.1^p *
        (enrichedJointEntry n (σ (e 0)) (σ (m+1))).2.1^d =
        D' (fun i => σ ((e i).val)) * monomialPair n p d (σ (e 0)) (σ (m+1))
      rw [show D' (fun i => σ ((e i).val)) =
        D (jointBlockView (m+1) (sampledOverlapArray (enrichedJointEntry n) σ)) from
          permutedBlockTest_embedding n e D σ]
      simp only [enrichedJointEntry,monomialPair,mul_assoc]
  have hblock : (∫ x, D (jointBlockView (m+1) x) ∂μ) =
      enrichedReplicaAverage P r n b h u ν φ D' := by
    apply enrichedArrayLawTest_integral hN n b hh h0 u hu ν P hm hK hφ r _ hcD.measurable
      D' hD' (fun j => (e j).val) (Fin.val_injective.comp e.injective)
    intro σ
    exact (permutedBlockTest_embedding n e D σ).symm
  have hpair : (∫ x, (x (0,1)).1.1^p*(x (0,1)).2.1^d ∂μ) =
      enrichedReplicaAverage P r n b h u ν φ
        (fun τ : Fin 2 → Spin N × LabeledLeaf n => monomialPair n p d (τ 1) (τ 0)) := by
    refine enrichedArrayLawTest_integral hN n b hh h0 u hu ν P hm hK hφ r _ (by fun_prop)
      _ (C := 1) (fun τ => hmono _ _) ![1,0] ?_ ?_
    · intro a b hab
      fin_cases a <;> fin_cases b <;> simp_all
    · intro σ
      rfl
  have hsumBound (σ : Fin (m+1) → Spin N × LabeledLeaf n) :
      |D' σ*(∑ l : Fin m, monomialPair n p d (σ 0) (σ l.succ))| ≤ B*m := by
    rw [abs_mul]
    apply mul_le_mul (hD' _) _ (abs_nonneg _) hB
    calc
      _ ≤ ∑ l : Fin m, |monomialPair n p d (σ 0) (σ l.succ)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _ : Fin m, (1:ℝ) := Finset.sum_le_sum (fun l _ => hmono _ _)
      _ = _ := by simp
  have hsum : (∑ j ∈ Finset.univ.erase (e 0),
      ∫ x, D (jointBlockView (m+1) x)*(x (e 0,j)).1.1^p*(x (e 0,j)).2.1^d ∂μ) =
      enrichedReplicaAverage P r n b h u ν φ
        (fun σ => D' σ*(∑ l : Fin m, monomialPair n p d (σ 0) (σ l.succ))) := by
    have hI (j : Fin (m+1)) : Integrable
        (fun x : JointArray => D (jointBlockView (m+1) x)*(x (e 0,j)).1.1^p*(x (e 0,j)).2.1^d) μ :=
      compact_integrable (hcD.mul (by fun_prop) |>.mul (by fun_prop))
    rw [← integral_finsetSum _ (fun j _ => hI j)]
    apply enrichedArrayLawTest_integral hN n b hh h0 u hu ν P hm hK hφ r _
      (by apply Finset.measurable_sum; intro j hj; exact (hcD.mul (by fun_prop) |>.mul (by fun_prop)).measurable)
      _ hsumBound (fun j => (e j).val) (Fin.val_injective.comp e.injective)
    intro σ
    rw [show D' (fun j => σ ((e j).val)) =
      D (jointBlockView (m+1) (sampledOverlapArray (enrichedJointEntry n) σ)) from
        permutedBlockTest_embedding n e D σ]
    rw [sum_nonzero_permutation e (fun j => monomialPair n p d (σ (e 0)) (σ j)),Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [sampledOverlapArray,enrichedJointEntry,monomialPair,mul_assoc]
  unfold jointMonomialResidual
  rw [hnew,hblock,hpair,hsum]
  rfl

end IsingPerceptron

 

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction
namespace IsingPerceptron

lemma jointMonomialResidual_zero (μ : Measure JointArray) [IsProbabilityMeasure μ]
    (m : ℕ) (i : Fin (m+1)) (D : JointBlock (m+1) → ℝ) :
    jointMonomialResidual μ (m+1) i D 0 0 = 0 := by
  classical
  simp only [jointMonomialResidual,pow_zero,mul_one,integral_const,probReal_univ,
    smul_eq_mul,Finset.sum_const,Finset.card_erase_of_mem (Finset.mem_univ i),
    Finset.card_univ,Fintype.card_fin,Nat.add_sub_cancel,nsmul_eq_mul,Nat.cast_add,Nat.cast_one]
  ring

lemma enrichedArrayLaw_residual_bound {N : ℕ} (hN : 0 < N) (n : ℕ) (b : ℕ → ℝ)
    (hb : CascadeExponents n b) {h : ℕ → ℝ} (hh : Monotone h) (h0 : 0 ≤ h 0)
    {H : ℝ} (hH : h n ≤ H) (u : Fin N → ℝ) (hu : ∀ j, u j ∈ Icc (1:ℝ) 2) (j : Fin N)
    (ν : Measure (Spin N)) [IsProbabilityMeasure ν]
    {A : Type*} [MeasurableSpace A] (P : Measure A) [IsProbabilityMeasure P]
    {φ : A → Spin N → ℝ} (hm : Measurable φ) {K : ℝ} (hK : 0 ≤ K)
    (hφ : ∀ y x, |φ y x| ≤ K) (r : ℝ≥0) {α : ℝ} (hr : (r:ℝ) ≤ α*N)
    (hmin : ∀ v : Fin N → ℝ, (∀ j, v j ∈ Icc (1:ℝ) 2) →
      enrichedPerturbationObjective P r n b h ν φ u ≤ enrichedPerturbationObjective P r n b h ν φ v)
    (he : perturbationScale N ≤ 1/8) (hs : contactStep N ≤ 1/4)
    {m : ℕ} (i : Fin (m+1)) (D : JointBlock (m+1) → ℝ) (hDc : Continuous D)
    {B : ℝ} (hB : 0 ≤ B) (hD : ∀ x, |D x| ≤ B) :
    |jointMonomialResidual (enrichedArrayLaw P r n b h u ν hm) (m+1) i D
        (monomialIndex j).1 (monomialIndex j).2| ≤
      contactGGRate N j
        (4*(∫ T, (Real.log (rawTreeTotal n T).toReal)^2 ∂(rawCascadeLaw n b : Measure (RawTree n)))+
          H+4+5*K^2*α) B := by
  classical
  have hua : ∀ l, |u l| ≤ 2 := fun l => abs_le.mpr ⟨by linarith [(hu l).1],(hu l).2⟩
  have hg := enrichedMonomialResidual_bound hN n b hb hh h0 hH u hu j ν P hm hK hφ r hr
    (enriched_minimum_coordinate P r n b h ν φ u hu hmin j) he hs
    (permutedBlockTest n (Equiv.swap 0 i) D) hB (fun σ => hD _)
  have ht := enrichedArrayLaw_residual hN n b hh h0 u hua ν P hm hK hφ r
    (Equiv.swap 0 i) D hDc hB hD (monomialIndex j).1 (monomialIndex j).2
  rw [Equiv.swap_apply_left] at ht
  rw [ht]
  exact hg

 

theorem enriched_minimizers_jointGG
    (N : ℕ → ℕ) (hN : ∀ k, 0 < N k) (hNlim : Tendsto N atTop atTop)
    (n : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b)
    (h : ℕ → ℕ → ℝ) (hh : ∀ k, Monotone (h k)) (h0 : ∀ k, 0 ≤ h k 0)
    (H : ℝ) (hH : ∀ k, h k n ≤ H)
    (u : (k : ℕ) → Fin (N k) → ℝ) (hu : ∀ k j, u k j ∈ Icc (1:ℝ) 2)
    (ν : (k : ℕ) → Measure (Spin (N k))) [∀ k, IsProbabilityMeasure (ν k)]
    (A : ℕ → Type*) [∀ k, MeasurableSpace (A k)]
    (P : (k : ℕ) → Measure (A k)) [∀ k, IsProbabilityMeasure (P k)]
    (φ : (k : ℕ) → A k → Spin (N k) → ℝ) (hm : ∀ k, Measurable (φ k))
    (K : ℝ) (hK : 0 ≤ K) (hφ : ∀ k y x, |φ k y x| ≤ K)
    (r : ℕ → ℝ≥0) (α : ℝ) (hr : ∀ k, (r k:ℝ) ≤ α*N k)
    (hmin : ∀ k (v : Fin (N k) → ℝ), (∀ j, v j ∈ Icc (1:ℝ) 2) →
      enrichedPerturbationObjective (P k) (r k) n b (h k) (ν k) (φ k) (u k) ≤
        enrichedPerturbationObjective (P k) (r k) n b (h k) (ν k) (φ k) v)
    (μ : ProbabilityMeasure JointArray)
    (hL : Tendsto (fun k => enrichedArrayLaw (P k) (r k) n b (h k) (u k) (ν k) (hm k)) atTop (𝓝 μ)) :
    HasEntryGhirlandaGuerra (fun x i j => x (i,j)) (μ : Measure JointArray) := by
  apply jointGG_of_weak_monomial_residuals hL
  intro m hm2 i D hDc p d
  cases m with
  | zero => omega
  | succ m =>
    by_cases hpd : p+d = 0
    · have hp : p = 0 := by omega
      have hd : d = 0 := by omega
      subst p d
      simpa only [jointMonomialResidual_zero] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0:ℝ)) atTop (𝓝 0))
    · obtain ⟨j,hj⟩ := monomialIndex_surjective p d (by omega)
      let BD := BoundedContinuousFunction.mkOfCompact ⟨D,hDc⟩
      have hD : ∀ x, |D x| ≤ ‖BD‖ := fun x => by
        simpa only [BD,BoundedContinuousFunction.mkOfCompact_apply,ContinuousMap.coe_mk,Real.norm_eq_abs] using BD.norm_coe_le_norm x
      let L := 4*(∫ T, (Real.log (rawTreeTotal n T).toReal)^2
        ∂(rawCascadeLaw n b : Measure (RawTree n)))+H+4+5*K^2*α
      have he : ∀ᶠ k in atTop, perturbationScale (N k) ≤ 1/8 :=
        (perturbationScale_tendsto.comp hNlim).eventually (eventually_le_nhds (by norm_num))
      have hs : ∀ᶠ k in atTop, contactStep (N k) ≤ 1/4 :=
        (contactStep_tendsto.comp hNlim).eventually (eventually_le_nhds (by norm_num))
      have hjN : ∀ᶠ k in atTop, j < N k := hNlim.eventually (eventually_gt_atTop j)
      apply squeeze_zero_norm' _ ((contactGGRate_tendsto j L ‖BD‖).comp hNlim)
      filter_upwards [he,hs,hjN] with k he hs hjN
      let j' : Fin (N k) := ⟨j,hjN⟩
      have ht := enrichedArrayLaw_residual_bound (hN k) n b hb (hh k) (h0 k) (hH k)
        (u k) (hu k) j' (ν k) (P k) (hm k) hK (hφ k) (r k) (hr k) (hmin k)
        he hs i D hDc (norm_nonneg BD) hD
      simpa only [j',hj,Prod.fst,Prod.snd,Real.norm_eq_abs,Function.comp_def,L] using ht

end IsingPerceptron

end

end OAI
