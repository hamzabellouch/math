import OAI.NumberTheory.CubicMoment.Estimates.PrimeCoordinateDifference

namespace OAI

/-! Restricting the indicator convolution to genuine primary primes,
followed by the exact squarefree discrepancy. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma orderedConvolution_primeIndicator (S : ι → Finset Eisenstein)
    (w : ι → Eisenstein → ℂ) (b : Eisenstein) :
    orderedConvolution S (fun i n => (primeIndicator n:ℂ)*w i n) b =
      orderedConvolution (fun i => (S i).filter Prime) w b := by
  unfold orderedConvolution
  let T := (Fintype.piFinset S).filter (fun n => (∏ i, n i) = b)
  let U := (Fintype.piFinset (fun i => (S i).filter Prime)).filter (fun n => (∏ i, n i) = b)
  have hsub : U ⊆ T := by
    intro n hn
    obtain ⟨hn,hprod⟩ := Finset.mem_filter.mp hn
    exact Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mpr (fun i =>
      (Finset.mem_filter.mp (Fintype.mem_piFinset.mp hn i)).1),hprod⟩
  have he : (∑ n ∈ U, ∏ i, (primeIndicator (n i):ℂ)*w i (n i)) =
      ∑ n ∈ T, ∏ i, (primeIndicator (n i):ℂ)*w i (n i) := by
    apply Finset.sum_subset hsub
    intro n hn hnot
    have hex : ∃ i, ¬Prime (n i) := by
      by_contra h
      push Not at h
      have ht := Finset.mem_filter.mp hn
      exact hnot (Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mpr
        (fun i => Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mp ht.1 i,h i⟩),ht.2⟩)
    obtain ⟨i,hi⟩ := hex
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp only [primeIndicator,ite_eq_right hi,Complex.ofReal_zero,zero_mul]
  change (∑ n ∈ T, _) = ∑ n ∈ U, _
  rw [← he]
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.prod_congr rfl
  intro i hi
  have hp := (Finset.mem_filter.mp (Fintype.mem_piFinset.mp (Finset.mem_filter.mp hn).1 i)).2
  simp only [primeIndicator,ite_eq_left hp,Complex.ofReal_one,one_mul]

def coordinatePrimeSupport (W : ι → ℝ → ℂ) (X : ι → ℝ) (Y : ℝ) (i : ι) : Finset Eisenstein :=
  (coordinateSupport W X Y i).filter Prime

omit [Fintype ι] [DecidableEq ι] in
lemma coordinatePrimeSupport_primary (W : ι → ℝ → ℂ) (X : ι → ℝ) (Y : ℝ) :
    ∀ i, ∀ p ∈ coordinatePrimeSupport W X Y i, primaryPrime p := by
  intro i p hp
  exact ⟨coordinateSupport_primary W X Y i p (Finset.mem_filter.mp hp).1,
    (Finset.mem_filter.mp hp).2⟩

lemma primeIndicatorTuple_eq_prime_convolution (a b : Eisenstein)
    (ha : primary a) (hb : primary b) (q : ι → Eisenstein)
    (η : (i : ι) → MulChar (Residues (q i)) ℂ) (t : ι → ℝ)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) (V : ℝ → ℂ) (Y : ℝ) :
    primaryPrimeIndicatorTuple a b q η t W X V Y =
      ∑ z ∈ orderedConvolutionSupport (coordinatePrimeSupport W X Y),
        orderedConvolution (coordinatePrimeSupport W X Y) (coordinateFactor q η t W X) z*
          (mixedCubic a b z*V (norm z/Y)) := by
  have hp := coordinate_convolution_collection (fun n => (primeIndicator n:ℂ))
    a b ha hb q η t W X V Y
  change primaryPrimeIndicatorTuple a b q η t W X V Y = _ at hp
  rw [hp]
  simp_rw [orderedConvolution_primeIndicator]
  symm
  apply Finset.sum_subset
  · intro z hz
    obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp hz
    exact Finset.mem_image.mpr ⟨n,Fintype.mem_piFinset.mpr (fun i =>
      (Finset.mem_filter.mp (Fintype.mem_piFinset.mp hn i)).1),rfl⟩
  · intro z hz hnot
    rw [orderedConvolution_eq_zero_of_not_mem _ _ hnot,zero_mul]

def primarySquarefreePrimeTuple (a b : Eisenstein) (q : ι → Eisenstein)
    (η : (i : ι) → MulChar (Residues (q i)) ℂ) (t : ι → ℝ)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) (V : ℝ → ℂ) (Y : ℝ) : ℂ :=
  ∑ z ∈ orderedConvolutionSupport (coordinatePrimeSupport W X Y),
    squarefreeConvolution (coordinatePrimeSupport W X Y) (coordinateFactor q η t W X) z*
      (mixedCubic a b z*V (norm z/Y))

lemma primeIndicator_sub_squarefree (a b : Eisenstein) (ha : primary a) (hb : primary b)
    (q : ι → Eisenstein) (η : (i : ι) → MulChar (Residues (q i)) ℂ) (t : ι → ℝ)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) (V : ℝ → ℂ) (Y : ℝ) :
    primaryPrimeIndicatorTuple a b q η t W X V Y-primarySquarefreePrimeTuple a b q η t W X V Y =
      ∑ z ∈ orderedConvolutionSupport (coordinatePrimeSupport W X Y),
        squarefreeConvolutionError (coordinatePrimeSupport W X Y) (coordinateFactor q η t W X) z*
          (mixedCubic a b z*V (norm z/Y)) := by
  rw [primeIndicatorTuple_eq_prime_convolution a b ha hb]
  simp only [primarySquarefreePrimeTuple,squarefreeConvolutionError,sub_mul,Finset.sum_sub_distrib]

def coordinatePrimeCutoff (W : ι → ℝ → ℂ) (X : ι → ℝ) (Y : ℝ) : Finset Eisenstein :=
  (orderedConvolutionSupport (coordinatePrimeSupport W X Y)).filter (fun b => norm b ≤ 2*Y)

lemma coordinatePrimeCutoff_spec (W : ι → ℝ → ℂ) (X : ι → ℝ) (Y : ℝ) :
    coordinatePrimeCutoff W X Y ⊆ orderedConvolutionSupport (coordinatePrimeSupport W X Y) ∧
      ∀ b ∈ coordinatePrimeCutoff W X Y, norm b ≤ 2*Y :=
  ⟨Finset.filter_subset _ _,fun _ hb => (Finset.mem_filter.mp hb).2⟩

lemma primeIndicator_sub_squarefree_cutoff (a b : Eisenstein)
    (ha : primary a) (hb : primary b) (q : ι → Eisenstein)
    (η : (i : ι) → MulChar (Residues (q i)) ℂ) (t : ι → ℝ)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) (V : ℝ → ℂ) {Y : ℝ} (hY : 0 < Y)
    (hV : ∀ x, 2 < x → V x = 0) :
    primaryPrimeIndicatorTuple a b q η t W X V Y-primarySquarefreePrimeTuple a b q η t W X V Y =
      ∑ z ∈ coordinatePrimeCutoff W X Y,
        squarefreeConvolutionError (coordinatePrimeSupport W X Y) (coordinateFactor q η t W X) z*
          (mixedCubic a b z*V (norm z/Y)) := by
  rw [primeIndicator_sub_squarefree a b ha hb]
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro z hz hnot
  have hlarge : 2*Y < norm z := lt_of_not_ge (fun h => hnot (Finset.mem_filter.mpr ⟨hz,h⟩))
  have hv := hV (norm z/Y) ((lt_div_iff₀ hY).mpr hlarge)
  rw [hv,mul_zero,mul_zero]

end CubicFirstMoment

end

end OAI
