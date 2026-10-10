import OAI.NumberTheory.CubicMoment.Estimates.StructuredWeightScaling

namespace OAI

/-! The factor cutoff may be moved to the current output dyad. It does
not impose a new condition on a product whose norm is already in that dyad. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma orderedConvolution_filter_norm (S : ι → Finset Eisenstein)
    (w : ι → Eisenstein → ℂ) {z : Eisenstein} {R : ℝ}
    (hz : z ≠ 0) (hR : norm z ≤ R) :
    orderedConvolution (fun i => (S i).filter (fun n => norm n ≤ R)) w z =
      orderedConvolution S w z := by
  have heq : (Fintype.piFinset (fun i => (S i).filter (fun n => norm n ≤ R))).filter
      (fun n => (∏ i, n i) = z) =
      (Fintype.piFinset S).filter (fun n => (∏ i, n i) = z) := by
    ext n
    simp only [Finset.mem_filter,Fintype.mem_piFinset]
    constructor
    · rintro ⟨hn,hprod⟩
      exact ⟨fun i => (hn i).1,hprod⟩
    · rintro ⟨hn,hprod⟩
      refine ⟨fun i => ⟨hn i,?_⟩,hprod⟩
      apply (norm_le_of_dvd hz ?_).trans hR
      rw [← hprod]
      exact Finset.dvd_prod_of_mem n (Finset.mem_univ i)
  unfold orderedConvolution
  rw [heq]

lemma squarefreeConvolution_filter_norm (S : ι → Finset Eisenstein)
    (w : ι → Eisenstein → ℂ) {z : Eisenstein} {R : ℝ}
    (hz : z ≠ 0) (hR : norm z ≤ R) :
    squarefreeConvolution (fun i => (S i).filter (fun n => norm n ≤ R)) w z =
      squarefreeConvolution S w z := by
  unfold squarefreeConvolution
  rw [orderedConvolution_filter_norm S w hz hR]

omit [Fintype ι] [DecidableEq ι] in
lemma coordinatePrimeSupport_trim (W : ι → ℝ → ℂ) (X : ι → ℝ)
    {Y Z : ℝ} (hYZ : Y ≤ Z) :
    coordinatePrimeSupport W X Y =
      fun i => (coordinatePrimeSupport W X Z i).filter (fun n => norm n ≤ 2*Y) := by
  funext i
  ext n
  simp only [coordinatePrimeSupport,coordinateSupport,Finset.mem_filter,mem_primaryElementBall]
  constructor
  · rintro ⟨⟨⟨hp,hY⟩,hw⟩,hq⟩
    exact ⟨⟨⟨⟨hp,by linarith⟩,hw⟩,hq⟩,hY⟩
  · rintro ⟨⟨⟨⟨hp,_⟩,hw⟩,hq⟩,hY⟩
    exact ⟨⟨⟨hp,hY⟩,hw⟩,hq⟩

lemma primeMomentCoefficient_dyad_consistent (W : ι → ℝ → ℂ) (X : ι → ℝ)
    {Y Z : ℝ} (hYZ : Y ≤ Z) {z : Eisenstein} (hz : z ≠ 0) (hN : norm z ≤ 2*Y) :
    primeMomentCoefficient W X Y z = primeMomentCoefficient W X Z z := by
  unfold primeMomentCoefficient
  rw [coordinatePrimeSupport_trim W X hYZ,squarefreeConvolution_filter_norm _ _ hz hN]

lemma orderedSupport_filter_norm (S : ι → Finset Eisenstein)
    {z : Eisenstein} {R : ℝ} (hz : z ≠ 0) (hR : norm z ≤ R)
    (hmem : z ∈ orderedConvolutionSupport S) :
    z ∈ orderedConvolutionSupport (fun i => (S i).filter (fun n => norm n ≤ R)) := by
  obtain ⟨n,hn,hprod⟩ := Finset.mem_image.mp hmem
  apply Finset.mem_image.mpr
  refine ⟨n,Fintype.mem_piFinset.mpr (fun i => Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mp hn i,?_⟩),hprod⟩
  apply (norm_le_of_dvd hz ?_).trans hR
  rw [← hprod]
  exact Finset.dvd_prod_of_mem n (Finset.mem_univ i)

def structuredPrimeMomentAt (a b v e : Eisenstein) (u : ℝ)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) (Z : ℝ) (V : ℝ → ℂ) (Y : ℝ) : ℂ :=
  ∑ z ∈ (orderedConvolutionSupport (coordinatePrimeSupport W X Z)).filter
      (fun z => IsCoprime z e),
    primeMomentCoefficient W X Z z*mellinPhase u (norm z)*
      cubicSymbol z (v*a*b^2)*V (norm z/Y)

lemma structuredPrimeMomentAt_eq (a b v e : Eisenstein) (u : ℝ)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) {Y Z : ℝ} (hY : 0 < Y) (hYZ : Y ≤ Z)
    (V : ℝ → ℂ) (hVhi : ∀ x, 2 < x → V x = 0) :
    structuredPrimeMomentAt a b v e u W X Z V Y =
      structuredPrimeMoment a b v e u W X V Y := by
  let T := (orderedConvolutionSupport (coordinatePrimeSupport W X Y)).filter
    (fun z => IsCoprime z e)
  let U := (orderedConvolutionSupport (coordinatePrimeSupport W X Z)).filter
    (fun z => IsCoprime z e)
  have hsub : T ⊆ U := by
    intro z hz
    obtain ⟨hz,hcop⟩ := Finset.mem_filter.mp hz
    obtain ⟨n,hn,hprod⟩ := Finset.mem_image.mp hz
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_image.mpr ⟨n,?_,hprod⟩,hcop⟩
    rw [coordinatePrimeSupport_trim W X hYZ] at hn
    exact Fintype.mem_piFinset.mpr (fun i => (Finset.mem_filter.mp (Fintype.mem_piFinset.mp hn i)).1)
  have hzero (z : Eisenstein) (hz : z ∈ U) (hnorm : ¬norm z ≤ 2*Y) :
      V (norm z/Y) = 0 := hVhi _ ((lt_div_iff₀ hY).mpr (lt_of_not_ge hnorm))
  have hnonzero (z : Eisenstein) (hz : z ∈ U) : z ≠ 0 :=
    primary_ne_zero (orderedPrimarySupport_primary (coordinatePrimeSupport W X Z)
      (fun i n hn => (coordinatePrimeSupport_primary W X Z i n hn).1)
      (Finset.mem_filter.mp hz).1)
  symm
  change (∑ z ∈ T, _) = ∑ z ∈ U, _
  calc
    _ = ∑ z ∈ T, primeMomentCoefficient W X Z z*mellinPhase u (norm z)*
        cubicSymbol z (v*a*b^2)*V (norm z/Y) := by
      apply Finset.sum_congr rfl
      intro z hz
      by_cases hN : norm z ≤ 2*Y
      · rw [primeMomentCoefficient_dyad_consistent W X hYZ (hnonzero z (hsub hz)) hN]
      · rw [hzero z (hsub hz) hN]
        simp only [mul_zero]
    _ = _ := Finset.sum_subset hsub (by
      intro z hz hnot
      have hN : ¬norm z ≤ 2*Y := by
        intro hN
        have hm := orderedSupport_filter_norm (coordinatePrimeSupport W X Z) (hnonzero z hz) hN
          (Finset.mem_filter.mp hz).1
        rw [← coordinatePrimeSupport_trim W X hYZ] at hm
        exact hnot (Finset.mem_filter.mpr ⟨hm,(Finset.mem_filter.mp hz).2⟩)
      rw [hzero z hz hN,mul_zero])

end CubicFirstMoment

end

end OAI
