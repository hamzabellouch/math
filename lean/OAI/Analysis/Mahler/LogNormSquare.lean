import OAI.Analysis.Mahler.NormSquareJet
import OAI.Analysis.Mahler.LogScalarJet
import Mathlib.Analysis.Calculus.ContDiff.Defs

namespace OAI

open Set Filter ContinuousLinearMap
open scoped Topology

namespace SymmetricMahler
noncomputable section
variable {E J : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [normedSpaceRealE : NormedSpace ℝ E]
    [isScalarTowerRealComplexE : IsScalarTower ℝ ℂ E] [fintypeJ : Fintype J]

def actualComplexTwoJet (f : J → E → ℂ) (x : E) : ComplexTwoJet E J :=
  ((fun j => f j x), (fun j => fderiv ℂ (f j) x),
    (fun j => fderiv ℂ (fderiv ℂ (f j)) x))

lemma C2_log_normSq_derivatives {U : Set E} (hU : IsOpen U)
    {f : J → E → ℂ} (hf : ∀ j, ContDiffOn ℂ 2 (f j) U)
    {x : E} (hx : x ∈ U) (hp : sumNormSq (fun j => f j x) ≠ 0) :
    fderiv ℝ (fun y => Real.log (sumNormSq (fun j => f j y))) x =
      logD (sumNormSq (fun j => f j x))
        (sumNormSqD (fun j => f j x) (fun j => fderiv ℂ (f j) x)) ∧
    fderiv ℝ (fderiv ℝ (fun y => Real.log (sumNormSq (fun j => f j y)))) x =
      logD2 (sumNormSq (fun j => f j x))
        (sumNormSqD (fun j => f j x) (fun j => fderiv ℂ (f j) x))
        (sumNormSqD2 (fun j => f j x) (fun j => fderiv ℂ (f j) x)
          (fun j => fderiv ℂ (fderiv ℂ (f j)) x)) := by
  have hd (j) := (hf j).differentiableOn (by norm_num : (2 : WithTop ℕ∞) ≠ 0)
  have hv (y) (hy : y ∈ U) (j) := ((hd j y hy).differentiableAt (hU.mem_nhds hy)).hasFDerivAt
  refine ⟨(hasFDerivAt_sumNormSq (hv x hx) |>.log hp).fderiv, ?_⟩
  apply fderiv_log_twice
  · filter_upwards [hU.mem_nhds hx] with y hy
    exact hasFDerivAt_sumNormSq (hv y hy)
  · exact hasFDerivAt_sumNormSqD (hv x hx)
      (fun j => ((((hf j).fderiv_of_isOpen (m := 1) hU (by norm_num)).differentiableOn
        (by norm_num : (1 : WithTop ℕ∞) ≠ 0) x hx).differentiableAt (hU.mem_nhds hx)).hasFDerivAt)
  · exact hp

omit normedSpaceRealE isScalarTowerRealComplexE fintypeJ in
lemma continuousOn_actualComplexTwoJet [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] [Fintype J] {U : Set E} (hU : IsOpen U) {f : J → E → ℂ}
    (hf : ∀ j, ContDiffOn ℂ 2 (f j) U) :
    ContinuousOn (actualComplexTwoJet f) U := by
  exact (continuousOn_pi.mpr (fun j => (hf j).continuousOn)).prodMk
    ((continuousOn_pi.mpr (fun j => (hf j).continuousOn_fderiv_of_isOpen hU (by norm_num))).prodMk
      (continuousOn_pi.mpr (fun j =>
        ((hf j).fderiv_of_isOpen (m := 1) hU (by norm_num)).continuousOn_fderiv_of_isOpen
          hU (by norm_num))))

omit normedSpaceRealE isScalarTowerRealComplexE in
lemma uniform_actualComplexTwoJet [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] {I : Type*} {l : Filter I} {K : Set E}
    {f : I → J → E → ℂ} {g : J → E → ℂ}
    (h0 : ∀ j, TendstoUniformlyOn (fun i => f i j) (g j) l K)
    (h1 : ∀ j, TendstoUniformlyOn (fun i => fderiv ℂ (f i j)) (fderiv ℂ (g j)) l K)
    (h2 : ∀ j, TendstoUniformlyOn (fun i => fderiv ℂ (fderiv ℂ (f i j)))
      (fderiv ℂ (fderiv ℂ (g j))) l K) :
    TendstoUniformlyOn (fun i => actualComplexTwoJet (f i)) (actualComplexTwoJet g) l K := by
  have v0 := uniform_finite_pi (V := ℂ) h0
  have v1 := uniform_finite_pi (V := E →L[ℂ] ℂ) h1
  have v2 := uniform_finite_pi (V := E →L[ℂ] (E →L[ℂ] ℂ)) h2
  have v12 := uniform_pair v1 v2
  exact uniform_pair v0 v12

/-- The analytic composition passage in the fixed-annulus argument.
Every convergence hypothesis concerns the original complex functions and
their actual complex derivatives. Every derivative in the conclusion is
an actual real Fréchet derivative of the logarithm of the finite norm sum. -/
theorem uniform_C2_log_sumNormSq [FiniteDimensional ℂ E] [FiniteDimensional ℝ E]
    {I : Type*} {l : Filter I} {K U : Set E} {f : I → J → E → ℂ} {g : J → E → ℂ}
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (hg : ∀ j, ContDiffOn ℂ 2 (g j) U)
    (hf : ∀ᶠ i in l, ∀ j, ContDiffOn ℂ 2 (f i j) U)
    (hp : ∀ x ∈ K, 0 < ∑ j, Complex.normSq (g j x))
    (h0 : ∀ j, TendstoUniformlyOn (fun i => f i j) (g j) l K)
    (h1 : ∀ j, TendstoUniformlyOn (fun i => fderiv ℂ (f i j)) (fderiv ℂ (g j)) l K)
    (h2 : ∀ j, TendstoUniformlyOn (fun i => fderiv ℂ (fderiv ℂ (f i j)))
      (fderiv ℂ (fderiv ℂ (g j))) l K) :
    (∃ c : ℝ, 0 < c ∧ ∀ᶠ i in l, ∀ x ∈ K, c ≤ ∑ j, Complex.normSq (f i j x)) ∧
    TendstoUniformlyOn (fun i x => Real.log (∑ j, Complex.normSq (f i j x)))
      (fun x => Real.log (∑ j, Complex.normSq (g j x))) l K ∧
    TendstoUniformlyOn
      (fun i => fderiv ℝ (fun x => Real.log (∑ j, Complex.normSq (f i j x))))
      (fderiv ℝ (fun x => Real.log (∑ j, Complex.normSq (g j x)))) l K ∧
    TendstoUniformlyOn
      (fun i => fderiv ℝ (fderiv ℝ (fun x => Real.log (∑ j, Complex.normSq (f i j x)))))
      (fderiv ℝ (fderiv ℝ (fun x => Real.log (∑ j, Complex.normSq (g j x))))) l K := by
  let : ProperSpace (ComplexTwoJet E J) := FiniteDimensional.proper ℂ (ComplexTwoJet E J)
  have hq := uniform_actualComplexTwoJet h0 h1 h2
  have hqc := (continuousOn_actualComplexTwoJet hU hg).mono hKU
  have c0 : Continuous (fun q : ComplexTwoJet E J => sumNormSq q.1) :=
    continuous_sumNormSq.comp continuous_fst
  have c1 := continuous_sumNormSqD (E := E) (J := J)
  have c2 := continuous_sumNormSqD2 (E := E) (J := J)
  have u0 := uniform_comp_of_compact (E := ComplexTwoJet E J) (H := ℝ) hK hqc hq c0
  have u1 := uniform_comp_of_compact (E := ComplexTwoJet E J) (H := E →L[ℝ] ℝ) hK hqc hq c1
  have u2 := uniform_comp_of_compact (E := ComplexTwoJet E J) (H := E →L[ℝ] (E →L[ℝ] ℝ)) hK hqc hq c2
  obtain ⟨⟨c, hc, hpos⟩, v0, v1, v2⟩ := uniform_log_jets hK
    (c0.comp_continuousOn hqc) (c1.comp_continuousOn hqc) (c2.comp_continuousOn hqc) hp u0 u1 u2
  have eg1 : ∀ x ∈ K,
      logD (sumNormSq (fun j => g j x))
        (sumNormSqD (fun j => g j x) (fun j => fderiv ℂ (g j) x)) =
      fderiv ℝ (fun y => Real.log (∑ j, Complex.normSq (g j y))) x := by
    intro x hx
    exact (C2_log_normSq_derivatives hU hg (hKU hx) (ne_of_gt (hp x hx))).1.symm
  have eg2 : ∀ x ∈ K,
      logD2 (sumNormSq (fun j => g j x))
        (sumNormSqD (fun j => g j x) (fun j => fderiv ℂ (g j) x))
        (sumNormSqD2 (fun j => g j x) (fun j => fderiv ℂ (g j) x)
          (fun j => fderiv ℂ (fderiv ℂ (g j)) x)) =
      fderiv ℝ (fderiv ℝ (fun y => Real.log (∑ j, Complex.normSq (g j y)))) x := by
    intro x hx
    exact (C2_log_normSq_derivatives hU hg (hKU hx) (ne_of_gt (hp x hx))).2.symm
  refine ⟨⟨c, hc, hpos⟩, v0, ?_, ?_⟩
  · apply (v1.congr_right eg1).congr
    filter_upwards [hf, hpos] with i hi hpi
    intro x hx
    exact (C2_log_normSq_derivatives hU hi (hKU hx)
      (ne_of_gt (lt_of_lt_of_le hc (hpi x hx)))).1.symm
  · apply (v2.congr_right eg2).congr
    filter_upwards [hf, hpos] with i hi hpi
    intro x hx
    exact (C2_log_normSq_derivatives hU hi (hKU hx)
      (ne_of_gt (lt_of_lt_of_le hc (hpi x hx)))).2.symm

end
end SymmetricMahler

end OAI
