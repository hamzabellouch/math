import OAI.Dynamics.StandardMap.TransportGraphs

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter Metric
open scoped Topology
namespace StandardMapEntropy
lemma forward_chart_jacobian (k : ℝ) (n : ℕ) (E I : Set ℝ) (X : ℝ × ℝ → ℝ) (yc : ℝ)
    (hX : ContinuousOn X (E ×ˢ I))
    (hlevel : ∀ s ∈ E, ∀ y ∈ I,
      liftedOrbit k y (X (s,y)) (n+1)=liftedOrbit k yc s (n+1))
    (ht : ∀ s ∈ E, ∀ y ∈ I, tSolution (orbitCoefficient k y (X (s,y))) (n+1) ≠ 0)
    (hr : ∀ s ∈ E, ∀ y ∈ I,
      Real.exp (-1152*Real.pi) ≤ |tSolution (orbitCoefficient k yc s) (n+1)|/
        |tSolution (orbitCoefficient k y (X (s,y))) (n+1)| ∧
      |tSolution (orbitCoefficient k yc s) (n+1)|/
        |tSolution (orbitCoefficient k y (X (s,y))) (n+1)| ≤ Real.exp (1152*Real.pi)) :
    ∃ J : (ℝ × ℝ) → (ℝ × ℝ) →L[ℝ] (ℝ × ℝ),
      (∀ z ∈ E ×ˢ I, HasFDerivWithinAt (fun w => (X w,w.2)) (J z) (E ×ˢ I) z) ∧
      (∀ z ∈ E ×ˢ I, Real.exp (-1152*Real.pi) ≤ |(J z).det| ∧
        |(J z).det| ≤ Real.exp (1152*Real.pi)) := by
  let J := fun z : ℝ × ℝ => planeMatrix
    (tSolution (orbitCoefficient k yc z.1) (n+1)/tSolution (orbitCoefficient k z.2 (X z)) (n+1))
    (-sSolution (orbitCoefficient k z.2 (X z)) (n+1)/tSolution (orbitCoefficient k z.2 (X z)) (n+1)) 0 1
  refine ⟨J,?_,?_⟩
  · intro z hz
    apply label_graph_derivative (fun v : ℝ × ℝ => liftedOrbit k v.2 v.1 (n+1)) X (E ×ˢ I) z yc _ _ _ _
      (hasStrictFDerivAt_liftedOrbit_swap k (X z) z.2 (n+1))
      (hasStrictFDerivAt_liftedOrbit_swap k z.1 yc (n+1)) (ht z.1 hz.1 z.2 hz.2) (hX z hz)
      _ (hlevel z.1 hz.1 z.2 hz.2)
    filter_upwards [self_mem_nhdsWithin] with w hw
    exact hlevel w.1 hw.1 w.2 hw.2
  · intro z hz
    simpa only [J,planeMatrix_det,mul_one,mul_zero,sub_zero,abs_div] using hr z.1 hz.1 z.2 hz.2
lemma forward_graph_lipschitz (I : Set ℝ) (X d : ℝ → ℝ) (a : ℝ)
    (hI : Convex ℝ I) (hd : ∀ y ∈ I, HasDerivAt X (d y) y)
    (hb : ∀ y ∈ I, |d y| ≤ a) (y z : ℝ) (hy : y ∈ I) (hz : z ∈ I) :
    |X y-X z| ≤ a*|y-z| := by
  have hh := hI.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun y hy => (hd y hy).hasDerivWithinAt) (by intro y hy; simpa [Real.norm_eq_abs] using hb y hy) hz hy
  simpa only [Real.norm_eq_abs] using hh
end StandardMapEntropy

end OAI
