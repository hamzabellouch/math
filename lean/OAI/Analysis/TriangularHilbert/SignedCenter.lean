import OAI.Analysis.TriangularHilbert.MaskedActual

namespace OAI

universe uι

section
namespace TriangularHilbert.Heat
open MatrixEnergy MeasureTheory
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder BigOperators
noncomputable section
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

def signedCenter (A : Three → Matrix ι ι ℂ) (h : ℝ) (u : ι → ℝ) (s : ℝ) : ℂ :=
  ∑ i, ∑ j, ∑ k, (h^3:ℝ)*(A 0 i j*A 1 j k*A 2 k i)*(signedKernel s (u i+u j+u k):ℂ)

lemma signedCenter_eq_integral (A : Three → Matrix ι ι ℂ) {h s : ℝ} (hh : 0 < h) (hs : 0 < s)
    (u : ι → ℝ) : signedCenter A h u s = ∫ z : ℝ×ℝ, windowTrace A h u (chart 2 0 z) s := by
  have hi (i j k : ι) : Integrable (fun z : ℝ×ℝ => (h^3:ℝ)*(A 0 i j*A 1 j k*A 2 k i)*
      ((oddWindow s (u i-z.1)*oddWindow s (u j-z.2)*oddWindow s (u k+z.1+z.2):ℝ):ℂ)) :=
    (oddWindow_triple_integrable hs (u i) (u j) (u k)).ofReal.const_mul _
  have he (z : ℝ×ℝ) : windowTrace A h u (chart 2 0 z) s =
      ∑ i, ∑ j, ∑ k, (h^3:ℝ)*(A 0 i j*A 1 j k*A 2 k i)*
        ((oddWindow s (u i-z.1)*oddWindow s (u j-z.2)*oddWindow s (u k+z.1+z.2):ℝ):ℂ) := by
    rw [windowTrace_eq A hh hs]
    congr 1
    ext i
    congr 1
    ext j
    congr 1
    ext k
    rw [show chart 2 0 z 0 = z.1 by rfl,show chart 2 0 z 1 = z.2 by rfl,
      show chart 2 0 z 2 = 0-z.1-z.2 by rfl,show u k-(0-z.1-z.2) = u k+z.1+z.2 by ring]
  simp_rw [he]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => integrable_finsetSum _ (fun k _ => hi i j k)))]
  unfold signedCenter
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum _ (fun j _ => integrable_finsetSum _ (fun k _ => hi i j k))]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_finsetSum _ (fun k _ => hi i j k)]
  apply Finset.sum_congr rfl
  intro k _
  rw [integral_const_mul,integral_complex_ofReal,integral_oddWindow_triple hs]

lemma signedCenter_norm_le (A : Three → Matrix ι ι ℂ) {h s : ℝ} (hh : 0 < h) (hs : 0 < s)
    (u : ι → ℝ) : ‖signedCenter A h u s‖ ≤ (440/3)*s*∑ v,
      planeIntegral (fun p => heatCost A h u p (fun z => strictRate v z*s) v v) 0 := by
  have hi (v : Three) := (heatPlane_integrable A hh u 0 (fun z => mul_pos (strictRate_pos v z) hs)).cost 2 v v
  rw [signedCenter_eq_integral A hh hs]
  have hb := norm_integral_le_of_norm_le
    ((integrable_finsetSum _ (fun v _ => hi v)).const_mul ((440/3)*s))
    (Filter.Eventually.of_forall (fun z => windowTrace_le A hh hs u (chart 2 0 z)))
  apply hb.trans_eq
  rw [integral_const_mul,integral_finsetSum _ (fun v _ => hi v)]
  rfl

lemma continuousOn_signedKernel (t : ℝ) : ContinuousOn (fun s => signedKernel s t) (Set.Ioi 0) := by
  intro s hs
  apply ContinuousAt.continuousWithinAt
  have hs' : 0 < s := hs
  unfold signedKernel density
  fun_prop (disch := positivity)

lemma signedKernel_intervalIntegrable {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (t : ℝ) :
    IntervalIntegrable (fun s => signedKernel s t / s) volume a b := by
  apply ContinuousOn.intervalIntegrable
  rw [Set.uIcc_of_le hab]
  exact ((continuousOn_signedKernel t).div continuousOn_id (fun s hs => ne_of_gt hs)).mono
    (fun s hs => ha.trans_le hs.1)
end
end TriangularHilbert.Heat
end

end OAI
