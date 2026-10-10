import OAI.Probability.InvariantIsing.Fields.FieldFiniteNeighborhood

namespace OAI

/-! Coordinate and line derivatives extracted from the actual joint
finite-height derivative data. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set Filter
open scoped BigOperators Topology

namespace InvariantIsing
namespace FieldFiniteFamily

variable {n : ℕ} {I : Set (Fin n → ℝ)} (F : FieldFiniteFamily n I)

lemma coordinate_derivative (r : Fin n → ℝ) (z : ℝ) (hr : r ∈ I) (i : Fin n) :
    HasDerivAt (fun t : ℝ => F.U (Function.update r i (r i + t), z))
      (F.P i (r, z)) 0 := by
  classical
  have hv : HasDerivAt (fun t : ℝ => Function.update r i (r i + t)) (Pi.single i 1) 0 := by
    apply hasDerivAt_pi.mpr
    intro j
    by_cases hji : j = i
    · subst j
      simpa using (hasDerivAt_id (0 : ℝ)).const_add (r i)
    · simpa [Function.update_of_ne hji, Pi.single_eq_of_ne hji] using
        hasDerivAt_const (0 : ℝ) (r j)
  have hp := hv.prodMk (hasDerivAt_const (0 : ℝ) z)
  have hF : HasFDerivAt F.U (fieldFiniteLinear (fun k => F.P k (r, z)) (F.X (r, z)))
      (Function.update r i (r i + 0), z) := by simpa using F.derivative (r, z) hr
  have hd := hF.comp_hasDerivAt 0 hp
  simpa [fieldFiniteLinear_apply, Function.comp_def, Pi.single_apply] using hd

lemma coordinate_gradient_derivative (r : Fin n → ℝ) (z : ℝ) (hr : r ∈ I) (i j : Fin n) :
    HasDerivAt (fun t : ℝ => F.P i (Function.update r j (r j + t), z))
      (F.PP i j (r, z)) 0 := by
  classical
  have hv : HasDerivAt (fun t : ℝ => Function.update r j (r j + t)) (Pi.single j 1) 0 := by
    apply hasDerivAt_pi.mpr
    intro k
    by_cases hkj : k = j
    · subst k
      simpa using (hasDerivAt_id (0 : ℝ)).const_add (r j)
    · simpa [Function.update_of_ne hkj, Pi.single_eq_of_ne hkj] using
        hasDerivAt_const (0 : ℝ) (r k)
  have hp := hv.prodMk (hasDerivAt_const (0 : ℝ) z)
  have hF : HasFDerivAt (F.P i) (fieldFiniteLinear (fun k => F.PP i k (r, z)) (F.PX i (r, z)))
      (Function.update r j (r j + 0), z) := by simpa using F.derivativeP i (r, z) hr
  have hd := hF.comp_hasDerivAt 0 hp
  simpa [fieldFiniteLinear_apply, Function.comp_def, Pi.single_apply] using hd

lemma line_derivative (r c : Fin n → ℝ) (z t : ℝ) (hr : r + t • c ∈ I) :
    HasDerivAt (fun s : ℝ => F.U (r + s • c, z))
      (∑ i, F.P i (r + t • c, z) * c i) t := by
  have hv := (hasDerivAt_const t r).add ((hasDerivAt_id t).smul_const c)
  have hp := hv.prodMk (hasDerivAt_const t z)
  have hd := (F.derivative (r + t • c, z) hr).comp_hasDerivAt t hp
  simpa [fieldFiniteLinear_apply, Function.comp_def] using hd

lemma line_gradient_derivative (r c : Fin n → ℝ) (z t : ℝ) (hr : r + t • c ∈ I) :
    HasDerivAt (fun s : ℝ => ∑ i, F.P i (r + s • c, z) * c i)
      (∑ i, ∑ j, F.PP i j (r + t • c, z) * c i * c j) t := by
  have hv := (hasDerivAt_const t r).add ((hasDerivAt_id t).smul_const c)
  have hp := hv.prodMk (hasDerivAt_const t z)
  have hd (i : Fin n) : HasDerivAt (fun s => F.P i (r + s • c, z) * c i)
      ((∑ j, F.PP i j (r + t • c, z) * c j) * c i) t := by
    simpa [fieldFiniteLinear_apply, Function.comp_def] using
      ((F.derivativeP i (r + t • c, z) hr).comp_hasDerivAt t hp).mul_const (c i)
  convert HasDerivAt.sum (fun i (_ : i ∈ Finset.univ) => hd i) using 1
  · funext s
    simp only [Finset.sum_apply]
  · simp only [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring

end FieldFiniteFamily
end InvariantIsing

end

end OAI
