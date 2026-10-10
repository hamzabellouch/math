import OAI.Geometry.Relativity.CKS.CKSPhysicalCoefficients
import OAI.Geometry.Relativity.CKS.CKSTensorFields

namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

lemma normalizedLie_smul_right (c : ℝ) {q : Point → Mat} {S : Point → Point} {x : Point}
    (hS : ContDiffAt ℝ 3 S x) (i k : I) :
    normalizedLie q (fun y => c • S y) x i k = c*normalizedLie q S x i k := by
  have hSa (a : I) := (contDiffAt_pi.mp hS a).differentiableAt (by norm_num)
  unfold normalizedLie
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  change (c*S x a)*D (basis a) (fun y => q y i k) x+
    q x a k*D (basis i) (fun y => c*S y a) x+
    q x i a*D (basis k) (fun y => c*S y a) x = _
  rw [D_const_mul _ c (hSa a),D_const_mul _ c (hSa a)]
  ring

theorem physical_expansion_coefficient {r : ℝ} (hr : r ≠ 0) {f : MassFields} {x : Point}
    (hf : f.RegularAt x)
    (h0 : determinant (cksQField (1/r) (normalizeMassFields r f) x) ≠ 0) :
    physicalExpansion r (cksGamma r f) (cksGammaRadial r f) (cksShift r f) x =
      1+(1/r)^3*cksDField (1/r) (normalizeMassFields r f) x := by
  have hn := normalizeMassFields_regular r hf
  have hq := cksQField_diff (1/r) hn
  have hH := cksHField_diff (1/r) hn h0
  have hs : cksShift r f = fun y => (1/r) • ((1/r)^4 • cksHField (1/r) (normalizeMassFields r f) y) := by
    rw [cksShift_normalized hr f]
    funext y i
    dsimp
    ring
  rw [cksGamma_normalized hr f,cksGammaRadial_normalized hr f,hs,
    physicalExpansion_normalized r hr hq (hH.const_smul ((1/r)^4)) h0]
  let z := 1/r
  let g := normalizeMassFields r f
  let A : Mat := (-3:ℝ) • g.mg x+z • (g.er x-(2:ℝ) • g.eg x-cksLieField z g x)
  let L : Mat := normalizedLie (cksQField z g) (fun y => z^4 • cksHField z g y) x
  have hLie : L = z^4 • cksLieField z g x := by
    funext i k
    exact normalizedLie_smul_right (z^4) hH i k
  have hQ : cksScaledQ r f x = z^3 • ((-3:ℝ) • g.mg x+z • (g.er x-(2:ℝ) • g.eg x)) := rfl
  have hdiff : cksScaledQ r f x - L = z^3 • A := by
    rw [hLie,hQ]
    dsimp only [A]
    module
  have hterm (i k : I) : cksScaledQ r f x k i -
      normalizedLie (cksQField z g) (fun y => z^4 • cksHField z g y) x k i = z^3*A k i := by
    exact congrArg (fun M : Mat => M k i) hdiff
  change 1+(1/4:ℝ)*(∑ i, ∑ k, inverse (cksQField z g x) i k*
      (cksScaledQ r f x k i-normalizedLie (cksQField z g) (fun y => z^4 • cksHField z g y) x k i)) =
    1+z^3*((1/4:ℝ)*traceProduct (inverse (cksQField z g x)) A)
  simp_rw [hterm]
  unfold traceProduct
  simp only [Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  ring

def cksPhysicalMass (r : ℝ) (f : MassFields) : Point → ℝ := fun x =>
  r/2*(1+(r/2*traceProduct (inverse (cksGamma r f x)) (cksTangentialK r f x))^2-
    ((1/Real.sqrt (cksSchur r f x))*
      physicalExpansion r (cksGamma r f) (cksGammaRadial r f) (cksShift r f) x)^2)

theorem physical_mass_eq_normalized {r : ℝ} (hr : r ≠ 0) {f : MassFields} {x : Point}
    (hf : f.RegularAt x)
    (h0 : determinant (cksQField (1/r) (normalizeMassFields r f) x) ≠ 0)
    (hpos : 0 < cksSchur r f x) :
    cksPhysicalMass r f x = cksFField (1/r) (normalizeMassFields r f) x := by
  have hsch := physical_schur_coefficient hr f x
  have hp : 0 < 1+(1/r)^3*cksVField (1/r) (normalizeMassFields r f) x := by
    rw [← hsch]
    positivity
  have hU : (1/Real.sqrt (cksSchur r f x))^2 =
      (1+r^2)/(1+(1/r)^3*cksVField (1/r) (normalizeMassFields r f) x) := by
    rw [div_pow,one_pow,Real.sq_sqrt hpos.le,← hsch]
    have hn : 1+r^2 ≠ 0 := ne_of_gt (by positivity)
    field_simp
  have hT := physical_trace_coefficient hr f x h0
  have hd := physical_expansion_coefficient hr hf h0
  have ht' : r/2*traceProduct (inverse (cksGamma r f x)) (cksTangentialK r f x) =
      r*(1+(1/r)^3*cksTField (1/r) (normalizeMassFields r f) x) := by
    rw [← hT]
    ring
  unfold cksPhysicalMass
  rw [ht',mul_pow (1/Real.sqrt (cksSchur r f x)),hU,hd]
  exact physical_mass_normalized hr hp.ne'

end
end CKSAngularGeometry

end

end OAI
