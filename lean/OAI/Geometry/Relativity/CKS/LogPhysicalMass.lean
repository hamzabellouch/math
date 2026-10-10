import OAI.Geometry.Relativity.CKS.LogPhysicalCoefficients

namespace OAI

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open CKSCalculus Set Filter
open CKSAngularGeometry (determinant inverse inverse_smul inverse_trace)
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

lemma traceProduct_sub (q p t : Mat) : traceProduct q (p-t) = traceProduct q p-traceProduct q t := by
  simp [traceProduct,mul_sub,Finset.sum_sub_distrib]

lemma traceProduct_inverse_smul {r : ℝ} (hr : r ≠ 0) (q p : Mat) :
    traceProduct (inverse (r • q)) p = (1/r)*traceProduct (inverse q) p := by
  have hi : inverse (r • q) = (1/r) • inverse q := by
    funext i k
    rw [inverse_smul _ _ hr]
    dsimp; ring
  exact hi ▸ traceProduct_smul_left (1/r) (inverse q) p

def logExpansion (f : MassFields) : Point → ℝ := fun x =>
  Real.exp (x 0)/4*traceProduct (inverse (logGamma f x))
    (logGammaRadial f x-(show Mat from normalizedLie (logGamma f) (logShift f) x))

lemma log_lie_coefficient {f : MassFields} {x : Point} (hf : f.RegularAt x)
    (h0 : determinant (cksQField (radiusPower (-1)) (normalizeMassLogFields f) x) ≠ 0) :
    normalizedLie (logGamma f) (logShift f) x =
      (1/Real.exp (x 0))^3 • cksLieField (radiusPower (-1)) (normalizeMassLogFields f) x := by
  rw [logGamma_normalized,logShift_normalized]
  have hn := normalizeMassLogFields_regular hf
  have hz := radiusPower_diff (-1) 3 x
  have hq := cksQField_diff hz hn
  have hH := cksHField_diff hz hn h0
  funext i k
  rw [normalizedLie_radius 2 (-5) hq hH i k,radiusPower_two,radiusPower_minus_five]
  change (Real.exp (x 0)^2*(1/Real.exp (x 0)^5))*
    normalizedLie (cksQField (radiusPower (-1)) (normalizeMassLogFields f))
        (cksHField (radiusPower (-1)) (normalizeMassLogFields f)) x i k =
    (1/Real.exp (x 0))^3*normalizedLie (cksQField (radiusPower (-1)) (normalizeMassLogFields f))
        (cksHField (radiusPower (-1)) (normalizeMassLogFields f)) x i k
  have hr := Real.exp_ne_zero (x 0)
  field_simp

lemma log_expansion_coefficient {f : MassFields} {x : Point} (hf : f.RegularAt x)
    (h0 : determinant (cksQField (radiusPower (-1)) (normalizeMassLogFields f) x) ≠ 0) :
    logExpansion f x =
      1+(1/Real.exp (x 0))^3*cksDField (radiusPower (-1)) (normalizeMassLogFields f) x := by
  let r := Real.exp (x 0)
  let z := 1/r
  let g := normalizeMassLogFields f
  let q := cksQField (radiusPower (-1)) g x
  let a : Mat := (-3:ℝ) • g.mg x+z • (g.er x-(2:ℝ) • g.eg x-cksLieField (radiusPower (-1)) g x)
  have hr : r ≠ 0 := Real.exp_ne_zero _
  have hm : logGammaRadial f x-(show Mat from normalizedLie (logGamma f) (logShift f) x) =
      (2*r) • q+(r*z^3) • a := by
    funext i k
    change logGammaRadial f x i k-normalizedLie (logGamma f) (logShift f) x i k =
      (2*r)*q i k+(r*z^3)*a i k
    have hrad := congrArg (fun F : Point → Mat => F x i k) (logGammaRadial_normalized f)
    change logGammaRadial f x i k = (2*r)*q i k+r*logScaledQ f x i k at hrad
    have hlie := congrArg (fun M : Mat => M i k) (log_lie_coefficient hf h0)
    change normalizedLie (logGamma f) (logShift f) x i k =
      z^3*cksLieField (radiusPower (-1)) g x i k at hlie
    rw [hrad,hlie]
    change (2*r)*q i k+r*(z^3*((-3)*f.mg x i k+z*(Real.exp (x 0)^2*radialMatrixD f.eg x i k-
      2*(Real.exp (x 0)^2*f.eg x i k))))-z^3*cksLieField (radiusPower (-1)) g x i k =
      (2*r)*q i k+(r*z^3)*((-3)*f.mg x i k+z*(radiusPower 2 x*radialMatrixD f.eg x i k-
        2*(radiusPower 2 x*f.eg x i k)-cksLieField (radiusPower (-1)) g x i k))
    rw [radiusPower_two]
    dsimp only [z,r]
    field_simp
    ring
  have hi : traceProduct (inverse q) q = 2 := inverse_trace q h0
  unfold logExpansion
  rw [hm,logGamma_normalized]
  simp only [radiusPower_two]
  change r/4*traceProduct (inverse (r^2 • q)) ((2*r) • q+(r*z^3) • a) = _
  rw [traceProduct_inverse_smul (pow_ne_zero 2 hr),traceProduct_add,
    traceProduct_smul,traceProduct_smul,hi]
  change _ = 1+z^3*((1/4:ℝ)*traceProduct (inverse q)
    ((-3:ℝ) • g.mg x+radiusPower (-1) x • (g.er x-(2:ℝ) • g.eg x-cksLieField (radiusPower (-1)) g x)))
  rw [radiusPower_inverse]
  change _ = 1+z^3*((1/4:ℝ)*traceProduct (inverse q) a)
  dsimp only [z]
  field_simp
  ring

def logPhysicalMass (f : MassFields) : Point → ℝ := fun x =>
  Real.exp (x 0)/2*(1+(Real.exp (x 0)/2*traceProduct (inverse (logGamma f x)) (logTangentialK f x))^2-
    ((1/Real.sqrt (logSchur f x))*logExpansion f x)^2)

lemma log_physical_mass_eq {f : MassFields} {x : Point} (hf : f.RegularAt x)
    (h0 : determinant (cksQField (radiusPower (-1)) (normalizeMassLogFields f) x) ≠ 0)
    (hpos : 0 < logSchur f x) :
    logPhysicalMass f x = cksFField (radiusPower (-1)) (normalizeMassLogFields f) x := by
  have hr := Real.exp_ne_zero (x 0)
  have hsch := log_schur_coefficient f x
  have hp : 0 < 1+(1/Real.exp (x 0))^3*cksVField (radiusPower (-1)) (normalizeMassLogFields f) x := by
    rw [← hsch]
    positivity
  have hU : (1/Real.sqrt (logSchur f x))^2 =
      (1+Real.exp (x 0)^2)/(1+(1/Real.exp (x 0))^3*cksVField (radiusPower (-1)) (normalizeMassLogFields f) x) := by
    rw [div_pow,one_pow,Real.sq_sqrt hpos.le,← hsch]
    have hn : 1+Real.exp (x 0)^2 ≠ 0 := ne_of_gt (by positivity)
    field_simp
  have hT := log_trace_coefficient h0
  have hd := log_expansion_coefficient hf h0
  have ht' : Real.exp (x 0)/2*traceProduct (inverse (logGamma f x)) (logTangentialK f x) =
      Real.exp (x 0)*(1+(1/Real.exp (x 0))^3*cksTField (radiusPower (-1)) (normalizeMassLogFields f) x) := by
    rw [← hT]
    ring
  unfold logPhysicalMass
  rw [ht',mul_pow (1/Real.sqrt (logSchur f x)),hU,hd]
  unfold cksFField normalizedMassField massNumeratorField
  rw [radiusPower_inverse]
  simpa only [mul_assoc] using CKSAngularGeometry.physical_mass_normalized
    (D := cksDField (radiusPower (-1)) (normalizeMassLogFields f) x)
    (T := cksTField (radiusPower (-1)) (normalizeMassLogFields f) x) hr hp.ne'

end
end CKSMixedGeometry

end

end OAI
