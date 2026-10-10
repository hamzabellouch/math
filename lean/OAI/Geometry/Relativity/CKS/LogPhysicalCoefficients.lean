import OAI.Geometry.Relativity.CKS.CKSPhysicalCoefficients
import OAI.Geometry.Relativity.CKS.MixedInputBounds

namespace OAI

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open CKSCalculus Set Filter
open CKSAngularGeometry (determinant inverse inverse_smul inverse_trace)
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

lemma radiusPower_neg_nat (n : ℕ) (x : Point) : radiusPower (-(n:ℝ)) x = 1/Real.exp (x 0)^n := by
  rw [radiusPower,neg_mul,Real.exp_neg,Real.exp_nat_mul,one_div]
lemma radiusPower_inverse (x : Point) : radiusPower (-1) x = 1/Real.exp (x 0) := by
  simpa using radiusPower_neg_nat 1 x

lemma radiusPower_two (x : Point) : radiusPower 2 x = Real.exp (x 0)^2 := radiusPower_nat 2 x
lemma radiusPower_three (x : Point) : radiusPower 3 x = Real.exp (x 0)^3 := radiusPower_nat 3 x
lemma radiusPower_six (x : Point) : radiusPower 6 x = Real.exp (x 0)^6 := radiusPower_nat 6 x
lemma radiusPower_minus_five (x : Point) : radiusPower (-5) x = 1/Real.exp (x 0)^5 := radiusPower_neg_nat 5 x

lemma D_radiusPower_angular (n : ℝ) (a : A) : D (basis a.succ) (radiusPower n) = 0 := by
  rw [D_radiusPower]
  funext x
  simp [basis]

lemma normalizedLie_radius (n m : ℝ) {q : Point → Mat} {S : Point → A → ℝ} {x : Point}
    (hq : ContDiffAt ℝ 3 q x) (hS : ContDiffAt ℝ 3 S x) (i k : A) :
    normalizedLie (fun y => radiusPower n y • q y) (fun y => radiusPower m y • S y) x i k =
      (radiusPower n x*radiusPower m x)*normalizedLie q S x i k := by
  have hqd (a b : A) := (component_diff hq a b).differentiableAt (by norm_num)
  have hSd (a : A) := (contDiffAt_pi.mp hS a).differentiableAt (by norm_num)
  have hn := (radiusPower_diff n 1 x).differentiableAt (by norm_num)
  have hm := (radiusPower_diff m 1 x).differentiableAt (by norm_num)
  unfold normalizedLie
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  change (radiusPower m x*S x a)*D (basis a.succ) (fun y => radiusPower n y*q y i k) x+
    (radiusPower n x*q x a k)*D (basis i.succ) (fun y => radiusPower m y*S y a) x+
    (radiusPower n x*q x i a)*D (basis k.succ) (fun y => radiusPower m y*S y a) x = _
  rw [D_mul _ hn (hqd i k),D_mul _ hm (hSd a),D_mul _ hm (hSd a),
    D_radiusPower_angular,D_radiusPower_angular,D_radiusPower_angular]
  dsimp
  ring

def logGamma (f : MassFields) : Point → Mat := fun y =>
  Real.exp (y 0)^2 • f.sigma y+(1/Real.exp (y 0)) • f.mg y+f.eg y

def logGammaRadial (f : MassFields) : Point → Mat := fun y =>
  (2*Real.exp (y 0)) • f.sigma y-(1/Real.exp (y 0)^2) • f.mg y+
    (1/Real.exp (y 0)) • radialMatrixD f.eg y

def logTangentialK (f : MassFields) : Point → Mat := fun y =>
  Real.exp (y 0)^2 • f.sigma y+(1/Real.exp (y 0)) • f.mK y+f.ek y

def logShift (f : MassFields) : Point → A → ℝ := fun y a =>
  ∑ b, inverse (logGamma f y) a b*f.b y b

def logRadialMetric (f : MassFields) : Point → ℝ := fun y =>
  1/(1+Real.exp (y 0)^2)+f.mr y/Real.exp (y 0)^5+f.err y

def logSchur (f : MassFields) : Point → ℝ := fun y =>
  logRadialMetric f y-∑ i, ∑ k, inverse (logGamma f y) i k*(f.b y i*f.b y k)

def logScaledQ (f : MassFields) : Point → Mat := fun y =>
  (1/Real.exp (y 0))^3 • ((-3:ℝ) • f.mg y+(1/Real.exp (y 0)) •
    (Real.exp (y 0)^2 • radialMatrixD f.eg y-(2:ℝ) • (Real.exp (y 0)^2 • f.eg y)))

lemma logGamma_normalized (f : MassFields) : logGamma f = fun y =>
    radiusPower 2 y • cksQField (radiusPower (-1)) (normalizeMassLogFields f) y := by
  funext y i k
  unfold logGamma cksQField normalizeMassLogFields
  simp only [radiusPower_inverse,radiusPower_two]
  dsimp
  have hr := Real.exp_ne_zero (y 0)
  field_simp

lemma logGammaRadial_normalized (f : MassFields) : logGammaRadial f = fun y =>
    (2*Real.exp (y 0)) • cksQField (radiusPower (-1)) (normalizeMassLogFields f) y+
    Real.exp (y 0) • logScaledQ f y := by
  funext y i k
  unfold logGammaRadial cksQField normalizeMassLogFields logScaledQ
  simp only [radiusPower_inverse,radiusPower_two]
  dsimp
  have hr := Real.exp_ne_zero (y 0)
  field_simp
  ring

lemma logShift_normalized (f : MassFields) : logShift f = fun y =>
    radiusPower (-5) y • cksHField (radiusPower (-1)) (normalizeMassLogFields f) y := by
  funext y a
  unfold logShift cksHField
  rw [logGamma_normalized]
  have hr := Real.exp_ne_zero (y 0)
  simp only [radiusPower_two,inverse_smul _ _ (pow_ne_zero 2 hr)]
  change (∑ b, inverse (cksQField (radiusPower (-1)) (normalizeMassLogFields f) y) a b/Real.exp (y 0)^2*f.b y b) =
    radiusPower (-5) y*(∑ b, inverse (cksQField (radiusPower (-1)) (normalizeMassLogFields f) y) a b*(radiusPower 3 y*f.b y b))
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  rw [radiusPower_minus_five,radiusPower_three]
  field_simp

lemma logTangentialK_normalized (f : MassFields) : logTangentialK f = fun y =>
    Real.exp (y 0)^2 • (cksQField (radiusPower (-1)) (normalizeMassLogFields f) y+
      (1/Real.exp (y 0))^3 • (f.mK y-f.mg y+(1/Real.exp (y 0)) •
        (Real.exp (y 0)^2 • f.ek y-Real.exp (y 0)^2 • f.eg y))) := by
  funext y i k
  unfold logTangentialK cksQField normalizeMassLogFields
  simp only [radiusPower_inverse,radiusPower_two]
  dsimp
  have hr := Real.exp_ne_zero (y 0)
  field_simp
  ring

lemma traceProduct_add (q p t : Mat) : traceProduct q (p+t) = traceProduct q p+traceProduct q t :=
  CKSAngularGeometry.traceProduct_add q p t
lemma traceProduct_smul (c : ℝ) (q p : Mat) : traceProduct q (c • p) = c*traceProduct q p :=
  CKSAngularGeometry.traceProduct_smul c q p
lemma traceProduct_smul_left (c : ℝ) (q p : Mat) : traceProduct (c • q) p = c*traceProduct q p := by
  unfold traceProduct
  simp only [Matrix.smul_apply,smul_eq_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  ring

lemma log_trace_coefficient {f : MassFields} {x : Point}
    (h0 : determinant (cksQField (radiusPower (-1)) (normalizeMassLogFields f) x) ≠ 0) :
    (1/2:ℝ)*traceProduct (inverse (logGamma f x)) (logTangentialK f x) =
      1+(1/Real.exp (x 0))^3*cksTField (radiusPower (-1)) (normalizeMassLogFields f) x := by
  have hr := Real.exp_ne_zero (x 0)
  rw [logGamma_normalized,logTangentialK_normalized]
  simp only [radiusPower_two]
  have hi : inverse (Real.exp (x 0)^2 • cksQField (radiusPower (-1)) (normalizeMassLogFields f) x) =
      (1/Real.exp (x 0)^2) • inverse (cksQField (radiusPower (-1)) (normalizeMassLogFields f) x) := by
    funext i k
    rw [inverse_smul _ _ (pow_ne_zero 2 hr)]
    dsimp; ring
  rw [hi,traceProduct_smul_left,traceProduct_smul,traceProduct_add,traceProduct_smul]
  have hinv := inverse_trace _ h0
  change traceProduct (inverse (cksQField (radiusPower (-1)) (normalizeMassLogFields f) x))
    (cksQField (radiusPower (-1)) (normalizeMassLogFields f) x) = 2 at hinv
  rw [hinv]
  unfold cksTField normalizeMassLogFields
  simp only [radiusPower_inverse,radiusPower_two]
  field_simp

lemma log_schur_coefficient (f : MassFields) (x : Point) :
    (1+Real.exp (x 0)^2)*logSchur f x =
      1+(1/Real.exp (x 0))^3*cksVField (radiusPower (-1)) (normalizeMassLogFields f) x := by
  have hr := Real.exp_ne_zero (x 0)
  have hbb : (∑ i, ∑ k, inverse (logGamma f x) i k*(f.b x i*f.b x k)) =
      (1/Real.exp (x 0))^8*cksBBField (radiusPower (-1)) (normalizeMassLogFields f) x := by
    rw [logGamma_normalized]
    simp only [radiusPower_two]
    unfold cksBBField
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro k _
    rw [inverse_smul _ _ (pow_ne_zero 2 hr)]
    dsimp only [normalizeMassLogFields]
    rw [radiusPower_three]
    dsimp
    field_simp
  unfold logSchur
  rw [hbb]
  unfold logRadialMetric cksVField
  dsimp only [normalizeMassLogFields]
  rw [radiusPower_inverse,radiusPower_six]
  have hn : 1+Real.exp (x 0)^2 ≠ 0 := ne_of_gt (by positivity)
  field_simp
  ring

end
end CKSMixedGeometry

end

end OAI
