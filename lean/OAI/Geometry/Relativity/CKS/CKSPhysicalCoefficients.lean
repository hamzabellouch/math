import OAI.Geometry.Relativity.CKS.CKSMassInputBounds
import OAI.Geometry.Relativity.CKS.CollarExpansionGeometry

namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

lemma inverse_smul (c : ℝ) (q : Mat) (hc : c ≠ 0) (i k : I) :
    inverse (c • q) i k = inverse q i k/c := inverse_rescale c (q,0,0) hc i k

def cksGamma (r : ℝ) (f : MassFields) : Point → Mat :=
  fun y => r^2 • f.sigma y+(1/r) • f.mg y+f.eg y

def cksGammaRadial (r : ℝ) (f : MassFields) : Point → Mat :=
  fun y => (2*r) • f.sigma y-(1/r^2) • f.mg y+f.er y

def cksTangentialK (r : ℝ) (f : MassFields) : Point → Mat :=
  fun y => r^2 • f.sigma y+(1/r) • f.mK y+f.ek y

def cksShift (r : ℝ) (f : MassFields) : Point → Point :=
  fun y a => ∑ b, inverse (cksGamma r f y) a b*f.b y b

def cksRadialMetric (r : ℝ) (f : MassFields) : Point → ℝ :=
  fun y => 1/(1+r^2)+f.mr y/r^5+f.err y

def cksSchur (r : ℝ) (f : MassFields) : Point → ℝ :=
  fun y => cksRadialMetric r f y - ∑ i, ∑ k, inverse (cksGamma r f y) i k*(f.b y i*f.b y k)

def cksScaledQ (r : ℝ) (f : MassFields) : Point → Mat :=
  fun y => (1/r)^3 • ((-3:ℝ) • f.mg y+(1/r) • ((r^3) • f.er y-(2:ℝ) • (r^2 • f.eg y)))

lemma cksGamma_normalized {r : ℝ} (hr : r ≠ 0) (f : MassFields) :
    cksGamma r f = fun y => r^2 • cksQField (1/r) (normalizeMassFields r f) y := by
  funext y i k
  dsimp [cksGamma,cksQField,normalizeMassFields]
  field_simp

lemma cksGammaRadial_normalized {r : ℝ} (hr : r ≠ 0) (f : MassFields) :
    cksGammaRadial r f = fun y =>
      (2*r) • cksQField (1/r) (normalizeMassFields r f) y+r • cksScaledQ r f y := by
  funext y i k
  dsimp [cksGammaRadial,cksQField,normalizeMassFields,cksScaledQ]
  field_simp
  ring

lemma cksShift_normalized {r : ℝ} (hr : r ≠ 0) (f : MassFields) :
    cksShift r f = fun y => (1/r)^5 • cksHField (1/r) (normalizeMassFields r f) y := by
  funext y a
  unfold cksShift cksHField
  rw [cksGamma_normalized hr f]
  change (∑ b, inverse (r^2 • cksQField (1/r) (normalizeMassFields r f) y) a b*f.b y b) = _
  simp only [inverse_smul (r^2) _ (pow_ne_zero _ hr)]
  change (∑ b, (inverse (cksQField (1/r) (normalizeMassFields r f) y) a b/r^2)*f.b y b) =
    (1/r)^5*(∑ b, inverse (cksQField (1/r) (normalizeMassFields r f) y) a b*(r^3*f.b y b))
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  field_simp

lemma traceProduct_add (q p t : Mat) : traceProduct q (p+t) = traceProduct q p+traceProduct q t := by
  simp [traceProduct,mul_add,Finset.sum_add_distrib]
lemma traceProduct_smul (c : ℝ) (q p : Mat) : traceProduct q (c • p) = c*traceProduct q p := by
  simp [traceProduct]
  ring

lemma cksTangentialK_normalized {r : ℝ} (hr : r ≠ 0) (f : MassFields) :
    cksTangentialK r f = fun y => r^2 • (cksQField (1/r) (normalizeMassFields r f) y+
      (1/r)^3 • (f.mK y-f.mg y+(1/r) • ((r^2) • f.ek y-(r^2) • f.eg y))) := by
  funext y i k
  dsimp [cksTangentialK,cksQField,normalizeMassFields]
  field_simp
  ring

theorem physical_trace_coefficient {r : ℝ} (hr : r ≠ 0) (f : MassFields) (x : Point)
    (h0 : determinant (cksQField (1/r) (normalizeMassFields r f) x) ≠ 0) :
    (1/2:ℝ)*traceProduct (inverse (cksGamma r f x)) (cksTangentialK r f x) =
      1+(1/r)^3*cksTField (1/r) (normalizeMassFields r f) x := by
  rw [cksGamma_normalized hr f,cksTangentialK_normalized hr f]
  have ht : traceProduct (inverse (r^2 • cksQField (1/r) (normalizeMassFields r f) x))
      (r^2 • (cksQField (1/r) (normalizeMassFields r f) x+
      (1/r)^3 • (f.mK x-f.mg x+(1/r) • ((r^2) • f.ek x-(r^2) • f.eg x)))) =
      traceProduct (inverse (cksQField (1/r) (normalizeMassFields r f) x))
      (cksQField (1/r) (normalizeMassFields r f) x+
      (1/r)^3 • (f.mK x-f.mg x+(1/r) • ((r^2) • f.ek x-(r^2) • f.eg x))) := by
    unfold traceProduct
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro k _
    rw [inverse_smul (r^2) _ (pow_ne_zero _ hr)]
    dsimp
    field_simp
  rw [ht,traceProduct_add,traceProduct_smul]
  have hi := inverse_trace _ h0
  change traceProduct (inverse (cksQField (1/r) (normalizeMassFields r f) x))
    (cksQField (1/r) (normalizeMassFields r f) x) = 2 at hi
  rw [hi]
  unfold cksTField
  dsimp only [normalizeMassFields]
  ring

theorem physical_schur_coefficient {r : ℝ} (hr : r ≠ 0) (f : MassFields) (x : Point) :
    (1+r^2)*cksSchur r f x = 1+(1/r)^3*cksVField (1/r) (normalizeMassFields r f) x := by
  have hbb : (∑ i, ∑ k, inverse (cksGamma r f x) i k*(f.b x i*f.b x k)) =
      (1/r)^8*cksBBField (1/r) (normalizeMassFields r f) x := by
    rw [cksGamma_normalized hr f]
    unfold cksBBField
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro k _
    rw [inverse_smul (r^2) _ (pow_ne_zero _ hr)]
    dsimp [normalizeMassFields]
    field_simp
  unfold cksSchur
  rw [hbb]
  unfold cksRadialMetric cksVField
  dsimp only [normalizeMassFields]
  have hn : 1+r^2 ≠ 0 := ne_of_gt (by positivity)
  field_simp
  ring

end
end CKSAngularGeometry

end

end OAI
