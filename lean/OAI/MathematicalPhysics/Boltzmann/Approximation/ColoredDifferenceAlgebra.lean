import OAI.MathematicalPhysics.Boltzmann.Model

namespace OAI

section

/-!
# The symmetric gain and colored collision algebra

The symmetric bilinear gain is defined from the paper's exact angular kernel.
Integral additivity carries integrability hypotheses. The resulting algebra
combines the cold and hot collision equations.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace BoltzmannNonuniqueness

def gainPairMeasure : Measure (Velocity × Sphere) :=
  (volume : Measure Velocity).prod sphereArea

def gainPairIntegrand (f g : Density) (x : Position) (v : Velocity)
    (p : Velocity × Sphere) : ℝ :=
  (collisionKernel v p.1 p.2 / 2) *
    (f (x, scatterLeft v p.1 p.2) * g (x, scatterRight v p.1 p.2) +
      g (x, scatterLeft v p.1 p.2) * f (x, scatterRight v p.1 p.2))

/-- The associated symmetric bilinear gain. -/
def symmetricGain (f g : Density) (x : Position) (v : Velocity) : ℝ :=
  ∫ p, gainPairIntegrand f g x v p ∂gainPairMeasure

theorem gainPairIntegrand_symm (f g : Density) (x : Position) (v : Velocity)
    (p : Velocity × Sphere) :
    gainPairIntegrand f g x v p = gainPairIntegrand g f x v p := by
  unfold gainPairIntegrand
  ring

theorem gainPairIntegrand_fun_symm (f g : Density) (x : Position) (v : Velocity) :
    gainPairIntegrand f g x v = gainPairIntegrand g f x v :=
  funext (gainPairIntegrand_symm f g x v)

theorem symmetricGain_symm (f g : Density) (x : Position) (v : Velocity) :
    symmetricGain f g x v = symmetricGain g f x v := by
  apply integral_congr_ae
  filter_upwards [] with p
  exact gainPairIntegrand_symm f g x v p

theorem symmetricGain_self (f : Density) (x : Position) (v : Velocity) :
    symmetricGain f f x v = gain f x v := by
  apply integral_congr_ae
  filter_upwards [] with p
  unfold gainPairIntegrand
  ring

theorem gainPairIntegrand_add_left (f g h : Density) (x : Position) (v : Velocity)
    (p : Velocity × Sphere) :
    gainPairIntegrand (f + g) h x v p =
      gainPairIntegrand f h x v p + gainPairIntegrand g h x v p := by
  simp only [gainPairIntegrand, Pi.add_apply]
  ring

theorem gainPairIntegrand_fun_add_left (f g h : Density) (x : Position) (v : Velocity) :
    gainPairIntegrand (f + g) h x v =
      gainPairIntegrand f h x v + gainPairIntegrand g h x v :=
  funext (gainPairIntegrand_add_left f g h x v)

theorem symmetricGain_add_left (f g h : Density) (x : Position) (v : Velocity)
    (hf : Integrable (gainPairIntegrand f h x v) gainPairMeasure)
    (hg : Integrable (gainPairIntegrand g h x v) gainPairMeasure) :
    symmetricGain (f + g) h x v = symmetricGain f h x v + symmetricGain g h x v := by
  unfold symmetricGain
  simp_rw [gainPairIntegrand_add_left]
  exact integral_add hf hg

theorem symmetricGain_add_right (f g h : Density) (x : Position) (v : Velocity)
    (hg : Integrable (gainPairIntegrand f g x v) gainPairMeasure)
    (hh : Integrable (gainPairIntegrand f h x v) gainPairMeasure) :
    symmetricGain f (g + h) x v = symmetricGain f g x v + symmetricGain f h x v := by
  have hg' : Integrable (gainPairIntegrand g f x v) gainPairMeasure := by
    rwa [gainPairIntegrand_fun_symm g f]
  have hh' : Integrable (gainPairIntegrand h f x v) gainPairMeasure := by
    rwa [gainPairIntegrand_fun_symm h f]
  rw [symmetricGain_symm, symmetricGain_add_left g h f x v hg' hh',
    symmetricGain_symm g f, symmetricGain_symm h f]

/-- Expansion into cold-cold, cold-hot, and hot-hot gains, before refining cold labels. -/
theorem cold_hot_gain_expansion (c h : Density) (x : Position) (v : Velocity)
    (hcc : Integrable (gainPairIntegrand c c x v) gainPairMeasure)
    (hch : Integrable (gainPairIntegrand c h x v) gainPairMeasure)
    (hhh : Integrable (gainPairIntegrand h h x v) gainPairMeasure) :
    gain (c + h) x v = gain c x v + 2 * symmetricGain c h x v + gain h x v := by
  have hhc : Integrable (gainPairIntegrand h c x v) gainPairMeasure := by
    rwa [gainPairIntegrand_fun_symm h c]
  have hc_sum : Integrable (gainPairIntegrand c (c + h) x v) gainPairMeasure := by
    rw [gainPairIntegrand_fun_symm c (c + h), gainPairIntegrand_fun_add_left,
      gainPairIntegrand_fun_symm h c]
    exact hcc.add hch
  have hh_sum : Integrable (gainPairIntegrand h (c + h) x v) gainPairMeasure := by
    rw [gainPairIntegrand_fun_symm h (c + h), gainPairIntegrand_fun_add_left,
      gainPairIntegrand_fun_symm c h]
    exact hhc.add hhh
  rw [← symmetricGain_self, symmetricGain_add_left c h (c + h) x v hc_sum hh_sum,
    symmetricGain_add_right c c h x v hcc hch,
    symmetricGain_add_right h c h x v hhc hhh,
    symmetricGain_self c, symmetricGain_self h, symmetricGain_symm h c]
  ring

end BoltzmannNonuniqueness

end

end

section

/-! # A finite-family quadratic difference estimate in the sum norm -/

noncomputable section

namespace BoltzmannNonuniqueness.ColoredAlgebra

theorem sum_abs_product_difference_le {I : Type*} (s : Finset I) {R E : ℝ}
    (hR : 0 ≤ R) (a b c d : I → ℝ)
    (hb : ∀ i ∈ s, 0 ≤ b i ∧ b i ≤ R) (hc : ∀ i ∈ s, 0 ≤ c i ∧ c i ≤ R)
    (hac : (∑ i ∈ s, |a i-c i|) ≤ E) (hbd : (∑ i ∈ s, |b i-d i|) ≤ E) :
    (∑ i ∈ s, |a i*b i-c i*d i|) ≤ 2*R*E := by
  calc
    _ ≤ ∑ i ∈ s, (R* |a i-c i| + R* |b i-d i|) := by
      apply Finset.sum_le_sum
      intro i hi
      calc
        _ = |(a i-c i)*b i+c i*(b i-d i)| := by congr 1; ring
        _ ≤ |(a i-c i)*b i| + |c i*(b i-d i)| := abs_add_le _ _
        _ = |a i-c i| * b i+c i* |b i-d i| := by
          rw [abs_mul,abs_mul,abs_of_nonneg (hb i hi).1,abs_of_nonneg (hc i hi).1]
        _ ≤ |a i-c i| * R+R* |b i-d i| := add_le_add
          (mul_le_mul_of_nonneg_left (hb i hi).2 (abs_nonneg _))
          (mul_le_mul_of_nonneg_right (hc i hi).2 (abs_nonneg _))
        _ = _ := by ring
    _ = R*(∑ i ∈ s, |a i-c i|)+R*(∑ i ∈ s, |b i-d i|) := by
      rw [Finset.sum_add_distrib,Finset.mul_sum,Finset.mul_sum]
    _ ≤ R*E+R*E := add_le_add (mul_le_mul_of_nonneg_left hac hR) (mul_le_mul_of_nonneg_left hbd hR)
    _ = _ := by ring

end BoltzmannNonuniqueness.ColoredAlgebra

end

end

end OAI
