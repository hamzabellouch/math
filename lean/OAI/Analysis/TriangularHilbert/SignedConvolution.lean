import OAI.Analysis.TriangularHilbert.SignedExpansion

namespace OAI

section
namespace TriangularHilbert.Heat
open MeasureTheory
noncomputable section

lemma density_equal_pair {s : ℝ} (hs : 0 < s) (a b p : ℝ) :
    density s (a-p)*density s (b+p) =
      density (2*s) (a+b)*density (s/2) (p-(a-b)/2) := by
  rw [show b+p = -((-b)-p) by ring,density_neg,density_product hs hs]
  congr 1
  · congr 1 <;> ring
  · congr 1
    · field_simp; ring
    · field_simp; ring

lemma weighted_signed_pair {s : ℝ} (hs : 0 < s) (a b p : ℝ) :
    (a-p)*(b+p)*density s (a-p)*density s (b+p) =
      density (2*s) (a+b)*(cubic ((a+b)^2/4) 0 (-1) 0 (p-(a-b)/2)*density (s/2) (p-(a-b)/2)) := by
  rw [mul_assoc ((a-p)*(b+p)),density_equal_pair hs]
  unfold cubic
  ring

lemma integral_signed_pair {s : ℝ} (hs : 0 < s) (a b : ℝ) :
    (∫ p : ℝ, (a-p)*(b+p)*density s (a-p)*density s (b+p)) =
      ((a+b)^2/4-s/2)*density (2*s) (a+b) := by
  simp_rw [weighted_signed_pair hs]
  rw [integral_const_mul,integral_shifted_cubic_density (by positivity : 0 < s/2)]
  ring

lemma integral_oddWindow_pair {s : ℝ} (hs : 0 < s) (a b : ℝ) :
    (∫ p : ℝ, oddWindow s (a-p)*oddWindow s (b+p)) =
      (((a+b)^2/4-s/2)*density (2*s) (a+b))/s := by
  have hr := (Real.sqrt_pos.mpr hs).ne'
  have he (p : ℝ) : oddWindow s (a-p)*oddWindow s (b+p) =
      ((a-p)*(b+p)*density s (a-p)*density s (b+p))/s := by
    unfold oddWindow
    field_simp
    rw [Real.sq_sqrt hs.le]
    ring
  simp_rw [he]
  rw [integral_div,integral_signed_pair hs]

lemma density_one_two_pair {s : ℝ} (hs : 0 < s) (a b p : ℝ) :
    density s (a-p)*density (2*s) (b+p) =
      density (3*s) (a+b)*density (2*s/3) (p-(2*a-b)/3) := by
  rw [show b+p = -((-b)-p) by ring,density_neg,density_product hs (by positivity : 0 < 2*s)]
  congr 1
  · congr 1 <;> ring
  · congr 1
    · field_simp; ring
    · field_simp; ring

lemma weighted_signed_outer {s : ℝ} (hs : 0 < s) (a b p : ℝ) :
    (a-p)*density s (a-p)*(((b+p)^2/4-s/2)*density (2*s) (b+p)) =
      density (3*s) (a+b)*(cubic ((a+b)^3/27-(a+b)*s/6) (s/2) (-(a+b)/4) (-1/4)
        (p-(2*a-b)/3)*density (2*s/3) (p-(2*a-b)/3)) := by
  calc
    _ = ((a-p)*((b+p)^2/4-s/2))*(density s (a-p)*density (2*s) (b+p)) := by ring
    _ = _ := by rw [density_one_two_pair hs]; unfold cubic; ring

lemma integral_signed_outer {s : ℝ} (hs : 0 < s) (a b : ℝ) :
    (∫ p : ℝ, (a-p)*density s (a-p)*(((b+p)^2/4-s/2)*density (2*s) (b+p))) =
      ((a+b)^3/27-(a+b)*s/3)*density (3*s) (a+b) := by
  simp_rw [weighted_signed_outer hs]
  rw [integral_const_mul,integral_shifted_cubic_density (by positivity : 0 < 2*s/3)]
  ring

def signedKernel (s t : ℝ) : ℝ :=
  (t^3/27-t*s/3)/(s*Real.sqrt s)*density (3*s) t

lemma integral_oddWindow_triple {s : ℝ} (hs : 0 < s) (a b c : ℝ) :
    (∫ z : ℝ×ℝ, oddWindow s (a-z.1)*oddWindow s (b-z.2)*oddWindow s (c+z.1+z.2)) =
      signedKernel s (a+b+c) := by
  rw [Measure.volume_eq_prod,integral_prod _ (oddWindow_triple_integrable hs a b c)]
  have inner (p : ℝ) : (∫ q : ℝ, oddWindow s (a-p)*oddWindow s (b-q)*oddWindow s (c+p+q)) =
      oddWindow s (a-p)*((((b+c+p)^2/4-s/2)*density (2*s) (b+c+p))/s) := by
    simp_rw [mul_assoc]
    rw [integral_const_mul,integral_oddWindow_pair hs]
    congr 3 <;> ring_nf
  simp_rw [inner]
  have he (p : ℝ) : oddWindow s (a-p)*((((b+c+p)^2/4-s/2)*density (2*s) (b+c+p))/s) =
      ((a-p)*density s (a-p)*(((b+c+p)^2/4-s/2)*density (2*s) (b+c+p)))/(s*Real.sqrt s) := by
    unfold oddWindow
    ring
  simp_rw [he]
  rw [integral_div,integral_signed_outer hs]
  unfold signedKernel
  rw [show a+(b+c) = a+b+c by ring]
  ring
end
end TriangularHilbert.Heat
end

end OAI
