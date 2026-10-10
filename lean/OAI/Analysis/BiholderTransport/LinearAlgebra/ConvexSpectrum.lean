import Mathlib
import OAI.Analysis.BiholderTransport.Regularity.MinMax
import OAI.Analysis.BiholderTransport.Convexity.BoundedConvexSecant

namespace OAI

section
section
noncomputable section
open Set

namespace WeakMTWTransport
section ConvexSpectrum
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma bounded_matrix_convex_eigen_secant {A : ℝ → E →ₗ[ℝ] E} {a b C d x y : ℝ}
    (hA : ∀ t∈Icc a b, (A t).IsSymmetric)
    (hc : ∀ v, ConvexOn ℝ (Icc a b) (fun t => inner ℝ (A t v) v))
    (hC : 0≤C) (hd : 0<d)
    (hb : ∀ t∈Icc a b, ∀ v, |inner ℝ (A t v) v|≤C*‖v‖^2)
    (hx : x∈Icc (a+d) (b-d)) (hy : y∈Icc (a+d) (b-d))
    (hxi : x∈Icc a b) (hyi : y∈Icc a b)
    {n : ℕ} (hn : Module.finrank ℝ E=n) (i : Fin n) :
    |(hA y hyi).eigenvalues hn i-(hA x hxi).eigenvalues hn i|≤(2*C/d)*|y-x| := by
  have H (v : E) := bounded_convex_secant (hc v) (mul_nonneg hC (sq_nonneg ‖v‖))
    hd (fun t ht => hb t ht v) hx hy
  have H' (v : E) : |inner ℝ (A y v) v-inner ℝ (A x v) v|≤
      ((2*C/d)*|y-x|)*‖v‖^2 := by
    convert H v using 1
    ring
  have hup := ordered_eigenvalue_quadratic_comparison (hA y hyi) (hA x hxi)
    (a := 1) (b := (2*C/d)*|y-x|) (by norm_num)
    (fun v => by have := (abs_le.mp (H' v)).2; linarith) hn i
  have hlo := ordered_eigenvalue_quadratic_comparison (hA x hxi) (hA y hyi)
    (a := 1) (b := (2*C/d)*|y-x|) (by norm_num)
    (fun v => by have := (abs_le.mp (H' v)).1; linarith) hn i
  exact abs_le.mpr ⟨by linarith,by linarith⟩

lemma matrix_convex_eigen_endpoint {A : ℝ → E →ₗ[ℝ] E} {a C e : ℝ}
    (ha : 0≤a) (he : e∈Icc (0:ℝ) 1)
    (hA : ∀ t∈Icc (-a) 1, (A t).IsSymmetric)
    (hc : ∀ v, ConvexOn ℝ (Icc (-a) 1) (fun t => inner ℝ (A t v) v))
    (hb : ∀ v, inner ℝ (A 0 v) v≤C*‖v‖^2)
    (hm : 1-e∈Icc (-a) 1) (h1 : (1:ℝ)∈Icc (-a) 1)
    {n : ℕ} (hn : Module.finrank ℝ E=n) (i : Fin n) :
    (hA (1-e) hm).eigenvalues hn i ≤
      (1-e)*(hA 1 h1).eigenvalues hn i+e*C := by
  refine ordered_eigenvalue_quadratic_comparison (hA (1-e) hm) (hA 1 h1)
    (show 0≤1-e by linarith [he.2]) ?_ hn i
  intro v
  have H := (hc v).2 (show (0:ℝ)∈Icc (-a) 1 by constructor <;> linarith) h1
    he.1 (show 0≤1-e by linarith [he.2]) (show e+(1-e)=1 by ring)
  simp only [smul_eq_mul,mul_zero,mul_one,zero_add] at H
  have H2 := mul_le_mul_of_nonneg_left (hb v) he.1
  nlinarith only [H,H2]
end ConvexSpectrum
end WeakMTWTransport

end

end

end

end OAI
