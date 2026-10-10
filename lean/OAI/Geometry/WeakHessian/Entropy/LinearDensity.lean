import Mathlib
import OAI.Geometry.WeakHessian.LocalBounds.ConstLp

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open Set Filter Topology Bornology
open scoped InnerProductSpace

attribute [local instance] Classical.propDecidable
open Set
open scoped NNReal
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

namespace WeakHessian
open WeakHessianFunctional MeasureTheory Set Filter
open scoped Topology InnerProductSpace

variable {X : Type*} [MeasurableSpace X] {m : Measure X}
  [IsProbabilityMeasure m]

def linearDensity (ε : ℝ) (u v : Lp ℝ 2 m) (s : ℝ) : Lp ℝ 2 m :=
  constLp 1 + ε • (u+s • (v-u))

lemma linearDensity_coe (ε : ℝ) (u v : Lp ℝ 2 m) (s : ℝ) :
    (linearDensity ε u v s : X → ℝ) =ᵐ[m] (fun x => 1+ε*(u x+s*(v x-u x))) := by
  filter_upwards [Lp.coeFn_add (constLp (m := m) 1) (ε • (u+s • (v-u))),
    constLp_coe (m := m) 1,Lp.coeFn_smul ε (u+s • (v-u)),
    Lp.coeFn_add u (s • (v-u)),Lp.coeFn_smul s (v-u),Lp.coeFn_sub v u] with x h1 h2 h3 h4 h5 h6
  simp only [linearDensity,h1,Pi.add_apply,h2,h3,h4,h5,h6,Pi.smul_apply,smul_eq_mul,Pi.sub_apply]

lemma linearDensity_mass (ε : ℝ) (u v : Lp ℝ 2 m)
    (hu : ∫ x,u x ∂m = 0) (hv : ∫ x,v x ∂m = 0) (s : ℝ) :
    (∫ x,linearDensity ε u v s x ∂m) = 1 := by
  have hui := (Lp.memLp u).integrable (by norm_num)
  have hvi := (Lp.memLp v).integrable (by norm_num)
  rw [integral_congr_ae (linearDensity_coe ε u v s)]
  have hd : Integrable (fun x => v x-u x) m := hvi.sub hui
  have hs : Integrable (fun x => s*(v x-u x)) m := hd.const_mul s
  have ha : Integrable (fun x => u x+s*(v x-u x)) m := hui.add hs
  have hε : Integrable (fun x => ε*(u x+s*(v x-u x))) m := ha.const_mul ε
  calc
    _ = (∫ x,(1:ℝ) ∂m)+(∫ x,ε*(u x+s*(v x-u x)) ∂m) :=
      integral_add (integrable_const (1:ℝ)) hε
    _ = 1 := by
      rw [integral_const_mul,integral_add hui hs,integral_const_mul,integral_sub hvi hui,hu,hv]
      simp

lemma linearDensity_bounds {ε B s : ℝ} (hε : 0 ≤ ε) (hB : 0 ≤ B) (hs : s ∈ Icc (0:ℝ) 1)
    {u v : Lp ℝ 2 m} (hu : ∀ᵐ x ∂m, |u x| ≤ B) (hv : ∀ᵐ x ∂m, |v x| ≤ B) :
    ∀ᵐ x ∂m, linearDensity ε u v s x ∈ Icc (1-ε*B) (1+ε*B) := by
  filter_upwards [linearDensity_coe ε u v s,hu,hv] with x hx hu hv
  rw [hx]
  have hl : -B ≤ u x+s*(v x-u x) := by
    have h1 := mul_le_mul_of_nonneg_left (abs_le.mp hu).1 (sub_nonneg.mpr hs.2)
    have h2 := mul_le_mul_of_nonneg_left (abs_le.mp hv).1 hs.1
    nlinarith
  have hr : u x+s*(v x-u x) ≤ B := by
    have h1 := mul_le_mul_of_nonneg_left (abs_le.mp hu).2 (sub_nonneg.mpr hs.2)
    have h2 := mul_le_mul_of_nonneg_left (abs_le.mp hv).2 hs.1
    nlinarith
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left hl hε]
  · nlinarith [mul_le_mul hr (le_refl ε) hε hB]

lemma continuous_linearDensity (ε : ℝ) (u v : Lp ℝ 2 m) : Continuous (linearDensity ε u v) := by
  unfold linearDensity
  fun_prop

lemma linearDensity_affine_deriv (ε : ℝ) (u v : Lp ℝ 2 m) (s d r : ℝ) :
    HasDerivAt (fun a : ℝ => linearDensity ε u v (s+d*a)) ((ε*d) • (v-u)) r := by
  have H := ((((hasDerivAt_id r).const_mul d).const_add s).smul_const (v-u)).const_add u
  have HH := (H.const_smul ε).const_add (constLp (m := m) 1)
  simpa only [linearDensity,smul_smul,mul_one,id_eq] using! HH

end WeakHessian

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

end

end OAI
