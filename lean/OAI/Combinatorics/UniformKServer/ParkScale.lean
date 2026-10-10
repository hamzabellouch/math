import Mathlib
import OAI.Combinatorics.UniformKServer.GeometricMass

namespace OAI

                                
section

/-! The actual pointwise scale sum for parks, including points of zero posterior
 mass. Add one to each ball mass exactly as in the held-size denominator. -/
noncomputable section
namespace UniformKServer.ParkCoefficients
open Finset
open scoped Classical
variable {X : Type*} [Fintype X] [MetricSpace X]

def outer (μ : X→ℝ) (y : X) (R q : ℝ) (j : ℕ) : ℝ :=
  1+GeometricMass.mass μ y (67*GeometricMass.radius R q j)
def inner (μ : X→ℝ) (y : X) (R q : ℝ) (j : ℕ) : ℝ :=
  1+GeometricMass.mass μ y (GeometricMass.radius R q j)

def bad (μ : X→ℝ) (y : X) (R q : ℝ) (j : ℕ) : Prop :=
  2*inner μ y R q j<outer μ y R q j

theorem outer_one (μ : X→ℝ) (hμ : ∀ z, 0≤μ z) (y : X) (R q : ℝ) (j : ℕ) :
    1≤outer μ y R q j := by
  unfold outer
  linarith [GeometricMass.mass_nonneg μ hμ y (67*GeometricMass.radius R q j)]

theorem inner_one (μ : X→ℝ) (hμ : ∀ z, 0≤μ z) (y : X) (R q : ℝ) (j : ℕ) :
    1≤ inner μ y R q j := by
  unfold inner
  linarith [GeometricMass.mass_nonneg μ hμ y (GeometricMass.radius R q j)]

theorem inner_outer (μ : X→ℝ) (hμ : ∀ z, 0≤μ z) (y : X) (R q : ℝ)
    (hR : 0<R) (hq : 0<q) (j : ℕ) : inner μ y R q j≤outer μ y R q j := by
  have hr := GeometricMass.radius_pos R q hR hq j
  have ht := GeometricMass.mass_mono μ hμ y (by linarith :
    GeometricMass.radius R q j≤67*GeometricMass.radius R q j)
  dsimp only [inner,outer]
  linarith

theorem outer_shift (μ : X→ℝ) (hμ : ∀ z, 0≤μ z) (y : X)
    (K R q : ℝ) (hK : ∑ z, μ z≤K-1) (hR : 0<R) (hq : 0<q)
    (p j : ℕ) (hs : 67*q^p≤1) :
    outer μ y R q j≤ if j<p then K else inner μ y R q (j-p) := by
  split_ifs with hj
  · have ht := (GeometricMass.mass_total μ hμ y (67*GeometricMass.radius R q j)).trans hK
    unfold outer; linarith
  · have ht := GeometricMass.mass_shift μ hμ y R q 1 67 hR hq p j (by omega) hs
    dsimp only [outer,inner]
    simp only [one_mul] at ht
    linarith

theorem scale_logs (μ : X→ℝ) (hμ : ∀ z, 0≤μ z) (y : X)
    (K R q : ℝ) (hK : ∑ z, μ z≤K-1) (hR : 0<R) (hq : 0<q)
    (p J : ℕ) (hs : 67*q^p≤1) :
    (∑ j∈range J, Real.log (outer μ y R q j/inner μ y R q j))≤(p:ℝ)*Real.log K := by
  have hk : 1≤K := by have ht := sum_nonneg fun z (_ : z∈univ) => hμ z; linarith
  simpa only [div_one] using PilotScales.scale_logarithms
    (inner μ y R q) (outer μ y R q) J p 1 K (by norm_num) hk
    (fun j _ => inner_one μ hμ y R q j) (fun j _ => inner_outer μ hμ y R q hR hq j)
    (fun j _ => outer_shift μ hμ y K R q hK hR hq p j hs)

theorem bad_count (μ : X→ℝ) (hμ : ∀ z, 0≤μ z) (y : X)
    (K R q : ℝ) (hK : ∑ z, μ z≤K-1) (hR : 0<R) (hq : 0<q)
    (p J : ℕ) (hs : 67*q^p≤1) :
    (((range J).filter (bad μ y R q)).card:ℝ)≤(p:ℝ)*Real.log K/Real.log 2 := by
  apply (le_div_iff₀ (Real.log_pos (by norm_num : (1:ℝ)<2))).mpr
  calc
    _ = ∑ j∈range J, if bad μ y R q j then Real.log 2 else 0 := by
      rw [←sum_filter,sum_const,nsmul_eq_mul]
    _ ≤ ∑ j∈range J, Real.log (outer μ y R q j/inner μ y R q j) := by
      apply sum_le_sum
      intro j _
      have hi : 0< inner μ y R q j := by linarith [inner_one μ hμ y R q j]
      split_ifs with hj
      · exact (Real.log_lt_log (by norm_num : (0:ℝ)<2) ((lt_div_iff₀ hi).mpr hj)).le
      · apply Real.log_nonneg
        exact (le_div_iff₀ hi).mpr (by simpa using inner_outer μ hμ y R q hR hq j)
    _ ≤ _ := scale_logs μ hμ y K R q hK hR hq p J hs

end UniformKServer.ParkCoefficients

end


end

end OAI
