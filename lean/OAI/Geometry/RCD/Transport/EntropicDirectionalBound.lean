import OAI.Geometry.RCD.Heat.EntropyPowerFirstVariation

namespace OAI

/-! # The exact finite-dimensional directional bound from the entropy chord

These are the scalar first-variation calculations in EKS, Lemma 3.20.
The separate flat formula avoids division by a vanishing hyperbolic sine.
-/

open Set Filter
open scoped Topology
noncomputable section
namespace RegularPointCoordinates

theorem hasDerivAt_hyperbolicChord_zero (q A B : ℝ) :
    HasDerivAt (hyperbolicChord q A B)
      (q*(B-Real.cosh q*A)/Real.sinh q) 0 := by
  have h0 : HasDerivAt (fun t : ℝ => q*(1-t)) (-q) 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).const_sub 1).const_mul q
  have h1 : HasDerivAt (fun t : ℝ => q*t) q 0 := by
    simpa using (hasDerivAt_id (0:ℝ)).const_mul q
  convert ((h0.sinh.mul_const A).add (h1.sinh.mul_const B)).div_const (Real.sinh q) using 1
  · rfl
  · simp only [sub_zero,mul_one,mul_zero,Real.cosh_zero,one_mul,mul_one]
    ring

theorem entropic_hyperbolic_directional_bound {E v : ℝ → ℝ} {N q A B d M : ℝ}
    (hN : 0 < N) (hq : 0 < q) (hA : 0 < A)
    (hE0 : E 0 = -N*Real.log A)
    (hp : ∀ᶠ t in 𝓝[>] (0:ℝ), hyperbolicChord q A B t ≤ Real.exp (-E t/N))
    (hv : ∀ᶠ t in 𝓝[>] (0:ℝ), v t ≤ (E t-E 0)/t+t*M)
    (hd : Tendsto v (𝓝[>] (0:ℝ)) (𝓝 d)) :
    d ≤ N*q/Real.sinh q*(Real.cosh q-B/A) := by
  have hzero : hyperbolicChord q A B 0=A := hyperbolicChord_zero hq A B
  have hh := entropy_power_first_variation hN (by rwa [hzero])
    (hasDerivAt_hyperbolicChord_zero q A B) (by rwa [hzero]) hp hv hd
  rw [hzero] at hh
  convert hh using 1
  field_simp [hA.ne',(Real.sinh_pos_iff.mpr hq).ne']
  ring

theorem entropic_flat_directional_bound {E v : ℝ → ℝ} {N A B d M : ℝ}
    (hN : 0 < N) (hA : 0 < A) (hE0 : E 0 = -N*Real.log A)
    (hp : ∀ᶠ t in 𝓝[>] (0:ℝ), (1-t)*A+t*B ≤ Real.exp (-E t/N))
    (hv : ∀ᶠ t in 𝓝[>] (0:ℝ), v t ≤ (E t-E 0)/t+t*M)
    (hd : Tendsto v (𝓝[>] (0:ℝ)) (𝓝 d)) : d ≤ N*(1-B/A) := by
  have hV : HasDerivAt (fun t : ℝ => (1-t)*A+t*B) (B-A) 0 := by
    convert (((hasDerivAt_id (0:ℝ)).const_sub 1).mul_const A).add
      ((hasDerivAt_id (0:ℝ)).mul_const B) using 1
    · ext t
      simp only [Pi.add_apply,id_eq]
    · ring
  have hh := entropy_power_first_variation hN (by simpa using hA) hV (by simpa using hE0) hp hv hd
  convert hh using 1
  field_simp [hA.ne']
  ring

end RegularPointCoordinates

end

end OAI
