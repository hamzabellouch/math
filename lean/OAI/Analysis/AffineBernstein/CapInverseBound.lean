import Mathlib
import OAI.Analysis.AffineBernstein.DeterminantVariation

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

/-- The literal inverse-Hessian norm of a restricted ambient affine covector. -/
def graphInverseMetric {n : ℕ} (u : Space n → ℝ)
    (a : Space n →L[ℝ] ℝ) (b d : ℝ) (x : Space n) : ℝ :=
  ∑ i, ∑ j, (hessian u x)⁻¹ i j *
    dirDeriv (coordinateVector n i) (graphAffineFunction u a b d) x *
    dirDeriv (coordinateVector n j) (graphAffineFunction u a b d) x

lemma graphInverseMetric_nonneg {n : ℕ} {u : Space n → ℝ} {x : Space n}
    (hp : (hessian u x).PosDef) (a : Space n →L[ℝ] ℝ) (b d : ℝ) :
    0 ≤ graphInverseMetric u a b d x := by
  let v := fun i => dirDeriv (coordinateVector n i) (graphAffineFunction u a b d) x
  have hh := hp.inv.posSemidef.dotProduct_mulVec_nonneg v
  simpa only [RCLike.re_to_real,star_trivial,graphInverseMetric,v,dotProduct,Matrix.mulVec,
    Finset.mul_sum,mul_left_comm,mul_assoc] using hh

lemma contDiffAt_graphInverseMetric {n : ℕ} {u : Space n → ℝ} {x : Space n}
    (hu : ContDiffAt ℝ ∞ u x) (hp : (hessian u x).PosDef)
    (a : Space n →L[ℝ] ℝ) (b d : ℝ) :
    ContDiffAt ℝ ∞ (graphInverseMetric u a b d) x := by
  have hq := contDiffAt_graphAffineFunction hu a b d
  have hi (i j : Fin n) : ContDiffAt ℝ ∞ (fun y => (hessian u y)⁻¹ i j) x := by
    simp only [Matrix.inv_def,Ring.inverse_eq_inv,Matrix.smul_apply,smul_eq_mul]
    exact ((contDiffAt_det_hessian hu).inv hp.det_pos.ne').mul
      (contDiffAt_adjugate_hessian_entry hu i j)
  apply ContDiffAt.sum
  intro i _
  apply ContDiffAt.sum
  intro j _
  exact ((hi i j).mul ((hq.fderiv_right (m := ∞) (by simp)).clm_apply contDiffAt_const)).mul
    ((hq.fderiv_right (m := ∞) (by simp)).clm_apply contDiffAt_const)

/-- The cap identity gives the genuine inverse-Hessian integral bound.
The hypotheses are geometric support and scalar cutoff bounds, not a bound
on the inverse Hessian. The right side is the area's actual integral, so the
separate area-in-a-ball geometric theorem is not silently assumed. -/
theorem affineMaximal_graph_cap_inverse_bound {n : ℕ} {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    (hp : ∀ x ∈ Ω, (hessian u x).PosDef) (hm : AffineMaximalOn Ω u)
    (o : Space n) (c : ℝ) (a : Space n →L[ℝ] ℝ) (b d : ℝ)
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    {K Q : Set (Space n)} (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    (hQ : MeasurableSet Q) (hQK : Q ⊆ K)
    (hs : ∀ x ∈ Ω, x ∉ K →
      ψ (graphAffineFunction u a b d x) = 0 ∧
      deriv ψ (graphAffineFunction u a b d x) = 0 ∧
      deriv (deriv ψ) (graphAffineFunction u a b d x) = 0)
    (hZ : ∀ x ∈ K, 0 ≤ radialSupport u o c x)
    (hρ : ∀ x ∈ K, 0 ≤ deriv (deriv ψ) (graphAffineFunction u a b d x))
    {r C : ℝ} (hr : 0 ≤ r)
    (hrZ : ∀ x ∈ Q, r ≤ radialSupport u o c x)
    (hρQ : ∀ x ∈ Q, 1 ≤ deriv (deriv ψ) (graphAffineFunction u a b d x))
    (hC : ∀ x ∈ K,
      (n:ℝ) * (graphAffineFunction u a b d x - (a o+b*c+d)) *
        deriv ψ (graphAffineFunction u a b d x) +
      (n:ℝ)*((n:ℝ)+1)*ψ (graphAffineFunction u a b d x) ≤ C) :
    r * (∫ x in Q, affineAreaDensity u x * graphInverseMetric u a b d x) ≤
      C * ∫ x in K, affineAreaDensity u x := by
  let q := graphAffineFunction u a b d
  let V := graphInverseMetric u a b d
  let Z := radialSupport u o c
  let A := affineAreaDensity u
  let F := fun x => A x * (Z x * V x * deriv (deriv ψ) (q x))
  let G := fun x => A x * ((n:ℝ)*(q x-(a o+b*c+d))*deriv ψ (q x) +
    (n:ℝ)*((n:ℝ)+1)*ψ (q x))
  have hAc : ContinuousOn A K := fun x hx =>
    (contDiffAt_affineAreaDensity (hu.contDiffAt (hΩ.mem_nhds (hKΩ hx)))
      (hp x (hKΩ hx))).continuousAt.continuousWithinAt
  have hVc : ContinuousOn V K := fun x hx =>
    (contDiffAt_graphInverseMetric (hu.contDiffAt (hΩ.mem_nhds (hKΩ hx)))
      (hp x (hKΩ hx)) a b d).continuousAt.continuousWithinAt
  have hzc : ContinuousOn Z K := fun x hx =>
    (contDiffAt_radialSupport (hu.contDiffAt (hΩ.mem_nhds (hKΩ hx))) o c).continuousAt.continuousWithinAt
  have hqc : ContinuousOn q K := fun x hx =>
    (contDiffAt_graphAffineFunction (hu.contDiffAt (hΩ.mem_nhds (hKΩ hx))) a b d).continuousAt.continuousWithinAt
  have hp0 := hψ.continuous.comp_continuousOn hqc
  have hψ1 : ContDiff ℝ ∞ (deriv ψ) := hψ.deriv'
  have hψ2 : ContDiff ℝ ∞ (deriv (deriv ψ)) := hψ1.deriv'
  have hp1 := hψ1.continuous.comp_continuousOn hqc
  have hp2 := hψ2.continuous.comp_continuousOn hqc
  have hFi : IntegrableOn F K := (hAc.mul ((hzc.mul hVc).mul hp2)).integrableOn_compact hK
  have hGi : IntegrableOn G K :=
    (hAc.mul (((continuousOn_const.mul (hqc.sub continuousOn_const)).mul hp1).add
      (continuousOn_const.mul hp0))).integrableOn_compact hK
  have hAi : IntegrableOn A K := hAc.integrableOn_compact hK
  have hAVi : IntegrableOn (fun x => A x*V x) K := (hAc.mul hVc).integrableOn_compact hK
  have hFG : (∫ x in K, F x-G x) = 0 := by
    have hh := affineMaximal_graph_cap_identity hΩ hu hp hm o c a b d hψ hK hKΩ
      (fun x hx hnot => (hs x hx hnot).1)
    rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hΩ.measurableSet hKΩ] at hh
    · convert hh using 1
      apply setIntegral_congr_fun hK.measurableSet
      intro x hx
      dsimp [F,G,V,graphInverseMetric,A,Z,q]
      ring
    · intro x hx
      obtain ⟨h0,h1,h2⟩ := hs x hx.1 hx.2
      simp only [h0,h1,h2,mul_zero,add_zero,sub_zero]
  have hFG' : (∫ x in K, F x) = ∫ x in K, G x := by
    rw [integral_sub hFi hGi] at hFG
    exact sub_eq_zero.mp hFG
  have hAp (x : Space n) (hx : x ∈ K) : 0 ≤ A x :=
    (Real.rpow_pos_of_pos (hp x (hKΩ hx)).det_pos _).le
  have hVp (x : Space n) (hx : x ∈ K) : 0 ≤ V x :=
    graphInverseMetric_nonneg (hp x (hKΩ hx)) a b d
  have hFp (x : Space n) (hx : x ∈ K) : 0 ≤ F x :=
    mul_nonneg (hAp x hx) (mul_nonneg (mul_nonneg (hZ x hx) (hVp x hx)) (hρ x hx))
  calc
    _ = ∫ x in Q, r*(A x*V x) := (integral_const_mul _ _).symm
    _ ≤ ∫ x in Q, F x := by
      apply setIntegral_mono_on ((hAVi.mono_set hQK).const_mul r)
        (hFi.mono_set hQK) hQ
      intro x hx
      have hz := hrZ x hx
      have hv := hVp x (hQK hx)
      have ha := hAp x (hQK hx)
      have hs' := hρQ x hx
      have hz0 : 0 ≤ Z x := hr.trans hz
      dsimp [F]
      calc
        _ = A x*(r*V x*1) := by ring
        _ ≤ A x*(Z x*V x*deriv (deriv ψ) (q x)) := by gcongr
    _ ≤ ∫ x in K, F x := setIntegral_mono_set hFi
      (ae_restrict_of_forall_mem hK.measurableSet hFp) (Filter.Eventually.of_forall fun _ hx => hQK hx)
    _ = ∫ x in K, G x := hFG'
    _ ≤ ∫ x in K, C*A x := by
      apply setIntegral_mono_on hGi (hAi.const_mul C) hK.measurableSet
      intro x hx
      dsimp [G]
      calc
        _ ≤ A x*C := mul_le_mul_of_nonneg_left (hC x hx) (hAp x hx)
        _ = _ := mul_comm _ _
    _ = _ := integral_const_mul _ _

end AffineBernstein
end

end OAI
