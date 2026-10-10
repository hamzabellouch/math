import Mathlib
import OAI.Analysis.AffineBernstein.CapInverseBound

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

theorem affineMaximal_graph_cap_weighted_inverse_bound {n : ℕ} {Ω : Set (Space n)}
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
    (W : Space n → ℝ) (hW : ContinuousOn W K)
    {r C : ℝ} (hr : 0 ≤ r)
    (hrZ : ∀ x ∈ Q, r*W x ≤ radialSupport u o c x)
    (hρQ : ∀ x ∈ Q, 1 ≤ deriv (deriv ψ) (graphAffineFunction u a b d x))
    (hC : ∀ x ∈ K,
      (n:ℝ) * (graphAffineFunction u a b d x - (a o+b*c+d)) *
        deriv ψ (graphAffineFunction u a b d x) +
      (n:ℝ)*((n:ℝ)+1)*ψ (graphAffineFunction u a b d x) ≤ C) :
    r * (∫ x in Q, affineAreaDensity u x * (W x * graphInverseMetric u a b d x)) ≤
      C * ∫ x in K, affineAreaDensity u x := by
  lift r to NNReal using hr
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
  have hAVi : IntegrableOn (fun x => A x*(W x*V x)) K := (hAc.mul (hW.mul hVc)).integrableOn_compact hK
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
    _ = ∫ x in Q, r*(A x*(W x*V x)) := (integral_const_mul _ _).symm
    _ ≤ ∫ x in Q, F x := by
      apply setIntegral_mono_on ((hAVi.mono_set hQK).const_mul r)
        (hFi.mono_set hQK) hQ
      intro x hx
      have hz := hrZ x hx
      have hv := hVp x (hQK hx)
      have ha := hAp x (hQK hx)
      have hs' := hρQ x hx
      have hz0 : 0 ≤ Z x := hZ x (hQK hx)
      dsimp [F]
      calc
        _ = A x*((r*W x)*V x*1) := by ring
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
