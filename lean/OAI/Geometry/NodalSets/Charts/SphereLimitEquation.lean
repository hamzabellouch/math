import OAI.Geometry.NodalSets.Coefficients.IntrinsicDivergenceCoefficients
import OAI.Geometry.NodalSets.Elliptic.RealDivergenceLimit

namespace OAI

namespace Yau.Target
open Manifold Yau.Analysis Yau.Geometry Set Filter
open scoped Topology ContDiff
noncomputable section

lemma intrinsic_operator_unweighted_divergence (A : IntrinsicTensor) (rho w : Base → ℝ)
    (p : Base) (x : Yau.Jets.Coord) :
    intrinsicWeightedChartOperator A rho w p (seedCoordEquiv x) =
      (rho (sphereChartCoordMap p x))⁻¹ * (roundCoordDensity x)⁻¹ *
        Yau.coordDiv (realMatrixFlux (intrinsicDivergencePrincipal A p) (w ∘ sphereChartCoordMap p)) x := by
  rw [intrinsicRealOperator_pullback]
  have hf : realMatrixFlux (intrinsicDivergencePrincipal A p) (w ∘ sphereChartCoordMap p) =
      fun y i ↦ roundCoordDensity y * ∑ j, intrinsicRealPrincipal A p y i j*
        Yau.coordPartial (w ∘ sphereChartCoordMap p) y j := by
    funext y i
    simp [realMatrixFlux,intrinsicDivergencePrincipal,Finset.mul_sum,mul_assoc]
  rw [hf]
  simp only [Yau.weightedDiv,mul_assoc]

theorem intrinsic_equation_of_unweighted_divergence (A : IntrinsicTensor) (rho w : Base → ℝ)
    (hrp : ∀ p, 0 < rho p) (lam : ℝ)
    (he : ∀ p x, Yau.coordDiv
      (realMatrixFlux (intrinsicDivergencePrincipal A p) (w ∘ sphereChartCoordMap p)) x+
      intrinsicDivergencePotential rho lam p x*(w ∘ sphereChartCoordMap p) x=0) :
    ∀ p z, -intrinsicWeightedChartOperator A rho w p z =
      lam*w ((extChartAt (𝓡 4) p).symm z) := by
  intro p z
  obtain ⟨x,rfl⟩ := seedCoordEquiv.surjective z
  rw [intrinsic_operator_unweighted_divergence]
  have hh := he p x
  have hd : Yau.coordDiv
      (realMatrixFlux (intrinsicDivergencePrincipal A p) (w ∘ sphereChartCoordMap p)) x =
      -(roundCoordDensity x*(lam*rho (sphereChartCoordMap p x))*w (sphereChartCoordMap p x)) := by
    simpa only [intrinsicDivergencePotential,intrinsicRealPotential,Function.comp_apply] using
      (eq_neg_of_add_eq_zero_left hh)
  rw [hd]
  change -((rho (sphereChartCoordMap p x))⁻¹ * (roundCoordDensity x)⁻¹ *
    -(roundCoordDensity x*(lam*rho (sphereChartCoordMap p x))*w (sphereChartCoordMap p x))) =
      lam*w (sphereChartCoordMap p x)
  field_simp [(hrp (sphereChartCoordMap p x)).ne',(roundCoordDensity_pos x).ne']

theorem sphere_limit_equation {T : Type*} [TopologicalSpace T]
    (A : T → IntrinsicTensor) (rho : T → Base → ℝ)
    (hA : ∀ t, IntrinsicTensorSmooth (A t))
    (hs : ∀ t p v w, A t p v w = A t p w v) (hp : ∀ t p v, v ≠ 0 → 0 < A t p v v)
    (hrp : ∀ t p, 0 < rho t p) (lam : ℝ)
    (hCjoint : ∀ p i j ds, Continuous (fun z : T × Yau.Jets.Coord ↦
      partialJet (fun x ↦ intrinsicDivergencePrincipal (A z.1) p x i j) ds z.2))
    (hVjoint : ∀ p ds, Continuous (fun z : T × Yau.Jets.Coord ↦
      partialJet (intrinsicDivergencePotential (rho z.1) lam p) ds z.2))
    (t : ℕ → T) (t0 : T) (ht : Tendsto t atTop (𝓝 t0))
    (w : ℕ → Base → ℝ) (v : Base → ℝ)
    (hw : ∀ j, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ (w j)) (hv : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ v)
    (he : ∀ j p z, -intrinsicWeightedChartOperator (A (t j)) (rho (t j)) (w j) p z =
      lam*w j ((extChartAt (𝓡 4) p).symm z))
    (hconv : ∀ p ds x, Tendsto (fun j ↦ partialJet (w j ∘ sphereChartCoordMap p) ds x) atTop
      (𝓝 (partialJet (v ∘ sphereChartCoordMap p) ds x))) :
    ∀ p z, -intrinsicWeightedChartOperator (A t0) (rho t0) v p z =
      lam*v ((extChartAt (𝓡 4) p).symm z) := by
  apply intrinsic_equation_of_unweighted_divergence (A t0) (rho t0) v (hrp t0) lam
  intro p
  apply real_divergence_limit_equation
    (fun j ↦ intrinsicDivergencePrincipal (A (t j)) p) (intrinsicDivergencePrincipal (A t0) p)
    (fun j ↦ intrinsicDivergencePotential (rho (t j)) lam p) (intrinsicDivergencePotential (rho t0) lam p)
    (fun j ↦ w j ∘ sphereChartCoordMap p) (v ∘ sphereChartCoordMap p)
    (fun j ↦ intrinsicDivergencePrincipal_smooth (A (t j)) (hA (t j)) (hs (t j)) (hp (t j)) p)
    (intrinsicDivergencePrincipal_smooth (A t0) (hA t0) (hs t0) (hp t0) p)
    (fun j ↦ spherePullback_smooth (w j) (hw j) p) (spherePullback_smooth v hv p)
  · intro i j ds x
    have htx : Tendsto (fun n ↦ (t n,x)) atTop (𝓝 (t0,x)) := ht.prodMk_nhds tendsto_const_nhds
    have hh := ((hCjoint p i j ds).tendsto (t0,x)).comp htx
    simpa only [Function.comp_def] using hh
  · intro x
    have htx : Tendsto (fun n ↦ (t n,x)) atTop (𝓝 (t0,x)) := ht.prodMk_nhds tendsto_const_nhds
    have hh := ((hVjoint p []).tendsto (t0,x)).comp htx
    simpa only [Function.comp_def,partialJet] using hh
  · exact hconv p
  · exact fun j ↦ intrinsic_unweighted_divergence_equation (A (t j)) (rho (t j)) (hrp (t j))
      (w j) lam (he j) p

end
end Yau.Target

end OAI
