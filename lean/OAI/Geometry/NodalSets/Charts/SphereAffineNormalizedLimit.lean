import OAI.Geometry.NodalSets.Charts.SphereAffinePositiveInterval
import OAI.Geometry.NodalSets.Charts.SphereNormalizedGlobalLimit

namespace OAI

namespace Yau.Target
open Manifold Yau.Analysis Yau.Geometry Set Filter
open scoped Topology ContDiff
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule
attribute [local instance] intrinsicRoundPerturbationLocalInst17 intrinsicRoundPerturbationLocalInst18

theorem sphere_affine_normalized_limit
    (A : IntrinsicTensor) (hA : IntrinsicTensorSmooth A)
    (hs : ∀ x v w, A x v w = A x w v) (hp : ∀ x v, v ≠ 0 → 0 < A x v v)
    (rho : Base → ℝ) (hr : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ rho) (hrp : ∀ x, 0 < rho x)
    (a b : Base → ℝ) (ha : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ a)
    (hb : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ b) (lam : ℝ)
    (t : ℕ → ℝ) (ht : Tendsto t atTop (𝓝 0))
    (w : ℕ → Base → ℝ) (hw : ∀ j, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ (w j))
    (he : ∀ j p z, -intrinsicWeightedChartOperator
      (fun x ↦ A x+roundTensorPerturbation (fun y ↦ t j*a y) x)
      (fun x ↦ rho x+t j*b x) (w j) p z = lam*w j ((extChartAt (𝓡 4) p).symm z))
    (hn : ∀ j, sphereWeightedPairing (fun x ↦ rho x+t j*b x) (w j) (w j)=1)
    (u : Base → ℝ) (hu : Continuous u)
    (ho : ∀ j, sphereWeightedPairing (fun x ↦ rho x+t j*b x) (w j) u=0) :
    ∃ v : Base → ℝ, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ v ∧ v ≠ 0 ∧
      (∀ p z, -intrinsicWeightedChartOperator A rho v p z =
        lam*v ((extChartAt (𝓡 4) p).symm z)) ∧
      sphereWeightedPairing rho v v=1 ∧ sphereWeightedPairing rho v u=0 ∧
      ∃ nu : ℕ → ℕ, StrictMono nu ∧ TendstoUniformly (fun j ↦ w (nu j)) v atTop ∧
        (∀ p ds (Q : Set Yau.Jets.Coord), IsCompact Q →
          TendstoUniformlyOn (fun j ↦ partialJet (w (nu j) ∘ sphereChartCoordMap p) ds)
            (partialJet (v ∘ sphereChartCoordMap p) ds) atTop Q) ∧
        (∀ p n (Q : Set Yau.Jets.Coord), IsCompact Q →
          TendstoUniformlyOn (fun j ↦ iteratedFDeriv ℝ n (w (nu j) ∘ sphereChartCoordMap p))
            (iteratedFDeriv ℝ n (v ∘ sphereChartCoordMap p)) atTop Q) := by
  obtain ⟨delta,hdelta,hpos,hrjoint,hCjoint,hVjoint⟩ :=
    sphere_affine_positive_interval A hA hs hp rho hr hrp a b ha hb lam
  have hmem : ∀ᶠ j in atTop, t j ∈ Icc (-delta) delta :=
    ht.eventually (Icc_mem_nhds (by linarith) hdelta)
  obtain ⟨N,hN⟩ := eventually_atTop.mp hmem
  let shift : ℕ → ℕ := fun j ↦ j+N
  have hshift : StrictMono shift := fun i j hij ↦ Nat.add_lt_add_right hij N
  let s : ℕ → Icc (-delta) delta := fun j ↦ ⟨t (shift j),hN _ (Nat.le_add_left N j)⟩
  let s0 : Icc (-delta) delta := ⟨0,by constructor <;> linarith⟩
  have hst : Tendsto s atTop (𝓝 s0) := tendsto_subtype_rng.mpr (ht.comp hshift.tendsto_atTop)
  let Af : Icc (-delta) delta → IntrinsicTensor :=
    fun t x ↦ A x+roundTensorPerturbation (fun y ↦ (t:ℝ)*a y) x
  let rf : Icc (-delta) delta → Base → ℝ := fun t x ↦ rho x+(t:ℝ)*b x
  obtain ⟨v,hv,hvne,hev,hvn,hvo,mu,hmu,hval,hpartial,hderiv⟩ := sphere_normalized_global_limit
    Af rf (fun t ↦ (hpos t t.property).1) (fun t ↦ (hpos t t.property).2.1)
    (fun t ↦ (hpos t t.property).2.2.1) (fun t ↦ (hpos t t.property).2.2.2.1)
    (fun t ↦ (hpos t t.property).2.2.2.2) hrjoint lam hCjoint hVjoint s s0 hst
    (fun j ↦ w (shift j)) (fun j ↦ hw _) (fun j ↦ he _) (fun j ↦ hn _) u hu (fun j ↦ ho _)
  have hAzero : Af s0 = A := by
    funext x
    simp [Af,s0,roundTensorPerturbation]
  have hrzero : rf s0 = rho := by
    funext x
    simp [rf,s0]
  rw [hAzero,hrzero] at hev
  rw [hrzero] at hvn hvo
  exact ⟨v,hv,hvne,hev,hvn,hvo,shift ∘ mu,hshift.comp hmu,hval,hpartial,hderiv⟩

end
end Yau.Target

end OAI
