import Mathlib
import OAI.Analysis.BiholderTransport.LinearAlgebra.HessianSmooth
import OAI.Analysis.BiholderTransport.Contact.UpperContactIteratedDeriv

namespace OAI

noncomputable section

open Set MeasureTheory Manifold Bundle
open scoped ContDiff Manifold ENNReal NNReal Topology

open Set Filter
open scoped Topology NNReal

open Set Filter
open scoped Topology

open Set Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set
open scoped Topology

open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff Manifold Bundle

open Set Filter ContinuousLinearMap InnerProductSpace
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff
open scoped NNReal

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology
open MeasureTheory
open scoped ContDiff ENNReal

open Set Filter Manifold Bundle ContinuousLinearMap MeasureTheory
open scoped Topology ContDiff Manifold Bundle ENNReal

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology Manifold

open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff Manifold Bundle

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold Bundle

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold Bundle

open Set Filter Bundle
open scoped Topology Bundle

open scoped Topology
open Function Manifold Set
open Manifold Bundle
open scoped Manifold Bundle
open Set

open Set Filter
open scoped Topology ContDiff

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

namespace WeakMTWTransport
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma upper_contact_block_trial {f : E → ℝ} {B : E×F → ℝ} {x : E} {q : F}
    (hf : ContDiffAt ℝ 2 f x) (hB : ContDiffAt ℝ 2 B (x,q))
    (hle : ∀ᶠ z in 𝓝 (x,q), f z.1≤B z) (heq : f x=B (x,q))
    (v : E) (k : F) (t : ℝ) :
    fderiv ℝ (fderiv ℝ f) x v v ≤
      fderiv ℝ (fderiv ℝ B) (x,q) (v,0) (v,0) +
      2*t*fderiv ℝ (fderiv ℝ B) (x,q) (v,0) (0,k) +
      t^2*fderiv ℝ (fderiv ℝ B) (x,q) (0,k) (0,k) := by
  let L : ℝ → E×F := fun s => (x,q)+s • (v,t • k)
  have hLc : ContDiffAt ℝ 2 L 0 := contDiffAt_const.add (contDiffAt_id.smul contDiffAt_const)
  have hL0 : L 0=(x,q) := by simp [L]
  have hLlim : Tendsto L (𝓝 0) (𝓝 (x,q)) := by
    simpa only [hL0] using hLc.continuousAt.tendsto
  have hBc : ContDiffAt ℝ 2 (B ∘ L) 0 := by
    have hB' : ContDiffAt ℝ 2 B (L 0) := by rwa [hL0]
    exact hB'.comp 0 hLc
  have hfc : ContDiffAt ℝ 2 (fun s : ℝ => f (x+s • v)) 0 := by
    have hf' : ContDiffAt ℝ 2 f (x+(0:ℝ) • v) := by simpa only [zero_smul,add_zero] using hf
    exact hf'.comp 0 (contDiffAt_const.add (contDiffAt_id.smul contDiffAt_const))
  have hle' : ∀ᶠ s : ℝ in 𝓝 0, f (x+s • v) ≤ (B ∘ L) s :=
    hLlim.eventually hle
  have heq' : f (x+(0:ℝ) • v)=(B ∘ L) 0 := by simpa only [Function.comp_apply,hL0,zero_smul,add_zero] using heq
  have H := upper_contact_iteratedDeriv_two hfc hBc hle' heq'
  change iteratedDeriv 2 (fun s : ℝ => f (x+s • v)) 0 ≤
    iteratedDeriv 2 (fun s : ℝ => B ((x,q)+s • (v,t • k))) 0 at H
  rw [iteratedDeriv_two_affine_line hf,iteratedDeriv_two_affine_line hB] at H
  have hv : (v,t • k)=(v,0)+t • ((0:E),k) := by ext <;> simp
  have hs := (hB.isSymmSndFDerivAt (by simp)).eq ((0:E),k) (v,(0:F))
  rw [hv] at H
  simp only [map_add,map_smul,add_apply,smul_apply,smul_eq_mul] at H
  rw [hs] at H
  nlinarith

lemma upper_contact_block_nonneg {f : E → ℝ} {B : E×F → ℝ} {x : E} {q : F}
    (hf : ContDiffAt ℝ 2 f x) (hB : ContDiffAt ℝ 2 B (x,q))
    (hle : ∀ᶠ z in 𝓝 (x,q), f z.1≤B z) (heq : f x=B (x,q)) (k : F) :
    0≤fderiv ℝ (fderiv ℝ B) (x,q) (0,k) (0,k) := by
  simpa only [show ((0:E),(0:F))=(0:E×F) from rfl, map_zero, zero_apply, one_mul,
    zero_add, one_pow, mul_zero] using upper_contact_block_trial hf hB hle heq 0 k 1

lemma upper_contact_block_positive {f : E → ℝ} {B : E×F → ℝ} {x : E} {q : F}
    (hf : ContDiffAt ℝ 2 f x) (hB : ContDiffAt ℝ 2 B (x,q))
    (hle : ∀ᶠ z in 𝓝 (x,q), f z.1≤B z) (heq : f x=B (x,q)) (v : E) (k : F)
    (hk : fderiv ℝ (fderiv ℝ B) (x,q) (v,0) (0,k)≠0) :
    0<fderiv ℝ (fderiv ℝ B) (x,q) (0,k) (0,k) :=
  nonzero_pairing_positive_test (upper_contact_block_nonneg hf hB hle heq k) hk
    (upper_contact_block_trial hf hB hle heq v k)

lemma upper_contact_block_schur {f : E → ℝ} {B : E×F → ℝ} {x : E} {q : F}
    (hf : ContDiffAt ℝ 2 f x) (hB : ContDiffAt ℝ 2 B (x,q))
    (hle : ∀ᶠ z in 𝓝 (x,q), f z.1≤B z) (heq : f x=B (x,q)) (v : E) (k : F)
    (hk : fderiv ℝ (fderiv ℝ B) (x,q) (v,0) (0,k)≠0) :
    fderiv ℝ (fderiv ℝ f) x v v ≤
      fderiv ℝ (fderiv ℝ B) (x,q) (v,0) (v,0) -
      (fderiv ℝ (fderiv ℝ B) (x,q) (v,0) (0,k))^2/
        fderiv ℝ (fderiv ℝ B) (x,q) (0,k) (0,k) :=
  positive_schur_test (upper_contact_block_positive hf hB hle heq v k hk)
    (upper_contact_block_trial hf hB hle heq v k)

end WeakMTWTransport

end

end OAI
