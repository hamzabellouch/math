import Mathlib
import OAI.Analysis.BiholderTransport.Coordinates.ExpNonconjugacy

namespace OAI

noncomputable section

namespace WeakMTWTransport

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

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Filter Set
open scoped Topology

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

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

section
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma exp_kernel_radial_orthogonal {x : M} {p k : TangentSpace 𝓘(ℝ,Model n) x}
    (hk : mfderiv 𝓘(ℝ,TangentSpace 𝓘(ℝ,Model n) x) 𝓘(ℝ,Model n) (riemannianExp x) p k=0) :
    inner ℝ p k=0 := by
  let V := TangentSpace 𝓘(ℝ,Model n) x
  have hline : HasDerivAt (fun s : ℝ => p+s • k) k 0 := by
    convert! (hasDerivAt_const (0:ℝ) p).add ((hasDerivAt_id (0:ℝ)).smul_const k) using 1
    simp
  let F : V → M := fun v => (sprayFlow 1 (⟨x,v⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1
  have hf : riemannianExp x=F := funext (fun v => riemannianExp_eq_sprayFlow x v)
  have hkF : mfderiv 𝓘(ℝ,V) 𝓘(ℝ,Model n) F p k=0 := by
    rw [←hf]
    exact hk
  have hs : ContMDiff 𝓘(ℝ,V) 𝓘(ℝ,Model n) ∞ F := by
    rw [←hf]
    exact contMDiff_riemannianExp_fiber x
  have he := ((hs (p+(0:ℝ) • k)).mdifferentiableAt (by simp)).hasMFDerivAt
  have hcomp := he.comp 0 hline.hasFDerivAt.hasMFDerivAt
  have hz : mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,Model n) (fun s : ℝ => F (p+s • k)) 0 1=0 := by
    have hc := hcomp.mfderiv
    simp only [Function.comp_def] at hc
    rw [hc]
    change (mfderiv 𝓘(ℝ,V) 𝓘(ℝ,Model n) F (p+(0:ℝ) • k)) ((1:ℝ) • k)=0
    rw [one_smul]
    convert! hkF using 1
    congr 1
    exact mfderiv_congr_point (by simp only [zero_smul,add_zero])
  have H := sprayFlow_gauss x p k (1:ℝ)
  rw [hz] at H
  have H' : inner ℝ (sprayFlow 1 (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).2
      (0 : TangentSpace 𝓘(ℝ,Model n) (sprayFlow 1 (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1)=inner ℝ p k := by
    convert! H using 1
    simp only [one_mul]
  simpa only [inner_zero_right] using H'.symm
end

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma exp_mfderiv_apply_eq_coordinate (x : M) (p k : TangentSpace 𝓘(ℝ,Model n) x) :
    mfderiv 𝓘(ℝ,TangentSpace 𝓘(ℝ,Model n) x) 𝓘(ℝ,Model n) (riemannianExp x) p k=
      (fderiv ℝ (fun v => extChartAt 𝓘(ℝ,Model n) (riemannianExp x p) (riemannianExp x v)) p :
        TangentSpace 𝓘(ℝ,Model n) x →L[ℝ] Model n) k := by
  have H := ((contMDiff_riemannianExp_fiber x p).mdifferentiableAt (by simp)).mfderiv
  have HH := congrArg (fun L => L k) H
  simp only [mfld_simps,chartAt_self_eq,Function.comp_def,fderivWithin_univ] at HH ⊢
  convert! HH using 1

end WeakMTWTransport

end

end OAI
