import OAI.Geometry.RCD.Heat.GaussianContinuousComparison
import OAI.Analysis.RCDHeat.ExistingAnalytic
import Mathlib.Topology.Order.ProjIcc

namespace OAI

/-! # Gaussian comparison for functions on the transport time interval -/

open Set
noncomputable section
namespace RegularPointCoordinates

theorem unitInterval_gaussian_comparison (u : Time → ℝ) {c : ℝ} (hc : 0 ≤ c)
    (hu : UpperSemicontinuous u) (hpos : ∀ t, 0 ≤ u t)
    (hm : ∀ s t : Time, Real.exp (-c*((s:ℝ)-(t:ℝ))^2/8)*(u s+u t)/2 ≤
      u (timeSegment s t midpointTime)) (t : Time) :
    (if c=0 then (1-(t:ℝ))*u 0+(t:ℝ)*u 1
      else hyperbolicChord (Real.sqrt c) (u 0) (u 1) t) ≤ u t := by
  let p : ℝ → Time := projIcc 0 1 (by norm_num)
  let v : ℝ → ℝ := u ∘ p
  have hp (r : Time) : p r=r := projIcc_val _ r
  have h0 : v 0=u 0 := congrArg u (hp 0)
  have h1 : v 1=u 1 := congrArg u (hp 1)
  have hp0 : p 0=0 := hp 0
  have hp1 : p 1=1 := hp 1
  have hvm : ∀ x ∈ Icc (0:ℝ) 1, ∀ y ∈ Icc (0:ℝ) 1,
      Real.exp (-c*(x-y)^2/8)*(v x+v y)/2 ≤ v ((x+y)/2) := by
    intro x hx y hy
    let s : Time := ⟨x,hx⟩
    let t : Time := ⟨y,hy⟩
    have hs : p x=s := projIcc_of_mem _ hx
    have ht : p y=t := projIcc_of_mem _ hy
    have hmid : p ((x+y)/2)=timeSegment s t midpointTime := by
      have hxy : (x+y)/2 ∈ Icc (0:ℝ) 1 := ⟨by linarith [hx.1,hy.1],by linarith [hx.2,hy.2]⟩
      rw [show p ((x+y)/2)=⟨(x+y)/2,hxy⟩ from projIcc_of_mem _ hxy]
      apply Subtype.ext
      change (x+y)/2=(1-(1/2:ℝ))*x+(1/2:ℝ)*y
      ring
    simpa only [v,Function.comp_def,hs,ht,hmid] using hm s t
  have hv : UpperSemicontinuousOn v (Icc 0 1) :=
    (hu.comp continuous_projIcc).upperSemicontinuousOn _
  have hh := gaussian_continuous_comparison v hc hv (fun x _ => hpos (p x)) hvm t.property
  simpa only [h0,h1,v,Function.comp_def,hp,hp0,hp1] using hh

end RegularPointCoordinates

end

end OAI
