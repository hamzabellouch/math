import OAI.NumberTheory.CubicMoment.Theta.CubicThetaGridDifferentiation

namespace OAI

/-! Actual coordinate differentiability of the infinite Eisenstein
series, and continuity of its constant-subtracted vertical slice. -/
noncomputable section
open Filter
open scoped Topology
namespace CubicFirstMoment

theorem cubicThetaEisenstein_coordinate_hasDerivAt (k : CubicThetaAxis)
    (s : ℂ) (hs : 2<s.re) (x y : ℝ) {v : ℝ} (hv : 0<v) :
    HasDerivAt (fun t => cubicThetaEisenstein (cubicThetaCoordinateLine k x y v t) s)
      (∑' cd : Eisenstein × Eisenstein, deriv
        (fun t => cubicThetaEisensteinGridTerm cd (cubicThetaCoordinateLine k x y v t) s)
        (cubicThetaCoordinateCenter k x y v)) (cubicThetaCoordinateCenter k x y v) := by
  obtain ⟨r,hr,u₁,u₂,hu₁,_,hbound⟩ := cubicThetaCoordinate_local_jets k s hs x y hv
  have hx : cubicThetaCoordinateCenter k x y v ∈
      Set.Ioo (cubicThetaCoordinateCenter k x y v-r) (cubicThetaCoordinateCenter k x y v+r) :=
    ⟨by linarith,by linarith⟩
  have h₀ : Summable (fun cd : Eisenstein × Eisenstein => cubicThetaEisensteinGridTerm cd
      (cubicThetaCoordinateLine k x y v (cubicThetaCoordinateCenter k x y v)) s) := by
    simpa only [cubicThetaCoordinateLine_center] using
      (cubicThetaEisensteinGrid_summable (p:=cubicThetaCartesianPoint x y v) hv hs)
  have hd := hasDerivAt_tsum_of_isPreconnected hu₁ isOpen_Ioo
    (convex_Ioo _ _).isPreconnected
    (fun cd t ht => (cubicThetaCoordinateLine_analytic k cd s x y v t
      (hbound cd t ht).1).differentiableAt.hasDerivAt)
    (fun cd t ht => (hbound cd t ht).2.1) hx h₀ hx
  simpa only [←cubicThetaEisenstein_eq_grid] using hd

theorem cubicThetaEisenstein_coordinate_twice_differentiable (k : CubicThetaAxis)
    (s : ℂ) (hs : 2<s.re) (x y : ℝ) {v : ℝ} (hv : 0<v) :
    DifferentiableAt ℝ
      (fun t => cubicThetaEisenstein (cubicThetaCoordinateLine k x y v t) s)
      (cubicThetaCoordinateCenter k x y v) ∧
    DifferentiableAt ℝ
      (deriv (fun t => cubicThetaEisenstein (cubicThetaCoordinateLine k x y v t) s))
      (cubicThetaCoordinateCenter k x y v) := by
  obtain ⟨r,hr,u₁,u₂,hu₁,hu₂,hbound⟩ := cubicThetaCoordinate_local_jets k s hs x y hv
  have hx : cubicThetaCoordinateCenter k x y v ∈
      Set.Ioo (cubicThetaCoordinateCenter k x y v-r) (cubicThetaCoordinateCenter k x y v+r) :=
    ⟨by linarith,by linarith⟩
  have h₀ : Summable (fun cd : Eisenstein × Eisenstein => cubicThetaEisensteinGridTerm cd
      (cubicThetaCoordinateLine k x y v (cubicThetaCoordinateCenter k x y v)) s) := by
    simpa only [cubicThetaCoordinateLine_center] using
      (cubicThetaEisensteinGrid_summable (p:=cubicThetaCartesianPoint x y v) hv hs)
  have h := cubicTheta_twice_hasDerivAt_tsum hu₁ hu₂ hx
    (fun cd t ht => cubicThetaCoordinateLine_analytic k cd s x y v t (hbound cd t ht).1)
    (fun cd t ht => (hbound cd t ht).2.1) (fun cd t ht => (hbound cd t ht).2.2) h₀
  simpa only [←cubicThetaEisenstein_eq_grid] using
    And.intro h.1.differentiableAt h.2.1.differentiableAt

theorem cubicThetaEisenstein_continuous_height {s : ℂ} (hs : 2<s.re) (z : ℂ) :
    ContinuousOn (fun v : ℝ => cubicThetaEisenstein (z,v) s) (Set.Ioi 0) := by
  intro v hv
  have h := (cubicThetaEisenstein_coordinate_hasDerivAt .height s hs z.re z.im hv).continuousAt
  have he (t : ℝ) : cubicThetaCartesianPoint z.re z.im t=(z,t) := by
    apply Prod.ext
    · apply Complex.ext <;> simp [cubicThetaCartesianPoint]
    · rfl
  simpa only [cubicThetaCoordinateLine,cubicThetaCoordinateCenter,he] using h.continuousWithinAt

lemma cubicThetaEisensteinConstantMode_continuousAt {s : ℂ} (hs : 1<s.re)
    {v : ℝ} (hv : 0<v) : ContinuousAt (fun t => cubicThetaEisensteinConstantMode t s) v := by
  let C : ℂ := ((2*Real.pi/(9*Real.sqrt 3):ℂ)/(s-1))*cubicThetaConstantDirichlet s
  have hG : ContinuousAt (fun t : ℝ => (t:ℂ)^s+C*(t:ℂ)^(2-s)) v :=
    (cubicThetaHeightPower_hasDerivAt s hv).continuousAt.add
      ((cubicThetaHeightPower_hasDerivAt (2-s) hv).continuousAt.const_mul C)
  have he : (fun t => cubicThetaEisensteinConstantMode t s) =ᶠ[𝓝 v]
      (fun t : ℝ => (t:ℂ)^s+C*(t:ℂ)^(2-s)) := by
    filter_upwards [eventually_gt_nhds hv] with t ht
    rw [cubicThetaEisensteinConstantMode_eq ht hs]
    dsimp [C]
    ring
  exact (continuousAt_congr he).mpr hG

theorem cubicThetaEisensteinRemainder_continuous_height {s : ℂ} (hs : 2<s.re) (z : ℂ) :
    ContinuousOn (fun v : ℝ => cubicThetaEisenstein (z,v) s-
      cubicThetaEisensteinConstantMode v s) (Set.Ioi 0) :=
  (cubicThetaEisenstein_continuous_height hs z).sub
    (fun _ hv => (cubicThetaEisensteinConstantMode_continuousAt (by linarith) hv).continuousWithinAt)

end CubicFirstMoment

end

end OAI
