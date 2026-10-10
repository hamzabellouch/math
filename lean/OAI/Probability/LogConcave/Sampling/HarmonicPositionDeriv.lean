import Mathlib
import OAI.Probability.LogConcave.Sampling.ProbabilityNodes

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory
open scoped NNReal

lemma harmonic_position_deriv {d : ℕ} {H : Point d → ℝ}
    (hH : Differentiable ℝ H) (Ξ : Point (d+d) → ℝ → Point (d+d))
    (hder : ∀y v,v∈Icc (0:ℝ) 1 → HasDerivWithinAt (Ξ y)
      (skewLieField (productPotential H (fun z : Point d => ‖z‖^2/2))
        (harmonicSkew d) (Ξ y v)) (Icc (0:ℝ) 1) v)
    (y : Point (d+d)) {v : ℝ} (hv : v∈Icc (0:ℝ) 1) :
    HasDerivWithinAt (fun u => (productPointEquiv d d (Ξ y u)).1)
      (productPointEquiv d d (Ξ y v)).2 (Icc (0:ℝ) 1) v := by
  have h := (productPointEquiv d d).toContinuousLinearMap.hasFDerivAt.comp_hasDerivWithinAt v (hder y v hv)
  change HasDerivWithinAt (fun u => productPointEquiv d d (Ξ y u))
    (productPointEquiv d d (skewLieField
      (productPotential H (fun z : Point d => ‖z‖^2/2)) (harmonicSkew d) (Ξ y v))) _ _ at h
  rw [harmonicSkew_field hH] at h
  exact h.fst

theorem kernel_action_derivative {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r T : ℝ} (hr : 0<r)
    (hl : (lam:ℝ)*r^2≤1/2) (hT0 : 0≤T) (hT1 : T<1)
    (t : Icc (0:ℝ) T) (y G : Point d)
    (Ξ : Point (d+d) → ℝ → Point (d+d)) (hinit : ∀p,Ξ p 0=p)
    (hder : ∀p v,v∈Icc (0:ℝ) 1 → HasDerivWithinAt (Ξ p)
      (skewLieField (centeringPotential F x r t) (harmonicSkew d) (Ξ p v)) (Icc (0:ℝ) 1) v) :
    let p := (productPointEquiv d d).symm
      (terminalBackward hF x hr.le hl hT0 hT1 (t,y),G)
    let W := fun v => (productPointEquiv d d (Ξ p v)).1
    HasDerivWithinAt (fun v => probabilityTransport hF x hr.le hl hT0 hT1
      t ⟨T,hT0,le_rfl⟩ (W v)-W v)
      ((terminalJacobian hF x hr hl hT0 hT1 (t,y)-ContinuousLinearMap.id ℝ (Point d)) G)
      (Icc (0:ℝ) 1) 0 := by
  intro p W
  have hH := (interpolationPotential_smooth hF x hr.le hl t.2.1 (t.2.2.trans_lt hT1)).differentiable
    (by norm_cast)
  have hw := harmonic_position_deriv hH Ξ hder p (by norm_num : (0:ℝ)∈Icc (0:ℝ) 1)
  rw [hinit] at hw
  change HasDerivWithinAt W ((productPointEquiv d d) p).2 (Icc (0:ℝ) 1) 0 at hw
  have hp : ((productPointEquiv d d) p).2 = G :=
    congrArg Prod.snd ((productPointEquiv d d).apply_symm_apply _)
  rw [hp] at hw
  have hw0 : W 0=terminalBackward hF x hr.le hl hT0 hT1 (t,y) := by
    dsimp [W]
    rw [hinit]
    exact (congrArg Prod.fst ((productPointEquiv d d).apply_symm_apply _))
  have hf := (probabilityTransport_smooth hF x hr.le hl hT0 hT1 t ⟨T,hT0,le_rfl⟩).differentiable
    (by norm_cast)
  have he := ((hf (W 0)).hasFDerivAt.comp_hasDerivWithinAt 0 hw).sub hw
  rw [hw0,←terminalJacobian_eq hF x hr hl hT0 hT1 t y] at he
  convert he using 1 <;> rfl
end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory TensorEnergy Quadrature
open scoped Classical BigOperators NNReal RealInnerProductSpace

local instance : DecidableEq Unit := Classical.decEq _

lemma meanOutputProjection_correction {d : ℕ} (f : Point d → Point d)
    (y : Point (d+d)) :
    meanOutputProjection d (tensorVector (jointCorrectionArray f) y)=
      f (productPointEquiv d d y).1 := by
  ext i
  change TensorEnergy.zeroExtend (slotEmbedding (fun _ : Unit => leftCoordinates d d))
    (fun a => vectorArray f a (coordinateProjection (leftCoordinates d d) y))
    (slotEmbedding (fun _ : Unit => leftCoordinates d d) (fun _ => i))=_
  rw [zeroExtend_apply,coordinateProjection_left]
  simp only [vectorArray,EuclideanSpace.basisFun_inner]

lemma projection_derivativeStencil {I E G : Type*} [Fintype I] [DecidableEq I]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
    (L : E →L[ℝ] G) (u : I → ℝ) (ψ : ℝ) (v : I → E) :
    L (derivativeStencil u ψ v)=derivativeStencil u ψ (fun i => L (v i)) := by
  simp only [derivativeStencil,map_sum,map_smul]

lemma kernel_action_lie_projection {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r R T : ℝ} (hr : 0<r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (hR : 0<R) (hRT : R^2≤1-T^2)
    (hT0 : 0≤T) (hT1 : T<1) (t : Icc (0:ℝ) T) (y G : Point d)
    (Ξ : Point (d+d) → ℝ → Point (d+d)) (hinit : ∀p,Ξ p 0=p)
    (hder : ∀p v,v∈Icc (0:ℝ) 1 → HasDerivWithinAt (Ξ p)
      (skewLieField (centeringPotential F x r t) (harmonicSkew d) (Ξ p v)) (Icc (0:ℝ) 1) v) :
    let p := (productPointEquiv d d).symm
      (terminalBackward hF x hr.le hl hT0 hT1 (t,y),G)
    let A := jointCorrectionArray (fun z => probabilityTransport hF x hr.le hl hT0 hT1
      t ⟨T,hT0,le_rfl⟩ z-z)
    meanOutputProjection d (tensorVector (iterTensorLie (centeringPotential F x r t)
      (harmonicSkew d) A 1) p)=
      (terminalJacobian hF x hr hl hT0 hT1 (t,y)-ContinuousLinearMap.id ℝ (Point d)) G := by
  intro p A
  have hH : PolySmooth (centeringPotential F x r t) := productPotential_polySmooth
    (interpolationPotential_polySmooth hF x hr hlam hl t.2.1 (t.2.2.trans_lt hT1))
      (gaussianPotential_polySmooth d)
  have hp := lie_vector_chain hH (harmonicSkew d) A (harmonicSkew_polySmooth d)
    (jointCorrectionArray_polySmooth hF x hr hlam hl hR hRT hT0 hT1 t ⟨T,hT0,le_rfl⟩)
    (jointSkew_skew _ 1) (Ξ p) (hder p) 0 (by norm_num : (0:ℝ)∈Icc (0:ℝ) 1)
  have hproj := (meanOutputProjection d).hasFDerivAt.comp_hasDerivWithinAt 0 hp
  change HasDerivWithinAt (fun v => meanOutputProjection d
    (tensorVector A (Ξ p v))) (meanOutputProjection d (tensorVector
      (iterTensorLie (centeringPotential F x r t) (harmonicSkew d) A 1) (Ξ p 0)))
      (Icc (0:ℝ) 1) 0 at hproj
  simp only [A,meanOutputProjection_correction,hinit] at hproj
  have hd := kernel_action_derivative hF x hr hl hT0 hT1 t y G Ξ hinit hder
  have hu := uniqueDiffOn_Icc (by norm_num : (0:ℝ)<1) 0 (by norm_num)
  exact (hproj.derivWithin hu).symm.trans (hd.derivWithin hu)

theorem kernel_action_stencil_rms {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r R T : ℝ} (hr : 0<r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (hR : 0<R) (hRT : R^2≤1-T^2)
    (hT0 : 0≤T) (hT1 : T<1) (t : Icc (0:ℝ) T)
    (Ξ : Point (d+d) → ℝ → Point (d+d)) (hinit : ∀p,Ξ p 0=p)
    (hder : ∀p v,v∈Icc (0:ℝ) 1 → HasDerivWithinAt (Ξ p)
      (skewLieField (centeringPotential F x r t) (harmonicSkew d) (Ξ p v)) (Icc (0:ℝ) 1) v)
    (hm : Measurable (fun p : ℝ × Point (d+d) => Ξ p.2 p.1))
    (hlaw : ∀v∈Icc (0:ℝ) 1,(gibbs (centeringPotential F x r t)).map (fun y => Ξ y v)=
      gibbs (centeringPotential F x r t))
    (n : ℕ) (hn : 1≤n) (ψ : ℝ) (hψ : 0<ψ) (hψn : ψ*n≤1) :
    let C := fun z => probabilityTransport hF x hr.le hl hT0 hT1 t ⟨T,hT0,le_rfl⟩ z-z
    let W := fun v p => (productPointEquiv d d (Ξ p v)).1
    let K := fun p => (terminalJacobian hF x hr hl hT0 hT1
      (t,terminalForward hF x hr.le hl hT0 hT1 (t,(productPointEquiv d d p).1))-
        ContinuousLinearMap.id ℝ (Point d)) (productPointEquiv d d p).2
    Integrable (fun p => ‖derivativeStencil (angleNodes n) ψ
      (fun i => C (W (ψ*angleNodes n i) p))-K p‖^2)
        (gibbs (centeringPotential F x r t)) ∧
    (∫p,‖derivativeStencil (angleNodes n) ψ
      (fun i => C (W (ψ*angleNodes n i) p))-K p‖^2
        ∂gibbs (centeringPotential F x r t))≤
      ((∑i,|derivativeWeight (angleNodes n) i|)/ψ)^2*
        (((ψ*n)^(n+1)/(n.factorial:ℝ))^2*
          ((d*((lam:ℝ)*r^2)^2)*(R⁻¹)^(4*(n+1))*harmonicCorrectionBudget (n+1))) := by
  intro C W K
  let A := jointCorrectionArray C
  let J := fun k v p => tensorVector (iterTensorLie (centeringPotential F x r t)
    (harmonicSkew d) A k) (Ξ p v)
  let E := fun p => derivativeStencil (angleNodes n) ψ (fun i => J 0 (ψ*angleNodes n i) p)-J 1 0 p
  have hH : PolySmooth (centeringPotential F x r t) := productPotential_polySmooth
    (interpolationPotential_polySmooth hF x hr hlam hl t.2.1 (t.2.2.trans_lt hT1))
      (gaussianPotential_polySmooth d)
  have hA := jointCorrectionArray_polySmooth hF x hr hlam hl hR hRT hT0 hT1 t ⟨T,hT0,le_rfl⟩
  have hJ (k : ℕ) (v : ℝ) : Measurable (J k v) := liePathJet_measurable hH
    (harmonicSkew d) A (harmonicSkew_polySmooth d) hA Ξ hm k v
  have hj0 (v : ℝ) (p : Point (d+d)) : meanOutputProjection d (J 0 v p)=C (W v p) :=
    meanOutputProjection_correction C (Ξ p v)
  have hj1 (p : Point (d+d)) : meanOutputProjection d (J 1 0 p)=K p := by
    have h := kernel_action_lie_projection hF x hr hlam hl hR hRT hT0 hT1 t
      (terminalForward hF x hr.le hl hT0 hT1 (t,(productPointEquiv d d p).1))
      (productPointEquiv d d p).2 Ξ hinit hder
    dsimp only at h
    rw [terminalBackward_forward hF x hr.le hl hT0 hT1,
      (productPointEquiv d d).symm_apply_apply] at h
    dsimp only [J]
    rw [hinit]
    exact h
  have he (p : Point (d+d)) : derivativeStencil (angleNodes n) ψ
      (fun i => C (W (ψ*angleNodes n i) p))-K p=meanOutputProjection d (E p) := by
    dsimp only [E]
    rw [map_sub,projection_derivativeStencil]
    simp only [hj0,hj1]
  have hb := harmonic_correction_stencil_rms hF x hr hlam hl hR hRT hT0 hT1
    t ⟨T,hT0,le_rfl⟩ t Ξ hder hm hlaw n hn ψ hψ hψn
  have hE : Measurable E := (Finset.measurable_sum _ (fun i _ =>
    (hJ 0 (ψ*angleNodes n i)).const_smul (derivativeWeight (angleNodes n) i/ψ))).sub (hJ 1 0)
  have hab (p : Point (d+d)) : ‖meanOutputProjection d (E p)‖^2≤‖E p‖^2 :=
    pow_le_pow_left₀ (norm_nonneg _) (finiteCoordinateProjection_norm_le _ _) 2
  simp_rw [he]
  have hi := hb.1.mono' (((meanOutputProjection d).continuous.measurable.comp hE).norm.pow_const 2).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun p => by simpa only [Real.norm_eq_abs,abs_sq,Function.comp_def,E,J,A,C] using hab p))
  exact ⟨hi,(integral_mono hi hb.1 hab).trans hb.2⟩

end LogConcaveSampling

end

end

end

end OAI
