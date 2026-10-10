import Mathlib
import OAI.Probability.LogConcave.Numerics.ReanchorWeight
import OAI.Probability.LogConcave.Sampling.HarmonicPositionDeriv

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory TensorEnergy Quadrature
open scoped Classical BigOperators NNReal

local instance : DecidableEq Unit := Classical.decEq _

def kernelTransportAction {d : ℕ} (f : Point d → Point d) (p : Point (d+d)) : Point d :=
  (fderiv ℝ f (productPointEquiv d d p).1) (productPointEquiv d d p).2-
    (productPointEquiv d d p).2

lemma kernel_action_between_derivative {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r T : ℝ} (hr : 0<r)
    (hl : (lam:ℝ)*r^2≤1/2) (hT0 : 0≤T) (hT1 : T<1)
    (s e : Icc (0:ℝ) T) (p : Point (d+d))
    (Ξ : Point (d+d) → ℝ → Point (d+d)) (hinit : ∀p,Ξ p 0=p)
    (hder : ∀p v,v∈Icc (0:ℝ) 1 → HasDerivWithinAt (Ξ p)
      (skewLieField (centeringPotential F x r s) (harmonicSkew d) (Ξ p v)) (Icc (0:ℝ) 1) v) :
    let fw := probabilityTransport hF x hr.le hl hT0 hT1 s e
    let W := fun v => (productPointEquiv d d (Ξ p v)).1
    HasDerivWithinAt (fun v => fw (W v)-W v) (kernelTransportAction fw p) (Icc (0:ℝ) 1) 0 := by
  intro fw W
  have hH := (interpolationPotential_smooth hF x hr.le hl s.2.1 (s.2.2.trans_lt hT1)).differentiable
    (by norm_cast)
  have hw := harmonic_position_deriv hH Ξ hder p (by norm_num : (0:ℝ)∈Icc (0:ℝ) 1)
  rw [hinit] at hw
  have hw0 : W 0=(productPointEquiv d d p).1 := by dsimp [W]; rw [hinit]
  have hf := (probabilityTransport_smooth hF x hr.le hl hT0 hT1 s e).differentiable (by norm_cast)
  have he := ((hf (W 0)).hasFDerivAt.comp_hasDerivWithinAt 0 hw).sub hw
  rw [hw0] at he
  exact he

lemma kernel_between_lie_projection {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r R T : ℝ} (hr : 0<r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (hR : 0<R) (hRT : R^2≤1-T^2)
    (hT0 : 0≤T) (hT1 : T<1) (s e : Icc (0:ℝ) T)
    (Ξ : Point (d+d) → ℝ → Point (d+d)) (hinit : ∀p,Ξ p 0=p)
    (hder : ∀p v,v∈Icc (0:ℝ) 1 → HasDerivWithinAt (Ξ p)
      (skewLieField (centeringPotential F x r s) (harmonicSkew d) (Ξ p v)) (Icc (0:ℝ) 1) v)
    (p : Point (d+d)) :
    let fw := probabilityTransport hF x hr.le hl hT0 hT1 s e
    let A := jointCorrectionArray (fun z => fw z-z)
    meanOutputProjection d (tensorVector (iterTensorLie (centeringPotential F x r s)
      (harmonicSkew d) A 1) p)=kernelTransportAction fw p := by
  intro fw A
  have hH : PolySmooth (centeringPotential F x r s) := productPotential_polySmooth
    (interpolationPotential_polySmooth hF x hr hlam hl s.2.1 (s.2.2.trans_lt hT1))
      (gaussianPotential_polySmooth d)
  have hp := lie_vector_chain hH (harmonicSkew d) A (harmonicSkew_polySmooth d)
    (jointCorrectionArray_polySmooth hF x hr hlam hl hR hRT hT0 hT1 s e)
    (jointSkew_skew _ 1) (Ξ p) (hder p) 0 (by norm_num : (0:ℝ)∈Icc (0:ℝ) 1)
  have hproj := (meanOutputProjection d).hasFDerivAt.comp_hasDerivWithinAt 0 hp
  change HasDerivWithinAt (fun v => meanOutputProjection d
    (tensorVector A (Ξ p v))) (meanOutputProjection d (tensorVector
      (iterTensorLie (centeringPotential F x r s) (harmonicSkew d) A 1) (Ξ p 0)))
      (Icc (0:ℝ) 1) 0 at hproj
  simp only [A,meanOutputProjection_correction,hinit] at hproj
  have hd := kernel_action_between_derivative hF x hr hl hT0 hT1 s e p Ξ hinit hder
  have hu := uniqueDiffOn_Icc (by norm_num : (0:ℝ)<1) 0 (by norm_num)
  exact (hproj.derivWithin hu).symm.trans (hd.derivWithin hu)

theorem kernel_action_between_stencil_rms {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r R T : ℝ} (hr : 0<r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (hR : 0<R) (hRT : R^2≤1-T^2)
    (hT0 : 0≤T) (hT1 : T<1) (s e : Icc (0:ℝ) T)
    (Ξ : Point (d+d) → ℝ → Point (d+d)) (hinit : ∀p,Ξ p 0=p)
    (hder : ∀p v,v∈Icc (0:ℝ) 1 → HasDerivWithinAt (Ξ p)
      (skewLieField (centeringPotential F x r s) (harmonicSkew d) (Ξ p v)) (Icc (0:ℝ) 1) v)
    (hm : Measurable (fun p : ℝ × Point (d+d) => Ξ p.2 p.1))
    (hlaw : ∀v∈Icc (0:ℝ) 1,(gibbs (centeringPotential F x r s)).map (fun y => Ξ y v)=
      gibbs (centeringPotential F x r s))
    (m : ℕ) (hm1 : 1 ≤ m) (ψ : ℝ) (hψ : 0<ψ) (hψm : ψ*m≤1) :
    let fw := probabilityTransport hF x hr.le hl hT0 hT1 s e
    let W := fun v p => (productPointEquiv d d (Ξ p v)).1
    let K := kernelTransportAction fw
    Measurable K ∧
    Integrable (fun p => ‖derivativeStencil (angleNodes m) ψ
      (fun i => fw (W (ψ*angleNodes m i) p)-W (ψ*angleNodes m i) p)-K p‖^2)
        (gibbs (centeringPotential F x r s)) ∧
    (∫p,‖derivativeStencil (angleNodes m) ψ
      (fun i => fw (W (ψ*angleNodes m i) p)-W (ψ*angleNodes m i) p)-K p‖^2
        ∂gibbs (centeringPotential F x r s))≤
      ((∑i,|derivativeWeight (angleNodes m) i|)/ψ)^2*
        (((ψ*m)^(m+1)/(m.factorial:ℝ))^2*
          ((d*((lam:ℝ)*r^2)^2)*(R⁻¹)^(4*(m+1))*harmonicCorrectionBudget (m+1))) := by
  intro fw W K
  let A := jointCorrectionArray (fun z => fw z-z)
  let J := fun k v p => tensorVector (iterTensorLie (centeringPotential F x r s)
    (harmonicSkew d) A k) (Ξ p v)
  let E := fun p => derivativeStencil (angleNodes m) ψ (fun i => J 0 (ψ*angleNodes m i) p)-J 1 0 p
  have hH : PolySmooth (centeringPotential F x r s) := productPotential_polySmooth
    (interpolationPotential_polySmooth hF x hr hlam hl s.2.1 (s.2.2.trans_lt hT1))
      (gaussianPotential_polySmooth d)
  have hA := jointCorrectionArray_polySmooth hF x hr hlam hl hR hRT hT0 hT1 s e
  have hJ (k : ℕ) (v : ℝ) : Measurable (J k v) := liePathJet_measurable hH
    (harmonicSkew d) A (harmonicSkew_polySmooth d) hA Ξ hm k v
  have hj0 (v : ℝ) (p : Point (d+d)) : meanOutputProjection d (J 0 v p)=fw (W v p)-W v p :=
    meanOutputProjection_correction _ (Ξ p v)
  have hj1 (p : Point (d+d)) : meanOutputProjection d (J 1 0 p)=K p := by
    dsimp only [J]
    rw [hinit]
    exact kernel_between_lie_projection hF x hr hlam hl hR hRT hT0 hT1 s e Ξ hinit hder p
  have hK : Measurable K := by
    have hh := (meanOutputProjection d).continuous.measurable.comp (hJ 1 0)
    simpa only [Function.comp_def,hj1] using hh
  refine ⟨hK,?_⟩
  have he (p : Point (d+d)) : derivativeStencil (angleNodes m) ψ
      (fun i => fw (W (ψ*angleNodes m i) p)-W (ψ*angleNodes m i) p)-K p=
        meanOutputProjection d (E p) := by
    dsimp only [E]
    rw [map_sub,projection_derivativeStencil]
    simp only [hj0,hj1]
  have hb := harmonic_correction_stencil_rms hF x hr hlam hl hR hRT hT0 hT1
    s e s Ξ hder hm hlaw m hm1 ψ hψ hψm
  have hE : Measurable E := (Finset.measurable_sum _ (fun i _ =>
    (hJ 0 (ψ*angleNodes m i)).const_smul (derivativeWeight (angleNodes m) i/ψ))).sub (hJ 1 0)
  have hab (p : Point (d+d)) : ‖meanOutputProjection d (E p)‖^2≤‖E p‖^2 :=
    pow_le_pow_left₀ (norm_nonneg _) (finiteCoordinateProjection_norm_le _ _) 2
  simp_rw [he]
  have hi := hb.1.mono' (((meanOutputProjection d).continuous.measurable.comp hE).norm.pow_const 2).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun p => by simpa only [Real.norm_eq_abs,abs_sq,Function.comp_def,E,J,A,fw] using hab p))
  exact ⟨hi,(integral_mono hi hb.1 hab).trans hb.2⟩
end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory Quadrature
open scoped Classical BigOperators NNReal

lemma finite_weighted_lipschitz {I X E : Type*} [Fintype I]
    [PseudoMetricSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (w : I → ℝ) (f : I → X → E) {K : ℝ≥0} (hf : ∀i,LipschitzWith K (f i)) :
    LipschitzWith ((∑i,‖w i‖₊)*K) (fun x => ∑i,w i • f i x) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm,←Finset.sum_sub_distrib]
  simp_rw [←smul_sub]
  calc
    _ ≤ ∑i,‖w i • (f i x-f i y)‖ := norm_sum_le _ _
    _ = ∑i,|w i| *dist (f i x) (f i y) := by simp only [norm_smul,Real.norm_eq_abs,dist_eq_norm]
    _ ≤ ∑i,|w i| *((K:ℝ)*dist x y) := Finset.sum_le_sum (fun i _ =>
      mul_le_mul_of_nonneg_left ((hf i).dist_le_mul x y) (abs_nonneg _))
    _ = _ := by simp only [←Finset.sum_mul,NNReal.coe_mul,NNReal.coe_sum,coe_nnnorm,Real.norm_eq_abs,mul_assoc]

def kernelActionPicard {d : ℕ} (F : Point d → ℝ) (x : Point d)
    (r T h ψ : ℝ) (n m N : ℕ) (s e : ProbabilityNode T h n)
    (p : Point d × Point d) : Point d :=
  derivativeStencil (angleNodes m) ψ (fun i =>
    let b := probabilityAnchoredPicard F x r T h n N e p.1 s
    let w := harmonicPicard F x r (probabilityNodeTime T h n s)
      (ψ*angleNodes m i) n N (b,p.2) (Fin.last n)
    probabilityAnchoredPicard F x r T h n (N+1) s w e-w)

theorem kernelActionPicard_lipschitz (n : ℕ) (hn : 0<n) :
    ∃A B : ℝ≥0,∀{d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0},
      Primitive F lam → ∀(x : Point d) {r T h ψ : ℝ},0≤r →
        (lam:ℝ)*r^2≤1/2 → 0<T → T<1 → 0<h → 0<ψ →
        ∀m : ℕ,ψ*m≤1 →
        A*probabilityMeanLipschitz lam r≤1/2 →
        B*probabilityMeanLipschitz lam r≤1/2 →
        ∀N : ℕ,∀s e : ProbabilityNode T h n,
      LipschitzWith ((∑i : Fin (m+1),‖derivativeWeight (angleNodes m) i/ψ‖₊)*
        (16*(A*probabilityMeanLipschitz lam r)))
        (kernelActionPicard F x r T h ψ n m N s e) := by
  obtain ⟨A,hA⟩ := probabilityAnchored_lipschitz n hn
  obtain ⟨B,hB⟩ := harmonicPicard_lipschitz n hn
  refine ⟨A,B,?_⟩
  intro d F lam hF x r T h ψ hr hl hT0 hT1 hh hψ m hψm hq hq' N s e
  have htime := probabilityNodeTime_mem hT0 hT1 hh hn s
  have hb : LipschitzWith 2 (fun p : Point d × Point d =>
      (probabilityAnchoredPicard F x r T h n N e p.1 s,p.2)) := by
    have h := (((LipschitzWith.eval s).comp (hA hF x hr hl hT0 hT1 hh hq N e).1).comp
      (LipschitzWith.prod_fst (α:=Point d) (β:=Point d))).prodMk
      (LipschitzWith.prod_snd (α:=Point d) (β:=Point d))
    convert h using 1 <;> first | rfl | norm_num
  have hc : LipschitzWith (2*(A*probabilityMeanLipschitz lam r))
      (fun w => probabilityAnchoredPicard F x r T h n (N+1) s w e-w) := by
    have h := (LipschitzWith.eval e).comp (hA hF x hr hl hT0 hT1 hh hq N s).2
    convert h using 1 <;> first | rfl | simp only [one_mul]
  apply finite_weighted_lipschitz
  intro i
  have hz0 : 0≤ψ*angleNodes m i := mul_nonneg hψ.le (Nat.cast_nonneg _)
  have hz1 : ψ*angleNodes m i≤1 := by
    apply le_trans _ hψm
    apply mul_le_mul_of_nonneg_left _ hψ.le
    change (i:ℝ)≤(m:ℝ)
    exact_mod_cast (Nat.le_of_lt_succ i.2)
  have hw := ((LipschitzWith.eval (Fin.last n)).comp
    (hB hF x hr hl htime.1 (htime.2.trans_lt hT1) hz0 hz1 hq' N).1).comp hb
  have h := hc.comp hw
  convert h using 1 <;> first | rfl | ring

end LogConcaveSampling

end

end

end

end OAI
