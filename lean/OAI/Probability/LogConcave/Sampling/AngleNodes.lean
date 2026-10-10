import Mathlib
import OAI.Probability.LogConcave.Numerics.CompositeAngle
import OAI.Probability.LogConcave.Complexity.HarmonicCorrectionBudget

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory
open scoped Classical BigOperators NNReal RealInnerProductSpace
open TensorEnergy Quadrature

local instance : DecidableEq Unit := Classical.decEq _

def angleNodes (n : ℕ) (i : Fin (n+1)) : ℝ := (i:ℝ)

lemma angleNodes_injective (n : ℕ) : Function.Injective (angleNodes n) := by
  intro i j h
  apply Fin.ext
  change (i:ℝ)=(j:ℝ) at h
  exact_mod_cast h

lemma liePathJet_measurable {S : Type} [Fintype S] {d : ℕ} {H : Point d → ℝ}
    (hH : PolySmooth H) (A : (Unit ⊕ Unit → Fin d) → Point d → ℝ)
    (F : (S → Fin d) → Point d → ℝ) (hA : ∀c,PolySmooth (A c)) (hF : ∀c,PolySmooth (F c))
    (Ξ : Point d → ℝ → Point d) (hm : Measurable (fun p : ℝ × Point d => Ξ p.2 p.1))
    (k : ℕ) (v : ℝ) :
    Measurable (fun y => tensorVector (iterTensorLie H A F k) (Ξ y v)) :=
  (tensorVector_contDiff _ (fun c => (iterTensorLie_polySmooth hH A F hA hF k c).smooth)).continuous.measurable.comp
    (hm.comp (measurable_const.prodMk measurable_id))

lemma chainTaylor_measurable {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] (J : ℕ → ℝ → Ω → E)
    (hm : ∀k t,Measurable (J k t)) (n : ℕ) (a b : ℝ) :
    Measurable (fun y => chainTaylor (fun k t => J k t y) n a b) := by
  unfold chainTaylor
  exact Finset.measurable_sum _ (fun k _ => (hm k a).const_smul _)

theorem harmonic_correction_stencil_rms {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r R T : ℝ}
    (hr : 0<r) (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2)
    (hR : 0<R) (hRT : R^2≤1-T^2) (hT0 : 0≤T) (hT1 : T<1)
    (s t u : Icc (0:ℝ) T)
    (Ξ : Point (d+d) → ℝ → Point (d+d))
    (hder : ∀y v,v∈Icc (0:ℝ) 1 → HasDerivWithinAt (Ξ y)
      (skewLieField (centeringPotential F x r u) (harmonicSkew d) (Ξ y v)) (Icc (0:ℝ) 1) v)
    (hm : Measurable (fun p : ℝ × Point (d+d) => Ξ p.2 p.1))
    (hlaw : ∀v∈Icc (0:ℝ) 1,(gibbs (centeringPotential F x r u)).map (fun y => Ξ y v)=
      gibbs (centeringPotential F x r u)) :
    let A := jointCorrectionArray (fun z => probabilityTransport hF x hr.le hl hT0 hT1 s t z-z)
    let J := fun k v y => tensorVector (iterTensorLie (centeringPotential F x r u) (harmonicSkew d) A k) (Ξ y v)
    ∀n : ℕ,1≤n → ∀ψ : ℝ,0<ψ → ψ*n≤1 →
      Integrable (fun y => ‖derivativeStencil (angleNodes n) ψ (fun i => J 0 (ψ*angleNodes n i) y)-J 1 0 y‖^2)
        (gibbs (centeringPotential F x r u)) ∧
      (∫y,‖derivativeStencil (angleNodes n) ψ (fun i => J 0 (ψ*angleNodes n i) y)-J 1 0 y‖^2
        ∂gibbs (centeringPotential F x r u))≤
      ((∑i,|derivativeWeight (angleNodes n) i|)/ψ)^2*
        (((ψ*n)^(n+1)/(n.factorial:ℝ))^2*
          ((d*((lam:ℝ)*r^2)^2)*(R⁻¹)^(4*(n+1))*harmonicCorrectionBudget (n+1))) := by
  intro A J n hn ψ hψ hψn
  have hu1 := u.2.2.trans_lt hT1
  have hH : PolySmooth (centeringPotential F x r u) := productPotential_polySmooth
    (interpolationPotential_polySmooth hF x hr hlam hl u.2.1 hu1) (gaussianPotential_polySmooth d)
  have hJ (k : ℕ) (v : ℝ) : Measurable (J k v) :=
    liePathJet_measurable hH (harmonicSkew d) A (harmonicSkew_polySmooth d)
      (jointCorrectionArray_polySmooth hF x hr hlam hl hR hRT hT0 hT1 s t) Ξ hm k v
  have hnode (i : Fin (n+1)) : 0≤ψ*angleNodes n i ∧ ψ*angleNodes n i≤ψ*n := by
    constructor
    · exact mul_nonneg hψ.le (Nat.cast_nonneg _)
    · apply mul_le_mul_of_nonneg_left _ hψ.le
      change (i:ℝ)≤(n:ℝ)
      exact_mod_cast Nat.le_of_lt_succ i.2
  have htay (i : Fin (n+1)) := harmonic_correction_taylor_rms hF x hr hlam hl hR hRT hT0 hT1
    s t u Ξ hder hm hlaw n 0 (ψ*angleNodes n i) le_rfl (hnode i).1 ((hnode i).2.trans hψn)
  apply derivative_stencil_error_rms (angleNodes n) (angleNodes_injective n) n hn (by simp) hψ J
  · intro i
    exact ((hJ 0 _).sub (chainTaylor_measurable J hJ n 0 _)).aestronglyMeasurable
  · intro i
    simpa only [J,iterTensorLie,sub_zero] using (htay i).1
  · intro i
    have hh := (htay i).2
    change (∫y,‖J 0 (ψ*angleNodes n i) y-chainTaylor
      (fun k v => J k v y) n 0 (ψ*angleNodes n i)‖^2 ∂gibbs (centeringPotential F x r u))≤_ at hh
    apply hh.trans
    simp only [sub_zero]
    apply mul_le_mul_of_nonneg_right _ (by positivity [harmonicCorrectionBudget_nonneg (n+1)])
    apply pow_le_pow_left₀ (div_nonneg (pow_nonneg (hnode i).1 _) (Nat.cast_nonneg _))
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    exact pow_le_pow_left₀ (hnode i).1 (hnode i).2 _
end LogConcaveSampling

end

end

end

end OAI
