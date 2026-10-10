import Mathlib
import OAI.Geometry.SplitTangent.Basic
import OAI.Geometry.SplitTangent.FormalBoxes
import OAI.Geometry.SplitTangent.ProjectiveLineFrame

namespace OAI

/-! Rational Curve Frames. -/

noncomputable section
open Set Filter Topology
open scoped Manifold ContDiff BigOperators
universe u
namespace SplitTangent

 

structure RationalCurveFrames {X : ComplexManifold.{u}}
    (e : ProjectiveEmbedding X) (g : RationalCurve X) where
  degree : ℕ
  P : Fin (e.N+1) → Polynomial ℂ
  Q : Fin (e.N+1) → Polynomial ℂ
  a : Fin (e.N+1) → Polynomial ℂ
  b : Fin (e.N+1) → Polynomial ℂ
  finite_bezout : ∑i,a i*P i=1
  infinity_bezout : ∑i,b i*Q i=1
  finite_incidence : ∀z,e.Incidence (g.finite z) (fun i => (P i).eval z)
  infinity_incidence : ∀z,e.Incidence (g.infinity z) (fun i => (Q i).eval z)
  transition : ∀z,z≠0 → ∀i,(P i).eval z=z^degree*(Q i).eval z⁻¹

theorem RationalCurve.exists_frames {X : ComplexManifold.{u}}
    (e : ProjectiveEmbedding X) (g : RationalCurve X) : Nonempty (RationalCurveFrames e g) := by
  classical
  obtain ⟨d,P,Q,hP,hQ,hdeg,hf,hi,ht⟩ := rationalCurve_two_chart_polynomials e g
  obtain ⟨a,ha⟩ := PolynomialTuple.bezout P hP
  obtain ⟨b,hb⟩ := PolynomialTuple.bezout Q hQ
  refine ⟨⟨d,P,Q,a,b,ha,hb,?_,?_,ht⟩⟩
  · intro z
    obtain ⟨k,hk⟩ := Function.ne_iff.mp (e.map (g.finite z)).rep_nonzero
    refine (e.incidence_iff_coordinates hk).mpr (fun j => ?_)
    exact (hf z k j hk).trans (mul_comm _ _)
  · intro z
    obtain ⟨k,hk⟩ := Function.ne_iff.mp (e.map (g.infinity z)).rep_nonzero
    refine (e.incidence_iff_coordinates hk).mpr (fun j => ?_)
    exact (hi z k j hk).trans (mul_comm _ _)

namespace RationalCurveFrames
variable {X : ComplexManifold.{u}} {e : ProjectiveEmbedding X} {g : RationalCurve X}
    (F : RationalCurveFrames e g)

def finite (z : ℂ) (x : X.Carrier) := e.linearFrame (fun i => (F.a i).eval z) x
def infinity (z : ℂ) (x : X.Carrier) := e.linearFrame (fun i => (F.b i).eval z) x

lemma finite_unit (z : ℂ) : ∑i,(F.a i).eval z*(F.P i).eval z=1 := by
  simpa only [Polynomial.eval_finsetSum,Polynomial.eval_mul,Polynomial.eval_one]
    using congrArg (Polynomial.eval z) F.finite_bezout
lemma infinity_unit (z : ℂ) : ∑i,(F.b i).eval z*(F.Q i).eval z=1 := by
  simpa only [Polynomial.eval_finsetSum,Polynomial.eval_mul,Polynomial.eval_one]
    using congrArg (Polynomial.eval z) F.infinity_bezout

lemma finite_denominator_ne (z : ℂ) :
    (∑i,(F.a i).eval z*(e.map (g.finite z)).rep i)≠0 :=
  e.linearFrame_denominator_ne (F.finite_incidence z) (F.finite_unit z)
lemma infinity_denominator_ne (z : ℂ) :
    (∑i,(F.b i).eval z*(e.map (g.infinity z)).rep i)≠0 :=
  e.linearFrame_denominator_ne (F.infinity_incidence z) (F.infinity_unit z)

lemma finite_on_curve (z : ℂ) : F.finite z (g.finite z)=fun i => (F.P i).eval z :=
  e.linearFrame_eq_of_incidence (F.finite_incidence z) (F.finite_unit z)
lemma infinity_on_curve (z : ℂ) : F.infinity z (g.infinity z)=fun i => (F.Q i).eval z :=
  e.linearFrame_eq_of_incidence (F.infinity_incidence z) (F.infinity_unit z)

 
def multiplier (z : ℂ) (x : X.Carrier) : ℂ :=
  ∑i,(F.b i).eval z⁻¹ * F.finite z x i

lemma multiplier_on_curve {z : ℂ} (hz : z≠0) :
    F.multiplier z (g.finite z)=z^F.degree := by
  simp only [multiplier,F.finite_on_curve,F.transition z hz]
  calc
    _ = z^F.degree * (∑i,(F.b i).eval z⁻¹ * (F.Q i).eval z⁻¹) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = _ := by rw [F.infinity_unit,mul_one]

lemma frame_transition (z : ℂ) (x : X.Carrier)
    (hb : (∑i,(F.b i).eval z⁻¹*(e.map x).rep i)≠0) :
    F.finite z x=F.multiplier z x • F.infinity z⁻¹ x :=
  e.linearFrame_change _ _ x hb

lemma finite_holomorphicAt (z : ℂ) :
    ContMDiffAt (ModelWithCorners X) 𝓘(ℂ,Fin (e.N+1) → ℂ) ω
      (F.finite z) (g.finite z) :=
  e.linearFrame_holomorphicAt (ModelWithCorners X) contMDiffAt_id
    contMDiffAt_const (F.finite_denominator_ne z)

lemma infinity_holomorphicAt (z : ℂ) :
    ContMDiffAt (ModelWithCorners X) 𝓘(ℂ,Fin (e.N+1) → ℂ) ω
      (F.infinity z) (g.infinity z) :=
  e.linearFrame_holomorphicAt (ModelWithCorners X) contMDiffAt_id
    contMDiffAt_const (F.infinity_denominator_ne z)

 

lemma finite_joint_holomorphicAt (z : ℂ) :
    ContMDiffAt (𝓘(ℂ,ℂ).prod (ModelWithCorners X)) 𝓘(ℂ,Fin (e.N+1) → ℂ) ω
      (fun q : ℂ × X.Carrier => F.finite q.1 q.2) (z,g.finite z) := by
  apply e.linearFrame_holomorphicAt _ contMDiffAt_snd _ (F.finite_denominator_ne z)
  apply contMDiffAt_pi_space.mpr
  intro i
  have hp : ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (fun t => (F.a i).eval t) z := by
    simpa [Polynomial.aeval_def] using
      ((F.a i).contDiff_aeval (𝕜 := ℂ) ω).contDiffAt.contMDiffAt
  exact hp.comp (z,g.finite z) (contMDiffAt_fst (I := 𝓘(ℂ,ℂ)) (J := ModelWithCorners X))

lemma infinity_joint_holomorphicAt (z : ℂ) :
    ContMDiffAt (𝓘(ℂ,ℂ).prod (ModelWithCorners X)) 𝓘(ℂ,Fin (e.N+1) → ℂ) ω
      (fun q : ℂ × X.Carrier => F.infinity q.1 q.2) (z,g.infinity z) := by
  apply e.linearFrame_holomorphicAt _ contMDiffAt_snd _ (F.infinity_denominator_ne z)
  apply contMDiffAt_pi_space.mpr
  intro i
  have hp : ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (fun t => (F.b i).eval t) z := by
    simpa [Polynomial.aeval_def] using
      ((F.b i).contDiff_aeval (𝕜 := ℂ) ω).contDiffAt.contMDiffAt
  exact hp.comp (z,g.infinity z) (contMDiffAt_fst (I := 𝓘(ℂ,ℂ)) (J := ModelWithCorners X))

end RationalCurveFrames
end SplitTangent

end

end OAI
