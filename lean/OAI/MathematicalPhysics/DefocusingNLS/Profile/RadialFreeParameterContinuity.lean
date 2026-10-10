import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialFreeSlowJet
import OAI.MathematicalPhysics.DefocusingNLS.Profile.SlowParameterHolomorphy

namespace OAI

/-! Parameter continuity of the actual free outgoing jet at a fixed matching point. -/

open Filter
namespace DefocusingNLS

theorem continuousAt_normalizedSlowSolution_parameter (q : ℂ) (n : ℕ) (x : ℂ)
    (hq : -1 < q.re) (hx : 0 ≤ x.re) (hx0 : x ≠ 0) :
    ContinuousAt (fun z => normalizedSlowSolution z n x) q := by
  exact ((hasDerivAt_id q).const_cpow (c := x) (Or.inl hx0)).continuousAt.mul
    (differentiableAt_regularizedSlowSolution_parameter_closed q n x hq hx hx0).continuousAt

theorem continuousAt_normalizedSlowFirst_parameter (q : ℂ) (n : ℕ) (x : ℂ)
    (hq : -1 < q.re) (hx : 0 ≤ x.re) (hx0 : x ≠ 0) :
    ContinuousAt (fun z => normalizedSlowFirst z n x) q := by
  have hshift : -1 < (q+1).re := by simp only [Complex.add_re,Complex.one_re]; linarith
  have hc : ContinuousAt (fun z : ℂ => normalizedSlowSolution (z+1) n x) q :=
    (continuousAt_normalizedSlowSolution_parameter (q+1) n x hshift hx hx0).comp
      (f := fun z : ℂ => z+1) (x := q)
      (continuousAt_id.add_const (1 : ℂ))
  have hf : ContinuousAt (fun z : ℂ => -z*((n : ℂ)-1-z)/x^2*
      normalizedSlowSolution (z+1) n x) q :=
    (((continuousAt_id.neg.mul (continuousAt_const.sub continuousAt_id)).div_const _).mul hc)
  apply hf.congr_of_eventuallyEq
  have hopen : ∀ᶠ z in nhds q, -1 < z.re :=
    Complex.continuous_re.continuousAt.eventually (lt_mem_nhds hq)
  filter_upwards [hopen] with z hz
  exact normalizedSlowFirst_eq_shift z n x hz hx hx0

theorem continuousAt_radialFreeSlowJet_parameter (q m : ℂ) (hq : -1 < q.re) (t : ℝ) :
    ContinuousAt (fun z : ℂ × ℂ => radialFreeSlowJet z.1 z.2 t) (q,m) := by
  have hx : 0 ≤ (radialFreeSlowArgument t).re := by rw [radialFreeSlowArgument_re]
  have hn := radialFreeSlowArgument_ne_zero t
  have hv : ContinuousAt (fun z : ℂ × ℂ =>
      normalizedSlowSolution z.1 6 (radialFreeSlowArgument t)) (q,m) :=
    (continuousAt_normalizedSlowSolution_parameter q 6 _ hq hx hn).comp
      (f := fun z : ℂ × ℂ => z.1) (x := (q,m)) continuousAt_fst
  have hd : ContinuousAt (fun z : ℂ × ℂ =>
      normalizedSlowFirst z.1 6 (radialFreeSlowArgument t)) (q,m) :=
    (continuousAt_normalizedSlowFirst_parameter q 6 _ hq hx hn).comp
      (f := fun z : ℂ × ℂ => z.1) (x := (q,m)) continuousAt_fst
  exact (continuousAt_snd.mul hv).prodMk
    (continuousAt_snd.mul (continuousAt_const.mul hd))

end DefocusingNLS

end OAI
