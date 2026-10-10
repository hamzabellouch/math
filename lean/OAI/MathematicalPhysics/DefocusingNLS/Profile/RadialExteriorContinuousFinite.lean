import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialExteriorFiniteContinuity
import Mathlib.Topology.Sequences

namespace OAI

/-! Continuous dependence of the actual backwards finite-interval construction. -/

open Set Filter
namespace DefocusingNLS

theorem exists_continuous_radialExterior_finite_solutions (S : Set (ℂ × ℂ))
    (n : ℕ) (m : ℝ → ℂ) (hm : Continuous m) (δ ρ u T : ℝ)
    (hδ : 0 ≤ δ) (hT : 0 ≤ T)
    (hb : ∀ t ∈ Icc (u-T) u, ‖m t‖+2*δ ≤ ρ)
    (x : S → ℂ × ℂ) (hx : Continuous x) :
    ∃ Z : S → ℝ → ℂ × ℂ,
      (∀ z, Continuous (Z z) ∧ Z z u=x z) ∧
      (∀ z t, t ∈ Icc (u-T) u →
        HasDerivAt (Z z) (radialExteriorFiniteField z.val.1 n m δ t (Z z t)) t) ∧
      ∀ t ∈ Icc (u-T) u, Continuous (fun z => Z z t) := by
  classical
  have hex (z : S) := exists_radialExterior_clipped_finite z.val.1 n m hm δ ρ u T
    hδ hT hb (x z)
  choose Z hc he hd using hex
  refine ⟨Z,(fun z => ⟨hc z,he z⟩),hd,?_⟩
  intro t ht
  apply SeqContinuous.continuous
  intro z z₀ hz
  have hν : Tendsto (fun i => (z i).val.1) atTop (nhds z₀.val.1) :=
    (continuous_subtype_val.fst.continuousAt.tendsto).comp hz
  exact (radialExterior_finite_parameter_limit n (fun i => (z i).val.1) z₀.val.1
    hν m hm δ ρ u T hδ hT hb (fun i => Z (z i)) (Z z₀)
    (fun i => hc (z i)) (hc z₀) (fun i => hd (z i)) (hd z₀)
    (by simpa only [he] using! hx.continuousAt.tendsto.comp hz)).tendsto_at ht

end DefocusingNLS

end OAI
