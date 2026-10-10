import OAI.Dynamics.ConditionalShuffle.InstrumentTV

namespace OAI

noncomputable section
namespace Revealed.Disintegration
open scoped Classical
open Thorp Thorp.Conditional
variable {E E' G Ω : Type} [Fintype E] [Fintype E'] [Fintype G] [Nonempty G] [Fintype Ω]

lemma conditional_map_injective (a : Ω → E) (b : Ω → G) (f : E → E')
    (hf : Function.Injective f) (e : E) :
    conditional (fairMass (fun ω => (f (a ω), b ω))) (f e) =
      conditional (fairMass (fun ω => (a ω, b ω))) e := by
  funext g
  have hm : marginal (fairMass (fun ω => (f (a ω), b ω))) (f e) =
      marginal (fairMass (fun ω => (a ω, b ω))) e := by
    simp only [marginal_fairMass, fairMass, hf.eq_iff]
  have hj : fairMass (fun ω => (f (a ω), b ω)) (f e,g) =
      fairMass (fun ω => (a ω, b ω)) (e,g) := by
    simp only [fairMass, Prod.mk.injEq, hf.eq_iff]
  simp only [conditional, hm, hj]

lemma weighted_conditional_map (a : Ω → E) (b : Ω → G) (f : E → E')
    (hf : Function.Injective f) (c : (G → ℝ) → ℝ) :
    (∑ e', marginal (fairMass (fun ω => (f (a ω), b ω))) e' *
      c (conditional (fairMass (fun ω => (f (a ω), b ω))) e')) =
    ∑ e, marginal (fairMass (fun ω => (a ω, b ω))) e *
      c (conditional (fairMass (fun ω => (a ω, b ω))) e) := by
  simp only [marginal_fairMass, fairMass_test]
  simp_rw [conditional_map_injective a b f hf]

end Revealed.Disintegration

end

end OAI
