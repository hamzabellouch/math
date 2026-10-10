import OAI.Probability.InvariantIsing.Magnetic.MagneticVariationalBounds
import OAI.Probability.InvariantIsing.Magnetic.MagneticVariationalContinuity

namespace OAI

/-! Each rational magnetic trial lies below the finite-field variational supremum. -/
noncomputable section
open scoped BigOperators
namespace InvariantIsing

lemma finiteMagnetic_trial_le {A ι : Type*} [Fintype A] [Fintype ι]
    (ρ eig : ι → ℝ) (hρ : ∀ a, 0<ρ a) (hsum : ∑ a, ρ a=1)
    (γ b : A → ℝ) (hγ : ∀ a, 0≤γ a) (hγsum : ∑ a, γ a=1)
    (q : RationalMagnetization A) :
    (magneticVariationalFunctional (finiteR ρ eig hρ hsum) γ (fun a => (q.val a:ℝ))).toReal+
      (∑ a, γ a*b a*(q.val a:ℝ)) ≤
      (finiteMagneticFunctional (finiteR ρ eig hρ hsum) γ b).toReal := by
  have hm := finiteMagneticVariational_ne_top_bot ρ eig hρ hsum γ
    (fun a => (q.val a:ℝ)) hγ hγsum (fun a => (q.property a).le)
  have hv := finiteVariational_ne_top_bot ρ eig hρ hsum
  have hf := finiteMagneticFunctional_ne_top_bot (finiteR ρ eig hρ hsum) γ b hγ hγsum hv.1 hv.2
  have hi := le_iSup (fun q : RationalMagnetization A =>
    ((∑ a, γ a*b a*(q.val a:ℝ) : ℝ) : EReal)+
      magneticVariationalFunctional (finiteR ρ eig hρ hsum) γ (fun a => (q.val a:ℝ))) q
  change _≤finiteMagneticFunctional (finiteR ρ eig hρ hsum) γ b at hi
  rw [←EReal.coe_toReal hm.1 hm.2,←EReal.coe_toReal hf.1 hf.2,←EReal.coe_add] at hi
  have := EReal.coe_le_coe_iff.mp hi
  linarith

end InvariantIsing

end

end OAI
