import OAI.Analysis.KadisonKastler.ModularPairingComplexification

namespace OAI

/-! # The modular pairing identity on two algebra vectors -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

theorem modular_pairing_products (Ω : H) (b : H →L[ℂ] H)
    (hb : b ∈ M.commutant) (hbs : IsSelfAdjoint b)
    (z : ℂ) (x : Algebra M)
    (hpair : ∀ a : selfAdjoint (Algebra M),
      (inner ℂ (a.val.val Ω) (b Ω)).re =
        (z * inner ℂ (a.val.val Ω) (x.val Ω)).re)
    (y w : Algebra M) :
    2 * inner ℂ (y.val Ω) (b (w.val Ω)) =
      z * inner ℂ (y.val Ω) (w.val (x.val Ω)) +
        star z * inner ℂ (y.val (x.val Ω)) (w.val Ω) := by
  have h := modular_pairing_complex Ω b hb hbs z x hpair (star y * w)
  have hw : w.val * b = b * w.val := hb _ (Set.mem_union_left _ w.property)
  have hwv : w.val (b Ω) = b (w.val Ω) := congrArg (fun T : H →L[ℂ] H => T Ω) hw
  change 2 * inner ℂ Ω ((star y.val * w.val) (b Ω)) =
    z * inner ℂ Ω ((star y.val * w.val) (x.val Ω)) +
      star z * inner ℂ (x.val Ω) ((star y.val * w.val) Ω) at h
  simp only [mul_apply_eq_comp, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_right, hwv] at h
  exact h

end

end KadisonKastler

end OAI
