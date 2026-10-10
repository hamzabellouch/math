import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralCircularPicard

namespace OAI

/-! A bounded weighted solution of the coupled circular differential equation. -/

namespace DefocusingNLS
local notation "E₄" => (ℂ × ℂ) × (ℂ × ℂ)

noncomputable def circularLeadingField (t : ℝ) (z : E₄) : E₄ :=
  ((0,-Complex.I*(Real.exp (2*t)/2 : ℝ)*z.1.2),
   (0,Complex.I*(Real.exp (2*t)/2 : ℝ)*z.2.2))

theorem exists_circular_weighted_ODE (κ L C : ℝ) (hκ : 0 < κ)
    (hL : 0 ≤ L) (hLκ : L < κ) (hC : 0 ≤ C)
    (N : ℝ → E₄ → E₄) (hN : Continuous (Function.uncurry N))
    (hN0 : ∀ t, ‖N t 0‖ ≤ C) (hLip : ∀ t z w, ‖N t z-N t w‖ ≤ L*‖z-w‖) :
    ∃ v : CircularTailSpace, ‖v‖ ≤ C/(κ-L) ∧
      circularPicard κ L C hκ hL N hN hN0 hLip v=v ∧
      ∀ t, HasDerivAt (circularTailEvaluation v)
        (κ • circularTailEvaluation v t+circularLeadingField t (circularTailEvaluation v t)+
          N t (circularTailEvaluation v t)) t := by
  obtain ⟨v,hv,_⟩ := existsUnique_circularTail κ L C hκ hL hLκ N hN hN0 hLip
  refine ⟨v,circularTail_fixedPoint_bound κ L C hκ hL hLκ hC N hN hN0 hLip v hv,hv,?_⟩
  intro t
  have hd := circularTail_hasDerivAt κ hκ (boundedCircularSource L C hL N hN hN0 hLip v) t
  change circularTail κ hκ (boundedCircularSource L C hL N hN hN0 hLip v)=v at hv
  rw [hv] at hd
  have hs := boundedCircularSource_evaluation L C hL N hN hN0 hLip v t
  apply hd.congr_deriv
  apply Prod.ext <;> simp only [Prod.fst_add,Prod.snd_add,Prod.smul_fst,Prod.smul_snd,
    circularTailEvaluation,circularLeadingField]
  · exact congrArg (fun y : ℂ × ℂ =>
      κ • v.1 t+(0,-Complex.I*(Real.exp (2*t)/2 : ℝ)*(v.1 t).2)+y) (congrArg Prod.fst hs)
  · exact congrArg (fun y : ℂ × ℂ =>
      κ • v.2 t+(0,Complex.I*(Real.exp (2*t)/2 : ℝ)*(v.2 t).2)+y) (congrArg Prod.snd hs)

end DefocusingNLS

end OAI
