import Mathlib
import OAI.Analysis.FreeWords.TraceTransferDefinitions

namespace OAI

noncomputable section

namespace KKLocalPatching

open KKTraceTransfer

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {M : VonNeumannAlgebra H} (τ : FaithfulNormalTrace M)

def mixedValue (u : ℤ → ConcreteAlgebra M) (s : List (ℤ × ConcreteAlgebra M)) : ConcreteAlgebra M :=
  (s.map (fun z => u z.1*z.2)).prod

def scaledMixed (c : ℂ) (s : List (ℤ × ConcreteAlgebra M)) : List (ℤ × ConcreteAlgebra M) :=
  s.map (fun z => (z.1,c • z.2))

theorem mixedValue_scaled (u : ℤ → ConcreteAlgebra M) (c : ℂ)
    (s : List (ℤ × ConcreteAlgebra M)) :
    mixedValue u (scaledMixed c s)=c^s.length • mixedValue u s := by
  induction s with
  | nil => simp [mixedValue,scaledMixed]
  | cons z s ih =>
    change u z.1*(c • z.2)*mixedValue u (scaledMixed c s)=
      c^(s.length+1) • (u z.1*z.2*mixedValue u s)
    simp only [ih,mul_smul_comm,smul_mul_assoc,smul_smul,pow_succ]

theorem mixedValue_restore (u : ℤ → ConcreteAlgebra M) (c : ℂ) (hc : c≠0)
    (s : List (ℤ × ConcreteAlgebra M)) :
    mixedValue u s=c^s.length • mixedValue u (scaledMixed c⁻¹ s) := by
  rw [mixedValue_scaled,smul_smul,← mul_pow,mul_inv_cancel₀ hc,one_pow,one_smul]

theorem norm_trace_scaled (u : ℤ → ConcreteAlgebra M) (R : ℝ) (hR : 0<R)
    (s : List (ℤ × ConcreteAlgebra M)) :
    ‖τ.map (mixedValue u s)‖=R^s.length*‖τ.map (mixedValue u (scaledMixed (R:ℂ)⁻¹ s))‖ := by
  rw [mixedValue_restore u (R:ℂ) (by exact_mod_cast hR.ne') s,map_smul,norm_smul,norm_pow]
  rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos hR]

end

end KKLocalPatching
end

end OAI
