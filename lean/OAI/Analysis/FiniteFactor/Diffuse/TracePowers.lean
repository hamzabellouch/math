import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Tactic.NoncommRing

namespace OAI

noncomputable section
open scoped BigOperators
namespace Nonhyperlinear.Diffuseness

/-- Cyclicity equates every polynomial defect moment; no spectral assumption is used. -/
theorem trace_defect_pow {A:Type*} [Ring A] [Algebra ℂ A]
    (f:A→ₗ[ℂ]ℂ) (hf:∀a b,f (a*b)=f (b*a)) (a b:A) (n:ℕ) :
    f ((1-a*b)^n)=f ((1-b*a)^n) := by
  have hsem : SemiconjBy b (1-a*b) (1-b*a) := by
    change b*(1-a*b)=(1-b*a)*b
    noncomm_ring
  induction n with
  | zero => simp
  | succ n ih =>
    have hp:= (hsem.pow_right n).eq
    have he : (1-a*b)^(n+1)=(1-a*b)^n-a*(b*(1-a*b)^n) := by
      rw [pow_succ']
      noncomm_ring
    have he' : (1-b*a)^(n+1)=(1-b*a)^n-((1-b*a)^n*b)*a := by
      rw [pow_succ]
      noncomm_ring
    rw [he,he',map_sub,map_sub,ih,hp,hf a]

end Nonhyperlinear.Diffuseness

end

end OAI
