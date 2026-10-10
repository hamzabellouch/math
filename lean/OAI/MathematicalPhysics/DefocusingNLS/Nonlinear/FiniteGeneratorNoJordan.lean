import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Tactic

namespace OAI

/-! Exclusion of length-two Jordan chains makes the eigenspaces span. -/

namespace DefocusingNLS

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

theorem generator_maxGenEigenspace_eq (G : Module.End ℂ V)
    (hJ : ∀ (lam : ℂ) (v w : V), w ≠ 0 → G w=lam • w → G v ≠ lam • v+w)
    (lam : ℂ) : G.maxGenEigenspace lam=G.eigenspace lam := by
  apply le_antisymm
  · intro x hx
    obtain ⟨k,hk⟩ := (Module.End.mem_maxGenEigenspace G lam x).mp hx
    have hpow : ∀ (k : ℕ) (x : V), ((G-lam • (1 : Module.End ℂ V))^k) x=0 → (G-lam • (1 : Module.End ℂ V)) x=0 := by
      intro k
      induction k with
      | zero =>
          intro x hx
          simpa only [pow_zero,Module.End.one_apply,map_zero] using congrArg (fun y : V => (G-lam • (1 : Module.End ℂ V)) y) hx
      | succ k ih =>
          intro x hx
          have hh : (G-lam • (1 : Module.End ℂ V)) ((G-lam • (1 : Module.End ℂ V)) x)=0 := by
            apply ih
            simpa only [pow_succ,Module.End.mul_apply] using hx
          by_contra hn
          have he : G ((G-lam • (1 : Module.End ℂ V)) x)=lam • ((G-lam • (1 : Module.End ℂ V)) x) := by
            simpa only [LinearMap.sub_apply,LinearMap.smul_apply,Module.End.one_apply,
              sub_eq_zero] using hh
          apply hJ lam x ((G-lam • (1 : Module.End ℂ V)) x) hn he
          simp only [LinearMap.sub_apply,LinearMap.smul_apply,Module.End.one_apply]
          abel
    rw [Module.End.mem_eigenspace_iff]
    simpa only [LinearMap.sub_apply,LinearMap.smul_apply,Module.End.one_apply,
      sub_eq_zero] using hpow k x hk
  · exact G.eigenspace_le_maxGenEigenspace

theorem generator_eigenspaces_span [FiniteDimensional ℂ V] (G : Module.End ℂ V)
    (hJ : ∀ (lam : ℂ) (v w : V), w ≠ 0 → G w=lam • w → G v ≠ lam • v+w) :
    (⨆ lam : ℂ, G.eigenspace lam)=⊤ := by
  simpa only [generator_maxGenEigenspace_eq G hJ] using G.iSup_maxGenEigenspace_eq_top

end DefocusingNLS

end OAI
