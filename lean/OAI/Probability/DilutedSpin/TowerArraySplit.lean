import OAI.Probability.DilutedSpin.CommonTreeSample

namespace OAI

section
namespace DilutedSpinGlass.KernelTower
variable {Ω Λ : Type} [Fintype Ω] [Fintype Λ]

def splitFirst (l : ℕ) (z : Ω × (Fin (l+1) → Λ)) : (Ω × (Fin l → Λ)) × Λ :=
  ((z.1,fun i => z.2 i.succ),z.2 0)

lemma splitFirst_projects (n l : ℕ) (T : KernelTower Ω n) (U : Fin (l+1) → KernelTower Λ n) :
    Projects (splitFirst l) n (prod n T (pi n U))
      (prod n (prod n T (pi n (fun i => U i.succ))) (U 0)) := by
  induction n with
  | zero => trivial
  | succ n ih =>
    refine ⟨?_,fun a => ih (T.2 a.1) (fun i => (U i).2 (a.2 i))⟩
    intro f
    change (T.1.bind (fun _ => FiniteLaw.pi (fun i => (U i).1))).expect (fun z => f (splitFirst l z)) =
      ((T.1.bind (fun _ => FiniteLaw.pi (fun i : Fin l => (U i.succ).1))).bind (fun _ => (U 0).1)).expect f
    simp only [FiniteLaw.expect_bind]
    apply FiniteLaw.expect_congr
    intro a
    rw [FiniteLaw.expect_pi_cons]
    rw [FiniteLaw.expect_comm]
    apply FiniteLaw.expect_congr
    intro b
    apply FiniteLaw.expect_congr
    intro c
    simp only [splitFirst,Fin.cons_zero,Fin.cons_succ]

lemma prod_empty_projects (n : ℕ) (T : KernelTower Ω n) (U : Fin 0 → KernelTower Λ n) :
    Projects Prod.fst n (prod n T (pi n U)) T := by
  induction n with
  | zero => trivial
  | succ n ih =>
    refine ⟨?_,fun a => ih (T.2 a.1) (fun i => (U i).2 (a.2 i))⟩
    intro f
    change (T.1.bind (fun _ => FiniteLaw.pi (fun i => (U i).1))).expect (fun a => f a.1)=T.1.expect f
    simp only [FiniteLaw.expect_bind,FiniteLaw.expect_const]

end DilutedSpinGlass.KernelTower

end

end OAI
