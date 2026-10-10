import OAI.Probability.DilutedSpin.CommonTreeSample
import OAI.Probability.DilutedSpin.UpperCountState

namespace OAI

section
namespace DilutedSpinGlass.PrescribedTree
open KernelTower
variable {ι Ω Λ R : Type} [Fintype ι] [DecidableEq ι]
    [Fintype Ω] [Fintype Λ] [Fintype R] {n p : ℕ}

/-- Duplicate every block at every site before selecting its actual allocation.
The unused duplicates disappear by prior-law projection, not by independence
of tilted physical sites. -/
def cavityJoin : (l : ℕ) → RootPath ι l →
    (ι → CavityState Ω Λ p l) → CavityState (ι → Ω) Λ p l
  | 0,_,z => z
  | l+1,c,z => (cavityJoin l c.2 (fun i => (z i).1),(z c.1).2)

omit [Fintype R] in
lemma cavityJoin_projects (T : ι → KernelTower Ω n) (U : R → KernelTower Λ n)
    (l : ℕ) (r : RootPath (Fin p → R) l) (c : RootPath ι l) :
    KernelTower.Projects (cavityJoin l c) n
      (KernelTower.pi n (fun i => cavityTower (T i) U l r))
      (cavityTower (KernelTower.pi n T) U l r) := by
  induction l with
  | zero => exact KernelTower.Projects.refl n _
  | succ l ih =>
    have h := KernelTower.pi_prod_projects n (fun i => cavityTower (T i) U l r.2)
      (fun _ : ι => piTower n (fun j => U (r.1 j))) c.1
    have g := KernelTower.Projects.prod n (ih r.2 c.2)
      (KernelTower.Projects.refl n (piTower n (fun j => U (r.1 j))))
    exact KernelTower.Projects.comp n h g

omit [Fintype ι] [DecidableEq ι] [Fintype Ω] [Fintype Λ] in
lemma pathMap_cavityJoin_zero (y : FinitePath (ι → Ω) n) (c : RootPath ι 0) :
    pathMap (cavityJoin (Ω := Ω) (Λ := Λ) (p := p) 0 c) n y=y :=
  pathMap_id n y

omit [Fintype ι] [DecidableEq ι] [Fintype Ω] [Fintype Λ] in
lemma pathFst_cavityJoin (l : ℕ) (c : RootPath ι (l+1))
    (y : FinitePath (ι → CavityState Ω Λ p (l+1)) n) :
    pathFst n (pathMap (cavityJoin (Ω := Ω) (Λ := Λ) (p := p) (l+1) c) n y)=
      pathMap (cavityJoin l c.2) n (pathMap (fun a i => (a i).1) n y) := by
  induction n with
  | zero => rfl
  | succ n ih => exact Prod.ext rfl (ih y.2)

omit [Fintype ι] [DecidableEq ι] [Fintype Ω] [Fintype Λ] in
lemma pathSnd_cavityJoin (l : ℕ) (c : RootPath ι (l+1))
    (y : FinitePath (ι → CavityState Ω Λ p (l+1)) n) :
    pathSnd n (pathMap (cavityJoin (Ω := Ω) (Λ := Λ) (p := p) (l+1) c) n y)=
      pathSnd n (FinitePath.proj n y c.1) := by
  induction n with
  | zero => rfl
  | succ n ih => exact Prod.ext rfl (ih y.2)

omit [Fintype ι] [DecidableEq ι] [Fintype Ω] [Fintype Λ] in
lemma cavityProject_join (l : ℕ) (c : RootPath ι l)
    (a : ι → CavityState Ω Λ p l) (i : ι) :
    cavityProject l (cavityJoin l c a) i=cavityProject l (a i) := by
  induction l with
  | zero => rfl
  | succ l ih => exact ih c.2 (fun i => (a i).1)

omit [Fintype ι] [DecidableEq ι] [Fintype Ω] [Fintype Λ] in
lemma cavityProject_pathJoin (l : ℕ) (c : RootPath ι l)
    (y : FinitePath (ι → CavityState Ω Λ p l) n) (i : ι) :
    pathMap (fun a : CavityState (ι → Ω) Λ p l => cavityProject l a i) n (pathMap (cavityJoin l c) n y)=
      pathMap (cavityProject l) n (FinitePath.proj n y i) := by
  induction n with
  | zero => rfl
  | succ n ih => exact Prod.ext (cavityProject_join l c y.1 i) (ih y.2)

end DilutedSpinGlass.PrescribedTree

end

end OAI
