import OAI.Probability.DilutedSpin.CavityMaskEnergy
import OAI.Probability.DilutedSpin.TowerArraySplit

namespace OAI

section
namespace DilutedSpinGlass.PrescribedTree
open KernelTower
variable {Ω Λ R : Type} [Fintype Ω] [Fintype Λ] [Fintype R] {n p : ℕ}

def cavityPack : (l : ℕ) → Ω × (Fin l → Fin p → Λ) → CavityState Ω Λ p l
  | 0,z => z.1
  | l+1,z => (cavityPack l (z.1,fun i => z.2 i.succ),z.2 0)

omit [Fintype R] in
lemma cavityPack_projects (T : KernelTower Ω n) (U : R → KernelTower Λ n) (l : ℕ)
    (r : RootPath (Fin p → R) l) :
    Projects (cavityPack l) n
      (prod n T (pi n (fun i : Fin l => piTower n (fun j => U (rootArray l r i j)))))
      (cavityTower T U l r) := by
  induction l with
  | zero => exact prod_empty_projects n T _
  | succ l ih =>
    have hg := splitFirst_projects n l T (fun i => piTower n (fun j => U (rootArray (l+1) r i j)))
    have hh := (ih r.2).prod n (Projects.refl n (piTower n (fun j => U (r.1 j))))
    exact hg.comp n hh

omit [Fintype Ω] [Fintype Λ] in
lemma cavityProject_pack (l : ℕ) (z : Ω × (Fin l → Fin p → Λ)) :
    cavityProject l (cavityPack l z)=z.1 := by
  induction l with
  | zero => rfl
  | succ l ih => exact ih (z.1,fun i => z.2 i.succ)

omit [Fintype Ω] [Fintype Λ] in
lemma pathFst_pack (l : ℕ) (y : FinitePath (Ω × (Fin (l+1) → Fin p → Λ)) n) :
    pathFst n (pathMap (cavityPack (l+1)) n y)=
      pathMap (cavityPack l) n (pathMap (fun z : Ω × (Fin (l+1) → Fin p → Λ) => (z.1,fun i => z.2 i.succ)) n y) := by
  induction n with
  | zero => rfl
  | succ n ih => exact Prod.ext rfl (ih y.2)

omit [Fintype Ω] [Fintype Λ] in
lemma pathSnd_pack (l : ℕ) (y : FinitePath (Ω × (Fin (l+1) → Fin p → Λ)) n) :
    pathSnd n (pathMap (cavityPack (l+1)) n y)=
      pathMap (fun z : Ω × (Fin (l+1) → Fin p → Λ) => z.2 0) n y := by
  induction n with
  | zero => rfl
  | succ n ih => exact Prod.ext rfl (ih y.2)

omit [Fintype Ω] [Fintype Λ] in
lemma pathProject_pack (l : ℕ) (y : FinitePath (Ω × (Fin l → Fin p → Λ)) n) :
    pathMap (cavityProject l) n (pathMap (cavityPack l) n y)=pathFst n y := by
  induction n with
  | zero => rfl
  | succ n ih => exact Prod.ext (cavityProject_pack l y.1) (ih y.2)

end DilutedSpinGlass.PrescribedTree

end

end OAI
