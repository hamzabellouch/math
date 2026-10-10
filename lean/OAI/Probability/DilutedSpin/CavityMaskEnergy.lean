import OAI.Probability.DilutedSpin.FullRootIncrement

namespace OAI

section
namespace DilutedSpinGlass.PrescribedTree
open KernelTower
variable {Ω Λ R : Type} [Fintype Ω] [Fintype Λ] [Fintype R] {n p N : ℕ} [NeZero N]

noncomputable def activeEnergy (V : FinitePath Ω n → Spin)
    (x : R → FinitePath Λ n → ℝ) (j : Fin p) :
    (l : ℕ) → RootPath (Fin p → R) l → RootPath (InteractionSample p) l →
      (FinitePath Ω n → ℝ) → FinitePath (CavityState Ω Λ p l) n → ℝ
  | 0,_,_,f,y => f y
  | l+1,r,z,f,y => activeEnergy V x j l r.2 z.2 f (pathFst n y)+
      singleBlockEnergy V x j l r.1 z.1 y

omit [Fintype Ω] [Fintype Λ] in
lemma pathFst_select_true (l : ℕ) (b : RootPath Bool l)
    (y : FinitePath (CavityState Ω Λ p (l+1)) n) :
    pathFst n (pathMap (selectCavity (l+1) (true,b)) n y)=
      pathMap (selectCavity l b) n (pathFst n y) := by
  induction n with
  | zero => rfl
  | succ n ih => exact Prod.ext rfl (ih y.2)

omit [Fintype Ω] [Fintype Λ] in
lemma pathSnd_select_true (l : ℕ) (b : RootPath Bool l)
    (y : FinitePath (CavityState Ω Λ p (l+1)) n) :
    pathSnd n (pathMap (selectCavity (l+1) (true,b)) n y)=pathSnd n y := by
  induction n with
  | zero => rfl
  | succ n ih => exact Prod.ext rfl (ih y.2)

omit [Fintype Ω] [Fintype Λ] in
lemma path_select_false (l : ℕ) (b : RootPath Bool l)
    (y : FinitePath (CavityState Ω Λ p (l+1)) n) :
    pathMap (selectCavity (l+1) (false,b)) n y=
      pathMap (selectCavity l b) n (pathFst n y) := by
  induction n with
  | zero => rfl
  | succ n ih => exact Prod.ext rfl (ih y.2)

noncomputable def maskedEnergy (V : FinitePath Ω n → Spin)
    (x : R → FinitePath Λ n → ℝ) (j : Fin p) :
    (l : ℕ) → RootPath Bool l → RootPath (Fin p → R) l → RootPath (InteractionSample p) l →
      (FinitePath Ω n → ℝ) → FinitePath (CavityState Ω Λ p l) n → ℝ
  | 0,_,_,_,f,y => f y
  | l+1,(b,bs),r,z,f,y => maskedEnergy V x j l bs r.2 z.2 f (pathFst n y)+
      if b then singleBlockEnergy V x j l r.1 z.1 y else 0

omit [Fintype Ω] [Fintype Λ] [Fintype R] in
lemma activeEnergy_select (V : FinitePath Ω n → Spin)
    (x : R → FinitePath Λ n → ℝ) (j : Fin p) (l : ℕ)
    (b : RootPath Bool l) (r : RootPath (Fin p → R) l) (z : RootPath (InteractionSample p) l)
    (f : FinitePath Ω n → ℝ) (y : FinitePath (CavityState Ω Λ p l) n) :
    activeEnergy V x j (selectedCount l b) (selectRoot l b r) (selectRoot l b z) f
      (pathMap (selectCavity l b) n y)=maskedEnergy V x j l b r z f y := by
  induction l with
  | zero => exact congrArg f (pathMap_id n (show FinitePath Ω n from y))
  | succ l ih =>
    rcases b with ⟨v,b⟩
    cases v
    · change activeEnergy V x j (selectedCount l b) (selectRoot l b r.2) (selectRoot l b z.2) f
        (pathMap (selectCavity (l+1) (false,b)) n y)=maskedEnergy V x j l b r.2 z.2 f (pathFst n y)+0
      exact (congrArg (activeEnergy V x j (selectedCount l b) (selectRoot l b r.2) (selectRoot l b z.2) f)
        (path_select_false l b y)).trans ((ih b r.2 z.2 (pathFst n y)).trans (add_zero _).symm)
    · change activeEnergy V x j (selectedCount l b) (selectRoot l b r.2) (selectRoot l b z.2) f
          (pathFst n (pathMap (selectCavity (l+1) (true,b)) n y))+
        singleBlockEnergy V x j (selectedCount l b) r.1 z.1 (pathMap (selectCavity (l+1) (true,b)) n y)=
        maskedEnergy V x j l b r.2 z.2 f (pathFst n y)+singleBlockEnergy V x j l r.1 z.1 y
      apply congrArg₂ (fun a b : ℝ => a+b)
      · exact (congrArg (activeEnergy V x j (selectedCount l b) (selectRoot l b r.2) (selectRoot l b z.2) f)
          (pathFst_select_true l b y)).trans (ih b r.2 z.2 (pathFst n y))
      · unfold singleBlockEnergy
        have hfst := pathFst_select_true l b y
        have hsnd := pathSnd_select_true l b y
        have hpjs := cavityProject_pathSelect l b (pathFst n y)
        apply congrArg₂ (mixedEnergy z.1 (fun a => decide (a=j)))
        · funext a
          exact congrArg V ((congrArg (pathMap (cavityProject (selectedCount l b)) n) hfst).trans hpjs)
        · funext a
          exact congrArg (fun w => x (r.1 a) (pathMap (fun b : Fin p → Λ => b a) n w)) hsnd

omit [Fintype Ω] [Fintype Λ] [Fintype R] [NeZero N] in
lemma allocatedEnergy_mask (V : FinitePath Ω n → Spin)
    (x : R → FinitePath Λ n → ℝ) (j : Fin p) (s : Fin N) (l : ℕ)
    (r : RootPath (Fin p → R) l) (c : RootPath (Fin N) l) (z : RootPath (InteractionSample p) l)
    (f : FinitePath Ω n → ℝ) (y : FinitePath (CavityState Ω Λ p l) n) :
    allocatedEnergy V x j s l r c z f y=
      maskedEnergy V x j l (rootMap (fun a => decide (a=s)) l c) r z f y := by
  induction l with
  | zero => rfl
  | succ l ih => simp only [allocatedEnergy,maskedEnergy,rootMap,decide_eq_true_eq,ih]

omit [Fintype R] [NeZero N] in
lemma allocatedRoot_selected (T : KernelTower Ω n) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Spin) (x : R → FinitePath Λ n → ℝ) (j : Fin p)
    (m : Fin n → ℝ) (s : Fin N) (l : ℕ)
    (r : RootPath (Fin p → R) l) (c : RootPath (Fin N) l) (z : RootPath (InteractionSample p) l)
    (f : FinitePath Ω n → ℝ) :
    backwardLog n (cavityTower T U l r) m (allocatedEnergy V x j s l r c z f)=
      backwardLog n (cavityTower T U (selectedCount l (rootMap (fun a => decide (a=s)) l c))
        (selectRoot l (rootMap (fun a => decide (a=s)) l c) r)) m
        (activeEnergy V x j (selectedCount l (rootMap (fun a => decide (a=s)) l c))
          (selectRoot l (rootMap (fun a => decide (a=s)) l c) r)
          (selectRoot l (rootMap (fun a => decide (a=s)) l c) z) f) := by
  rw [← backwardLog_of_projects n (selectCavity_projects T U l (rootMap (fun a => decide (a=s)) l c) r)]
  congr 1
  funext y
  rw [activeEnergy_select,allocatedEnergy_mask]

end DilutedSpinGlass.PrescribedTree

end

end OAI
