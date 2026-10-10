import OAI.Probability.DilutedSpin.RootProductLaw
import OAI.Probability.DilutedSpin.UpperTrial

namespace OAI

section
namespace DilutedSpinGlass.PrescribedTree
open _root_.MeasureTheory _root_.OAI.MeasureTheory KernelTower
open scoped BigOperators

/-- Each cavity interaction has its own independent p-tuple of trial trees. -/
def CavityState (Ω Λ : Type) (p : ℕ) : ℕ → Type
  | 0 => Ω
  | l+1 => CavityState Ω Λ p l × (Fin p → Λ)

instance cavityStateFintype (Ω Λ : Type) [Fintype Ω] [Fintype Λ] (p : ℕ) :
    (l : ℕ) → Fintype (CavityState Ω Λ p l)
  | 0 => inferInstanceAs (Fintype Ω)
  | l+1 => by
    letI := cavityStateFintype Ω Λ p l
    exact inferInstanceAs (Fintype (CavityState Ω Λ p l × (Fin p → Λ)))

def cavityProject {Ω Λ : Type} {p : ℕ} : (l : ℕ) → CavityState Ω Λ p l → Ω
  | 0,σ => σ
  | l+1,σ => cavityProject l σ.1

variable {Ω Λ R : Type} [Fintype Ω] [Fintype Λ] [Fintype R] {n p N : ℕ} [NeZero N]

noncomputable def cavityTower (T : KernelTower Ω n) (U : R → KernelTower Λ n) :
    (l : ℕ) → RootPath (Fin p → R) l → KernelTower (CavityState Ω Λ p l) n
  | 0,_ => T
  | l+1,r => KernelTower.prod n (cavityTower T U l r.2) (piTower n (fun j => U (r.1 j)))

noncomputable def cavityEnergy (V : FinitePath Ω n → Fin N → Spin)
    (x : R → FinitePath Λ n → ℝ) (j : Fin p) :
    (l : ℕ) → RootPath (Fin p → R) l → RootPath (Fin p → Fin N) l →
      RootPath (InteractionSample p) l → (FinitePath Ω n → ℝ) →
        FinitePath (CavityState Ω Λ p l) n → ℝ
  | 0,_,_,_,f,y => f y
  | l+1,r,i,z,f,y => cavityEnergy V x j l r.2 i.2 z.2 f (pathFst n y)+
      mixedTreeEnergy z.1 (fun a => decide (a=j))
        (fun y => V (pathMap (cavityProject l) n y)) x r.1 i.1 y

omit [Fintype Ω] in
lemma pathMap_id (n : ℕ) (y : FinitePath Ω n) : pathMap id n y=y := by
  induction n with
  | zero => rfl
  | succ n ih => exact Prod.ext rfl (ih y.2)

omit [Fintype Ω] [Fintype Λ] in
lemma pathMap_cavityProject (l : ℕ) (y : FinitePath (CavityState Ω Λ p (l+1)) n) :
    pathMap (cavityProject (l+1)) n y=pathMap (cavityProject l) n (pathFst n y) := by
  induction n with
  | zero => rfl
  | succ n ih => exact Prod.ext rfl (ih y.2)

omit [Fintype Ω] [Fintype Λ] [Fintype R] [NeZero N] in
lemma cavityEnergy_add (V : FinitePath Ω n → Fin N → Spin)
    (x : R → FinitePath Λ n → ℝ) (j : Fin p)
    (l : ℕ) (r : RootPath (Fin p → R) l) (i : RootPath (Fin p → Fin N) l)
    (z : RootPath (InteractionSample p) l) (f g : FinitePath Ω n → ℝ)
    (y : FinitePath (CavityState Ω Λ p l) n) :
    cavityEnergy V x j l r i z (f+g) y=
      cavityEnergy V x j l r i z f y+g (pathMap (cavityProject l) n y) := by
  induction l with
  | zero =>
    have hy : pathMap id n (show FinitePath Ω n from y)=y := pathMap_id n y
    exact congrArg (fun t => f y+g t) hy.symm
  | succ l ih =>
    change cavityEnergy V x j l r.2 i.2 z.2 (f+g) (pathFst n y)+_=_
    rw [ih,pathMap_cavityProject]
    dsimp only [cavityEnergy]
    ring

omit [Fintype Ω] [Fintype Λ] [Fintype R] [NeZero N] in
lemma cavityEnergy_bound (V : FinitePath Ω n → Fin N → Spin)
    (x : R → FinitePath Λ n → ℝ) (j : Fin p)
    (l : ℕ) (r : RootPath (Fin p → R) l) (i : RootPath (Fin p → Fin N) l)
    (z : RootPath (InteractionSample p) l) (f : FinitePath Ω n → ℝ)
    {B : ℝ} (hf : ∀ y,|f y|≤B) (y : FinitePath (CavityState Ω Λ p l) n) :
    |cavityEnergy V x j l r i z f y|≤B+∑ a,‖(rootArray l z a).1‖ := by
  induction l with
  | zero => simpa [cavityEnergy] using hf y
  | succ l ih =>
    apply (abs_add_le _ _).trans
    calc
      _ ≤ (B+∑ a,‖(rootArray l z.2 a).1‖)+‖z.1.1‖ :=
        add_le_add (ih r.2 i.2 z.2 (pathFst n y)) (mixedEnergy_bound z.1 (fun a => decide (a=j)) _ _)
      _ = _ := by simp only [rootArray,Fin.sum_univ_succ,Fin.cons_zero,Fin.cons_succ]; ring

noncomputable def cavityRoot (T : KernelTower Ω n) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Fin N → Spin) (x : R → FinitePath Λ n → ℝ)
    (m : Fin n → ℝ) (j : Fin p) (l : ℕ)
    (r : RootPath (Fin p → R) l) (i : RootPath (Fin p → Fin N) l)
    (z : RootPath (InteractionSample p) l) (f : FinitePath Ω n → ℝ) : ℝ :=
  backwardLog n (cavityTower T U l r) m (cavityEnergy V x j l r i z f)

omit [Fintype R] [NeZero N] in
lemma cavityRoot_bound (T : KernelTower Ω n) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Fin N → Spin) (x : R → FinitePath Λ n → ℝ)
    (m : Fin n → ℝ) (hm : ∀ d,0 < m d) (j : Fin p) (l : ℕ)
    (r : RootPath (Fin p → R) l) (i : RootPath (Fin p → Fin N) l)
    (z : RootPath (InteractionSample p) l) (f : FinitePath Ω n → ℝ)
    {B : ℝ} (hf : ∀ y,|f y|≤B) :
    |cavityRoot T U V x m j l r i z f|≤B+∑ a,‖(rootArray l z a).1‖ :=
  backwardLog_bound n _ m hm (cavityEnergy_bound V x j l r i z f hf)

/-- Appending an actual cavity block is the fresh-tree term of the physical
local interpolation. There is no endpoint or increment hypothesis. -/
lemma cavityRoot_succ_difference (T : KernelTower Ω n) (Q : FiniteLaw R)
    (U : R → KernelTower Λ n) (V : FinitePath Ω n → Fin N → Spin)
    (x : R → FinitePath Λ n → ℝ) (m : Fin (n+1) → ℝ) (j : Fin p) (l : ℕ)
    (r : RootPath (Fin p → R) l) (i : RootPath (Fin p → Fin N) l)
    (z : RootPath (InteractionSample p) l) (f : FinitePath Ω n → ℝ) (θ : InteractionSample p) :
    (FiniteLaw.pi (fun _ : Fin p => (FiniteLaw.uniform : FiniteLaw (Fin N)))).expect (fun a =>
      (FiniteLaw.pi (fun _ : Fin p => Q)).expect (fun b =>
        cavityRoot T U V x (fun d => m d.succ) j (l+1) (b,r) (a,i) (θ,z) f))-
      cavityRoot T U V x (fun d => m d.succ) j l r i z f =
    mixedRootIncrement (cavityTower T U l r) Q U
      (fun y => V (pathMap (cavityProject l) n y)) x m
      (cavityEnergy V x j l r i z f) θ (fun a => decide (a=j)) := by
  simp only [mixedRootIncrement,FiniteLaw.expect_sub,FiniteLaw.expect_const]
  rfl

end DilutedSpinGlass.PrescribedTree

end

end OAI
