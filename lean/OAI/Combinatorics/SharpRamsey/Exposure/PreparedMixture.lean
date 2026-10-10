import Mathlib
import OAI.Combinatorics.SharpRamsey.Selection.MixedLoss
import OAI.Combinatorics.SharpRamsey.Selection.PredeletionMean

namespace OAI

section
namespace SharpLogRamsey.Selection.Windows
open Finset ExposureModel ActualPivot
open scoped Classical BigOperators
noncomputable section
variable {K V Ω Θ : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
  [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]
  [Fintype Ω] [Fintype Θ] {d : ℕ} {b : ℝ}
variable (w n k : ℕ) (p : Law Ω) (θ : Ω→Θ)
  (G : Ω→Slot w (n+k)→Projectivization K (Module.Dual K V)×Projectivization K V) (t : Fin k)
local instance mixBlockDec : DecidableEq (Block w) := Classical.decEq _
variable (hp : ∀ z,0<(model w n k p θ G t).remaining z)
local notation "M" => model w n k p θ G t

abbrev PositiveHistory := {z : (M).FreshHistory // ((M).freshLaw hp).mass z≠0}

variable (e : ∀ z : PositiveHistory w n k p θ G t hp,
  Realization (K:=K) (V:=V) (I:=Fin w) (d:=d) (b:=b) (ExposureModel.tupleLaw (model w n k p θ G t) (Sigma.fst (Subtype.val z))))

def mixedPrepared := Realization.mix (K:=K) (V:=V) (I:=Fin w) (d:=d) (b:=b) ((M).freshLaw hp) (fun z=>(M).tupleLaw z.1) e

def attachedPrepared :=
  (mixedPrepared w n k p θ G t hp e).attach p
    (fun x=>(x.1.1.1,(M).restore x.1.1 x.2)) (fun ω=>(θ ω,G ω))
    (afterDraw_tagged_map n k p θ G (fun _=>embedding w (n+k)) (fun _=>owner w (n+k)) t hp)

omit [Finite K] [FiniteDimensional K V] in
lemma attachedPrepared_tuple (ω : (attachedPrepared w n k p θ G t hp e).Ω)
    (hω : (attachedPrepared w n k p θ G t hp e).μ.mass ω≠0) :
    p.mass ω.2≠0 ∧ θ ω.2=ω.1.1.val.1.1 ∧
      ∀ i,G ω.2 ((M).origin ω.1.1.val.1 i)=(e ω.1.1).source ω.1.2 i := by
  have hh:=(mixedPrepared w n k p θ G t hp e).attach_agrees p
    (fun x=>(x.1.1.1,(M).restore x.1.1 x.2)) (fun ω=>(θ ω,G ω))
    (afterDraw_tagged_map n k p θ G (fun _=>embedding w (n+k)) (fun _=>owner w (n+k)) t hp) ω hω
  refine ⟨hh.2.1,congrArg Prod.fst hh.2.2,?_⟩
  intro i
  have he:=congrFun (congrArg Prod.snd hh.2.2) ((M).origin ω.1.1.val.1 i)
  exact he.trans ((M).restore_origin ω.1.1.val.1 ((e ω.1.1).source ω.1.2) i)

omit [Finite K] [FiniteDimensional K V] in
lemma attachedPrepared_original (f : Ω→ℝ) :
    (∑ ω,(attachedPrepared w n k p θ G t hp e).μ.mass ω*f ω.2)=∑ x,p.mass x*f x :=
  (attachedPrepared w n k p θ G t hp e).integral f

omit [Finite K] [FiniteDimensional K V] in
lemma attachedPrepared_left (f : (mixedPrepared w n k p θ G t hp e).Ω→ℝ) :
    (∑ ω,(attachedPrepared w n k p θ G t hp e).μ.mass ω*f ω.1)=
      ∑ x,(mixedPrepared w n k p θ G t hp e).μ.mass x*f x :=
  Law.attach_left _ _ _ _ _

omit [Finite K] [FiniteDimensional K V] in
theorem attachedPrepared_loss {A : Type} [Fintype A] (ρ : Law A)
    (N : ℕ) (pop : (M).FreshHistory→ℕ)
    (out : A→(mixedPrepared w n k p θ G t hp e).Ω→ℕ) (δ B : ℝ) (hδ : 0≤δ)
    (hsize : ∀ z,pop z≤N)
    (hlocal : ∀ z,(∑ a,ρ.mass a*∑ y,(e z).μ.mass y*
      ((pop z.val:ℝ)-(out a ⟨z,y⟩:ℝ)))≤(pop z.val:ℝ)*δ)
    (hdelete : (∑ z,((M).freshLaw hp).mass z*((N:ℝ)-(pop z:ℝ)))≤B) :
    (∑ a,ρ.mass a*∑ ω,(attachedPrepared w n k p θ G t hp e).μ.mass ω*
      ((N:ℝ)-(out a ω.1:ℝ)))≤B+(N:ℝ)*δ := by
  have heq : (∑ a,ρ.mass a*∑ ω,(attachedPrepared w n k p θ G t hp e).μ.mass ω*
      ((N:ℝ)-(out a ω.1:ℝ)))=
      ∑ a,ρ.mass a*∑ y,(mixedPrepared w n k p θ G t hp e).μ.mass y*
        ((N:ℝ)-(out a y:ℝ)) := by
    apply sum_congr rfl
    intro a _
    congr 1
    exact attachedPrepared_left w n k p θ G t hp e (fun y=>(N:ℝ)-(out a y:ℝ))
  rw [heq]
  exact (Law.mixed_loss ((M).freshLaw hp) (fun z=>(e z).μ) ρ N pop out δ hδ hsize hlocal).trans
    (add_le_add hdelete le_rfl)
end
end SharpLogRamsey.Selection.Windows

end

end OAI
