import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumRationalCrossing

namespace OAI

/-! Group a selected family of physical crossing edges without assuming a matrix
identity. Each source edge is either retained or assigned to one crossing pair. -/

noncomputable section
namespace ContinuumCoulomb
open scoped BigOperators Classical

theorem qmaSumSubtypePredicate {α M : Type*} [Fintype α] [AddCommMonoid M]
    (p : α → Prop) [DecidablePred p] (f : α → M) :
    (∑ a : {a // p a}, f a.val) = ∑ a, if p a then f a else 0 := by
  rw [← Finset.sum_subtype (Finset.univ.filter p) (by simp) f]
  exact Finset.sum_filter _ _

theorem qmaOptionFiberSum {α β M : Type*} [Fintype α] [Fintype β] [DecidableEq β] [AddCommMonoid M]
    (tag : α → Option β) (f : α → M) :
    (∑ a : {a // tag a = none}, f a.val) +
      (∑ b : β, ∑ a : {a // tag a = some b}, f a.val) = ∑ a, f a := by
  rw [qmaSumSubtypePredicate]
  simp_rw [qmaSumSubtypePredicate]
  rw [Finset.sum_comm,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  cases tag a with
  | none => simp
  | some b => simp [eq_comm]

structure QMARationalCrossingSelection (G : QMARationalExchangeGraph) (r : ℕ) where
  site : Fin r → Fin 4 → Fin G.n
  injective : ∀ i, Function.Injective (site i)
  tag : G.Edge → Option (Fin r × Fin 2)
  tagged : ∀ e i a, tag e = some (i,a) →
    (G.left e = site i (if a = 0 then 0 else 1) ∧ G.right e = site i (if a = 0 then 2 else 3)) ∨
    (G.left e = site i (if a = 0 then 2 else 3) ∧ G.right e = site i (if a = 0 then 0 else 1))

namespace QMARationalCrossingSelection
variable {G : QMARationalExchangeGraph} {r : ℕ} (S : QMARationalCrossingSelection G r)

abbrev retained : QMARationalExchangeGraph where
  n := G.n
  Edge := {e : G.Edge // S.tag e = none}
  left := fun e => G.left e.val
  right := fun e => G.right e.val
  distinct := fun e => G.distinct e.val
  weight := fun e => G.weight e.val
  constant := G.constant

def weight (p : Fin r × Fin 2) : ℚ := ∑ e : {e // S.tag e = some p}, G.weight e.val

def layer : QMARationalCrossingLayer r where
  base := S.retained
  site := S.site
  injective := S.injective
  J := fun i => S.weight (i,0)
  K := fun i => S.weight (i,1)

theorem tagged_matrix (e : G.Edge) (i : Fin r) (a : Fin 2) (he : S.tag e = some (i,a)) :
    sourceHeisenbergMatrix G.n (G.left e) (G.right e) =
      sourceHeisenbergMatrix G.n (S.site i (if a = 0 then 0 else 1))
        (S.site i (if a = 0 then 2 else 3)) := by
  rcases S.tagged e i a he with ⟨hl,hr⟩ | ⟨hl,hr⟩
  · rw [hl,hr]
  · rw [hl,hr,qmaHeisenberg_symm]

theorem weight_matrix (p : Fin r × Fin 2) :
    (S.weight p:ℂ) • sourceHeisenbergMatrix G.n (S.site p.1 (if p.2 = 0 then 0 else 1))
      (S.site p.1 (if p.2 = 0 then 2 else 3)) =
    ∑ e : {e // S.tag e = some p}, (G.weight e.val:ℂ) •
      sourceHeisenbergMatrix G.n (G.left e.val) (G.right e.val) := by
  unfold weight
  push_cast
  rw [Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro e _
  rw [S.tagged_matrix e.val p.1 p.2 e.property]

theorem source_matrix :
    qmaExchangeMatrix S.layer.source.left S.layer.source.right
      (fun e => (S.layer.source.weight e:ℝ)) S.layer.source.constant =
    qmaExchangeMatrix G.left G.right (fun e => (G.weight e:ℝ)) G.constant := by
  rw [S.layer.source_matrix]
  let f := fun e : G.Edge => (G.weight e:ℂ) • sourceHeisenbergMatrix G.n (G.left e) (G.right e)
  have hp := qmaOptionFiberSum S.tag f
  have hs : (∑ i, ((S.weight (i,0):ℂ) • sourceHeisenbergMatrix G.n (S.site i 0) (S.site i 2) +
      (S.weight (i,1):ℂ) • sourceHeisenbergMatrix G.n (S.site i 1) (S.site i 3))) =
      ∑ p : Fin r × Fin 2, ∑ e : {e // S.tag e = some p}, f e.val := by
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro i _
    rw [Fin.sum_univ_two]
    simpa only [f,ite_true,ite_false,show (1 : Fin 2) ≠ 0 from by decide] using
      congrArg₂ (· + ·) (S.weight_matrix (i,0)) (S.weight_matrix (i,1))
  change ((∑ e : {e // S.tag e = none}, f e.val)+(G.constant:ℂ) • 1)+
    (∑ i, ((S.weight (i,0):ℂ) • sourceHeisenbergMatrix G.n (S.site i 0) (S.site i 2) +
      (S.weight (i,1):ℂ) • sourceHeisenbergMatrix G.n (S.site i 1) (S.site i 3))) =
        (∑ e, f e)+(G.constant:ℂ) • 1
  rw [hs]
  calc
    _ = ((∑ e : {e // S.tag e = none}, f e.val)+
        ∑ p : Fin r × Fin 2, ∑ e : {e // S.tag e = some p}, f e.val)+(G.constant:ℂ) • 1 := by abel
    _ = _ := congrArg (fun x => x+(G.constant:ℂ) • 1) hp

theorem source_energy : S.layer.source.energy = G.energy := by
  unfold QMARationalExchangeGraph.energy
  rw [S.source_matrix]
  rfl

theorem output_energy_error {N : ℚ} (hN : 0 < N) :
    |(S.layer.output N).energy-G.energy| ≤ 1/(N:ℝ) := by
  rw [← S.source_energy]
  exact S.layer.output_energy_error hN

end QMARationalCrossingSelection
end ContinuumCoulomb

end

end OAI
