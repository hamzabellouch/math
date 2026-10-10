import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumSpatialModel
import Mathlib.Order.Interval.Finset.Nat

namespace OAI

/-! Neighboring-cell geometry gives a constant interaction-degree bound. -/

noncomputable section
namespace ContinuumCoulomb
open scoped BigOperators Classical

def qmaLineNeighbors {n : ℕ} (p : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun q => q.val ≤ p.val+1 ∧ p.val ≤ q.val+1)

theorem qmaLineNeighbors_card {n : ℕ} (p : Fin n) : (qmaLineNeighbors p).card ≤ 3 := by
  have hm : (qmaLineNeighbors p).card ≤ (Finset.Icc (p.val-1) (p.val+1)).card := by
    apply Finset.card_le_card_of_injOn Fin.val
    · intro q hq
      have h := (Finset.mem_filter.mp hq).2
      simp only [Finset.mem_coe,Finset.mem_Icc]
      omega
    · intro q _ r _ h
      exact Fin.ext h
  rw [Nat.card_Icc] at hm
  omega

def qmaGridNeighbors {rows width : ℕ} (p : QMAGridCell rows width) :
    Finset (QMAGridCell rows width) := qmaLineNeighbors p.1 ×ˢ qmaLineNeighbors p.2

theorem qmaGridNeighbors_mem {rows width : ℕ} (p q : QMAGridCell rows width) :
    q ∈ qmaGridNeighbors p ↔ QMAGridCellsNear q p := by
  simp only [qmaGridNeighbors,Finset.mem_product,qmaLineNeighbors,Finset.mem_filter,
    Finset.mem_univ,true_and,QMAGridCellsNear]
  tauto

theorem qmaGridNeighbors_card {rows width : ℕ} (p : QMAGridCell rows width) :
    (qmaGridNeighbors p).card ≤ 9 := by
  rw [qmaGridNeighbors,Finset.card_product]
  exact (Nat.mul_le_mul (qmaLineNeighbors_card p.1) (qmaLineNeighbors_card p.2)).trans (by decide)

theorem qmaGrid_incidence_bound {Q E : Type*} [Fintype E] [DecidableEq Q]
    {rows width B : ℕ} (cell : Q → QMAGridCell rows width)
    (anchor : E → QMAGridCell rows width) (sites : E → Finset Q)
    (hlocal : ∀ a, ∀ q ∈ sites a, QMAGridCellsNear (cell q) (anchor a))
    (hdensity : ∀ p, (Finset.univ.filter (fun a => anchor a = p)).card ≤ B) (q : Q) :
    (Finset.univ.filter (fun a => q ∈ sites a)).card ≤ 9*B := by
  let near := qmaGridNeighbors (cell q)
  let fiber := fun p => Finset.univ.filter (fun a => anchor a = p)
  have hs : Finset.univ.filter (fun a => q ∈ sites a) ⊆ near.biUnion fiber := by
    intro a ha
    apply Finset.mem_biUnion.mpr
    refine ⟨anchor a,?_,?_⟩
    · apply (qmaGridNeighbors_mem _ _).mpr
      exact qmaGridCellsNear_symm (hlocal a q (Finset.mem_filter.mp ha).2)
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,rfl⟩
  calc
    _ ≤ (near.biUnion fiber).card := Finset.card_le_card hs
    _ ≤ ∑ p ∈ near, (fiber p).card := Finset.card_biUnion_le
    _ ≤ ∑ _p ∈ near, B := Finset.sum_le_sum (fun p _ => hdensity p)
    _ = near.card*B := by simp
    _ ≤ 9*B := Nat.mul_le_mul_right B (qmaGridNeighbors_card _)


theorem QMASpatialModel.incidence_bound {d A B : ℕ} (M : QMASpatialModel d A B) (q : M.Q) :
    (Finset.univ.filter (fun a => q ∈ M.sites a)).card ≤ 9*B :=
  qmaGrid_incidence_bound M.cell M.anchor M.sites M.geometry M.termDensity q

theorem qmaGrid_density_card {Q : Type*} [Fintype Q] {rows width A : ℕ}
    (cell : Q → QMAGridCell rows width)
    (hdensity : ∀ p, (Finset.univ.filter (fun q => cell q = p)).card ≤ A) :
    Fintype.card Q ≤ (rows+1)*(width+1)*A := by
  calc
    Fintype.card Q = ∑ p : QMAGridCell rows width,
        (Finset.univ.filter (fun q => cell q = p)).card := by
      exact Finset.card_eq_sum_card_fiberwise (fun _ _ => Finset.mem_univ _)
    _ ≤ ∑ _p : QMAGridCell rows width, A :=
      Finset.sum_le_sum (fun p _ => hdensity p)
    _ = (rows+1)*(width+1)*A := by simp [Fintype.card_prod]

end ContinuumCoulomb

end

end OAI
