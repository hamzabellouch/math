import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumForkListDegree

namespace OAI

/-! Initial mediator singlets have degree one and avoid every original center. -/

noncomputable section
namespace ContinuumCoulomb.QuantumForkList
open MediatorListProgram
open scoped BigOperators Classical

def singletBonds (n m : ℕ) (R : ℚ) : List Bond :=
  (List.range m).map (fun e => (n+2*e,n+2*e+1,R^2))

theorem singlet_degree_le_one (n m : ℕ) (R : ℚ) (v : ℕ) :
    degree (singletBonds n m R) v ≤ 1 := by
  have hinj : Function.Injective (fun p : Fin m × Fin 2 => n+2*p.1.val+p.2.val) := by
    rintro ⟨e,b⟩ ⟨f,c⟩ h
    change n+2*e.val+b.val=n+2*f.val+c.val at h
    have hb := b.isLt
    have hc := c.isLt
    apply Prod.ext
    · apply Fin.ext
      change e.val=f.val
      omega
    · apply Fin.ext
      change b.val=c.val
      omega
  have hh := qmaCount_eq_le_one _ hinj v
  have he : degree (singletBonds n m R) v=
      ∑ p : Fin m × Fin 2, if n+2*p.1.val+p.2.val=v then 1 else 0 := by
    simp only [degree,incident,singletBonds,List.map_map,Function.comp_def,range_sum,
      Fintype.sum_prod_type,Fin.sum_univ_two,Nat.add_zero,Fin.val_zero,Fin.val_one]
    apply Finset.sum_congr rfl
    intro e _
    split_ifs <;> omega
  rw [he]
  exact hh

theorem singlet_degree_center (n m : ℕ) (R : ℚ) (v : ℕ) (hv : v<n) :
    degree (singletBonds n m R) v=0 := by
  simp only [degree,incident,singletBonds,List.map_map,Function.comp_def,range_sum]
  apply Finset.sum_eq_zero
  intro e _
  have h0 : n+2*e.val ≠ v := by omega
  have h1 : n+2*e.val+1 ≠ v := by omega
  simp only [h0,h1,false_or,ite_false]

theorem initial_degreeBounds (n : ℕ) (bs : List Bond) (c N : ℚ) :
    DegreeBounds (initial n bs c N) where
  ordinary := by
    intro v
    exact (singlet_degree_le_one n bs.length (initialScale N bs c) v.val).trans (by decide)
  center := by
    intro i hi
    have hi' : i<n := by simpa only [initial,List.length_map,List.length_range] using hi
    exact singlet_degree_center n bs.length (initialScale N bs c) i hi'
  port := by
    intro i j
    exact singlet_degree_le_one n bs.length (initialScale N bs c) _

end ContinuumCoulomb.QuantumForkList

end

end OAI
