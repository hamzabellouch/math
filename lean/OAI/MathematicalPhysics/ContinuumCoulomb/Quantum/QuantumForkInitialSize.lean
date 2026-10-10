import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumForkInitial

namespace OAI

/-! Explicit linear-size bounds for the constant-round degree reduction. -/

noncomputable section
namespace ContinuumCoulomb
open scoped BigOperators Classical

theorem qmaOriginalPortCount_sum {n m : ℕ} (left right : Fin m → Fin n) :
    (∑ i, qmaOriginalPortCount left right i) = 2*m := by
  calc
    _ = Fintype.card (Σ i, Fin (qmaOriginalPortCount left right i)) := by
      simp only [Fintype.card_sigma,Fintype.card_fin]
    _ = Fintype.card (Fin m × Fin 2) := Fintype.card_congr (qmaOriginalPortEquiv left right)
    _ = 2*m := by simp only [Fintype.card_prod,Fintype.card_fin]; omega

theorem qmaSubdivision_vertices {n m : ℕ} (left right : Fin m → Fin n) (D : ℕ) :
    ((qmaSubdivisionNetwork left right).iterate D).n ≤ n+2*m+4*D*m := by
  have h := (qmaSubdivisionNetwork left right).iterate_vertices D
  change ((qmaSubdivisionNetwork left right).iterate D).n ≤
    n+m*2+2*D*(∑ i, qmaOriginalPortCount left right i) at h
  rw [qmaOriginalPortCount_sum] at h
  convert h using 1; ring

theorem qmaSubdivision_edges {n m : ℕ} (left right : Fin m → Fin n) (D : ℕ) :
    Fintype.card (((qmaSubdivisionNetwork left right).iterate D).Edge ⊕
      (Σ i, Fin (((qmaSubdivisionNetwork left right).iterate D).degree i))) ≤ 3*m+8*D*m := by
  let G := qmaSubdivisionNetwork left right
  have hb := G.iterate_background_edges D
  have hm := G.iterate_mass_le D
  have hs : (∑ i, G.degree i) = 2*m := qmaOriginalPortCount_sum left right
  have he : Fintype.card G.Edge = m := Fintype.card_fin m
  rw [hs,he] at hb
  rw [hs] at hm
  change Fintype.card ((G.iterate D).Edge ⊕ (Σ i, Fin ((G.iterate D).degree i))) ≤ _
  simp only [Fintype.card_sum,Fintype.card_sigma,Fintype.card_fin]
  calc
    _ ≤ (m+4*D*(2*m))+2*m := Nat.add_le_add hb hm
    _ = 3*m+8*D*m := by ring

end ContinuumCoulomb

end

end OAI
