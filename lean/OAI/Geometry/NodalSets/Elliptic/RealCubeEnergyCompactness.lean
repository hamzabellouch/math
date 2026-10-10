import OAI.Geometry.NodalSets.Elliptic.RealCountableScalarCompactness
import OAI.Geometry.NodalSets.Elliptic.RealCubeCellDistance
import OAI.Geometry.NodalSets.Elliptic.RealFiniteWeightedCauchy

namespace OAI

namespace Yau.Geometry
open MeasureTheory Set Filter
open scoped ContDiff Topology
noncomputable section

theorem real_countable_cube_energy_subsequence {P : Type*} [Countable P]
    (W : P → ℕ → Yau.Jets.Coord → ℝ)
    (hW : ∀ p j, ContDiff ℝ ∞ (W p j)) (C : P → ℝ) (hC : ∀ p, 0 < C p)
    (hbound : ∀ p j, (∫ x in realFinCube 4, (W p j x)^2)+
      (∫ x in realFinCube 4, ∑ i, (Yau.coordPartial (W p j) x i)^2) ≤ C p) :
    ∃ nu : ℕ → ℕ, StrictMono nu ∧ ∀ p, ∀ eps > 0, ∃ N : ℕ,
      ∀ i ≥ N, ∀ j ≥ N, (∫ x in realFinCube 4, (W p (nu i) x-W p (nu j) x)^2) < eps := by
  have hs (p : P) (j : ℕ) : (∫ x in realFinCube 4, (W p j x)^2) ≤ C p :=
    (le_add_of_nonneg_right (integral_nonneg (fun x ↦ Finset.sum_nonneg (fun i _ ↦ sq_nonneg _)))).trans (hbound p j)
  have he (p : P) (j : ℕ) : (∫ x in realFinCube 4, ∑ i, (Yau.coordPartial (W p j) x i)^2) ≤ C p :=
    (le_add_of_nonneg_left (integral_nonneg (fun x ↦ sq_nonneg (W p j x)))).trans (hbound p j)
  let I := P × ((n : ℕ) × (Fin 4 → Fin (n+1)))
  let a : ℕ → I → ℝ := fun j k ↦ realCubeCellMean (W k.1 j) (k.2.1+1) k.2.2
  let B : I → ℝ := fun k ↦ C k.1/(2/((k.2.1+1:ℕ):ℝ))^4+1
  have hb (j : ℕ) (k : I) : |a j k| ≤ B k :=
    realCubeCell_mean_bound (Nat.succ_pos k.2.1) k.2.2 (W k.1 j) (hW k.1 j).continuous (hC k.1).le (hs k.1 j)
  obtain ⟨f,nu,hnu,ht⟩ := real_countable_bounded_subsequence a B hb
  refine ⟨nu,hnu,?_⟩
  intro p eps heps
  obtain ⟨m,hm⟩ := exists_nat_gt (32*C p/eps)
  have hnR : (1:ℝ) ≤ ((m+1:ℕ):ℝ) := by exact_mod_cast (Nat.succ_le_succ (Nat.zero_le m))
  have hn0 : (0:ℝ) < ((m+1:ℕ):ℝ) := zero_lt_one.trans_le hnR
  have hsize : 16*C p/((m+1:ℕ):ℝ)^2 < eps/2 := by
    have hbig : 32*C p/eps < ((m+1:ℕ):ℝ) := hm.trans (by exact_mod_cast Nat.lt_succ_self m)
    have hh := (div_lt_iff₀ heps).mp hbig
    have hsquare : ((m+1:ℕ):ℝ) ≤ ((m+1:ℕ):ℝ)^2 := by nlinarith
    apply (div_lt_iff₀ (sq_pos_of_pos hn0)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hsquare heps.le]
  obtain ⟨N,hN⟩ := real_finite_weighted_cauchy
    (fun (j : ℕ) (k : Fin 4 → Fin (m+1)) ↦ realCubeCellMean (W p (nu j)) (m+1) k)
    (fun k ↦ f ⟨p,m,k⟩) (fun _ ↦ (2/((m+1:ℕ):ℝ))^4)
    (fun _ ↦ by positivity) (fun k ↦ ht ⟨p,m,k⟩) (eps/2) (by linarith)
  refine ⟨N,fun i hi j hj ↦ ?_⟩
  have h := realCubeCell_distance_bound (Nat.succ_pos m) (W p (nu i)) (W p (nu j)) (hW p (nu i)) (hW p (nu j))
  have henergy := mul_le_mul_of_nonneg_left (add_le_add (he p (nu i)) (he p (nu j)))
    (show 0 ≤ 8/((m+1:ℕ):ℝ)^2 by positivity)
  have henergy' : (8/((m+1:ℕ):ℝ)^2)*
      ((∫ x in realFinCube 4, ∑ k, (Yau.coordPartial (W p (nu i)) x k)^2)+
        (∫ x in realFinCube 4, ∑ k, (Yau.coordPartial (W p (nu j)) x k)^2)) < eps/2 := by
    apply henergy.trans_lt
    calc
      _ = 16*C p/((m+1:ℕ):ℝ)^2 := by ring
      _ < _ := hsize
  exact h.trans_lt (by linarith [henergy',hN i hi j hj])

theorem real_cube_energy_subsequence (W : ℕ → Yau.Jets.Coord → ℝ)
    (hW : ∀ j, ContDiff ℝ ∞ (W j)) {C : ℝ} (hC : 0 < C)
    (hbound : ∀ j, (∫ x in realFinCube 4, (W j x)^2)+
      (∫ x in realFinCube 4, ∑ i, (Yau.coordPartial (W j) x i)^2) ≤ C) :
    ∃ nu : ℕ → ℕ, StrictMono nu ∧ ∀ eps > 0, ∃ N : ℕ,
      ∀ i ≥ N, ∀ j ≥ N, (∫ x in realFinCube 4, (W (nu i) x-W (nu j) x)^2) < eps := by
  obtain ⟨nu,hnu,h⟩ := real_countable_cube_energy_subsequence
    (fun _ : Unit ↦ W) (fun _ ↦ hW) (fun _ ↦ C) (fun _ ↦ hC) (fun _ ↦ hbound)
  exact ⟨nu,hnu,h ()⟩

end
end Yau.Geometry

end OAI
