import OAI.Geometry.HeilbronnTriangle.ZeroEqualMatrices
import OAI.Geometry.HeilbronnTriangle.ZeroAffineShell
import OAI.Geometry.HeilbronnTriangle.RowLatticeMatrices

namespace OAI


noncomputable section

namespace Problem355.RowLatticeEqualShell

open Matrix IntegralPlaneLattice PrimitiveNormal PairingDivisor
open scoped BigOperators

theorem weighted_matrix_shell_bound
    (q : ℕ) [Fact q.Prime] (L : Submodule ℤ (Fin 3 → ℤ))
    (E : ℕ) (hE : 0 < E) (hEq : IsUnit (E : ZMod q))
    (hcontain : ∀ v : Fin 3 → ℤ, E • v ∈ L)
    (i j : Fin 3) (hij : i ≠ j)
    (S : Finset (Fin 3 → ℤ))
    (hprimitive : ∀ x ∈ S, IsPrimitive x)
    (hspan : ∀ x ∈ S, ¬ ∃ a : ZMod q, (fun k => (x k : ZMod q)) =
      a • PlaneFunctional.coordinateDifference i j)
    (F : (Fin 3 → ℤ) → Finset (Matrix (Fin 3) (Fin 3) ℤ))
    (hF : ∀ x ∈ S, ∀ A ∈ F x, A *ᵥ x = 0 ∧ ∀ k, A k ∈ L)
    (W : Matrix (Fin 3) (Fin 3) ℤ → ℝ)
    (R N I h W₀ : ℝ) (hR : 1 ≤ R) (hN : 0 ≤ N)
    (hI : 0 < I) (hW₀ : 0 ≤ W₀)
    (hindex : (L.toAddSubgroup.index : ℝ) = I)
    (hEbound : (E : ℝ) ^ 3 ≤ I * h ^ 2)
    (hshell : ∀ x ∈ S, R ≤ ‖toEuclidean x‖ ∧ ‖toEuclidean x‖ ≤ 2 * R)
    (hequal : ∀ x ∈ S, ∀ A ∈ F x, ∀ k, (A k i : ZMod q) = (A k j : ZMod q))
    (hcoord : ∀ x ∈ S, ∀ A ∈ F x, ∀ k l, |(A k l : ℝ)| ≤ 2 * N)
    (hproj : ∀ x ∈ S, ∀ A ∈ F x, ∃ s t : Fin 3,
      A 2 s ≠ 0 ∧ A 2 t ≠ 0 ∧
      PlaneRowTransport.projectedColumn A s ≠ PlaneRowTransport.projectedColumn A t)
    (hW : ∀ x ∈ S, ∀ A ∈ F x, W A ≤ W₀) :
    (∑ x ∈ S, ∑ A ∈ F x, W A) ≤
      125 * (144 * Real.pi) ^ 3 * W₀ * N ^ 6 * h ^ 2 /
        ((q : ℝ) ^ 3 * I ^ 2) := by
  classical
  let z : (Fin 3 → ℤ) → Fin 3 → ℤ := fun x =>
    if hx : IsPrimitive x then
      Classical.choose ((isPrimitive_iff_exists_dot_eq_one x).mp hx)
    else 0
  have hz : ∀ x ∈ S, dotProduct x (z x) = 1 := by
    intro x hx
    dsimp [z]
    rw [dite_eq_left (hprimitive x hx)]
    exact Classical.choose_spec ((isPrimitive_iff_exists_dot_eq_one x).mp
      (hprimitive x hx))
  let g : (Fin 3 → ℤ) → ℝ := fun x => (pairingDivisor L.toAddSubgroup x : ℝ)
  have hgdata (x : Fin 3 → ℤ) (hx : x ∈ S) :
      0 < pairingDivisor L.toAddSubgroup x ∧ pairingDivisor L.toAddSubgroup x ∣ E :=
    pairingDivisor_pos_and_dvd L.toAddSubgroup x (z x) (hz x hx) E hE hcontain
  have hg : ∀ x ∈ S, 0 < g x := by
    intro x hx
    dsimp [g]
    exact_mod_cast (hgdata x hx).1
  have hg3 : ∀ x ∈ S, g x ^ 3 ≤ I * h ^ 2 := by
    intro x hx
    have hle : g x ≤ (E : ℝ) := by
      dsimp [g]
      exact_mod_cast Nat.le_of_dvd hE (hgdata x hx).2
    exact (pow_le_pow_left₀ (hg x hx).le hle 3).trans hEbound
  have hcov : ∀ x ∈ S, ZLattice.covolume (latticeIn x L) =
      I * ‖LatticeBox.realVector x‖ / g x := by
    intro x hx
    have hc := ZeroAffineShell.canonical_pairing_covolume x (hprimitive x hx)
      L E hE hcontain
    rw [hindex] at hc
    exact hc
  have hrow : ∀ x ∈ S, ∀ A ∈ F x, ∀ k, A k ∈ integerPlaneIn x L := by
    intro x hx A hA k
    refine ⟨(hF x hx A hA).2 k, ?_⟩
    change x ⬝ᵥ A k = 0
    rw [dotProduct_comm]
    exact congrFun (hF x hx A hA).1 k
  have hnorm : ∀ x ∈ S, ∀ A ∈ F x, ∀ k, ‖castVec (A k)‖ ≤ 4 * N := by
    intro x hx A hA k
    exact PlaneRowTransport.norm_rows_le_four_mul x
      ⟨A, (hF x hx A hA).1⟩ k hN (hcoord x hx A hA k)
  have hpair : ∀ x ∈ S, ∀ A ∈ F x, ∃ k l : Fin 3,
      LinearIndependent ℝ ![castVec (A k), castVec (A l)] := by
    intro x hx A hA
    obtain ⟨s, t, hs, ht, hne⟩ := hproj x hx A hA
    obtain ⟨k, _, hk⟩ := PlaneRowTransport.exists_minor_of_projected_columns_ne
      A s t hs ht hne
    refine ⟨k, 2, PlaneRowTransport.linearIndependent_of_minor_ne_zero
      (castVec (A k)) (castVec (A 2)) s t ?_⟩
    simp only [castVec_apply]
    exact_mod_cast hk
  have hb := ZeroEqualAdditional.weighted_matrix_shell_bound q L (E : ℤ)
    (by simpa using hEq) (by simpa only [Nat.cast_smul_eq_nsmul] using hcontain)
    i j hij S z hz hspan F W R (4 * N) I h W₀ hR (by positivity) hI hW₀
    g hshell hg hg3 hcov hrow hequal hnorm hpair hW
  calc
    _ ≤ 125 * W₀ * (9 * Real.pi) ^ 3 * (4 * N) ^ 6 * h ^ 2 /
        ((q : ℝ) ^ 3 * I ^ 2) := hb
    _ = _ := by ring

end Problem355.RowLatticeEqualShell

end

end OAI
