import OAI.NumberTheory.PrimePackets.RootRelations

namespace OAI

/-! # A generic lattice stabilizer cannot have an identity column -/

noncomputable section
open Matrix MeasureTheory

namespace DukePrimeDegree
open PrimeDegreePackets

theorem stabilizer_trivial_of_identity_column {n : ℕ} (x : X n)
    (hx : ∀ v ∈ pointLattice x, v ≠ 0 → ∀ j, v j ≠ 0)
    (g : G n) (hfix : rightAction x g = x) (k : Fin n)
    (hcol : ∀ r, g.val r k = (1 : Matrix (Fin n) (Fin n) ℝ) r k) : g = 1 := by
  have hvec (v : Fin n → ℝ) (hv : v ∈ pointLattice x) : v ᵥ* g.val = v := by
    let w := v ᵥ* g.val - v
    have hw : w ∈ pointLattice x := by
      apply Submodule.sub_mem _ _ hv
      simpa only [hfix] using vecMul_mem_pointLattice_rightAction x g v hv
    have he : (v ᵥ* g.val) k = v k := by
      calc
        _ = (v ᵥ* (1 : Matrix (Fin n) (Fin n) ℝ)) k := by
          change (∑ r, v r * g.val r k) = ∑ r, v r * (1 : Matrix (Fin n) (Fin n) ℝ) r k
          simp_rw [hcol]
        _ = _ := by rw [Matrix.vecMul_one]
    have hwk : w k = 0 := by change (v ᵥ* g.val) k - v k = 0; exact sub_eq_zero.mpr he
    have hw0 : w = 0 := by
      by_contra h
      exact hx w hw h k hwk
    exact sub_eq_zero.mp hw0
  induction x using Quotient.inductionOn with
  | h q =>
    have hm : q.val * g.val = q.val := by
      ext r s
      have hmem : q.val r ∈ pointLattice (Quotient.mk _ q) := by
        rw [pointLattice_mk, ← integerRowMap_range]
        refine ⟨Pi.single r 1, ?_⟩
        ext j
        simp [integerRowMap_apply, Matrix.vecMul, dotProduct, Pi.single_apply]
      exact congrFun (hvec (q.val r) hmem) s
    have hgroup : q * g = q := Subtype.ext hm
    exact mul_left_cancel (hgroup.trans (mul_one q).symm)

end DukePrimeDegree

end

end OAI
