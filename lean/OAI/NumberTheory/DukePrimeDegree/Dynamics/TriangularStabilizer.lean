import OAI.NumberTheory.DukePrimeDegree.Dynamics.GenericLatticeStabilizer
import OAI.NumberTheory.PrimePackets.InverseEntropy

namespace OAI

/-!
# A trace gap for positive triangular lattice stabilizers

The trace of an actual lattice stabilizer is an integer.  A positive
triangular stabilizer of determinant one whose trace is less than `n+1`
therefore has all diagonal entries equal to one.  At the generic lattices
used in the entropy argument it is the identity.
-/

noncomputable section
open Matrix Set
open scoped BigOperators Topology

namespace DukePrimeDegree
open PrimeDegreePackets

lemma sum_ge_card_of_pos_prod_one {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (ha : ∀ i, 0 < a i) (hp : ∏ i, a i = 1) :
    (Fintype.card ι : ℝ) ≤ ∑ i, a i := by
  have hlog : ∑ i, Real.log (a i) = 0 := by
    rw [← Real.log_prod (fun i _ => (ha i).ne'), hp, Real.log_one]
  have h := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) =>
    Real.log_le_sub_one_of_pos (ha i)
  simpa only [hlog, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, mul_one, sub_nonneg] using h

lemma eq_one_of_pos_prod_one_sum_card {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (ha : ∀ i, 0 < a i) (hp : ∏ i, a i = 1)
    (hs : ∑ i, a i = Fintype.card ι) : ∀ i, a i = 1 := by
  classical
  intro j
  by_contra hj
  have hlog : ∑ i, Real.log (a i) = 0 := by
    rw [← Real.log_prod (fun i _ => (ha i).ne'), hp, Real.log_one]
  have h := Finset.sum_lt_sum
    (fun i (_ : i ∈ Finset.univ) => Real.log_le_sub_one_of_pos (ha i))
    ⟨j, Finset.mem_univ j, Real.log_lt_sub_one_of_pos (ha j) hj⟩
  simp only [hlog, Finset.sum_sub_distrib, hs, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, mul_one, sub_self, lt_self_iff_false] at h

/-- Actual lattice stabilizers have integral trace, by conjugating them
back to the integer special linear group. -/
theorem stabilizer_trace_integral {n : ℕ} (x : X n) (g : G n)
    (hfix : rightAction x g = x) : ∃ z : ℤ, g.val.trace = z := by
  obtain ⟨q, rfl⟩ := Quotient.exists_rep x
  have heq : Quotient.mk (QuotientGroup.rightRel (integralGroup n)) (q * g) =
      Quotient.mk (QuotientGroup.rightRel (integralGroup n)) q := hfix
  have hΓ : q * g * q⁻¹ ∈ integralGroup n :=
    QuotientGroup.rightRel_apply.mp (Quotient.exact heq.symm)
  obtain ⟨γ, hγ⟩ := hΓ
  refine ⟨γ.val.trace, ?_⟩
  have ht : (q * g * q⁻¹).val.trace = g.val.trace := by
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.trace_mul_cycle,
      ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.SpecialLinearGroup.coe_one, Matrix.one_mul]
  rw [← ht, ← hγ]
  change (γ.val.map (Int.castRingHom ℝ)).trace = _
  simp only [Matrix.trace, Matrix.diag, Matrix.map_apply, Int.cast_sum]
  rfl

/-- Positivity and the integral trace gap force the diagonal to be one. -/
theorem triangular_stabilizer_diagonal_eq_one {n : ℕ} (x : X n) (g : G n)
    (hfix : rightAction x g = x) (htri : g.val.IsUpperTriangular)
    (hpos : ∀ i, 0 < g.val i i) (htrace : g.val.trace < n + 1) :
    ∀ i, g.val i i = 1 := by
  have hp : ∏ i, g.val i i = 1 :=
    (Matrix.det_of_isUpperTriangular htri).symm.trans g.property
  have hlo : (n : ℝ) ≤ g.val.trace := by
    simpa only [Fintype.card_fin, Matrix.trace, Matrix.diag] using
      sum_ge_card_of_pos_prod_one (fun i => g.val i i) hpos hp
  obtain ⟨z, hz⟩ := stabilizer_trace_integral x g hfix
  have hzlo : (n : ℤ) ≤ z := by exact_mod_cast hz ▸ hlo
  have hzhi : z < (n : ℤ) + 1 := by exact_mod_cast hz ▸ htrace
  have hzn : z = n := by omega
  apply eq_one_of_pos_prod_one_sum_card (fun i => g.val i i) hpos hp
  simp only [Fintype.card_fin]
  change g.val.trace = (n : ℝ)
  rw [hz, hzn]
  simp

/-- In the generic locus a positive triangular stabilizer below the first
possible nonunipotent integral trace is trivial. -/
theorem triangular_stabilizer_eq_one {d : ℕ} (x : X (d+1))
    (hx : ∀ v ∈ pointLattice x, v ≠ 0 → ∀ j, v j ≠ 0)
    (g : G (d+1)) (hfix : rightAction x g = x)
    (htri : g.val.IsUpperTriangular) (hpos : ∀ i, 0 < g.val i i)
    (htrace : g.val.trace < (d+1 : ℕ) + 1) : g = 1 := by
  have hdiag := triangular_stabilizer_diagonal_eq_one x g hfix htri hpos htrace
  apply stabilizer_trivial_of_identity_column x hx g hfix 0
  intro r
  by_cases hr : r = 0
  · subst r
    simpa only [Matrix.one_apply_eq] using hdiag 0
  · have hlt : (0 : Fin (d+1)) < r := Fin.pos_iff_ne_zero.mpr hr
    rw [htri hlt, Matrix.one_apply_ne hr]

lemma upperTriangular_mul_diag {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.IsUpperTriangular) (hB : B.IsUpperTriangular) (i : Fin n) :
    (A * B) i i = A i i * B i i := by
  classical
  change (∑ j, A i j * B j i) = _
  apply Finset.sum_eq_single i
  · intro j _ hji
    rcases lt_or_gt_of_ne hji with h | h
    · rw [hA h, zero_mul]
    · rw [hB h, mul_zero]
  · simp

lemma specialLinear_upperTriangular_inv {n : ℕ} (g : G n)
    (htri : g.val.IsUpperTriangular) : (g⁻¹).val.IsUpperTriangular := by
  let : Invertible g.val := Matrix.invertibleOfIsUnitDet g.val
    (g.property.symm ▸ isUnit_one)
  have he : (g⁻¹).val = g.val⁻¹ := by
    rw [Matrix.inv_def, g.property, Ring.inverse_one, one_smul]
    rfl
  rw [he]
  exact Matrix.blockTriangular_inv_of_blockTriangular htri

/-- A sufficiently small triangular lift along a positive unipotent leaf
is the leaf element itself. The radius is independent of the lattice. -/
theorem exists_uniform_triangular_lift_radius (d : ℕ) :
    ∃ r : ℝ, 0 < r ∧ ∀ (x : X (d+1)),
      (∀ v ∈ pointLattice x, v ≠ 0 → ∀ j, v j ≠ 0) →
      ∀ (u g : G (d+1)), u.val.IsUpperTriangular → (∀ i, u.val i i = 1) →
      g ∈ matrixBall (d+1) r → g.val.IsUpperTriangular →
      rightAction x u = rightAction x g → u = g := by
  let V : Set (G (d+1)) := {g | (∀ i, 0 < (g⁻¹).val i i) ∧
    (g⁻¹).val.trace < (d+1 : ℕ) + 1}
  have htr : Continuous (fun g : G (d+1) => (g⁻¹).val.trace) := by
    change Continuous (fun g : G (d+1) => ∑ i, (g⁻¹).val i i)
    exact continuous_finsetSum _ fun i _ => by fun_prop
  have hV : V ∈ 𝓝 (1 : G (d+1)) := by
    apply IsOpen.mem_nhds
    · apply IsOpen.inter
      · change IsOpen {g : G (d+1) | ∀ i, 0 < (g⁻¹).val i i}
        simp only [Set.ofPred_forall]
        apply isOpen_iInter_of_finite
        intro i
        exact isOpen_lt continuous_const (by fun_prop)
      · exact isOpen_lt htr continuous_const
    · constructor
      · intro i
        simp
      · simp [Matrix.trace, Matrix.diag]
  obtain ⟨r, hr, hrV⟩ := matrixBall_nhds_basis hV
  refine ⟨r, hr, ?_⟩
  intro x hx u g hu hdu hg hgt heq
  have hginv := specialLinear_upperTriangular_inv g hgt
  have hv := hrV hg
  let a := u * g⁻¹
  have hfix : rightAction x a = x := by
    dsimp [a]
    rw [← rightAction_mul, heq, rightAction_mul, mul_inv_cancel, rightAction_one]
  have hdiag (i : Fin (d+1)) : a.val i i = (g⁻¹).val i i := by
    change (u.val * (g⁻¹).val) i i = _
    rw [upperTriangular_mul_diag _ _ hu hginv, hdu, one_mul]
  have hat : a.val.IsUpperTriangular := hu.mul hginv
  have htrace : a.val.trace = (g⁻¹).val.trace := by
    apply Finset.sum_congr rfl
    intro i _
    exact hdiag i
  have ha : a = 1 := triangular_stabilizer_eq_one x hx a hfix hat
    (fun i => (hdiag i).symm ▸ hv.1 i) (htrace.symm ▸ hv.2)
  exact mul_inv_eq_one.mp ha

end DukePrimeDegree

end

end OAI
