import OAI.Combinatorics.Progressions.Linear.AllocatedKernelScaleWithCutoff

namespace OAI

section

namespace Erdos3.VectorPolynomial

variable {m : ℕ} {I : Fin m → Type*} {n : Fin m → ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)

theorem allocatedGridAxis_of_axisScale_exp_bound {P : ℝ} {L : ℕ}
    (haxis : ∀ j i, (basisAxisScale (basis j) i : ℝ) ≤ Real.exp P)
    (hL : ⌈Real.exp P⌉₊ ≤ L) :
    ∀ j i, allocatedGridAxis (I := I) U basis L ⟨j, Sum.inr i⟩ := by
  have hLpos : 0 < L := (Nat.ceil_pos.mpr (Real.exp_pos P)).trans_le hL
  intro j i
  change basisAxisScale (basis j) i ≤ L^(layerTailDegree m+1)
  have haxisL : basisAxisScale (basis j) i ≤ L :=
    (Nat.cast_le.mp ((haxis j i).trans (Nat.le_ceil _))).trans hL
  apply haxisL.trans
  simpa only [pow_one] using
    Nat.pow_le_pow_right hLpos (show 1 ≤ layerTailDegree m+1 by omega)

theorem allocatedTailCutoffCompatible_of_axisScale_exp_bound {P : ℝ} {L : ℕ}
    (haxis : ∀ j i, (basisAxisScale (basis j) i : ℝ) ≤ Real.exp P)
    (hL : ⌈Real.exp P⌉₊ ≤ L) (d : ℕ) :
    AllocatedTailCutoffCompatible U basis L d :=
  allocatedTailCutoffCompatible_of_moderate U basis L d
    (allocatedGridAxis_of_axisScale_exp_bound (I := fun _ : Fin m => Fin 0) U basis haxis hL)

noncomputable def allocatedAllGridScaleFloor (Lmin : ℕ) (P : ℝ) : ℕ :=
  max Lmin ⌈Real.exp P⌉₊

theorem allocatedAllGridScaleFloor_bounds (Lmin : ℕ) {P Pmin : ℝ}
    (hP : 0 ≤ P) (hPmin : 0 ≤ Pmin) (hLmin : (Lmin : ℝ) ≤ Real.exp Pmin) :
    Lmin ≤ allocatedAllGridScaleFloor Lmin P ∧
    ⌈Real.exp P⌉₊ ≤ allocatedAllGridScaleFloor Lmin P ∧
    (allocatedAllGridScaleFloor Lmin P : ℝ) ≤ Real.exp (Pmin+P+1) := by
  refine ⟨le_max_left _ _, le_max_right _ _, ?_⟩
  simp only [allocatedAllGridScaleFloor, Nat.cast_max]
  apply max_le
  · exact hLmin.trans (Real.exp_le_exp.mpr (by linarith only [hP]))
  · exact (ceil_exp_le_exp_add_one hP).trans
      (Real.exp_le_exp.mpr (by linarith only [hPmin]))

end Erdos3.VectorPolynomial

end

end OAI
