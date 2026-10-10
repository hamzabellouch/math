import OAI.Geometry.EinsteinFour.DirichletEndpointInvertible

namespace OAI

/-! Positivity of the full discrete form controls every Jacobi endpoint. -/
namespace PositiveEinsteinFour.Jacobi
open Matrix
noncomputable section

theorem dirichlet_leading_posDef (D : ℕ → NormalMatrix) {n N : ℕ} (hn : n ≤ N)
    (hpos : (dirichletMatrix (fun i : Fin N => D i.val)).PosDef) :
    (dirichletMatrix (fun i : Fin n => D i.val)).PosDef := by
  let f : Fin 3 × Fin n → Fin 3 × Fin N := fun p => (p.1, Fin.castLE hn p.2)
  have hf : Function.Injective f := by
    intro p q h
    apply Prod.ext
    · exact congrArg (fun z : Fin 3 × Fin N => z.1) h
    · apply Fin.ext
      exact congrArg (fun z => z.2.val) h
  convert hpos.submatrix hf using 1
  ext ⟨a,i⟩ ⟨b,j⟩
  simp [dirichletMatrix, Matrix.submatrix, f]

theorem jacobi_prefix_isUnit_of_dirichlet_posDef
    (D Y : ℕ → NormalMatrix) (N : ℕ)
    (h0 : Y 0 = 0) (h1 : Y 1 = 1)
    (hrec : ∀ i, Y (i + 2) = D i * Y (i + 1) - Y i)
    (hpos : (dirichletMatrix (fun i : Fin N => D i.val)).PosDef)
    (i : ℕ) (hi : 1 ≤ i) (hiN : i ≤ N + 1) : IsUnit (Y i) := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
  exact jacobi_endpoint_isUnit_of_dirichlet_posDef D Y n h0 h1 hrec
    (dirichlet_leading_posDef D (by omega) hpos)

theorem curvatureDirichlet_determinant_of_posDef {N : ℕ} {t : ℝ} (ht : t ≠ 0)
    (R : ℕ → NormalMatrix) (hsym : ∀ i, (R i)ᵀ = R i)
    (hpos : (curvatureDirichlet t (fun i : Fin N => R (i.val + 1) - 1)).PosDef) :
    (curvatureDirichlet t (fun i : Fin N => R (i.val + 1) - 1)).det =
      (normalizedDiscrete R (t / (N + 1)) (N + 1)).det := by
  let D := fun i => (2 : ℝ) • (1 : NormalMatrix) - (t / (N + 1)) ^ 2 • R (i + 1)
  have hD : (dirichletMatrix (fun i : Fin N => D i.val)).PosDef := by
    simpa only [curvatureDirichlet_eq, add_sub_cancel] using hpos
  have hh : t / ((N : ℝ) + 1) ≠ 0 := div_ne_zero ht (by positivity)
  apply curvatureDirichlet_determinant ht R hsym
  intro i hi hiN
  exact (Matrix.isUnit_iff_isUnit_det _).mp
    (jacobi_prefix_isUnit_of_dirichlet_posDef D (normalizedDiscrete R (t / (N + 1))) N
      (normalizedDiscrete_zero _ _) (normalizedDiscrete_one _ hh)
      (normalizedDiscrete_recurrence R _) hD i hi hiN)

end
end PositiveEinsteinFour.Jacobi

end OAI
