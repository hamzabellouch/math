import OAI.NumberTheory.DukePrimeDegree.Dynamics.RootOrbitRationality

namespace OAI

/-!
# A generic finite root orbit has a commutative stabilizer centralizer

One invariant root forces one column of every centralizing matrix to be
scalar. In the rational centralizer, evaluation in that column is
faithful by genericity of the actual lattice. Rational centralizing
matrices therefore commute, and scalar extension gives the same result
for the real centralizer. This removes any need to exclude singleton
blocks before treating the larger homogeneous orbit group.
-/

noncomputable section
open Matrix Set MeasureTheory
open scoped Classical

namespace DukePrimeDegree
open PrimeDegreePackets

lemma offColumn_zero_of_commute_root {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n)
    (hM : Commute M (Matrix.transvection i j (1 : ℝ)))
    (a : Fin n) (hai : a ≠ i) : M a i = 0 := by
  have he := congrArg (fun A : Matrix (Fin n) (Fin n) ℝ => A a j) hM.eq
  simp only [Matrix.mul_transvection_apply_same,
    Matrix.transvection_mul_apply_of_ne (i := i) (j := j) a j hai 1 M, one_mul] at he
  linarith

/-- Genericity makes any column of the lattice matrix faithful for
rational matrices; the matrix here is not assumed diagonal. -/
theorem rationalMatrix_eq_zero_of_conjugate_column_zero {n : ℕ}
    (g : G n)
    (hgeneric : ∀ v ∈ rowLattice g.val, v ≠ 0 → ∀ j, v j ≠ 0)
    (B : Matrix (Fin n) (Fin n) ℚ) (i : Fin n)
    (hB : ∀ a, slMatrixConjugation g (rationalMatrixCast B) a i = 0) : B = 0 := by
  have hg : g.val * g⁻¹.val = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
      Matrix.SpecialLinearGroup.coe_one]
  have hconj : rationalMatrixCast B * g.val =
      g.val * slMatrixConjugation g (rationalMatrixCast B) := by
    simp only [slMatrixConjugation, ← mul_assoc, hg, one_mul]
  ext a b
  have hz : rationalRowMap g.val (B a) i = 0 := by
    simp only [rationalRowMap_apply, Matrix.vecMul, dotProduct]
    change (∑ k, (B a k : ℝ) * g.val k i) = 0
    change (rationalMatrixCast B * g.val) a i = 0
    rw [hconj, Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro k _
    rw [hB, mul_zero]
  have hv := rationalRowSpace_no_coordinate_zero g hgeneric
    (rationalRowMap g.val (B a)) ⟨B a, rfl⟩ i hz
  have ha : B a = 0 := rationalRowMap_injective g (hv.trans (map_zero _).symm)
  exact congrFun ha b

lemma commute_root_of_finite_root_orbit {n : ℕ}
    (g : G n) (L : Subgroup (G n))
    (μ : Measure (LatticeOrbitQuotient g L)) [IsFiniteMeasure μ] (hμ : μ ≠ 0)
    (hinv : ∀ h : L, μ.map (fun x => latticeOrbitRightAction g L x h) = μ)
    (i j : Fin n) (hij : i ≠ j)
    (hroot : Matrix.SpecialLinearGroup.transvection hij (1 : ℝ) ∈ L)
    (M : Matrix (Fin n) (Fin n) ℝ)
    (hM : ∀ s : pointOrbitStabilizer g L, Commute M s.val.val) :
    Commute M (Matrix.transvection i j (1 : ℝ)) := by
  let F := conjugationOrbitMap g L M hM
  let ν := μ.map F
  have hF : Continuous F := continuous_conjugationOrbitMap g L M hM
  have hm : Matrix.SpecialLinearGroup.transvection hij (-1 : ℝ) ∈ L := by
    simpa only [Matrix.SpecialLinearGroup.transvection_inv] using L.inv_mem hroot
  have hr : ν.map (rootMatrixConjugation i j 1) = ν := by
    rw [← slMatrixConjugation_root i j hij]
    exact conjugationOrbitMap_map_invariant g L M hM μ hinv
      ⟨Matrix.SpecialLinearGroup.transvection hij (-1 : ℝ), hm⟩
  have hae : ∀ᵐ x ∂μ, Commute (F x) (Matrix.transvection i j (1 : ℝ)) :=
    ae_of_ae_map hF.measurable.aemeasurable
      (ae_commute_root_of_conjugation_invariance ν i j hij hr)
  have hclosed : IsClosed {x | Commute (F x) (Matrix.transvection i j (1 : ℝ))} :=
    isClosed_eq (hF.mul continuous_const) (continuous_const.mul hF)
  have hbase : (Quotient.mk _ (1 : L) : LatticeOrbitQuotient g L) ∈ μ.support := by
    rw [latticeOrbit_support_eq_univ g L μ hμ hinv]
    trivial
  have he := Measure.support_subset_of_isClosed hclosed hae hbase
  change Commute (conjugationOrbitMap g L M hM (Quotient.mk _ (1 : L)))
    (Matrix.transvection i j (1 : ℝ)) at he
  rwa [conjugationOrbitMap_identity] at he

lemma conjugate_offColumn_zero_of_finite_root_orbit {n : ℕ}
    (g : G n) (L : Subgroup (G n))
    (μ : Measure (LatticeOrbitQuotient g L)) [IsFiniteMeasure μ] (hμ : μ ≠ 0)
    (hinv : ∀ h : L, μ.map (fun x => latticeOrbitRightAction g L x h) = μ)
    (i j : Fin n) (hij : i ≠ j)
    (hroot : Matrix.SpecialLinearGroup.transvection hij (1 : ℝ) ∈ L)
    (M : Matrix (Fin n) (Fin n) ℝ)
    (hM : ∀ s : pointOrbitStabilizer g L, Commute M s.val.val) :
    ∀ a, a ≠ i → M a i = 0 :=
  offColumn_zero_of_commute_root M i j
    (commute_root_of_finite_root_orbit g L μ hμ hinv i j hij hroot M hM)

private lemma commutator_column_zero {n : ℕ}
    (M N : Matrix (Fin n) (Fin n) ℝ) (i : Fin n)
    (hM : ∀ a, a ≠ i → M a i = 0) (hN : ∀ a, a ≠ i → N a i = 0) :
    ∀ a, (M * N - N * M) a i = 0 := by
  have hm (a : Fin n) : (M * N) a i = M a i * N i i := by
    rw [Matrix.mul_apply, Finset.sum_eq_single i]
    · intro b _ hbi
      rw [hN b hbi, mul_zero]
    · simp
  have hn (a : Fin n) : (N * M) a i = N a i * M i i := by
    rw [Matrix.mul_apply, Finset.sum_eq_single i]
    · intro b _ hbi
      rw [hM b hbi, mul_zero]
    · simp
  intro a
  rw [Matrix.sub_apply, hm, hn]
  by_cases hai : a = i
  · subst a
    ring
  · rw [hM a hai, hN a hai]
    simp

/-- A single invariant root makes the rational stabilizer centralizer
commutative at a generic lattice point. -/
theorem rationalStabilizer_commutative_of_finite_root_orbit {n : ℕ}
    (g : G n)
    (hgeneric : ∀ v ∈ rowLattice g.val, v ≠ 0 → ∀ j, v j ≠ 0)
    (L : Subgroup (G n))
    (μ : Measure (LatticeOrbitQuotient g L)) [IsFiniteMeasure μ] (hμ : μ ≠ 0)
    (hinv : ∀ h : L, μ.map (fun x => latticeOrbitRightAction g L x h) = μ)
    (i j : Fin n) (hij : i ≠ j)
    (hroot : Matrix.SpecialLinearGroup.transvection hij (1 : ℝ) ∈ L)
    (B C : Matrix (Fin n) (Fin n) ℚ)
    (hB : B ∈ (commutatorFamily (latticeStabilizerMatrix g L)).ker)
    (hC : C ∈ (commutatorFamily (latticeStabilizerMatrix g L)).ker) : Commute B C := by
  have hcol (D : Matrix (Fin n) (Fin n) ℚ)
      (hD : D ∈ (commutatorFamily (latticeStabilizerMatrix g L)).ker) :
      ∀ a, a ≠ i → slMatrixConjugation g (rationalMatrixCast D) a i = 0 := by
    apply conjugate_offColumn_zero_of_finite_root_orbit g L μ hμ hinv i j hij hroot
    intro s
    obtain ⟨γ, hγ⟩ := pointOrbitStabilizer_eq_conjugate g L s
    rw [← hγ]
    exact ((commute_rationalMatrixCast_iff D (latticeStabilizerMatrix g L γ)).mpr
      ((mem_commutatorFamily_ker _ _).mp hD γ)).map (slMatrixConjugationHom g)
  have hzero : B * C - C * B = 0 := by
    apply rationalMatrix_eq_zero_of_conjugate_column_zero g hgeneric _ i
    have he : slMatrixConjugation g (rationalMatrixCast (B * C - C * B)) =
        slMatrixConjugation g (rationalMatrixCast B) *
          slMatrixConjugation g (rationalMatrixCast C) -
        slMatrixConjugation g (rationalMatrixCast C) *
          slMatrixConjugation g (rationalMatrixCast B) := by
      change slMatrixConjugationLinear g
        ((Algebra.ofId ℚ ℝ).mapMatrix (B * C - C * B)) = _
      rw [map_sub, map_mul, map_mul, map_sub]
      exact congrArg₂ (fun X Y => X - Y)
        ((slMatrixConjugationHom g).map_mul _ _)
        ((slMatrixConjugationHom g).map_mul _ _)
    rw [he]
    exact commutator_column_zero _ _ i (hcol B hB) (hcol C hC)
  exact sub_eq_zero.mp hzero

private lemma commute_of_mem_span_pairwise {n : ℕ}
    {s : Set (Matrix (Fin n) (Fin n) ℝ)}
    (hcomm : ∀ M ∈ s, ∀ N ∈ s, Commute M N)
    {M N : Matrix (Fin n) (Fin n) ℝ}
    (hM : M ∈ Submodule.span ℝ s) (hN : N ∈ Submodule.span ℝ s) : Commute M N := by
  have hs : Submodule.span ℝ s ≤ (Subalgebra.centralizer ℝ s).toSubmodule := by
    apply Submodule.span_le.mpr
    intro A hA
    apply (Subalgebra.mem_centralizer_iff ℝ).mpr
    intro B hB
    exact (hcomm B hB A hA).eq
  have hMs := hs hM
  have hsM : Submodule.span ℝ s ≤
      (Subalgebra.centralizer ℝ ({M} : Set (Matrix (Fin n) (Fin n) ℝ))).toSubmodule := by
    apply Submodule.span_le.mpr
    intro A hA
    apply (Subalgebra.mem_centralizer_iff ℝ).mpr
    intro B hB
    have hBM : B = M := Set.mem_singleton_iff.mp hB
    subst B
    exact ((Subalgebra.mem_centralizer_iff ℝ).mp hMs A hA).symm
  exact (Subalgebra.mem_centralizer_iff ℝ).mp (hsM hN) M (by simp)

/-- Scalar extension transports the preceding commutativity to the full
real centralizer of the actual integral stabilizer. -/
theorem realStabilizer_commutative_of_finite_root_orbit {n : ℕ}
    (g : G n)
    (hgeneric : ∀ v ∈ rowLattice g.val, v ≠ 0 → ∀ j, v j ≠ 0)
    (L : Subgroup (G n))
    (μ : Measure (LatticeOrbitQuotient g L)) [IsFiniteMeasure μ] (hμ : μ ≠ 0)
    (hinv : ∀ h : L, μ.map (fun x => latticeOrbitRightAction g L x h) = μ)
    (i j : Fin n) (hij : i ≠ j)
    (hroot : Matrix.SpecialLinearGroup.transvection hij (1 : ℝ) ∈ L)
    (B C : Matrix (Fin n) (Fin n) ℝ)
    (hB : B ∈ (commutatorFamily
      (fun γ => rationalMatrixCast (latticeStabilizerMatrix g L γ))).ker)
    (hC : C ∈ (commutatorFamily
      (fun γ => rationalMatrixCast (latticeStabilizerMatrix g L γ))).ker) : Commute B C := by
  rw [latticeStabilizer_commutant_rational] at hB hC
  apply commute_of_mem_span_pairwise _ hB hC
  rintro _ ⟨D, hD, rfl⟩ _ ⟨E, hE, rfl⟩
  exact (commute_rationalMatrixCast_iff D E).mpr
    (rationalStabilizer_commutative_of_finite_root_orbit
      g hgeneric L μ hμ hinv i j hij hroot D E hD hE)

/-- Transport a centralizer element to the original integral coordinates. -/
lemma inverseConjugate_mem_realStabilizer {n : ℕ} (g : G n) (L : Subgroup (G n))
    (M : Matrix (Fin n) (Fin n) ℝ)
    (hM : ∀ s : pointOrbitStabilizer g L, Commute M s.val.val) :
    slMatrixConjugation g⁻¹ M ∈ (commutatorFamily
      (fun γ => rationalMatrixCast (latticeStabilizerMatrix g L γ))).ker := by
  rw [mem_commutatorFamily_ker]
  intro γ
  let h : L := ⟨(MulAut.conj g⁻¹)
    (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) γ.val), γ.property⟩
  have hs : h ∈ pointOrbitStabilizer g L := by
    change (MulAut.conj g) h.val ∈ integralGroup n
    refine ⟨γ.val, ?_⟩
    simp only [h, MulAut.conj_apply, inv_inv]
    simp [mul_assoc]
  have he : h.val.val = slMatrixConjugation g
      (rationalMatrixCast (latticeStabilizerMatrix g L γ)) := by
    rw [rationalMatrixCast_latticeStabilizer]
    simp only [h, slMatrixConjugation, MulAut.conj_apply, inv_inv,
      Matrix.SpecialLinearGroup.coe_mul]
  have hcomm := (hM ⟨h, hs⟩).map (slMatrixConjugationHom g⁻¹)
  change Commute (slMatrixConjugation g⁻¹ M)
    (slMatrixConjugation g⁻¹ h.val.val) at hcomm
  rw [he] at hcomm
  simpa only [← slMatrixConjugation_mul, mul_inv_cancel, slMatrixConjugation_one] using hcomm

/-- Commutativity in the actual orbit coordinates, with no diagonal-flow
or singleton-block hypothesis. -/
theorem pointStabilizer_commutative_of_finite_root_orbit {n : ℕ}
    (g : G n)
    (hgeneric : ∀ v ∈ rowLattice g.val, v ≠ 0 → ∀ j, v j ≠ 0)
    (L : Subgroup (G n))
    (μ : Measure (LatticeOrbitQuotient g L)) [IsFiniteMeasure μ] (hμ : μ ≠ 0)
    (hinv : ∀ h : L, μ.map (fun x => latticeOrbitRightAction g L x h) = μ)
    (i j : Fin n) (hij : i ≠ j)
    (hroot : Matrix.SpecialLinearGroup.transvection hij (1 : ℝ) ∈ L)
    (M N : Matrix (Fin n) (Fin n) ℝ)
    (hM : ∀ s : pointOrbitStabilizer g L, Commute M s.val.val)
    (hN : ∀ s : pointOrbitStabilizer g L, Commute N s.val.val) : Commute M N := by
  have he := (realStabilizer_commutative_of_finite_root_orbit g hgeneric L μ hμ hinv
    i j hij hroot _ _ (inverseConjugate_mem_realStabilizer g L M hM)
    (inverseConjugate_mem_realStabilizer g L N hN)).map (slMatrixConjugationHom g)
  change Commute (slMatrixConjugation g (slMatrixConjugation g⁻¹ M))
    (slMatrixConjugation g (slMatrixConjugation g⁻¹ N)) at he
  simpa only [slMatrixConjugation_inverse] using he

end DukePrimeDegree

end

end OAI
