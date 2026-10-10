import OAI.Combinatorics.EuclideanRamsey.Main
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Basis.VectorSpace

namespace OAI

/-! Quadratic row independence gives a tensor lift and the Ramsey property. -/

noncomputable section
open scoped TensorProduct BigOperators RealInnerProductSpace Matrix

namespace EuclideanRamsey.Quadratic

theorem field_rightInverse {F ι ν : Type*} [Field F]
    [Fintype ι] [Fintype ν] [DecidableEq ι] [DecidableEq ν]
    (E : Matrix ι ν F) (hE : LinearIndependent F E.row) :
    ∃ S : Matrix ν ι F, E * S = 1 := by
  have hinj : Function.Injective E.vecMulLinear := Matrix.vecMul_injective_iff.mpr hE
  obtain ⟨g, hg⟩ := E.vecMulLinear.exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr hinj)
  let S : Matrix ν ι F := fun q j => g (Pi.single q 1) j
  refine ⟨S, ?_⟩
  ext i j
  have hrow : E.vecMulLinear (Pi.single i 1) = E i := by
    ext q
    change (∑ x : ι, (Pi.single i (1 : F) : ι → F) x * E x q) = E i q
    rw [Finset.sum_eq_single i]
    · simp
    · intro x _ hxi
      simp [hxi]
    · simp
  have hgi : g (E i) = Pi.single i 1 := by
    have ht := LinearMap.congr_fun hg (Pi.single i 1)
    simpa only [LinearMap.comp_apply, LinearMap.id_apply, hrow] using ht
  have hsum : (∑ q : ν, E i q • Pi.single q (1 : F)) = E i := by
    ext q
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_eq_single q]
    · simp
    · intro x _ hxq
      simp [Ne.symm hxq]
    · simp
  have ht := congrArg (fun x : ν → F => g x j) hsum
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at ht
  change (∑ q, E i q * g (Pi.single q 1) j) = _
  rw [ht, hgi]
  simp [Matrix.one_apply, Pi.single_apply, eq_comm]

theorem lift_kernel {F B ι ν : Type*} [Field F] [CommRing B]
    [Fintype ι] [Fintype ν] [DecidableEq ι] [DecidableEq ν]
    (μ : B →+* F) (σ : F →+* B) (hsection : ∀ x, μ (σ x) = x)
    (D : Matrix ι ν B) (hrows : LinearIndependent F (D.map μ).row)
    (h : ν → F) (hh : D.map μ *ᵥ h = 0) :
    ∃ z : ν → B, D *ᵥ z = 0 ∧ (fun q => μ (z q)) = h := by
  obtain ⟨S, hS⟩ := field_rightInverse (D.map μ) hrows
  let J : Matrix ν ι B := S.map σ
  let M : Matrix ι ι B := D * J
  let b : ν → B := fun q => σ (h q)
  have hJ : J.map μ = S := by
    ext q i
    exact hsection _
  have hM : M.map μ = 1 := by
    calc
      M.map μ = D.map μ * J.map μ := by
        ext i j
        simp [M, Matrix.mul_apply]
      _ = 1 := by rw [hJ, hS]
  have hdet : μ M.det = 1 := by
    rw [μ.map_det]
    change (M.map μ).det = 1
    rw [hM, Matrix.det_one]
  have hb : (fun q => μ (b q)) = h := by
    funext q
    exact hsection _
  have hDb : (fun i => μ ((D *ᵥ b) i)) = 0 := by
    ext i
    rw [μ.map_mulVec]
    change (D.map μ *ᵥ (fun q => μ (b q))) i = 0
    rw [hb, hh]
    rfl
  let z : ν → B := M.det • b - J *ᵥ (M.adjugate *ᵥ (D *ᵥ b))
  refine ⟨z, ?_, ?_⟩
  · change D *ᵥ (M.det • b - J *ᵥ (M.adjugate *ᵥ (D *ᵥ b))) = 0
    rw [Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_mulVec]
    change M.det • (D *ᵥ b) - M *ᵥ (M.adjugate *ᵥ (D *ᵥ b)) = 0
    rw [Matrix.mulVec_mulVec, Matrix.mul_adjugate, Matrix.smul_mulVec,
      Matrix.one_mulVec, sub_self]
  · have hAdj : (fun i => μ ((M.adjugate *ᵥ (D *ᵥ b)) i)) = 0 := by
      ext i
      rw [μ.map_mulVec]
      change (M.adjugate.map μ *ᵥ (fun j => μ ((D *ᵥ b) j))) i = 0
      rw [hDb, Matrix.mulVec_zero]
      rfl
    have hCorrection : (fun q => μ ((J *ᵥ (M.adjugate *ᵥ (D *ᵥ b))) q)) = 0 := by
      ext q
      rw [μ.map_mulVec]
      change (J.map μ *ᵥ (fun i => μ ((M.adjugate *ᵥ (D *ᵥ b)) i))) q = 0
      rw [hAdj, Matrix.mulVec_zero]
      rfl
    funext q
    change μ (M.det * b q - (J *ᵥ (M.adjugate *ᵥ (D *ᵥ b))) q) = h q
    rw [map_sub, map_mul, hdet, one_mul, congrFun hCorrection q]
    change μ (b q) - (0 : F) = h q
    rw [sub_zero]
    exact congrFun hb q

end EuclideanRamsey.Quadratic

namespace EuclideanRamsey

abbrev QuadraticIndex (d : ℕ) := Option (Fin d) × Option (Fin d)

def augmentedQuadraticRows {s d : ℕ} (a : Fin s → Space d) :
    Matrix (Fin s) (QuadraticIndex d) (Coeff a) :=
  fun i q => augmented a i q.1 * augmented a i q.2

theorem sphere_field_quadratic {s d : ℕ} (a : Fin s → Space d)
    (hsphere : ∃ c : Space d, ∃ r : ℝ, ∀ i, dist (a i) c = r) :
    ∃ h : QuadraticIndex d → Coeff a,
      augmentedQuadraticRows a *ᵥ h = 0 ∧
      ∀ j k : Fin d, h (some j, some k) = if j = k then 1 else 0 := by
  classical
  obtain ⟨c, r, hr⟩ := hsphere
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_eq_one (Coeff a)
    (one_ne_zero : (1 : ℝ) ≠ 0)
  have hfix (x : Coeff a) : φ (x : ℝ) = x := by
    have ht := φ.map_smul x (1 : ℝ)
    simpa [Algebra.smul_def, hφ] using ht
  have hmul (x : Coeff a) (t : ℝ) : φ ((x : ℝ) * t) = x * φ t := by
    simpa [Algebra.smul_def] using φ.map_smul x t
  let C : ℝ := (∑ j, (c j)^2) - r^2
  let h : QuadraticIndex d → Coeff a := fun q =>
    match q.1, q.2 with
    | none, none => φ C
    | none, some j => φ (-2 * c j)
    | some _, none => 0
    | some j, some k => if j = k then 1 else 0
  refine ⟨h, ?_, fun _ _ => rfl⟩
  funext i
  have hreal : C + (∑ j, a i j * (-2 * c j)) + (∑ j, (a i j)^2) = 0 := by
    have hdist : (∑ j, (a i j - c j)^2) = r^2 := by
      calc
        (∑ j, (a i j - c j)^2) = dist (a i) c ^ 2 := by
          simpa only [Real.dist_eq, sq_abs] using
            (EuclideanSpace.dist_sq_eq (a i) c).symm
        _ = r^2 := congrArg (fun x : ℝ => x^2) (hr i)
    have hexpand : (∑ j, (a i j - c j)^2) =
        (∑ j, (a i j)^2) + (∑ j, a i j * (-2*c j)) + (∑ j, (c j)^2) := by
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      ring
    dsimp [C]
    linarith
  have hdesc := congrArg φ hreal
  simp only [map_add, map_sum, map_zero] at hdesc
  have hlinear (j : Fin d) : φ (a i j * (-2*c j)) =
      coordinate a i j * φ (-2*c j) := hmul (coordinate a i j) _
  have hsquare (j : Fin d) : φ ((a i j)^2) = (coordinate a i j)^2 := by
    change φ (((coordinate a i j)^2 : Coeff a) : ℝ) = (coordinate a i j)^2
    exact hfix _
  simp only [hlinear, hsquare] at hdesc
  change (∑ q : QuadraticIndex d, augmentedQuadraticRows a i q * h q) = 0
  simpa [augmentedQuadraticRows, Fintype.sum_prod_type, Fintype.sum_option,
    augmented, h, mul_ite, ite_mul, pow_two, mul_comm, mul_left_comm,
    mul_assoc] using hdesc

theorem quadraticIndependent_fieldCriterion {s d : ℕ} (a : Fin s → Space d)
    (hrows : LinearIndependent (Coeff a) (augmentedQuadraticRows a).row)
    (h : QuadraticIndex d → Coeff a)
    (hzero : augmentedQuadraticRows a *ᵥ h = 0)
    (hspatial : ∀ j k : Fin d, h (some j, some k) = if j = k then 1 else 0) :
    FieldCriterion a := by
  classical
  let D : Matrix (Fin s) (QuadraticIndex d) (TensorRing a) :=
    fun i q => augmented a i q.1 ⊗ₜ[ℚ] augmented a i q.2
  let μ : TensorRing a →+* Coeff a := (multiply a).toRingHom
  let σ : Coeff a →+* TensorRing a := Algebra.TensorProduct.includeLeftRingHom
  have hsection (x : Coeff a) : μ (σ x) = x := by
    simp [μ, σ, multiply, Algebra.TensorProduct.includeLeftRingHom]
  have hD : D.map μ = augmentedQuadraticRows a := by
    funext i q
    change Algebra.TensorProduct.lmul' ℚ
      (augmented a i q.1 ⊗ₜ[ℚ] augmented a i q.2) =
        augmented a i q.1 * augmented a i q.2
    exact Algebra.TensorProduct.lmul'_apply_tmul _ _
  obtain ⟨z, hz, hm⟩ := Quadratic.lift_kernel μ σ hsection D
    (by simpa only [hD] using hrows) h (by simpa only [hD] using hzero)
  refine ⟨fun α β => z (α, β), ?_, ?_⟩
  · intro i
    have ht := congrFun hz i
    change (∑ q, D i q * z q) = 0 at ht
    have hsand (x y : Coeff a) (T : TensorRing a) :
        (x ⊗ₜ[ℚ] (1 : Coeff a)) * T * ((1 : Coeff a) ⊗ₜ[ℚ] y) =
          (x ⊗ₜ[ℚ] y) * T := by
      have hpair :
          ((x ⊗ₜ[ℚ] (1 : Coeff a)) : TensorRing a) *
              ((1 : Coeff a) ⊗ₜ[ℚ] y) = x ⊗ₜ[ℚ] y :=
        (Algebra.TensorProduct.tmul_mul_tmul x (1 : Coeff a) (1 : Coeff a) y).trans
          (congrArg₂ (fun u v : Coeff a => u ⊗ₜ[ℚ] v) (mul_one x) (one_mul y))
      exact (mul_right_comm ((x ⊗ₜ[ℚ] (1 : Coeff a)) : TensorRing a) T
        (((1 : Coeff a) ⊗ₜ[ℚ] y) : TensorRing a)).trans
          (congrArg (fun U : TensorRing a => U * T) hpair)
    simp only [hsand]
    simpa only [D, Fintype.sum_prod_type] using ht
  · intro j k
    exact (congrFun hm (some j, some k)).trans (hspatial j k)

theorem spherical_quadraticIndependent_ramsey_of_dimension {s d : ℕ}
    (a : Fin s → Space d) (hs : 2 ≤ s) (hd : 1 ≤ d)
    (ha : Function.Injective a)
    (hsphere : ∃ c : Space d, ∃ r : ℝ, ∀ i, dist (a i) c = r)
    (hrows : LinearIndependent (Coeff a)
      (fun i : Fin s => fun q : Option (Fin d) × Option (Fin d) =>
        augmented a i q.1 * augmented a i q.2)) : Ramsey a := by
  obtain ⟨h, hzero, hspatial⟩ := sphere_field_quadratic a hsphere
  exact fieldCriterion_ramsey a hs hd ha
    (quadraticIndependent_fieldCriterion a hrows h hzero hspatial)

theorem spherical_quadraticIndependent_ramsey {s d : ℕ} (a : Fin s → Space d)
    (hs : 0 < s) (ha : Function.Injective a)
    (hspan : affineSpan ℝ (Set.range a) = ⊤)
    (hsphere : ∃ c : Space d, ∃ r : ℝ, ∀ i, dist (a i) c = r)
    (hrows : LinearIndependent (Coeff a)
      (fun i : Fin s => fun q : Option (Fin d) × Option (Fin d) =>
        augmented a i q.1 * augmented a i q.2)) : Ramsey a := by
  classical
  by_cases hs1 : s = 1
  · subst s
    exact singleton_ramsey a
  have hs2 : 2 ≤ s := by omega
  have hd : 1 ≤ d := by
    by_contra hd
    have hd0 : d = 0 := by omega
    subst d
    have he : a ⟨0, by omega⟩ = a ⟨1, by omega⟩ := Subsingleton.elim _ _
    have hi := congrArg Fin.val (ha he)
    norm_num at hi
  obtain ⟨h, hzero, hspatial⟩ := sphere_field_quadratic a hsphere
  apply (classification a hs2 hd ha hspan).mpr
  exact quadraticIndependent_fieldCriterion a hrows h hzero hspatial

theorem quadratic_empty_ramsey {d : ℕ} (a : Fin 0 → Space d) : Ramsey a := by
  intro r hr
  refine ⟨1, by omega, ?_⟩
  intro c
  refine ⟨fun i => Fin.elim0 i, ?_, ⟨0, by omega⟩, ?_⟩
  · intro i
    exact Fin.elim0 i
  · intro i
    exact Fin.elim0 i

theorem spherical_quadraticIndependent_ramsey_all {s d : ℕ}
    (a : Fin s → Space d) (ha : Function.Injective a)
    (hspan : affineSpan ℝ (Set.range a) = ⊤)
    (hsphere : ∃ c : Space d, ∃ r : ℝ, ∀ i, dist (a i) c = r)
    (hrows : LinearIndependent (Coeff a)
      (fun i : Fin s => fun q : Option (Fin d) × Option (Fin d) =>
        augmented a i q.1 * augmented a i q.2)) : Ramsey a := by
  by_cases hs : 0 < s
  · exact spherical_quadraticIndependent_ramsey a hs ha hspan hsphere hrows
  · have hs0 : s = 0 := by omega
    subst s
    exact quadratic_empty_ramsey a

end EuclideanRamsey

end

end OAI
