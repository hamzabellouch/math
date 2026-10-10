import OAI.GroupTheory.PolycyclicRecognition.Algebra.ConeQuotientBounds
import OAI.GroupTheory.PolycyclicRecognition.Geometry.PositiveWeightCones
import OAI.GroupTheory.PolycyclicRecognition.Geometry.BoundaryLimits

namespace OAI

/-!
# Contraction on the constructed positive-ray quotient

This proves the linear logarithmic estimate underlying
`boundary.tex`, equation (quotient-contraction). The basis is made of actual
pure bracket words in the quotient by the mixed-word ideal. Its scalar
weights are positive multiples of the chosen ray, while its residual
Cartan action has the already-proved polynomial bound.
-/

noncomputable section

namespace PolycyclicRecognition

open Module LieAlgebra LieModule
open scoped BigOperators

/-- A pure word in positive multiples of one form has a strictly positive
multiple of that form as its total exponent. -/
theorem pure_ray_word_exponent
    {I V : Type*} [Fintype I] [DecidableEq I] [AddCommGroup V] [Module ℝ V]
    (α : V →ₗ[ℝ] ℝ) (weight : I → V →ₗ[ℝ] ℝ) (w : FreeMagma I)
    (hw : ¬IsMixedWord (fun i => weight i ∉ positiveWeightRay α) w) :
    ∃ c : ℝ, 0 < c ∧ ∀ v, bracketWordExponent (fun i => weight i v) w = c * α v := by
  induction w using FreeMagma.rec with
  | of i =>
    obtain ⟨c, hc, he⟩ := Classical.not_not.mp hw
    refine ⟨c, hc, ?_⟩
    intro v
    simp only [bracketWordExponent_of, he, LinearMap.smul_apply, smul_eq_mul]
  | mul u v hu hv =>
    obtain ⟨a, ha, he⟩ := hu (fun h => hw (Or.inl h))
    obtain ⟨b, hb, hf⟩ := hv (fun h => hw (Or.inr h))
    refine ⟨a + b, add_pos ha hb, ?_⟩
    intro x
    change bracketWordExponent (fun i => weight i x) (u * v) = _
    rw [bracketWordExponent_mul, he, hf, add_mul]

/-- A finite family of positive numbers has one strictly positive lower
bound, including when the index type is empty. -/
theorem exists_pos_le_finite_family {J : Type*} [Fintype J]
    (a : J → ℝ) (ha : ∀ j, 0 < a j) :
    ∃ c : ℝ, 0 < c ∧ ∀ j, c ≤ a j := by
  classical
  let S : Finset ℝ := insert 1 (Finset.univ.image a)
  have hS : S.Nonempty := ⟨1, Finset.mem_insert_self _ _⟩
  refine ⟨S.min' hS, (Finset.lt_min'_iff _ _).mpr ?_, ?_⟩
  · intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact zero_lt_one
    · obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hx
      exact ha j
  · intro j
    exact Finset.min'_le _ _ (Finset.mem_insert_of_mem (Finset.mem_image.mpr
      ⟨j, Finset.mem_univ j, rfl⟩))

namespace CartanWordModel

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  {n : ℕ} (T : TriangularAdjoint L n)

/-- The exact dilation contracts a pure-word ray quotient basis at a
common exponential rate in every nonpositive ray direction. -/
theorem exists_ray_dilation_bound
    (α : H →ₗ[ℝ] ℝ) {J : Type*} [Fintype J]
    (b : Basis J ℝ ((cartanRootIdeal H) ⧸ M.coneWordIdeal (positiveWeightRay α)))
    (words : J → FreeMagma (Fin M.letterCount))
    (hpure : ∀ j, ¬IsMixedWord
      (fun i => (M.weight i : H →ₗ[ℝ] ℝ) ∉ positiveWeightRay α) (words j))
    (hb : ∀ j, (M.coneWordIdeal (positiveWeightRay α)).toSubmodule.mkQ
      (evalBracketWord M.letter (words j)) = b j) :
    ∃ c : ℝ, 0 < c ∧ ∀ (h : H), α h ≤ 0 →
      ∀ v : (cartanRootIdeal H) ⧸ M.coneWordIdeal (positiveWeightRay α),
      ‖b.equivFun ((M.coneWordIdeal (positiveWeightRay α)).toSubmodule.mapQ
        (M.coneWordIdeal (positiveWeightRay α)).toSubmodule
        (cartanIdealWeightDilation T H h).toLinearEquiv.toLinearMap
        (M.coneWordIdeal_dilation_mem T (positiveWeightRay α) h) v)‖ ≤
        Real.exp (c * α h) * ‖b.equivFun v‖ := by
  classical
  choose a ha he using fun j => pure_ray_word_exponent α
    (fun i => (M.weight i : H →ₗ[ℝ] ℝ)) (words j) (hpure j)
  obtain ⟨c, hc, hca⟩ := exists_pos_le_finite_family a ha
  refine ⟨c, hc, ?_⟩
  intro h hh v
  let S := (M.coneWordIdeal (positiveWeightRay α)).toSubmodule
  let D := S.mapQ S (cartanIdealWeightDilation T H h).toLinearEquiv.toLinearMap
    (M.coneWordIdeal_dilation_mem T (positiveWeightRay α) h)
  have hD (j : J) : D (b j) = Real.exp (a j * α h) • b j := by
    rw [← hb j]
    change S.mkQ (cartanIdealWeightDilation T H h
      (evalBracketWord M.letter (words j))) = _
    have hexp := he j h
    change bracketWordExponent (fun i => M.weight i h) (words j) = _ at hexp
    rw [M.idealWeightDilation_word T h, hexp, map_smul]
  have hcoord (j : J) : b.repr (D v) j = Real.exp (a j * α h) * b.repr v j := by
    have heq : (b.coord j).comp D = Real.exp (a j * α h) • b.coord j := by
      apply b.ext
      intro k
      by_cases hkj : k = j
      · subst k
        simp [hD]
      · simp [hD, Basis.coord_apply, hkj]
    exact DFunLike.congr_fun heq v
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro j
  change ‖b.repr (D v) j‖ ≤ _
  rw [hcoord, norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul (Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_right (hca j) hh))
    (norm_le_pi_norm (b.equivFun v) j) (norm_nonneg _) (Real.exp_pos _).le

/-- The actual Cartan action on the quotient by the positive-ray
mixed-word ideal has polynomial times exponential contraction. -/
theorem exists_ray_quotient_contraction (α : H →ₗ[ℝ] ℝ) :
    ∃ (b : Basis
        (Fin (finrank ℝ ((cartanRootIdeal H) ⧸ M.coneWordIdeal (positiveWeightRay α))))
        ℝ ((cartanRootIdeal H) ⧸ M.coneWordIdeal (positiveWeightRay α)))
      (A : ℝ) (p : ℕ) (c : ℝ),
      0 ≤ A ∧ 0 < c ∧ ∀ (h : H), α h ≤ 0 →
        ∀ v : (cartanRootIdeal H) ⧸ M.coneWordIdeal (positiveWeightRay α),
        ‖b.equivFun (M.coneAdjointAutomorphism T (positiveWeightRay α)
          (positiveWeightRay_add α) h v)‖ ≤
        A * (1 + ‖(Module.finBasis ℝ H).equivFun h‖) ^ p *
          Real.exp (c * α h) * ‖b.equivFun v‖ := by
  obtain ⟨b, words, hpure, hb⟩ := exists_pure_quotient_word_basis M.letter
    (fun i => (M.weight i : H →ₗ[ℝ] ℝ) ∉ positiveWeightRay α) M.generates
  obtain ⟨c, hc, hdilation⟩ := M.exists_ray_dilation_bound T α b words hpure hb
  obtain ⟨A, p, hA, hresidual⟩ := M.exists_cone_residual_coordinate_bound T
    (positiveWeightRay α) (positiveWeightRay_add α) b
  refine ⟨b, A, p, c, hA, hc, ?_⟩
  intro h hh v
  let S := (M.coneWordIdeal (positiveWeightRay α)).toSubmodule
  let R := S.mapQ S (cartanIdealResidualAutomorphism T H h).toLinearEquiv.toLinearMap
    (M.coneWordIdeal_residual_mem T (positiveWeightRay α) (positiveWeightRay_add α) h)
  have hfactor : M.coneAdjointAutomorphism T (positiveWeightRay α)
      (positiveWeightRay_add α) h v =
      S.mapQ S (cartanIdealWeightDilation T H h).toLinearEquiv.toLinearMap
        (M.coneWordIdeal_dilation_mem T (positiveWeightRay α) h) (R v) := by
    obtain ⟨x, rfl⟩ := S.mkQ_surjective v
    rfl
  rw [hfactor]
  apply (hdilation h hh (R v)).trans
  calc
    _ ≤ Real.exp (c * α h) *
        (A * (1 + ‖(Module.finBasis ℝ H).equivFun h‖) ^ p * ‖b.equivFun v‖) :=
      mul_le_mul_of_nonneg_left (hresidual h v) (Real.exp_pos _).le
    _ = _ := by ring_nf; rfl

/-- Polynomially bounded Cartan parameters with uniformly negative linear
ray height give one summable bound on the images of every bounded set in
the actual quotient. The parameter type allows a whole family of paths. -/
theorem exists_summable_ray_quotient_bound
    (α : H →ₗ[ℝ] ℝ) {P : Type*} (h : P → ℕ → H)
    (K R δ : ℝ) (q : ℕ) (hK : 0 ≤ K) (hR : 0 ≤ R) (hδ : 0 < δ)
    (hbound : ∀ x n, ‖(Module.finBasis ℝ H).equivFun (h x n)‖ ≤
      K * (1 + (n : ℝ)) ^ q)
    (hheight : ∀ x n, α (h x n) ≤ -δ * n) :
    ∃ (b : Basis
        (Fin (finrank ℝ ((cartanRootIdeal H) ⧸ M.coneWordIdeal (positiveWeightRay α))))
        ℝ ((cartanRootIdeal H) ⧸ M.coneWordIdeal (positiveWeightRay α)))
      (C : ℝ) (m : ℕ) (c : ℝ),
      0 ≤ C ∧ 0 < c ∧
      Summable (fun n : ℕ => C * (1 + (n : ℝ)) ^ m * Real.exp (-c * n)) ∧
      ∀ x n (v : (cartanRootIdeal H) ⧸ M.coneWordIdeal (positiveWeightRay α)),
        ‖b.equivFun v‖ ≤ R →
        ‖b.equivFun (M.coneAdjointAutomorphism T (positiveWeightRay α)
          (positiveWeightRay_add α) (h x n) v)‖ ≤
          C * (1 + (n : ℝ)) ^ m * Real.exp (-c * n) := by
  obtain ⟨b, A, p, c, hA, hc, hcontract⟩ := M.exists_ray_quotient_contraction T α
  let C := A * (1 + K) ^ p * R
  refine ⟨b, C, q * p, c * δ, by dsimp [C]; positivity,
    mul_pos hc hδ, summable_polynomial_exp_decay C (q * p) (mul_pos hc hδ), ?_⟩
  intro x n v hv
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hnegative : α (h x n) ≤ 0 :=
    (hheight x n).trans (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hδ.le) hn)
  have hbase : 1 + ‖(Module.finBasis ℝ H).equivFun (h x n)‖ ≤
      (1 + K) * (1 + (n : ℝ)) ^ q := by
    have hpow : 1 ≤ (1 + (n : ℝ)) ^ q := one_le_pow₀ (by linarith)
    nlinarith [hbound x n]
  have hpoly : (1 + ‖(Module.finBasis ℝ H).equivFun (h x n)‖) ^ p ≤
      (1 + K) ^ p * (1 + (n : ℝ)) ^ (q * p) := by
    calc
      _ ≤ ((1 + K) * (1 + (n : ℝ)) ^ q) ^ p := by gcongr
      _ = _ := by rw [mul_pow, ← pow_mul]
  have hexp : Real.exp (c * α (h x n)) ≤ Real.exp (-(c * δ) * n) := by
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_left (hheight x n) hc.le
    nlinarith
  apply (hcontract (h x n) hnegative v).trans
  calc
    _ ≤ A * ((1 + K) ^ p * (1 + (n : ℝ)) ^ (q * p)) *
        Real.exp (-(c * δ) * n) * R := by gcongr
    _ = C * (1 + (n : ℝ)) ^ (q * p) * Real.exp (-(c * δ) * n) := by
      dsimp [C]
      ring

end CartanWordModel
end PolycyclicRecognition

end

end OAI
