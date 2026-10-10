import Mathlib

namespace OAI

noncomputable section

namespace UniversalStrongKK

open scoped BigOperators InnerProductSpace

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

variable {ι : Type*} [Fintype ι]

abbrev DirectSum (ι H : Type*) [Fintype ι] [NormedAddCommGroup H] :=
  PiLp 2 (fun _ : ι => H)

def diagonalOp (T : H →L[ℂ] H) : DirectSum ι H →L[ℂ] DirectSum ι H :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : ι => H)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun i => T.comp (PiLp.proj 2 (fun _ : ι => H) i)))

omit [CompleteSpace H] in
@[simp] theorem diagonalOp_apply (T : H →L[ℂ] H) (ξ : DirectSum ι H) (i : ι) :
    (diagonalOp T ξ).ofLp i = T (ξ.ofLp i) := by simp [diagonalOp]

theorem diagonalOp_star (T : H →L[ℂ] H) :
    diagonalOp (star T) = star (diagonalOp (ι := ι) T) := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_left ℂ
  intro y
  simp only [ContinuousLinearMap.star_eq_adjoint]
  rw [ContinuousLinearMap.adjoint_inner_right]
  simp only [PiLp.inner_apply, diagonalOp_apply,
    ContinuousLinearMap.adjoint_inner_right]

def coordinateOp [DecidableEq ι] (T : DirectSum ι H →L[ℂ] DirectSum ι H) (i j : ι) : H →L[ℂ] H :=
  (PiLp.proj 2 (fun _ : ι => H) i).comp
    (T.comp ((PiLp.continuousLinearEquiv 2 ℂ (fun _ : ι => H)).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.single ℂ (fun _ : ι => H) j)))

omit [CompleteSpace H] in
@[simp] theorem coordinateOp_apply [DecidableEq ι]
    (T : DirectSum ι H →L[ℂ] DirectSum ι H) (i j : ι) (x : H) :
    coordinateOp T i j x = (T (PiLp.single 2 j x)).ofLp i := by
  rfl

omit [CompleteSpace H] in
@[simp] theorem diagonalOp_single [DecidableEq ι] (T : H →L[ℂ] H) (j : ι) (x : H) :
    diagonalOp (ι := ι) T (PiLp.single 2 j x) = PiLp.single 2 j (T x) := by
  ext i
  by_cases h : i=j
  · subst i; simp
  · simp [h]

omit [CompleteSpace H] in
theorem coordinate_commute_of_diagonal [DecidableEq ι]
    (T : H →L[ℂ] H) (S : DirectSum ι H →L[ℂ] DirectSum ι H)
    (h : diagonalOp T * S = S * diagonalOp T) (i j : ι) :
    T * coordinateOp S i j = coordinateOp S i j * T := by
  ext x
  have hh := congrArg (fun Q : DirectSum ι H →L[ℂ] DirectSum ι H =>
    (Q (PiLp.single 2 j x)).ofLp i) h
  simpa only [mul_apply_eq_comp, diagonalOp_apply, diagonalOp_single,
    coordinateOp_apply] using hh

omit [InnerProductSpace ℂ H] [CompleteSpace H] in
theorem sum_single_direct [DecidableEq ι] (x : DirectSum ι H) :
    ∑ j, PiLp.single 2 j (x.ofLp j) = x := by
  ext i
  simp [Pi.single_apply]

omit [CompleteSpace H] in
theorem diagonal_commute_of_coordinates [DecidableEq ι]
    (T : H →L[ℂ] H) (S : DirectSum ι H →L[ℂ] DirectSum ι H)
    (h : ∀ i j, T * coordinateOp S i j = coordinateOp S i j * T) :
    diagonalOp T * S = S * diagonalOp T := by
  ext x i
  have hs (x : DirectSum ι H) :
      (S x).ofLp i = ∑ j, coordinateOp S i j (x.ofLp j) := by
    conv_lhs => rw [← sum_single_direct x]
    simp
  simp only [mul_apply_eq_comp, diagonalOp_apply, hs, map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  exact congrArg (fun Q : H →L[ℂ] H => Q (x.ofLp j)) (h i j)

theorem commute_projection_of_invariant {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] (V : Submodule ℂ E) [V.HasOrthogonalProjection]
    (L : E →L[ℂ] E)
    (hL : ∀ x ∈ V, L x ∈ V) (hLs : ∀ x ∈ V, star L x ∈ V) :
    Commute L V.starProjection := by
  apply ContinuousLinearMap.ext
  intro x
  change L (V.starProjection x) = V.starProjection (L x)
  symm
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    (hL _ (Submodule.starProjection_apply_mem _ _))
  intro y hy
  rw [← map_sub, ← ContinuousLinearMap.adjoint_inner_right]
  exact Submodule.inner_left_of_mem_orthogonal (hLs y hy)
    (Submodule.sub_starProjection_mem_orthogonal x)

def orbitCore (A : StarSubalgebra ℂ (H →L[ℂ] H)) (ξ : DirectSum ι H) :
    Submodule ℂ (DirectSum ι H) where
  carrier := {y | ∃ a ∈ A, diagonalOp a ξ = y}
  zero_mem' := by
    refine ⟨0, zero_mem A, ?_⟩
    ext i; simp
  add_mem' := by
    rintro x y ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    refine ⟨a+b, add_mem ha hb, ?_⟩
    ext i; simp
  smul_mem' := by
    rintro c x ⟨a, ha, rfl⟩
    refine ⟨c • a, A.smul_mem ha c, ?_⟩
    ext i; simp

def closedOrbit (A : StarSubalgebra ℂ (H →L[ℂ] H)) (ξ : DirectSum ι H) :
    Submodule ℂ (DirectSum ι H) := (orbitCore A ξ).topologicalClosure

instance closedOrbit_complete (A : StarSubalgebra ℂ (H →L[ℂ] H)) (ξ : DirectSum ι H) :
    CompleteSpace (closedOrbit A ξ) :=
  (Submodule.isClosed_topologicalClosure _).completeSpace_coe

theorem diagonal_closedOrbit_mem (A : StarSubalgebra ℂ (H →L[ℂ] H))
    (ξ : DirectSum ι H) {a : H →L[ℂ] H} (ha : a ∈ A)
    {y : DirectSum ι H} (hy : y ∈ closedOrbit A ξ) :
    diagonalOp a y ∈ closedOrbit A ξ := by
  change diagonalOp a y ∈ closure (orbitCore A ξ : Set (DirectSum ι H))
  apply map_mem_closure (diagonalOp a).continuous hy
  rintro z ⟨b, hb, rfl⟩
  refine ⟨a*b, mul_mem ha hb, ?_⟩
  ext i; simp [mul_apply_eq_comp]

theorem identityVector_mem_closedOrbit (A : StarSubalgebra ℂ (H →L[ℂ] H))
    (ξ : DirectSum ι H) : ξ ∈ closedOrbit A ξ := by
  apply subset_closure
  refine ⟨1, one_mem A, ?_⟩
  ext i; simp

theorem bicommutant_diagonal_mem_closedOrbit
    (A : StarSubalgebra ℂ (H →L[ℂ] H)) (T : H →L[ℂ] H)
    (hT : T ∈ Set.centralizer (Set.centralizer (A : Set (H →L[ℂ] H))))
    (ξ : DirectSum ι H) : diagonalOp T ξ ∈ closedOrbit A ξ := by
  classical
  let V := closedOrbit A ξ
  have hc (a : H →L[ℂ] H) (ha : a ∈ A) :
      diagonalOp a * V.starProjection = V.starProjection * diagonalOp a := by
    apply (commute_projection_of_invariant V (diagonalOp a) ?_ ?_).eq
    · exact fun x hx => diagonal_closedOrbit_mem A ξ ha hx
    · rw [← diagonalOp_star]
      exact fun x hx => diagonal_closedOrbit_mem A ξ (star_mem ha) hx
  have hentry (i j : ι) : coordinateOp V.starProjection i j ∈
      Set.centralizer (A : Set (H →L[ℂ] H)) := by
    intro a ha
    exact coordinate_commute_of_diagonal a V.starProjection (hc a ha) i j
  have hdiag : diagonalOp T * V.starProjection = V.starProjection * diagonalOp T :=
    diagonal_commute_of_coordinates T V.starProjection (fun i j => (hT _ (hentry i j)).symm)
  have he : V.starProjection ξ = ξ :=
    Submodule.starProjection_eq_self_iff.mpr (identityVector_mem_closedOrbit A ξ)
  have h := congrArg (fun Q : DirectSum ι H →L[ℂ] DirectSum ι H => Q ξ) hdiag
  simp only [mul_apply_eq_comp, he] at h
  rw [h]
  exact Submodule.starProjection_apply_mem _ _

theorem bicommutant_strong_approximation
    (A : StarSubalgebra ℂ (H →L[ℂ] H)) (T : H →L[ℂ] H)
    (hT : T ∈ Set.centralizer (Set.centralizer (A : Set (H →L[ℂ] H))))
    (n : ℕ) (ξ : Fin n → H) (ε : ℝ) (hε : 0 < ε) :
    ∃ a ∈ A, ∀ i, ‖(a-T) (ξ i)‖ < ε := by
  let η : DirectSum (Fin n) H := WithLp.toLp 2 ξ
  have hm := bicommutant_diagonal_mem_closedOrbit A T hT η
  change diagonalOp T η ∈ closure (orbitCore A η : Set _) at hm
  obtain ⟨y, ⟨a, ha, hay⟩, hyd⟩ := Metric.mem_closure_iff.mp hm ε hε
  refine ⟨a, ha, fun i => ?_⟩
  subst y
  have hh := PiLp.norm_apply_le (diagonalOp a η - diagonalOp T η) i
  have hd : ‖diagonalOp a η - diagonalOp T η‖ < ε := by
    simpa only [dist_eq_norm, norm_sub_rev] using hyd
  simpa only [PiLp.sub_apply, diagonalOp_apply, sub_apply]
    using hh.trans_lt hd

end

end UniversalStrongKK
end

end OAI
