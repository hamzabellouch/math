import OAI.Analysis.OInfinity.BergTower

namespace OAI

/-! # Finite Berg towers: connectedness and seam formulas

The finite assembled tower is an actual connected unitary when its initial row
extension and terminal coefficient are connected. Its layer sum includes the
terminal coefficient explicitly. The exact boundary formula gives the seam
estimate while accounting for the terminal corner.
-/

noncomputable section
open scoped CStarAlgebra

namespace WeakPureInfiniteness

variable {E I : Type*} [CStarAlgebra E] [Fintype I] [DecidableEq I]

omit [DecidableEq I] in
lemma bergTransfer_add (s t : I → E) (x y : E) :
    finiteCuntzTransfer s t (x + y) =
      finiteCuntzTransfer s t x + finiteCuntzTransfer s t y := by
  simp only [finiteCuntzTransfer, mul_add, add_mul, Finset.sum_add_distrib]

omit [DecidableEq I] in
lemma bergTransfer_sum {J : Type*} (s t : I → E) (f : J → E) (S : Finset J) :
    finiteCuntzTransfer s t (∑ j ∈ S, f j) =
      ∑ j ∈ S, finiteCuntzTransfer s t (f j) := by
  simp only [finiteCuntzTransfer, Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_comm

omit [DecidableEq I] in
/-- The complete layer sum, including its last transfer corner. -/
lemma bergFiniteTower_eq_sum (s t : I → E) (v : unitary E) (N : ℕ) (x : E) :
    bergFiniteTower s t v N x =
      (∑ k ∈ Finset.range N,
        finiteCuntzTransferIter s t k (bergBottomCoefficient s t v)) +
      finiteCuntzTransferIter s t N x := by
  induction N with
  | zero => simp only [bergFiniteTower_zero, Finset.range_zero, Finset.sum_empty,
      finiteCuntzTransferIter_zero, zero_add]
  | succ N ih =>
    rw [bergFiniteTower_succ, ih, bergTransfer_add, bergTransfer_sum,
      Finset.sum_range_succ']
    simp only [finiteCuntzTransferIter_zero, finiteCuntzTransferIter_succ]
    abel

/-- The bundled unitary represented by a finite tower. -/
def bergFiniteTowerUnitary (s t : I → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (ht : ∀ i j, star (t i) * t j = if i = j then 1 else 0)
    (v : unitary E) (hv : ∀ i, (v : E) * s i = t i)
    (N : ℕ) (x : unitary E) : unitary E :=
  ⟨bergFiniteTower s t v N (x : E),
    bergFiniteTower_mem_unitary s t hs ht v hv N (x : E) x.property⟩

lemma bergFiniteTowerUnitary_continuous (s t : I → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (ht : ∀ i j, star (t i) * t j = if i = j then 1 else 0)
    (v : unitary E) (hv : ∀ i, (v : E) * s i = t i) (N : ℕ) :
    Continuous (bergFiniteTowerUnitary s t hs ht v hv N) :=
  ((bergFiniteTower_continuous s t v N).comp continuous_subtype_val).subtype_mk _

lemma bergFiniteTowerUnitary_step_one (s t : I → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (ht : ∀ i j, star (t i) * t j = if i = j then 1 else 0)
    (v : unitary E) (hv : ∀ i, (v : E) * s i = t i) :
    bergFiniteTowerUnitary s t hs ht v hv 1 1 = v := by
  apply Subtype.ext
  change ((v : E) - finiteCuntzTransfer s t 1) + finiteCuntzTransfer s t 1 = (v : E)
  exact sub_add_cancel _ _

/-- Connectedness is preserved by the finite tower, rather than assumed for
its assembled output. -/
lemma bergFiniteTowerUnitary_joined (s t : I → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (ht : ∀ i j, star (t i) * t j = if i = j then 1 else 0)
    (v : unitary E) (hv : ∀ i, (v : E) * s i = t i)
    (hvpath : Joined (1 : unitary E) v) (N : ℕ)
    (x : unitary E) (hxpath : Joined (1 : unitary E) x) :
    Joined (1 : unitary E) (bergFiniteTowerUnitary s t hs ht v hv N x) := by
  induction N with
  | zero => exact hxpath
  | succ N ih =>
    have h := ih.map (bergFiniteTowerUnitary_continuous s t hs ht v hv 1)
    rw [bergFiniteTowerUnitary_step_one] at h
    exact hvpath.trans h

omit [DecidableEq I] in
lemma bergFiniteTower_succ_right (s t : I → E) (v : unitary E) (N : ℕ) (x : E) :
    bergFiniteTower s t v (N + 1) x =
      bergFiniteTower s t v N (bergFiniteTower s t v 1 x) := by
  induction N with
  | zero => rfl
  | succ N ih =>
    change bergBottomCoefficient s t v +
      finiteCuntzTransfer s t (bergFiniteTower s t v (N + 1) x) =
        bergBottomCoefficient s t v +
          finiteCuntzTransfer s t (bergFiniteTower s t v N (bergFiniteTower s t v 1 x))
    rw [ih]

omit [DecidableEq I] in
/-- All the variation between adjacent tower heights comes from the terminal
coefficient, whose norm is not presumed small. -/
lemma bergFiniteTower_boundary (s t : I → E) (v : unitary E) (N : ℕ) (x : E) :
    bergFiniteTower s t v N x - bergFiniteTower s t v (N + 1) x =
      finiteCuntzTransferIter s t N
        (x - (bergBottomCoefficient s t v + finiteCuntzTransfer s t x)) := by
  rw [bergFiniteTower_succ_right, bergFiniteTower_sub]
  rfl

lemma bergFiniteTower_exact_seam (s t : I → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (v : unitary E) (hv : ∀ i, (v : E) * s i = t i) (N : ℕ) (x : E) (i : I) :
    bergFiniteTower s t v (N + 1) x * s i - t i * bergFiniteTower s t v (N + 1) x =
      t i * finiteCuntzTransferIter s t N
        (x - (bergBottomCoefficient s t v + finiteCuntzTransfer s t x)) := by
  rw [bergFiniteTower_residual s t hs v hv, bergFiniteTower_boundary]

section OrthogonalCorners

variable {J : Type*}

omit [Fintype I] [DecidableEq I] in
/-- Orthogonal source and range supports remove the cost of summing blocks. -/
lemma bergOrthogonal_add_norm_le (x y : E) (C : ℝ) (hC : 0 ≤ C)
    (hxy : star x * y = 0) (hyx : x * star y = 0)
    (hx : ‖x‖ ≤ C) (hy : ‖y‖ ≤ C) : ‖x + y‖ ≤ C := by
  have hyx' : star y * x = 0 := by
    simpa only [star_mul, star_star, star_zero] using congrArg star hxy
  have hgram : (star x * x) * (star y * y) = 0 := by
    calc
      _ = star x * (x * star y) * y := by noncomm_ring
      _ = 0 := by rw [hyx, mul_zero, zero_mul]
  have hsx : IsSelfAdjoint (star x * x) := by
    simp only [IsSelfAdjoint, star_mul, star_star]
  have hsy : IsSelfAdjoint (star y * y) := by
    simp only [IsSelfAdjoint, star_mul, star_star]
  have he : star (x + y) * (x + y) = star x * x + star y * y := by
    rw [star_add, add_mul, mul_add, mul_add, hxy, hyx', add_zero, zero_add]
  have hn := hsx.norm_add_eq_max hsy hgram
  rw [← he, CStarRing.norm_star_mul_self, CStarRing.norm_star_mul_self,
    CStarRing.norm_star_mul_self] at hn
  have hsq : max (‖x‖ * ‖x‖) (‖y‖ * ‖y‖) ≤ C * C :=
    max_le (mul_self_le_mul_self (norm_nonneg x) hx)
      (mul_self_le_mul_self (norm_nonneg y) hy)
  nlinarith only [hn, hsq, norm_nonneg (x + y), hC]

omit [Fintype I] [DecidableEq I] in
lemma bergOrthogonal_sum_norm_le (f : J → E) (S : Finset J) (C : ℝ) (hC : 0 ≤ C)
    (hcross : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → star (f i) * f j = 0 ∧ f i * star (f j) = 0)
    (hnorm : ∀ i ∈ S, ‖f i‖ ≤ C) : ‖∑ i ∈ S, f i‖ ≤ C := by
  classical
  induction S using Finset.induction with
  | empty => simpa only [Finset.sum_empty, norm_zero] using hC
  | @insert i S hi ih =>
    have hs : ‖∑ j ∈ S, f j‖ ≤ C := ih
      (fun j hj k hk hne => hcross j (Finset.mem_insert_of_mem hj) k
        (Finset.mem_insert_of_mem hk) hne)
      (fun j hj => hnorm j (Finset.mem_insert_of_mem hj))
    rw [Finset.sum_insert hi]
    apply bergOrthogonal_add_norm_le _ _ C hC
    · rw [Finset.mul_sum]
      exact Finset.sum_eq_zero fun j hj =>
        (hcross i (Finset.mem_insert_self i S) j (Finset.mem_insert_of_mem hj)
          (by intro he; subst j; exact hi hj)).1
    · rw [star_sum, Finset.mul_sum]
      exact Finset.sum_eq_zero fun j hj =>
        (hcross i (Finset.mem_insert_self i S) j (Finset.mem_insert_of_mem hj)
          (by intro he; subst j; exact hi hj)).2
    · exact hnorm i (Finset.mem_insert_self i S)
    · exact hs

omit [Fintype I] [DecidableEq I] in
private lemma bergSupported_mul_zero (p q x y : E) (hxp : x * p = x)
    (hqy : q * y = y) (hpq : p * q = 0) : x * y = 0 := by
  calc
    x * y = (x * p) * (q * y) := by rw [hxp, hqy]
    _ = x * (p * q) * y := by noncomm_ring
    _ = 0 := by rw [hpq, mul_zero, zero_mul]

omit [Fintype I] [DecidableEq I] in
lemma bergRotationDeviation_support (a : E)
    (ha : a * star a * a = a) (haa : a * a = 0) (θ : ℝ) :
    bergSupport a * (partialIsometryBergRotation a θ - 1) =
        partialIsometryBergRotation a θ - 1 ∧
      (partialIsometryBergRotation a θ - 1) * bergSupport a =
        partialIsometryBergRotation a θ - 1 := by
  have hd : partialIsometryBergRotation a θ - 1 =
      (Real.cos θ - 1) • bergSupport a + Real.sin θ • bergSkew a := by
    unfold partialIsometryBergRotation bergRotationCore
    module
  rw [hd]
  constructor
  · rw [mul_add, mul_smul_comm, mul_smul_comm, bergSupport_sq a ha haa,
      bergSupport_mul_skew a ha haa]
  · rw [add_mul, smul_mul_assoc, smul_mul_assoc, bergSupport_sq a ha haa,
      bergSkew_mul_support a ha haa]

omit [Fintype I] [DecidableEq I] in
/-- The sum of rotations in orthogonal corners is a single unitary. -/
def bergFiniteRotation (a : J → E) (S : Finset J) (θ : J → ℝ) : E :=
  1 + ∑ j ∈ S, (partialIsometryBergRotation (a j) (θ j) - 1)

omit [Fintype I] [DecidableEq I] in
lemma bergFiniteRotation_mem (a : J → E) (S : Finset J) (θ : J → ℝ)
    (ha : ∀ j ∈ S, a j * star (a j) * a j = a j)
    (haa : ∀ j ∈ S, a j * a j = 0)
    (horth : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → bergSupport (a i) * bergSupport (a j) = 0) :
    bergFiniteRotation a S θ ∈ unitary E := by
  classical
  induction S using Finset.induction with
  | empty => simp only [bergFiniteRotation, Finset.sum_empty, add_zero, OneMemClass.one_mem]
  | @insert i S hi ih =>
    have hiS : i ∈ insert i S := Finset.mem_insert_self i S
    have hs := ih (fun j hj => ha j (Finset.mem_insert_of_mem hj))
      (fun j hj => haa j (Finset.mem_insert_of_mem hj))
      (fun j hj k hk hne => horth j (Finset.mem_insert_of_mem hj) k
        (Finset.mem_insert_of_mem hk) hne)
    have hzero : (partialIsometryBergRotation (a i) (θ i) - 1) *
        (∑ j ∈ S, (partialIsometryBergRotation (a j) (θ j) - 1)) = 0 := by
      rw [Finset.mul_sum]
      apply Finset.sum_eq_zero
      intro j hj
      exact bergSupported_mul_zero _ _ _ _
        (bergRotationDeviation_support (a i) (ha i hiS) (haa i hiS) (θ i)).2
        (bergRotationDeviation_support (a j) (ha j (Finset.mem_insert_of_mem hj))
          (haa j (Finset.mem_insert_of_mem hj)) (θ j)).1
        (horth i hiS j (Finset.mem_insert_of_mem hj)
          (by intro he; subst j; exact hi hj))
    have he : bergFiniteRotation a (insert i S) θ =
        partialIsometryBergRotation (a i) (θ i) * bergFiniteRotation a S θ := by
      unfold bergFiniteRotation
      rw [Finset.sum_insert hi]
      have hex : partialIsometryBergRotation (a i) (θ i) =
          1 + (partialIsometryBergRotation (a i) (θ i) - 1) := by abel
      conv_rhs => lhs; rw [hex]
      rw [add_mul, one_mul, mul_add, mul_one, hzero]
      abel
    rw [he]
    exact (unitary E).mul_mem
      (partialIsometryBergRotation_mem (a i) (ha i hiS) (haa i hiS) (θ i)) hs

omit [Fintype I] [DecidableEq I] in
/-- Adjacent angle changes in orthogonal blocks are controlled by their
largest change, independently of the number of blocks. -/
lemma bergFiniteRotation_sub_norm_le (a : J → E) (S : Finset J) (θ φ : J → ℝ)
    (ha : ∀ j ∈ S, a j * star (a j) * a j = a j)
    (haa : ∀ j ∈ S, a j * a j = 0)
    (horth : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → bergSupport (a i) * bergSupport (a j) = 0)
    (δ : ℝ) (hδ : 0 ≤ δ) (hangle : ∀ j ∈ S, |θ j - φ j| ≤ δ) :
    ‖bergFiniteRotation a S θ - bergFiniteRotation a S φ‖ ≤ 2 * δ := by
  let f (j : J) := partialIsometryBergRotation (a j) (θ j) -
    partialIsometryBergRotation (a j) (φ j)
  have hsupport (j : J) (hj : j ∈ S) : bergSupport (a j) * f j = f j ∧
      f j * bergSupport (a j) = f j := by
    have hθ := bergRotationDeviation_support (a j) (ha j hj) (haa j hj) (θ j)
    have hφ := bergRotationDeviation_support (a j) (ha j hj) (haa j hj) (φ j)
    have he : f j = (partialIsometryBergRotation (a j) (θ j) - 1) -
        (partialIsometryBergRotation (a j) (φ j) - 1) := by dsimp only [f]; abel
    rw [he, mul_sub, sub_mul, hθ.1, hφ.1, hθ.2, hφ.2]
    exact ⟨rfl, rfl⟩
  have he : bergFiniteRotation a S θ - bergFiniteRotation a S φ = ∑ j ∈ S, f j := by
    simp only [bergFiniteRotation, add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    dsimp only [f]
    abel
  rw [he]
  apply bergOrthogonal_sum_norm_le f S (2 * δ) (by positivity)
  · intro i hi j hj hne
    have hstari : star (f i) * bergSupport (a i) = star (f i) := by
      simpa only [star_mul, bergSupport_star] using congrArg star (hsupport i hi).1
    have hstarj : bergSupport (a j) * star (f j) = star (f j) := by
      simpa only [star_mul, bergSupport_star] using congrArg star (hsupport j hj).2
    exact ⟨bergSupported_mul_zero _ _ _ _ hstari (hsupport j hj).1 (horth i hi j hj hne),
      bergSupported_mul_zero _ _ _ _ (hsupport i hi).2 hstarj (horth i hi j hj hne)⟩
  · intro j hj
    exact (partialIsometryBergRotation_sub_norm_le (a j) (ha j hj) (haa j hj)
      (θ j) (φ j)).trans (mul_le_mul_of_nonneg_left (hangle j hj) (by norm_num))

end OrthogonalCorners

end WeakPureInfiniteness

end

end OAI
