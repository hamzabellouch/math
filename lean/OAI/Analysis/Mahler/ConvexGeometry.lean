import OAI.Analysis.Mahler.ConvexApproximation
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

namespace OAI

namespace SymmetricMahler
open Set Finset MeasureTheory Filter
open scoped Topology
variable {I J : Type*} [fintypeI : Fintype I] [fintypeJ : Fintype J] [decidableEqI : DecidableEq I]

omit fintypeI decidableEqI in
/-- The center of an origin-symmetric convex set with interior is interior. -/
theorem zero_mem_interior_of_symmetric [Fintype I] [DecidableEq I] {K : Set (I → ℝ)} (hconv : Convex ℝ K)
    (hsym : ∀ x ∈ K, -x ∈ K) (hint : (interior K).Nonempty) :
    (0 : I → ℝ) ∈ interior K := by
  obtain ⟨x, hx⟩ := hint
  have h := hconv.combo_interior_self_mem_interior hx (hsym x (interior_subset hx))
    (a := (1/2 : ℝ)) (b := (1/2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)
  simpa using h

/-- Compactness supplies small nonzero coordinate rows in the polar. -/
theorem exists_coordinate_rows {K : Set (I → ℝ)} (hK : IsCompact K) :
    ∃ c : ℝ, 0 < c ∧ ∀ i : I, Pi.single i c ∈ coordinatePolar K := by
  obtain ⟨R, hR, hb⟩ := hK.isBounded.exists_pos_norm_le
  refine ⟨R⁻¹, inv_pos.mpr hR, ?_⟩
  intro i x hx
  have hxi : x i ≤ R := (le_abs_self _).trans ((norm_le_pi_norm x i).trans (hb x hx))
  have hbound : R⁻¹ * x i ≤ (1 : ℝ) := by
    rw [inv_mul_le_iff₀ hR]
    simpa using hxi
  simpa [Pi.single_apply] using hbound

omit fintypeJ decidableEqI in
/-- Finite strip constraints form a closed set. -/
theorem isClosed_stripBody [Fintype J] [DecidableEq I] (A : J → I → ℝ) : IsClosed (stripBody A) := by
  have he : stripBody A = ⋂ j, {x | |measurement A x j| ≤ 1} := by
    ext x
    simp [stripBody]
  rw [he]
  refine isClosed_iInter (fun j => isClosed_le ?_ continuous_const)
  exact (continuous_finsetSum _ (fun i _ => continuous_const.mul (continuous_apply i))).abs

/-- Independent coordinate rows followed by a finite prefix of polar rows. -/
def approximationRows (c : ℝ) (a : ℕ → I → ℝ) (N : ℕ) : (I ⊕ Fin N) → I → ℝ :=
  Sum.elim (fun i => Pi.single i c) (fun j => a j)

lemma approximationRows_basis (c : ℝ) (a : ℕ → I → ℝ) (N : ℕ) (x : I → ℝ) (i : I) :
    measurement (approximationRows c a N) x (.inl i) = c * x i := by
  simp [measurement, approximationRows, Pi.single_apply]

lemma approximationRows_sequence (c : ℝ) (a : ℕ → I → ℝ) (N : ℕ) (x : I → ℝ) (j : Fin N) :
    measurement (approximationRows c a N) x (.inr j) = ∑ i, a j i * x i := rfl

/-- The first rows alone ensure full rank of every finite matrix. -/
theorem approximationRows_injective (c : ℝ) (hc : c ≠ 0) (a : ℕ → I → ℝ) (N : ℕ) :
    Function.Injective (measurement (approximationRows c a N)) := by
  intro x y h
  ext i
  have hi := congrFun h (.inl i)
  simp only [approximationRows_basis] at hi
  exact mul_left_cancel₀ hc hi

lemma stripBody_approximationRows_mem (c : ℝ) (a : ℕ → I → ℝ) (N : ℕ) (x : I → ℝ) :
    x ∈ stripBody (approximationRows c a N) ↔
      (∀ i, |c*x i| ≤ 1) ∧ (∀ j < N, |∑ i, a j i*x i| ≤ 1) := by
  constructor
  · intro hx
    refine ⟨fun i => ?_, fun j hj => ?_⟩
    · simpa only [approximationRows_basis] using hx (.inl i)
    · exact hx (.inr ⟨j, hj⟩)
  · rintro ⟨hb, hs⟩ (i | j)
    · simpa only [approximationRows_basis] using hb i
    · exact hs j j.isLt

/-- A single fixed coordinate box bounds every approximating strip body. -/
theorem approximation_subset_box {c : ℝ} (hc : 0 < c) (a : ℕ → I → ℝ) (N : ℕ) :
    stripBody (approximationRows c a N) ⊆ Icc (fun _ => -c⁻¹) (fun _ => c⁻¹) := by
  intro x hx
  have hb := (stripBody_approximationRows_mem c a N x).mp hx |>.1
  have hi : ∀ i, |x i| ≤ c⁻¹ := by
    intro i
    have h := hb i
    rw [abs_mul, abs_of_pos hc] at h
    simpa using (le_inv_mul_iff₀ hc).mpr h
  exact ⟨fun i => (abs_le.mp (hi i)).1, fun i => (abs_le.mp (hi i)).2⟩

theorem isCompact_approximation {c : ℝ} (hc : 0 < c) (a : ℕ → I → ℝ) (N : ℕ) :
    IsCompact (stripBody (approximationRows c a N)) :=
  isCompact_Icc.of_isClosed_subset (isClosed_stripBody _) (approximation_subset_box hc a N)

lemma approximation_antitone (c : ℝ) (a : ℕ → I → ℝ) :
    Antitone (fun N => stripBody (approximationRows c a N)) := by
  intro M N hMN x hx
  rw [stripBody_approximationRows_mem] at hx ⊢
  exact ⟨hx.1, fun j hj => hx.2 j (lt_of_lt_of_le hj hMN)⟩

/-- The polar of a symmetric body is bounded because K contains a ball. -/
theorem isCompact_coordinatePolar {K : Set (I → ℝ)}
    (hsym : ∀ x ∈ K, -x ∈ K) (hzero : (0 : I → ℝ) ∈ interior K) :
    IsCompact (coordinatePolar K) := by
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hzero)
  have hb : ∀ i : I, Pi.single i (r/2) ∈ K := by
    intro i
    apply hball
    simp only [Metric.mem_ball, dist_zero_right, Pi.norm_single, Real.norm_eq_abs,
      abs_of_pos (half_pos hr)]
    linarith
  apply (isCompact_Icc : IsCompact
    (Icc (fun _ : I => -(r/2)⁻¹) (fun _ => (r/2)⁻¹))).of_isClosed_subset
    (isClosed_coordinatePolar K)
  intro p hp
  have hpi : ∀ i, |p i| ≤ (r/2)⁻¹ := by
    intro i
    have h := polar_pairing_abs hsym hp (hb i)
    simp [Pi.single_apply, abs_mul, abs_of_pos (half_pos hr)] at h
    have h' : (r/2)*|p i| ≤ 1 := by nlinarith
    simpa using (le_inv_mul_iff₀ (half_pos hr)).mpr h'
  exact ⟨fun i => (abs_le.mp (hpi i)).1, fun i => (abs_le.mp (hpi i)).2⟩

lemma subset_approximation {K : Set (I → ℝ)} (hsym : ∀ x ∈ K, -x ∈ K)
    (c : ℝ) (hcK : ∀ i, Pi.single i c ∈ coordinatePolar K)
    (a : ℕ → coordinatePolar K) (N : ℕ) :
    K ⊆ stripBody (approximationRows c (fun j => (a j).val) N) := by
  intro x hx j
  cases j with
  | inl i => exact polar_pairing_abs hsym (hcK i) hx
  | inr j => exact polar_pairing_abs hsym (a j).property hx

/-- The common intersection is literally K, including the fixed initial rows. -/
theorem iInter_approximation {K : Set (I → ℝ)} (hconv : Convex ℝ K)
    (hclosed : IsClosed K) (hzero : (0 : I → ℝ) ∈ K) (hsym : ∀ x ∈ K, -x ∈ K)
    (c : ℝ) (hcK : ∀ i, Pi.single i c ∈ coordinatePolar K)
    (a : ℕ → coordinatePolar K) (ha : DenseRange a) :
    (⋂ N, stripBody (approximationRows c (fun j => (a j).val) N)) = K := by
  apply Set.Subset.antisymm
  · intro x hx
    rw [← dense_polar_strips_intersection hconv hclosed hzero hsym a ha]
    intro j
    have h := mem_iInter.mp hx (j+1)
    exact h (.inr ⟨j, Nat.lt_succ_self j⟩)
  · exact subset_iInter (fun N => subset_approximation hsym c hcK a N)

end SymmetricMahler

end OAI
