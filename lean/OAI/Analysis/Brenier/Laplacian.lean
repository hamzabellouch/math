import Mathlib

namespace OAI

/-! Algebraic facts about the weighted cell-adjacency Laplacian. -/

noncomputable section
open scoped BigOperators

namespace Problem358
namespace CellLaplacian

variable {ι : Type*} [Fintype ι]

/-- The intercept derivative of the cell masses, written in coordinates. -/
def apply (g : ι → ι → ℝ) (q : ι → ℝ) (i : ι) : ℝ :=
  ∑ j, g i j * (q i - q j)

lemma apply_const (g : ι → ι → ℝ) (c : ℝ) :
    apply g (fun _ => c) = 0 := by
  funext i
  simp [apply]

lemma sum_apply (g : ι → ι → ℝ) (hsym : ∀ i j, g i j = g j i)
    (q : ι → ℝ) : ∑ i, apply g q i = 0 := by
  have hswap : (∑ i, ∑ j, g i j * q j) = ∑ i, ∑ j, g i j * q i := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [hsym j i]
  simp only [apply, mul_sub, Finset.sum_sub_distrib]
  rw [hswap, sub_self]

lemma energy_identity (g : ι → ι → ℝ) (hsym : ∀ i j, g i j = g j i)
    (q : ι → ℝ) :
    2 * (∑ i, q i * apply g q i) = ∑ i, ∑ j, g i j * (q i - q j) ^ 2 := by
  have hswap : (∑ i, ∑ j, q j * (g i j * (q j - q i))) =
      ∑ i, ∑ j, q i * (g i j * (q i - q j)) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [hsym j i]
  calc
    2 * (∑ i, q i * apply g q i) =
        (∑ i, ∑ j, q i * (g i j * (q i - q j))) +
        (∑ i, ∑ j, q j * (g i j * (q j - q i))) := by
      rw [hswap]
      have he : (∑ i, q i * apply g q i) =
          ∑ i, ∑ j, q i * (g i j * (q i - q j)) := by
        simp only [apply, Finset.mul_sum]
      rw [he]
      ring
    _ = ∑ i, ∑ j, (q i * (g i j * (q i - q j)) +
        q j * (g i j * (q j - q i))) := by
      simp only [Finset.sum_add_distrib]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring

lemma eq_of_positive_edge_of_apply_eq_zero
    (g : ι → ι → ℝ) (hsym : ∀ i j, g i j = g j i)
    (hnonneg : ∀ i j, 0 ≤ g i j) (q : ι → ℝ)
    (hq : apply g q = 0) {i j : ι} (hij : 0 < g i j) : q i = q j := by
  have he : (∑ i, ∑ j, g i j * (q i - q j) ^ 2) = 0 := by
    rw [← energy_identity g hsym q, hq]
    simp
  have hrow : (∑ j, g i j * (q i - q j) ^ 2) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun k _ =>
      Finset.sum_nonneg (fun l _ => mul_nonneg (hnonneg k l) (sq_nonneg _)))).mp he i
      (Finset.mem_univ i)
  have hterm : g i j * (q i - q j) ^ 2 = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun k _ =>
      mul_nonneg (hnonneg i k) (sq_nonneg _))).mp hrow j (Finset.mem_univ j)
  have hsquare : (q i - q j) ^ 2 = 0 := (mul_eq_zero.mp hterm).resolve_left hij.ne'
  nlinarith [sq_nonneg (q i - q j)]

/-- Connectivity may be supplied by any graph whose edges have positive weights. -/
lemma constant_of_apply_eq_zero
    (g : ι → ι → ℝ) (hsym : ∀ i j, g i j = g j i)
    (hnonneg : ∀ i j, 0 ≤ g i j) (G : SimpleGraph ι)
    (hG : G.Connected) (hpos : ∀ i j, G.Adj i j → 0 < g i j)
    (q : ι → ℝ) (hq : apply g q = 0) : ∃ c : ℝ, ∀ i, q i = c := by
  let : Nonempty ι := hG.nonempty
  let i₀ : ι := Classical.choice inferInstance
  refine ⟨q i₀, fun i => ?_⟩
  have hwalk : ∀ {u v : ι}, G.Walk u v → q u = q v := by
    intro u v p
    induction p with
    | nil => rfl
    | @cons u v w huv p ih =>
        exact (eq_of_positive_edge_of_apply_eq_zero g hsym hnonneg q hq
          (hpos u v huv)).trans ih
  obtain ⟨p⟩ := hG i i₀
  exact hwalk p

lemma apply_eq_zero_iff_constant
    (g : ι → ι → ℝ) (hsym : ∀ i j, g i j = g j i)
    (hnonneg : ∀ i j, 0 ≤ g i j) (G : SimpleGraph ι)
    (hG : G.Connected) (hpos : ∀ i j, G.Adj i j → 0 < g i j)
    (q : ι → ℝ) : apply g q = 0 ↔ ∃ c : ℝ, ∀ i, q i = c := by
  constructor
  · exact constant_of_apply_eq_zero g hsym hnonneg G hG hpos q
  · rintro ⟨c, hc⟩
    have heq : q = fun _ => c := funext hc
    rw [heq]
    exact apply_const g c

/-- The mass-weighted normalization eliminates the constant kernel. -/
lemma eq_zero_of_normalized_kernel
    (g : ι → ι → ℝ) (hsym : ∀ i j, g i j = g j i)
    (hnonneg : ∀ i j, 0 ≤ g i j) (G : SimpleGraph ι)
    (hG : G.Connected) (hpos : ∀ i j, G.Adj i j → 0 < g i j)
    (m q : ι → ℝ) (hm : ∑ i, m i = 1)
    (hq : apply g q = 0) (hmean : ∑ i, m i * q i = 0) : q = 0 := by
  obtain ⟨c, hc⟩ := constant_of_apply_eq_zero g hsym hnonneg G hG hpos q hq
  have hc0 : c = 0 := by
    simp_rw [hc] at hmean
    rw [← Finset.sum_mul, hm, one_mul] at hmean
    exact hmean
  funext i
  simpa [hc0] using hc i

lemma pairing_symmetric (g : ι → ι → ℝ) (hsym : ∀ i j, g i j = g j i)
    (q r : ι → ℝ) :
    (∑ i, apply g q i * r i) = ∑ i, q i * apply g r i := by
  have hswap : (∑ i, ∑ j, g i j * q j * r i) =
      ∑ i, ∑ j, g i j * q i * r j := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [hsym j i]
  calc
    (∑ i, apply g q i * r i) =
        (∑ i, ∑ j, g i j * q i * r i) -
        (∑ i, ∑ j, g i j * q j * r i) := by
      simp only [apply, Finset.sum_mul, mul_sub, sub_mul, Finset.sum_sub_distrib]
    _ = (∑ i, ∑ j, g i j * q i * r i) -
        (∑ i, ∑ j, g i j * q i * r j) := by rw [hswap]
    _ = ∑ i, q i * apply g r i := by
      simp only [apply, Finset.mul_sum, mul_sub, Finset.sum_sub_distrib]
      congr 1 <;> apply Finset.sum_congr rfl <;> intro i hi <;>
        apply Finset.sum_congr rfl <;> intro j hj <;> ring

/-- The cell Laplacian as an operator on Euclidean coordinate space. -/
def linearMap (g : ι → ι → ℝ) :
    EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι where
  toFun q := WithLp.toLp 2 (apply g q)
  map_add' q r := by
    ext i
    simp only [PiLp.add_apply, apply]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  map_smul' c q := by
    ext i
    simp only [PiLp.smul_apply, apply, smul_eq_mul,
      RingHom.id_apply]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring

@[simp] lemma linearMap_apply (g : ι → ι → ℝ) (q : EuclideanSpace ℝ ι) (i : ι) :
    linearMap g q i = apply g q i := rfl

lemma linearMap_isSymmetric (g : ι → ι → ℝ)
    (hsym : ∀ i j, g i j = g j i) : (linearMap g).IsSymmetric := by
  intro q r
  simpa only [PiLp.inner_apply, Real.inner_apply, linearMap_apply, mul_comm]
    using pairing_symmetric g hsym q r

/-- The image of a connected symmetric cell Laplacian is the zero-sum hyperplane. -/
lemma mem_range_iff_sum_eq_zero
    (g : ι → ι → ℝ) (hsym : ∀ i j, g i j = g j i)
    (hnonneg : ∀ i j, 0 ≤ g i j) (G : SimpleGraph ι)
    (hG : G.Connected) (hpos : ∀ i j, G.Adj i j → 0 < g i j)
    (z : EuclideanSpace ℝ ι) :
    z ∈ LinearMap.range (linearMap g) ↔ ∑ i, z i = 0 := by
  constructor
  · rintro ⟨q, rfl⟩
    exact sum_apply g hsym q
  · intro hz
    have hr : LinearMap.range (linearMap g) =
        (LinearMap.ker (linearMap g))ᗮ := by
      rw [← (linearMap_isSymmetric g hsym).orthogonal_range,
        Submodule.orthogonal_orthogonal]
    rw [hr, Submodule.mem_orthogonal]
    intro q hq
    have hzero : linearMap g q = 0 := hq
    have hq' : apply g q = 0 := by
      funext i
      exact congrArg (fun x : EuclideanSpace ℝ ι => x i) hzero
    obtain ⟨c, hc⟩ := constant_of_apply_eq_zero g hsym hnonneg G hG hpos q hq'
    simp only [PiLp.inner_apply, Real.inner_apply]
    simp_rw [hc]
    rw [← Finset.mul_sum, hz, mul_zero]

lemma exists_apply_eq_of_sum_eq_zero
    (g : ι → ι → ℝ) (hsym : ∀ i j, g i j = g j i)
    (hnonneg : ∀ i j, 0 ≤ g i j) (G : SimpleGraph ι)
    (hG : G.Connected) (hpos : ∀ i j, G.Adj i j → 0 < g i j)
    (z : ι → ℝ) (hz : ∑ i, z i = 0) : ∃ q : ι → ℝ, apply g q = z := by
  have hz' : WithLp.toLp 2 z ∈ LinearMap.range (linearMap g) :=
    (mem_range_iff_sum_eq_zero g hsym hnonneg G hG hpos _).mpr hz
  obtain ⟨q, hq⟩ := hz'
  refine ⟨q, funext (fun i => ?_)⟩
  exact congrArg (fun x : EuclideanSpace ℝ ι => x i) hq

lemma apply_sub_const (g : ι → ι → ℝ) (q : ι → ℝ) (c : ℝ) :
    apply g (fun i => q i - c) = apply g q := by
  funext i
  apply Finset.sum_congr rfl
  intro j hj
  congr 1
  ring

lemma apply_sub (g : ι → ι → ℝ) (q r : ι → ℝ) :
    apply g (q - r) = apply g q - apply g r := by
  funext i
  simp only [apply, Pi.sub_apply, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- The mass-weighted normalization determines the solution of the cell equation uniquely. -/
lemma existsUnique_normalized_solution
    (g : ι → ι → ℝ) (hsym : ∀ i j, g i j = g j i)
    (hnonneg : ∀ i j, 0 ≤ g i j) (G : SimpleGraph ι)
    (hG : G.Connected) (hpos : ∀ i j, G.Adj i j → 0 < g i j)
    (m z : ι → ℝ) (hm : ∑ i, m i = 1) (hz : ∑ i, z i = 0) :
    ∃! q : ι → ℝ, apply g q = z ∧ ∑ i, m i * q i = 0 := by
  obtain ⟨q, hq⟩ := exists_apply_eq_of_sum_eq_zero g hsym hnonneg G hG hpos z hz
  let c := ∑ i, m i * q i
  let q' : ι → ℝ := fun i => q i - c
  have hq' : apply g q' = z := (apply_sub_const g q c).trans hq
  have hmean : ∑ i, m i * q' i = 0 := by
    simp only [q', mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hm, one_mul]
    exact sub_self c
  refine ⟨q', ⟨hq', hmean⟩, ?_⟩
  rintro r ⟨hr, hrmean⟩
  have hkernel : apply g (r - q') = 0 := by rw [apply_sub, hr, hq', sub_self]
  have hdiffmean : ∑ i, m i * (r - q') i = 0 := by
    simp only [Pi.sub_apply, mul_sub, Finset.sum_sub_distrib, hrmean, hmean, sub_self]
  have hdiff := eq_zero_of_normalized_kernel g hsym hnonneg G hG hpos m (r - q')
    hm hkernel hdiffmean
  exact sub_eq_zero.mp hdiff

end CellLaplacian
end Problem358

namespace Problem358.CellLaplacian

variable {ι : Type*} [Fintype ι]

/-- The weighted intercept normalization functional. -/
def weightedMean (m : ι → ℝ) : (ι → ℝ) →ₗ[ℝ] ℝ where
  toFun q := ∑ i, m i * q i
  map_add' q r := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' c q := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    simp_rw [mul_left_comm (m _) c]
    exact (Finset.mul_sum _ _ _).symm

/-- The hyperplane of intercepts with weighted average zero. -/
def normalizedSpace (m : ι → ℝ) : Submodule ℝ (ι → ℝ) := (weightedMean m).ker

@[simp] lemma mem_normalizedSpace (m q : ι → ℝ) :
    q ∈ normalizedSpace m ↔ ∑ i, m i * q i = 0 := Iff.rfl

/-- The weighted Laplacian on coordinate functions, without a change of norm. -/
def coordinateLinearMap (g : ι → ι → ℝ) : (ι → ℝ) →ₗ[ℝ] (ι → ℝ) where
  toFun := apply g
  map_add' q r := by
    funext i
    simp only [apply, Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  map_smul' c q := by
    funext i
    simp only [apply, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring

@[simp] lemma coordinateLinearMap_apply (g : ι → ι → ℝ) (q : ι → ℝ) :
    coordinateLinearMap g q = apply g q := rfl

/-- The normalized mass Jacobian, with codomain the zero-sum mass variations. -/
def normalizedLinearMap (g : ι → ι → ℝ) (hsym : ∀ i j, g i j = g j i)
    (m : ι → ℝ) : normalizedSpace m →ₗ[ℝ] normalizedSpace (fun _ : ι => 1) :=
  ((coordinateLinearMap g).comp (normalizedSpace m).subtype).codRestrict
    (normalizedSpace (fun _ : ι => 1)) (by
      intro q
      change (∑ i, 1 * apply g q i) = 0
      simpa only [one_mul] using sum_apply g hsym q)

@[simp] lemma normalizedLinearMap_apply (g : ι → ι → ℝ)
    (hsym : ∀ i j, g i j = g j i) (m : ι → ℝ) (q : normalizedSpace m) :
    (normalizedLinearMap g hsym m q : ι → ℝ) = apply g q := rfl

lemma normalizedLinearMap_bijective
    (g : ι → ι → ℝ) (hsym : ∀ i j, g i j = g j i)
    (hnonneg : ∀ i j, 0 ≤ g i j) (G : SimpleGraph ι)
    (hG : G.Connected) (hpos : ∀ i j, G.Adj i j → 0 < g i j)
    (m : ι → ℝ) (hm : ∑ i, m i = 1) :
    Function.Bijective (normalizedLinearMap g hsym m) := by
  constructor
  · intro q r hqr
    apply Subtype.ext
    have happly : apply g q = apply g r := congrArg Subtype.val hqr
    have hkernel : apply g ((q : ι → ℝ) - r) = 0 := by
      rw [apply_sub, happly, sub_self]
    have hmean : ∑ i, m i * ((q : ι → ℝ) - r) i = 0 := by
      simp only [Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
      change weightedMean m q - weightedMean m r = 0
      rw [q.property, r.property, sub_self]
    exact sub_eq_zero.mp
      (eq_zero_of_normalized_kernel g hsym hnonneg G hG hpos m _ hm hkernel hmean)
  · intro z
    have hz : ∑ i, (z : ι → ℝ) i = 0 := by
      simpa only [mem_normalizedSpace, one_mul] using z.property
    obtain ⟨q, hq, _⟩ :=
      existsUnique_normalized_solution g hsym hnonneg G hG hpos m z hm hz
    exact ⟨⟨q, hq.2⟩, Subtype.ext hq.1⟩

/-- The invertible normalized cell-mass Jacobian.
This is the continuous-linear-equivalence interface needed by the implicit function theorem.
Its existence makes no assertion of a uniform bound on the inverse. -/
def normalizedEquiv
    (g : ι → ι → ℝ) (hsym : ∀ i j, g i j = g j i)
    (hnonneg : ∀ i j, 0 ≤ g i j) (G : SimpleGraph ι)
    (hG : G.Connected) (hpos : ∀ i j, G.Adj i j → 0 < g i j)
    (m : ι → ℝ) (hm : ∑ i, m i = 1) :
    normalizedSpace m ≃L[ℝ] normalizedSpace (fun _ : ι => 1) :=
  (LinearEquiv.ofBijective (normalizedLinearMap g hsym m)
    (normalizedLinearMap_bijective g hsym hnonneg G hG hpos m hm)).toContinuousLinearEquiv

@[simp] lemma normalizedEquiv_apply
    (g : ι → ι → ℝ) (hsym : ∀ i j, g i j = g j i)
    (hnonneg : ∀ i j, 0 ≤ g i j) (G : SimpleGraph ι)
    (hG : G.Connected) (hpos : ∀ i j, G.Adj i j → 0 < g i j)
    (m : ι → ℝ) (hm : ∑ i, m i = 1) (q : normalizedSpace m) :
    (normalizedEquiv g hsym hnonneg G hG hpos m hm q : ι → ℝ) = apply g q := rfl

/-- Applying the inverse solves the normalized cell-mass equation. -/
@[simp] lemma apply_normalizedEquiv_symm
    (g : ι → ι → ℝ) (hsym : ∀ i j, g i j = g j i)
    (hnonneg : ∀ i j, 0 ≤ g i j) (G : SimpleGraph ι)
    (hG : G.Connected) (hpos : ∀ i j, G.Adj i j → 0 < g i j)
    (m : ι → ℝ) (hm : ∑ i, m i = 1)
    (z : normalizedSpace (fun _ : ι => 1)) :
    apply g ((normalizedEquiv g hsym hnonneg G hG hpos m hm).symm z) = z :=
  congrArg Subtype.val ((normalizedEquiv g hsym hnonneg G hG hpos m hm).apply_symm_apply z)

/-- The inverse automatically has the required weighted normalization. -/
lemma normalizedEquiv_symm_weightedMean
    (g : ι → ι → ℝ) (hsym : ∀ i j, g i j = g j i)
    (hnonneg : ∀ i j, 0 ≤ g i j) (G : SimpleGraph ι)
    (hG : G.Connected) (hpos : ∀ i j, G.Adj i j → 0 < g i j)
    (m : ι → ℝ) (hm : ∑ i, m i = 1)
    (z : normalizedSpace (fun _ : ι => 1)) :
    ∑ i, m i * ((normalizedEquiv g hsym hnonneg G hG hpos m hm).symm z : ι → ℝ) i = 0 :=
  ((normalizedEquiv g hsym hnonneg G hG hpos m hm).symm z).property

end Problem358.CellLaplacian

end

/-! Implicit-function glue for normalized prescribed cell masses. -/

noncomputable section
open scoped Topology BigOperators ContDiff
open Filter

namespace Problem358

section UniqueImplicit
variable {P Q R : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]
  [NormedAddCommGroup Q] [NormedSpace ℝ Q] [CompleteSpace Q]
  [NormedAddCommGroup R] [NormedSpace ℝ R] [CompleteSpace R]

/-- A uniquely specified solution agrees locally with the implicit branch, and so inherits
its regularity. No prior continuity of the selected solution is required. -/
theorem contDiffAt_unique_implicit_solution
    {n : ℕ∞ω} {F : P × Q → R} {s : P → Q} {p : P}
    (hn : n ≠ 0) (hF : ContDiffAt ℝ n F (p, s p))
    (hpartial : (fderiv ℝ F (p, s p) ∘L ContinuousLinearMap.inr ℝ P Q).IsInvertible)
    (hzero : F (p, s p) = 0)
    (hunique : ∀ᶠ x in 𝓝 p, ∀ q, F (x, q) = 0 → q = s x) :
    ContDiffAt ℝ n s p := by
  let ψ := hF.implicitFunction hn hpartial
  have heq : s =ᶠ[𝓝 p] ψ := by
    filter_upwards [hF.eventually_apply_implicitFunction hn hpartial, hunique] with x hx hu
    exact (hu _ (hx.trans hzero)).symm
  exact (hF.contDiffAt_implicitFunction hn hpartial).congr_of_eventuallyEq heq

/-- The derivative of the uniquely specified branch is the usual implicit derivative. -/
theorem hasStrictFDerivAt_unique_implicit_solution
    {n : ℕ∞ω} {F : P × Q → R} {s : P → Q} {p : P}
    (hn : n ≠ 0) (hF : ContDiffAt ℝ n F (p, s p))
    (hpartial : (fderiv ℝ F (p, s p) ∘L ContinuousLinearMap.inr ℝ P Q).IsInvertible)
    (hzero : F (p, s p) = 0)
    (hunique : ∀ᶠ x in 𝓝 p, ∀ q, F (x, q) = 0 → q = s x) :
    HasStrictFDerivAt s
      (-(fderiv ℝ F (p, s p) ∘L ContinuousLinearMap.inr ℝ P Q).inverse ∘L
        (fderiv ℝ F (p, s p) ∘L ContinuousLinearMap.inl ℝ P Q)) p := by
  let ψ := hF.implicitFunction hn hpartial
  have heq : s =ᶠ[𝓝 p] ψ := by
    filter_upwards [hF.eventually_apply_implicitFunction hn hpartial, hunique] with x hx hu
    exact (hu _ (hx.trans hzero)).symm
  exact (hF.hasStrictFDerivAt_implicitFunction hn hpartial).congr_of_eventuallyEq heq.symm

omit [CompleteSpace R] in
/-- An invertible derivative makes the fiber of a map locally a singleton. -/
theorem eventually_eq_of_hasStrictFDerivAt_equiv [CompleteSpace R]
    {f : Q → R} {q : Q} (e : Q ≃L[ℝ] R)
    (hf : HasStrictFDerivAt f e.toContinuousLinearMap q) :
    ∀ᶠ r in 𝓝 q, f r = f q → r = q := by
  filter_upwards [hf.eventually_left_inverse] with r hr hfr
  rw [hfr, hf.localInverse_apply_image] at hr
  exact hr.symm

end UniqueImplicit

namespace CellLaplacian
variable {ι P : Type*} [Fintype ι]
  [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]

omit [CompleteSpace P] in
/-- Invertibility of the intercept partial derivative follows from the connected cell graph. -/
theorem partial_isInvertible_of_laplacian [CompleteSpace P]
    (g : ι → ι → ℝ) (hsym : ∀ i j, g i j = g j i)
    (hnonneg : ∀ i j, 0 ≤ g i j) (G : SimpleGraph ι)
    (hG : G.Connected) (hpos : ∀ i j, G.Adj i j → 0 < g i j)
    (m : ι → ℝ) (hm : ∑ i, m i = 1)
    (A : P × normalizedSpace m →L[ℝ] normalizedSpace (fun _ : ι => 1))
    (hA : A ∘L ContinuousLinearMap.inr ℝ P (normalizedSpace m) =
      (normalizedEquiv g hsym hnonneg G hG hpos m hm).toContinuousLinearMap) :
    (A ∘L ContinuousLinearMap.inr ℝ P (normalizedSpace m)).IsInvertible := by
  rw [hA]
  exact ContinuousLinearMap.isInvertible_equiv

/-- The analytic hypothesis on the mass map and the algebraic cell graph together imply
smooth dependence of its uniquely normalized solution on the sites. -/
theorem contDiffAt_normalized_solution
    {n : ℕ∞ω} (hn : n ≠ 0)
    (g : ι → ι → ℝ) (hsym : ∀ i j, g i j = g j i)
    (hnonneg : ∀ i j, 0 ≤ g i j) (G : SimpleGraph ι)
    (hG : G.Connected) (hpos : ∀ i j, G.Adj i j → 0 < g i j)
    (m : ι → ℝ) (hm : ∑ i, m i = 1)
    (F : P × normalizedSpace m → normalizedSpace (fun _ : ι => 1))
    (s : P → normalizedSpace m) (p : P)
    (hF : ContDiffAt ℝ n F (p, s p))
    (hA : fderiv ℝ F (p, s p) ∘L ContinuousLinearMap.inr ℝ P (normalizedSpace m) =
      (normalizedEquiv g hsym hnonneg G hG hpos m hm).toContinuousLinearMap)
    (hzero : F (p, s p) = 0)
    (hunique : ∀ᶠ x in 𝓝 p, ∀ q, F (x, q) = 0 → q = s x) :
    ContDiffAt ℝ n s p := by
  exact contDiffAt_unique_implicit_solution hn hF
    (partial_isInvertible_of_laplacian g hsym hnonneg G hG hpos m hm _ hA) hzero hunique

end CellLaplacian
end Problem358

namespace Problem358.CellLaplacian

variable {ι : Type*} [Fintype ι]

/-- Along a real parameter, the derivative of the prescribed normalized intercepts
is the negative inverse mass Jacobian applied to the site variation. -/
theorem hasDerivAt_normalized_solution
    {n : ℕ∞ω} (hn : n ≠ 0)
    (g : ι → ι → ℝ) (hsym : ∀ i j, g i j = g j i)
    (hnonneg : ∀ i j, 0 ≤ g i j) (G : SimpleGraph ι)
    (hG : G.Connected) (hpos : ∀ i j, G.Adj i j → 0 < g i j)
    (m : ι → ℝ) (hm : ∑ i, m i = 1)
    (F : ℝ × normalizedSpace m → normalizedSpace (fun _ : ι => 1))
    (s : ℝ → normalizedSpace m) (t : ℝ)
    (hF : ContDiffAt ℝ n F (t, s t))
    (hA : fderiv ℝ F (t, s t) ∘L ContinuousLinearMap.inr ℝ ℝ (normalizedSpace m) =
      (normalizedEquiv g hsym hnonneg G hG hpos m hm).toContinuousLinearMap)
    (hzero : F (t, s t) = 0)
    (hunique : ∀ᶠ x in 𝓝 t, ∀ q, F (x, q) = 0 → q = s x) :
    HasDerivAt s
      (-((normalizedEquiv g hsym hnonneg G hG hpos m hm).symm
        (fderiv ℝ F (t, s t) (1, 0)))) t := by
  have h := (Problem358.hasStrictFDerivAt_unique_implicit_solution hn hF
    (partial_isInvertible_of_laplacian g hsym hnonneg G hG hpos m hm _ hA)
    hzero hunique).hasStrictDerivAt.hasDerivAt
  simpa only [hA, ContinuousLinearMap.inverse_equiv, ContinuousLinearMap.comp_apply,
    neg_apply, ContinuousLinearMap.inl_apply,
    ContinuousLinearEquiv.coe_coe] using h

/-- The differentiated fixed-mass constraint, directly in cell coordinates. -/
theorem laplacian_deriv_normalized_solution
    {n : ℕ∞ω} (hn : n ≠ 0)
    (g : ι → ι → ℝ) (hsym : ∀ i j, g i j = g j i)
    (hnonneg : ∀ i j, 0 ≤ g i j) (G : SimpleGraph ι)
    (hG : G.Connected) (hpos : ∀ i j, G.Adj i j → 0 < g i j)
    (m : ι → ℝ) (hm : ∑ i, m i = 1)
    (F : ℝ × normalizedSpace m → normalizedSpace (fun _ : ι => 1))
    (s : ℝ → normalizedSpace m) (t : ℝ)
    (hF : ContDiffAt ℝ n F (t, s t))
    (hA : fderiv ℝ F (t, s t) ∘L ContinuousLinearMap.inr ℝ ℝ (normalizedSpace m) =
      (normalizedEquiv g hsym hnonneg G hG hpos m hm).toContinuousLinearMap)
    (hzero : F (t, s t) = 0)
    (hunique : ∀ᶠ x in 𝓝 t, ∀ q, F (x, q) = 0 → q = s x) :
    apply g (↑(deriv s t : normalizedSpace m) : ι → ℝ) = -(fderiv ℝ F (t, s t) (1, 0) : ι → ℝ) := by
  rw [(hasDerivAt_normalized_solution hn g hsym hnonneg G hG hpos m hm
    F s t hF hA hzero hunique).deriv]
  change coordinateLinearMap g
    (-((normalizedEquiv g hsym hnonneg G hG hpos m hm).symm
      (fderiv ℝ F (t, s t) (1, 0)) : ι → ℝ)) = _
  rw [map_neg, coordinateLinearMap_apply, apply_normalizedEquiv_symm]

end Problem358.CellLaplacian

end

noncomputable section
open scoped BigOperators Topology ContDiff

namespace Problem358.CellLaplacian
variable {ι : Type*} [Fintype ι]

/-- A continuous linear projection onto zero-sum mass variations. -/
def zeroSumProjection (m : ι → ℝ) (hm : ∑ i, m i = 1) :
    (ι → ℝ) →L[ℝ] normalizedSpace (fun _ : ι => 1) :=
  LinearMap.toContinuousLinearMap {
    toFun := fun z => ⟨fun i => z i - (∑ j, z j) * m i, by
      simp only [mem_normalizedSpace, one_mul, Finset.sum_sub_distrib,
        ← Finset.mul_sum, hm, mul_one, sub_self]⟩
    map_add' := by
      intro z w
      apply Subtype.ext
      funext i
      change z i + w i - (∑ j, (z j + w j)) * m i =
        (z i - (∑ j, z j) * m i) + (w i - (∑ j, w j) * m i)
      rw [Finset.sum_add_distrib]
      ring
    map_smul' := by
      intro a z
      apply Subtype.ext
      funext i
      change a * z i - (∑ j, a * z j) * m i =
        a * (z i - (∑ j, z j) * m i)
      rw [← Finset.mul_sum]
      ring }

@[simp] theorem zeroSumProjection_apply (m : ι → ℝ) (hm : ∑ i, m i = 1)
    (z : ι → ℝ) (i : ι) :
    (zeroSumProjection m hm z : ι → ℝ) i = z i - (∑ j, z j) * m i := rfl

/-- The projection fixes all genuine mass variations. -/
theorem zeroSumProjection_eq (m : ι → ℝ) (hm : ∑ i, m i = 1)
    (z : ι → ℝ) (hz : ∑ i, z i = 0) :
    (zeroSumProjection m hm z : ι → ℝ) = z := by
  funext i
  simp [hz]

/-- The mass residual for an ordinary coordinate-valued mass map. -/
def massResidual {P : Type*} (m : ι → ℝ) (hm : ∑ i, m i = 1)
    (M : P × normalizedSpace m → (ι → ℝ)) :
    P × normalizedSpace m → normalizedSpace (fun _ : ι => 1) :=
  fun x => zeroSumProjection m hm (M x - m)

/-- On probability mass vectors the projected residual is exactly the physical residual. -/
theorem massResidual_coe {P : Type*} (m : ι → ℝ) (hm : ∑ i, m i = 1)
    (M : P × normalizedSpace m → (ι → ℝ)) (x : P × normalizedSpace m)
    (hM : ∑ i, M x i = 1) :
    (massResidual m hm M x : ι → ℝ) = M x - m := by
  apply zeroSumProjection_eq
  simp only [Pi.sub_apply, Finset.sum_sub_distrib, hM, hm, sub_self]

theorem massResidual_eq_zero_iff {P : Type*} (m : ι → ℝ) (hm : ∑ i, m i = 1)
    (M : P × normalizedSpace m → (ι → ℝ)) (x : P × normalizedSpace m)
    (hM : ∑ i, M x i = 1) : massResidual m hm M x = 0 ↔ M x = m := by
  rw [← Subtype.coe_inj, massResidual_coe m hm M x hM]
  change M x - m = 0 ↔ _
  exact sub_eq_zero

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem contDiffAt_massResidual {n : ℕ∞ω} (m : ι → ℝ) (hm : ∑ i, m i = 1)
    {M : P × normalizedSpace m → (ι → ℝ)} {x : P × normalizedSpace m}
    (hM : ContDiffAt ℝ n M x) : ContDiffAt ℝ n (massResidual m hm M) x := by
  exact (zeroSumProjection m hm).contDiff.contDiffAt.comp x (hM.sub contDiffAt_const)

theorem hasFDerivAt_massResidual (m : ι → ℝ) (hm : ∑ i, m i = 1)
    {M : P × normalizedSpace m → (ι → ℝ)} {x : P × normalizedSpace m}
    {A : P × normalizedSpace m →L[ℝ] (ι → ℝ)} (hM : HasFDerivAt M A x) :
    HasFDerivAt (massResidual m hm M) ((zeroSumProjection m hm) ∘L A) x := by
  exact (zeroSumProjection m hm).hasFDerivAt.comp x (hM.sub_const m)

/-- Projection does not alter a Laplacian derivative: its image already has zero sum. -/
theorem zeroSumProjection_laplacian (m : ι → ℝ) (hm : ∑ i, m i = 1)
    (g : ι → ι → ℝ) (hsym : ∀ i j, g i j = g j i)
    (q : normalizedSpace m) :
    zeroSumProjection m hm (apply g q) = normalizedLinearMap g hsym m q := by
  apply Subtype.ext
  exact zeroSumProjection_eq m hm _ (sum_apply g hsym q)

/-- An ordinary coordinate derivative with Laplacian intercept part induces precisely
the normalized continuous linear equivalence used by the implicit function theorem. -/
theorem massResidual_partial_eq
    (g : ι → ι → ℝ) (hsym : ∀ i j, g i j = g j i)
    (hnonneg : ∀ i j, 0 ≤ g i j) (G : SimpleGraph ι)
    (hG : G.Connected) (hpos : ∀ i j, G.Adj i j → 0 < g i j)
    (m : ι → ℝ) (hm : ∑ i, m i = 1)
    (A : P × normalizedSpace m →L[ℝ] (ι → ℝ))
    (hA : ∀ q : normalizedSpace m, A (0, q) = apply g q) :
    ((zeroSumProjection m hm) ∘L A) ∘L
        ContinuousLinearMap.inr ℝ P (normalizedSpace m) =
      (normalizedEquiv g hsym hnonneg G hG hpos m hm).toContinuousLinearMap := by
  ext q i
  change (zeroSumProjection m hm (A (0, q)) : ι → ℝ) i = apply g q i
  rw [hA]
  exact congrFun (zeroSumProjection_eq m hm _ (sum_apply g hsym q)) i

end Problem358.CellLaplacian

end

end OAI
