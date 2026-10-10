import Mathlib
import OAI.Analysis.AffineBernstein.Basic
import OAI.Analysis.AffineBernstein.ConvexLocalLimits

namespace OAI

noncomputable section

namespace AffineBernstein
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
open Filter Metric
open scoped Topology Pointwise

section AffineFamily
open Filter Metric
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]

/- For distance functions, pointwise convergence is automatically locally
uniform, by the common unit Lipschitz constant and a finite compact cover. -/
omit [NormedSpace ℝ E] in
theorem LocalDistanceConverges.of_pointwise {Cj : ℕ → Set E} {C : Set E}
    (hpt : ∀ x, Tendsto (fun j => infDist x (Cj j)) atTop (𝓝 (infDist x C))) :
    LocalDistanceConverges Cj C := by
  classical
  apply tendstoLocallyUniformly_iff_forall_isCompact.mpr
  intro K hK
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨t, htK, ht⟩ := hK.elim_nhds_subcover (fun x => ball x (ε / 3))
    (fun x _ => ball_mem_nhds x (by positivity))
  have he : ∀ x ∈ t, ∀ᶠ j in atTop, dist (infDist x C) (infDist x (Cj j)) < ε / 3 := by
    intro x hx
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (hpt x) (ε / 3) (by positivity)
    filter_upwards [eventually_ge_atTop N] with j hj
    simpa [dist_comm] using hN j hj
  filter_upwards [(t.eventually_all).mpr he] with j hj x hx
  obtain ⟨y, hyt, hxy⟩ := mem_iUnion₂.mp (ht hx)
  have hd : dist x y < ε / 3 := hxy
  have h1 : dist (infDist x C) (infDist y C) ≤ dist x y := by
    simpa using (lipschitz_infDist_pt C).dist_le_mul x y
  have h2 : dist (infDist y (Cj j)) (infDist x (Cj j)) ≤ dist x y := by
    simpa [dist_comm] using (lipschitz_infDist_pt (Cj j)).dist_le_mul y x
  calc
    dist (infDist x C) (infDist x (Cj j)) ≤
        dist (infDist x C) (infDist y C) + dist (infDist y C) (infDist y (Cj j)) +
          dist (infDist y (Cj j)) (infDist x (Cj j)) := dist_triangle4 _ _ _ _
    _ < ε := by linarith [hj y hyt]

/- Fixed changes of coordinates preserve local set convergence. A proper
homeomorphism suffices: compact preimages supply the lower distance bound and
actual approximating points supply the upper bound. In particular this applies
to every fixed invertible affine change of coordinates. -/
omit [NormedSpace ℝ E] in
theorem LocalDistanceConverges.homeomorph
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [ProperSpace F]
    {Cj : ℕ → Set E} {C : Set E} (h : LocalDistanceConverges Cj C)
    (hcl : IsClosed C) (hne : C.Nonempty)
    (hclj : ∀ j, IsClosed (Cj j)) (hnej : ∀ j, (Cj j).Nonempty)
    (A : E ≃ₜ F) : LocalDistanceConverges (fun j => A '' Cj j) (A '' C) := by
  apply LocalDistanceConverges.of_pointwise
  intro x
  apply tendsto_order.2
  constructor
  · intro a ha
    by_cases haneg : a < 0
    · exact Eventually.of_forall fun j => haneg.trans_le infDist_nonneg
    let S : Set E := A.symm '' closedBall x a
    have hSc : IsCompact S := (isCompact_closedBall x a).image A.symm.continuous
    have hdis : Disjoint C S := by
      rw [Set.disjoint_left]
      rintro y hy ⟨z, hz, rfl⟩
      have he : infDist x (A '' C) ≤ dist x z := by
        apply infDist_le_dist_of_mem
        exact ⟨A.symm z, hy, A.apply_symm_apply z⟩
      have hz' : dist x z ≤ a := by simpa [mem_closedBall, dist_comm] using hz
      linarith
    filter_upwards [h.eventually_disjoint_compact hcl hne hSc hdis] with j hj
    obtain ⟨z, hz, hdist⟩ := (A.isClosedMap _ (hclj j)).exists_infDist_eq_dist ((hnej j).image A) x
    rw [hdist]
    by_contra hn
    obtain ⟨y, hy, rfl⟩ := hz
    apply Set.disjoint_left.mp hj hy
    exact ⟨A y, by simpa [mem_closedBall, dist_comm] using not_lt.mp hn, A.symm_apply_apply y⟩
  · intro b hb
    obtain ⟨z, hz, hdist⟩ := (A.isClosedMap _ hcl).exists_infDist_eq_dist (hne.image A) x
    obtain ⟨y, hy, rfl⟩ := hz
    obtain ⟨yj, hyj, hyt⟩ := h.exists_approximating hclj hnej hy
    have ht : Tendsto (fun j => dist x (A (yj j))) atTop (𝓝 (dist x (A y))) :=
      tendsto_const_nhds.dist ((A.continuous.tendsto y).comp hyt)
    have hb' : dist x (A y) < b := by simpa [hdist] using hb
    filter_upwards [ht.eventually_lt_const hb'] with j hj
    exact (infDist_le_dist_of_mem (s := A '' Cj j) ⟨yj j, hyj j, rfl⟩).trans_lt hj

/- A diagonal choice of approximating bodies. The bounds on the growing
closed balls are the literal metric construction behind the affine-family
closure assertion, not an assumed transitivity of sequential limits. -/
omit [NormedSpace ℝ E] in
theorem LocalDistanceConverges.diagonal
    {Cj : ℕ → Set E} {C : Set E} {D : ℕ → ℕ → Set E}
    (h : LocalDistanceConverges Cj C)
    (hD : ∀ j, LocalDistanceConverges (D j) (Cj j)) :
    ∃ q : ℕ → ℕ, LocalDistanceConverges (fun j => D j (q j)) C := by
  have hgood : ∀ j : ℕ, ∃ q : ℕ, ∀ x ∈ closedBall (0 : E) (j + 1 : ℝ),
      dist (infDist x (Cj j)) (infDist x (D j q)) < (j + 1 : ℝ)⁻¹ := by
    intro j
    have hu := tendstoLocallyUniformly_iff_forall_isCompact.mp (hD j)
      (closedBall (0 : E) (j + 1 : ℝ)) (isCompact_closedBall _ _)
    exact (Metric.tendstoUniformlyOn_iff.mp hu _ (by positivity)).exists
  choose q hq using hgood
  refine ⟨q, LocalDistanceConverges.of_pointwise ?_⟩
  intro x
  have hdist : Tendsto (fun j => dist (infDist x (Cj j)) (infDist x (D j (q j)))) atTop (𝓝 0) := by
    have hsmall : Tendsto (fun j : ℕ => (j + 1 : ℝ)⁻¹) atTop (𝓝 0) := by
      simpa [one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    obtain ⟨N, hN⟩ := exists_nat_gt ‖x‖
    have he : ∀ᶠ j in atTop, dist (infDist x (Cj j)) (infDist x (D j (q j))) ≤ (j + 1 : ℝ)⁻¹ := by
      filter_upwards [eventually_ge_atTop N] with j hj
      apply (hq j x ?_).le
      rw [mem_closedBall, dist_zero_right]
      have hn : (N : ℝ) ≤ j := by exact_mod_cast hj
      linarith
    exact squeeze_zero' (Eventually.of_forall fun _ => dist_nonneg) he hsmall
  exact (h.pointwise x).congr_dist hdist

/- Literal full-dimensional affine local-limit family of geometry.tex:87.
The affine maps may vary along the approximating sequence. -/
structure InAffineLimitFamily {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (D : Set E) (C : Set F) : Prop where
  closed : IsClosed C
  convex : Convex ℝ C
  interior_nonempty : (interior C).Nonempty
  approximation : ∃ A : ℕ → (E ≃ᴬ[ℝ] F), LocalDistanceConverges (fun j => A j '' D) C

namespace InAffineLimitFamily
variable {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [ProperSpace F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [ProperSpace G]
  {D : Set E} {C : Set F}

omit [ProperSpace E] [ProperSpace F] in
theorem nonempty (h : InAffineLimitFamily D C) : C.Nonempty :=
  h.interior_nonempty.mono interior_subset

omit [ProperSpace E] in
theorem affine_image (h : InAffineLimitFamily D C)
    (hD : IsClosed D) (hneD : D.Nonempty) (B : F ≃ᴬ[ℝ] G) :
    InAffineLimitFamily D (B '' C) := by
  obtain ⟨A, hA⟩ := h.approximation
  refine ⟨B.toHomeomorph.isClosedMap _ h.closed,
    h.convex.affine_image B.toAffineEquiv.toAffineMap, ?_, ?_⟩
  · change (interior (B.toHomeomorph '' C)).Nonempty
    rw [← B.toHomeomorph.image_interior]
    exact h.interior_nonempty.image B.toHomeomorph
  · refine ⟨fun j => (A j).trans B, ?_⟩
    convert hA.homeomorph h.closed h.nonempty
      (fun j => (A j).toHomeomorph.isClosedMap _ hD)
      (fun j => hneD.image (A j)) B.toHomeomorph using 1
    · ext j x
      simp only [Set.mem_image, ContinuousAffineEquiv.trans_apply]
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨A j y, ⟨y, hy, rfl⟩, rfl⟩
      · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
        exact ⟨z, hz, rfl⟩
    · rfl

omit [ProperSpace E] in
theorem diagonal_closure {Cj : ℕ → Set F}
    (hj : ∀ j, InAffineLimitFamily D (Cj j))
    (h : LocalDistanceConverges Cj C) (hc : IsClosed C) (hv : Convex ℝ C)
    (hi : (interior C).Nonempty) : InAffineLimitFamily D C := by
  choose A hA using fun j => (hj j).approximation
  obtain ⟨q, hq⟩ := h.diagonal hA
  exact ⟨hc, hv, hi, fun j => A j (q j), hq⟩

omit [ProperSpace E] in
theorem of_affine_image (hD : IsClosed D) (hvD : Convex ℝ D)
    (hiD : (interior D).Nonempty) (A : E ≃ᴬ[ℝ] F) :
    InAffineLimitFamily D (A '' D) := by
  refine ⟨A.toHomeomorph.isClosedMap _ hD, hvD.affine_image A.toAffineEquiv.toAffineMap, ?_, ?_⟩
  · change (interior (A.toHomeomorph '' D)).Nonempty
    rw [← A.toHomeomorph.image_interior]
    exact hiD.image A.toHomeomorph
  · exact ⟨fun _ => A, LocalDistanceConverges.of_pointwise (fun _ => tendsto_const_nhds)⟩

end InAffineLimitFamily

end AffineFamily

open scoped Pointwise

/- The coordinate action of the actual matrix linear equivalence. -/
theorem matrixLinearEquiv_apply {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : IsUnit A.det) (x : Space n) (i : Fin n) :
    Matrix.toLinearEquiv (EuclideanSpace.basisFun (Fin n) ℝ).toBasis A hA x i =
      A.mulVec x i := by
  simp [Matrix.toLinearEquiv_apply, Matrix.toLin_apply,
    EuclideanSpace.basisFun_apply, Pi.single_apply,
    OrthonormalBasis.coe_toBasis_repr_apply, EuclideanSpace.basisFun_repr,
      Matrix.mulVec, dotProduct]

/- A convex combination allowing unused mass at the origin. -/
theorem convex_sum_mem_le_one {E : Type*} [AddCommGroup E] [Module ℝ E]
    {ι : Type*} [Fintype ι] {K : Set E} (hK : Convex ℝ K) (h0 : (0 : E) ∈ K)
    (c : ι → ℝ) (v : ι → E) (hc : ∀ i, 0 ≤ c i)
    (hsum : ∑ i, c i ≤ 1) (hv : ∀ i, v i ∈ K) : (∑ i, c i • v i) ∈ K := by
  classical
  have hn : 0 ≤ ∑ i, c i := Finset.sum_nonneg fun i _ => hc i
  by_cases hz : ∑ i, c i = 0
  · have hc0 : ∀ i, c i = 0 := fun i =>
      (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hc i)).mp hz i (Finset.mem_univ i)
    simpa [hc0] using h0
  · have hp : 0 < ∑ i, c i := lt_of_le_of_ne hn (Ne.symm hz)
    have hm := hK.centerMass_mem (t := Finset.univ) (w := c) (z := v)
      (fun i _ => hc i) hp (fun i _ => hv i)
    have he := hK.smul_mem_of_zero_mem h0 hm ⟨hn, hsum⟩
    simpa [Finset.centerMass, smul_smul, hz] using he

/- The cross-polytope spanned by any points of a symmetric convex body lies
in that body. This is the inner-inclusion half of max-determinant normalization. -/
theorem symmetric_convex_sum_mem {n : ℕ} {K : Set (Space n)}
    (hK : Convex ℝ K) (h0 : (0 : Space n) ∈ K)
    (hneg : ∀ x ∈ K, -x ∈ K) (v : Fin n → Space n)
    (hv : ∀ i, v i ∈ K) (c : Fin n → ℝ) (hc : ∑ i, |c i| ≤ 1) :
    (∑ i, c i • v i) ∈ K := by
  classical
  let w : Fin n → Space n := fun i => if 0 ≤ c i then v i else -v i
  have hw (i : Fin n) : w i ∈ K := by
    dsimp [w]; split_ifs <;> first | exact hv i | exact hneg _ (hv i)
  have he (i : Fin n) : |c i| • w i = c i • v i := by
    dsimp [w]; split_ifs with hi
    · rw [abs_of_nonneg hi]
    · rw [abs_of_neg (lt_of_not_ge hi), neg_smul, smul_neg, neg_neg]
  simpa only [he] using convex_sum_mem_le_one hK h0 (fun i => |c i|) w
    (fun i => abs_nonneg _) hc hw

/- The exact ℓ¹/Euclidean comparison used for the inner ball. -/
theorem sum_abs_coordinate_le {n : ℕ} (x : Space n) :
    ∑ i, |x i| ≤ Real.sqrt n * ‖x‖ := by
  have he := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun i : Fin n => |x i|)
    (fun _ => (1 : ℝ))
  have hn := PiLp.norm_sq_eq_of_L2 (fun _ : Fin n => ℝ) x
  simpa only [mul_one, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one, one_mul, ← Real.norm_eq_abs, ← hn, Real.sqrt_sq (norm_nonneg _),
    mul_comm] using he

/- The exact ℓ∞/Euclidean comparison used for the outer ball. -/
theorem norm_le_sqrt_card_of_coordinate_le {n : ℕ} (x : Space n)
    (hx : ∀ i, |x i| ≤ 1) : ‖x‖ ≤ Real.sqrt n := by
  have hn := PiLp.norm_sq_eq_of_L2 (fun _ : Fin n => ℝ) x
  have hs : ‖x‖ ^ 2 ≤ (n : ℝ) := by
    rw [hn]
    calc
      _ ≤ ∑ i : Fin n, (1 : ℝ) := Finset.sum_le_sum fun i _ => by
        have := hx i
        rw [Real.norm_eq_abs]
        nlinarith [sq_nonneg (|x i| - 1), abs_nonneg (x i)]
      _ = n := by simp
  exact (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
    (by rwa [Real.sq_sqrt (Nat.cast_nonneg n)])

/- A compact body's column determinant has a maximizer, with nonzero value
whenever the body contains a ball about zero. -/
theorem exists_max_det_columns {n : ℕ} {K : Set (Space n)}
    (hK : IsCompact K) {r : ℝ} (hr : 0 < r)
    (hball : Metric.closedBall (0 : Space n) r ⊆ K) :
    ∃ v : Fin n → Space n, (∀ i, v i ∈ K) ∧
      (Matrix.det (fun i j => v j i) ≠ 0) ∧
      ∀ w : Fin n → Space n, (∀ i, w i ∈ K) →
        |Matrix.det (fun i j => w j i)| ≤ |Matrix.det (fun i j => v j i)| := by
  classical
  let S : Set (Fin n → Space n) := {v | ∀ i, v i ∈ K}
  have hS : IsCompact S := isCompact_pi_infinite (fun _ => hK)
  let w : Fin n → Space n := fun j => r • EuclideanSpace.single j 1
  have hw : w ∈ S := by
    intro i
    apply hball
    simp [w, Metric.mem_closedBall, dist_zero_right, norm_smul,
      Real.norm_eq_abs, abs_of_pos hr]
  have hM : (fun i j => w j i) = (r : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ) := by
    ext i j
    simp [w, Matrix.one_apply]
  have hd : Matrix.det (fun i j => w j i) ≠ 0 := by rw [hM]; simp [hr.ne']
  obtain ⟨v, hv, hmax⟩ := hS.exists_isMaxOn ⟨w, hw⟩
    (show Continuous (fun v : Fin n → Space n => |Matrix.det (fun i j => v j i)|) by
      fun_prop).continuousOn
  refine ⟨v, hv, ?_, fun w hw => hmax hw⟩
  intro hz
  have hh := hmax hw
  change |Matrix.det (fun i j => w j i)| ≤ |Matrix.det (fun i j => v j i)| at hh
  rw [hz, abs_zero] at hh
  exact hd (abs_eq_zero.mp (le_antisymm hh (abs_nonneg _)))

/- Maximal determinant makes each inverse coordinate of a body point at most
one. The proof is the literal one-column replacement identity. -/
theorem maxdet_coordinate_bound {n : ℕ} {K : Set (Space n)}
    (v : Fin n → Space n) (hv : ∀ i, v i ∈ K)
    (hd : Matrix.det (fun i j => v j i) ≠ 0)
    (hmax : ∀ w : Fin n → Space n, (∀ i, w i ∈ K) →
      |Matrix.det (fun i j => w j i)| ≤ |Matrix.det (fun i j => v j i)|) :
    ∃ q : Space n ≃ₗ[ℝ] Space n,
      (∀ x : Space n, q x = ∑ i, x i • v i) ∧
      ∀ x ∈ K, ∀ i, |q.symm x i| ≤ 1 := by
  classical
  let M : Matrix (Fin n) (Fin n) ℝ := fun i j => v j i
  let q : Space n ≃ₗ[ℝ] Space n :=
    Matrix.toLinearEquiv (EuclideanSpace.basisFun (Fin n) ℝ).toBasis M
      (isUnit_iff_ne_zero.mpr hd)
  have hq (x : Space n) : q x = ∑ i, x i • v i := by
    ext j
    rw [show q x j = M.mulVec x j from matrixLinearEquiv_apply M _ x j]
    simp [Matrix.mulVec, dotProduct, M, mul_comm]
  refine ⟨q, hq, ?_⟩
  intro x hx j
  have hw : ∀ i, Function.update v j x i ∈ K := by
    intro i
    by_cases h : i = j
    · simpa [h] using hx
    · simpa [Function.update_of_ne h] using hv i
  have hm := hmax (Function.update v j x) hw
  have hcol : (fun i k => Function.update v j x k i) = M.updateCol j x := by
    ext i k
    simp [Matrix.updateCol, M, Function.update_apply]
    split_ifs <;> rfl
  have hsum : (fun k => ∑ i, (q.symm x i) • M k i) = (fun k => x k) := by
    funext k
    have he := congrArg (fun p : Space n => p k) (hq (q.symm x))
    simpa [M, mul_comm] using he.symm
  rw [hcol] at hm
  change |(M.updateCol j (fun k => x k)).det| ≤ |M.det| at hm
  rw [← hsum, Matrix.det_updateCol_sum, smul_eq_mul, abs_mul] at hm
  have hdpos : 0 < |M.det| := abs_pos.mpr hd
  change |q.symm x j| * |M.det| ≤ |M.det| at hm
  exact (mul_le_mul_iff_left₀ hdpos).mp (by simpa using hm)

/- The symmetric max-determinant normalization, with the exact weaker radius
n sufficient for all centered normalizations used in the source. -/
theorem symmetric_body_normalization {n : ℕ} (hn : 1 ≤ n)
    {K : Set (Space n)} (hK : IsCompact K) (hconv : Convex ℝ K)
    (h0 : (0 : Space n) ∈ K) (hneg : ∀ x ∈ K, -x ∈ K)
    {r : ℝ} (hr : 0 < r) (hball : Metric.closedBall (0 : Space n) r ⊆ K) :
    ∃ A : Space n ≃L[ℝ] Space n,
      Metric.closedBall 0 1 ⊆ A '' K ∧ A '' K ⊆ Metric.closedBall 0 n := by
  obtain ⟨v, hv, hd, hmax⟩ := exists_max_det_columns hK hr hball
  obtain ⟨q, hq, hh⟩ := maxdet_coordinate_bound v hv hd hmax
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hspos : 0 < Real.sqrt n := Real.sqrt_pos.mpr hnpos
  let S := LinearEquiv.smulOfNeZero ℝ (Space n) (Real.sqrt n) hspos.ne'
  let A := (q.symm.trans S).toContinuousLinearEquiv
  have hA (x : Space n) : A x = Real.sqrt n • q.symm x := rfl
  refine ⟨A, ?_, ?_⟩
  · intro x hx
    have hxn : ‖x‖ ≤ 1 := by simpa [Metric.mem_closedBall, dist_zero_right] using hx
    let y : Space n := (Real.sqrt n)⁻¹ • x
    have hy : ∑ i, |y i| ≤ 1 := by
      calc
        _ ≤ Real.sqrt n * ‖y‖ := sum_abs_coordinate_le y
        _ = ‖x‖ := by simp [y, norm_smul, Real.norm_eq_abs, abs_of_pos hspos,
          hspos.ne']
        _ ≤ 1 := hxn
    have hmem : q y ∈ K := hq y ▸ symmetric_convex_sum_mem hconv h0 hneg v hv
      (fun i => y i) hy
    refine ⟨q y, hmem, ?_⟩
    rw [hA, LinearEquiv.symm_apply_apply]
    simp [y, smul_smul, hspos.ne']
  · rintro x ⟨y, hy, rfl⟩
    rw [Metric.mem_closedBall, dist_zero_right, hA, norm_smul,
      Real.norm_eq_abs, abs_of_pos hspos]
    calc
      _ ≤ Real.sqrt n * Real.sqrt n := mul_le_mul_of_nonneg_left
        (norm_le_sqrt_card_of_coordinate_le _ (hh y hy)) hspos.le
      _ = n := Real.mul_self_sqrt hnpos.le

open scoped Pointwise

/- Exact centered normalization in geometry.tex (2/(C+1), 2n), proved
without importing John's theorem: first normalize the symmetric difference
body, then use the actual balance inclusion. -/
theorem centered_body_normalization {n : ℕ} (hn : 1 ≤ n)
    {K : Set (Space n)} (hK : IsCompact K) (hconv : Convex ℝ K)
    (hint : (interior K).Nonempty) (h0 : (0 : Space n) ∈ K)
    {C : ℝ} (hC : 1 ≤ C) (hbal : -K ⊆ C • K) :
    ∃ A : Space n ≃L[ℝ] Space n,
      Metric.closedBall 0 (2 / (C + 1)) ⊆ A '' K ∧
      A '' K ⊆ Metric.closedBall 0 (2 * n) := by
  let D := K - K
  have hDeq : D = (fun p : Space n × Space n => p.1 - p.2) '' (K ×ˢ K) := by
    ext x
    constructor
    · rintro ⟨a, ha, b, hb, rfl⟩
      exact ⟨(a, b), ⟨ha, hb⟩, rfl⟩
    · rintro ⟨⟨a, b⟩, ⟨ha, hb⟩, rfl⟩
      exact ⟨a, ha, b, hb, rfl⟩
  have hDc : IsCompact D := by
    rw [hDeq]
    exact (hK.prod hK).image (continuous_fst.sub continuous_snd)
  have hDv : Convex ℝ D := hconv.sub hconv
  have hD0 : (0 : Space n) ∈ D := ⟨0, h0, 0, h0, sub_self _⟩
  have hDneg : ∀ x ∈ D, -x ∈ D := by
    rintro x ⟨a, ha, b, hb, rfl⟩
    exact ⟨b, hb, a, ha, (neg_sub _ _).symm⟩
  obtain ⟨p, hp⟩ := hint
  obtain ⟨r, hr, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    (mem_interior_iff_mem_nhds.mp hp)
  have hDb : Metric.closedBall (0 : Space n) r ⊆ D := by
    intro x hx
    have hpx : p + x ∈ K := hball (by simpa [Metric.mem_closedBall, dist_eq_norm] using hx)
    exact ⟨p + x, hpx, p, interior_subset hp, by abel_nf⟩
  obtain ⟨L, hLin, hLout⟩ := symmetric_body_normalization hn hDc hDv hD0 hDneg hr hDb
  have hCp : 0 < C + 1 := by linarith
  have hscale : ∀ d ∈ D, (C + 1)⁻¹ • d ∈ K := by
    rintro d ⟨a, ha, b, hb, rfl⟩
    have hnb : -b ∈ -K := by simpa using hb
    obtain ⟨z, hz, hzb⟩ := Set.mem_smul_set.mp (hbal hnb)
    have h := hconv ha hz (inv_nonneg.mpr hCp.le)
      (div_nonneg (by linarith : 0 ≤ C) hCp.le)
      (show (C + 1)⁻¹ + C / (C + 1) = 1 by field_simp; ring)
    convert h using 1
    rw [smul_sub, sub_eq_add_neg, ← smul_neg, ← hzb, smul_smul]
    congr 1
    simp [div_eq_mul_inv, mul_comm]
  let A := (L.toLinearEquiv.trans
    (LinearEquiv.smulOfNeZero ℝ (Space n) 2 (by norm_num))).toContinuousLinearEquiv
  have hA (x : Space n) : A x = (2 : ℝ) • L x := rfl
  refine ⟨A, ?_, ?_⟩
  · intro x hx
    have hn : ‖x‖ ≤ 2 / (C + 1) := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hx
    have hy : ((C + 1) / 2) • x ∈ Metric.closedBall (0 : Space n) 1 := by
      rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
        abs_of_pos (by positivity : 0 < (C + 1) / 2)]
      have := mul_le_mul_of_nonneg_left hn (show 0 ≤ (C + 1) / 2 by positivity)
      have he : (C + 1) / 2 * (2 / (C + 1)) = 1 := by field_simp
      simpa [he] using this
    obtain ⟨d, hd, he⟩ := hLin hy
    refine ⟨(C + 1)⁻¹ • d, hscale d hd, ?_⟩
    rw [hA, map_smul, he, smul_smul, smul_smul]
    have heq : 2 * ((C + 1)⁻¹ * ((C + 1) / 2)) = 1 := by field_simp
    rw [mul_assoc, heq, one_smul]
  · rintro x ⟨y, hy, rfl⟩
    have hyd : y ∈ D := ⟨y, hy, 0, h0, sub_zero _⟩
    have hn : ‖L y‖ ≤ n := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hLout ⟨y, hyd, rfl⟩
    rw [Metric.mem_closedBall, dist_zero_right, hA, norm_smul]
    simp only [Real.norm_eq_abs, abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num)]
    linarith

/- A dimension-only inscribed ball in the standard simplex. This allows
noncentered model fibers to be normalized without importing John's theorem. -/
theorem simplex_ball_coordinates {n : ℕ} (hn : 1 ≤ n) (z : Space n)
    (hz : z ∈ Metric.closedBall (WithLp.toLp 2 (fun _ : Fin n => (1 : ℝ) / (n + 1)))
      (1 / ((n : ℝ) + 1) ^ 2)) :
    (∀ i, 0 ≤ z i) ∧ (∑ i, z i) ≤ 1 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hN : 0 < (n : ℝ) + 1 := by positivity
  have hN2 : 0 < ((n : ℝ) + 1) ^ 2 := by positivity
  have hd : ∀ i, |z i - 1 / ((n : ℝ) + 1)| ≤ 1 / ((n : ℝ) + 1) ^ 2 := by
    intro i
    have h := PiLp.norm_apply_le (p := (2 : ENNReal)) (z - WithLp.toLp 2 (fun _ => (1 : ℝ) / (n + 1))) i
    have hz' : ‖z - WithLp.toLp 2 (fun _ : Fin n => (1 : ℝ) / (n + 1))‖ ≤
        1 / ((n : ℝ) + 1) ^ 2 := by simpa [Metric.mem_closedBall, dist_eq_norm] using hz
    have hi : |z i - 1 / ((n : ℝ) + 1)| ≤
        ‖z - WithLp.toLp 2 (fun _ : Fin n => (1 : ℝ) / (n + 1))‖ := by
      simpa [Real.norm_eq_abs] using h
    exact hi.trans hz'
  have hr : 1 / ((n : ℝ) + 1) ^ 2 ≤ 1 / ((n : ℝ) + 1) := by
    apply (div_le_div_iff₀ hN2 hN).mpr
    nlinarith
  constructor
  · intro i
    have h := (abs_le.mp (hd i)).1
    linarith
  · have hsum : (∑ i, z i) ≤ ∑ _ : Fin n, (1 / ((n : ℝ) + 1) + 1 / ((n : ℝ) + 1) ^ 2) :=
      Finset.sum_le_sum fun i _ => by have h := (abs_le.mp (hd i)).2; linarith
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
    have hbound : (n : ℝ) * (1 / ((n : ℝ) + 1) + 1 / ((n : ℝ) + 1) ^ 2) ≤ 1 := by
      apply (mul_le_mul_iff_left₀ hN2).mp
      field_simp
      nlinarith
    exact hsum.trans hbound

/- A linear normalization of an arbitrary full-dimensional compact convex
body containing the distinguished origin. The dimension-only outer radius
is intentionally not John's sharp radius; it suffices for the compactness
argument and does not alter the source's final centered normalization. -/
theorem noncentered_body_normalization {n : ℕ} (hn : 1 ≤ n)
    {K : Set (Space n)} (hK : IsCompact K) (hconv : Convex ℝ K)
    (hint : (interior K).Nonempty) (h0 : (0 : Space n) ∈ K) :
    ∃ (A : Space n ≃L[ℝ] Space n) (c : Space n),
      Metric.closedBall c 1 ⊆ A '' K ∧
      A '' K ⊆ Metric.closedBall 0 (2 * ((n : ℝ) + 1) ^ 3) ∧
      ‖c‖ ≤ 2 * ((n : ℝ) + 1) ^ 3 := by
  classical
  obtain ⟨a, ha⟩ := hint
  obtain ⟨r, hr, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    (mem_interior_iff_mem_nhds.mp ha)
  let K' : Set (Space n) := (fun x => x - a) '' K
  have hK' : IsCompact K' := hK.image (continuous_id.sub continuous_const)
  have hcv' : Convex ℝ K' := hconv.affine_image (AffineMap.id ℝ (Space n) - AffineMap.const ℝ (Space n) a)
  have h0' : (0 : Space n) ∈ K' := ⟨a, interior_subset ha, sub_self _⟩
  have hb : Metric.closedBall (0 : Space n) r ⊆ K' := by
    intro x hx
    refine ⟨x + a, hball ?_, by abel_nf⟩
    simpa [Metric.mem_closedBall, dist_eq_norm] using hx
  obtain ⟨v, hv, hd, hmax⟩ := exists_max_det_columns hK' hr hb
  obtain ⟨q, hq, hcoord⟩ := maxdet_coordinate_bound v hv hd hmax
  let L := q.symm.toContinuousLinearEquiv
  let N : ℝ := (n : ℝ) + 1
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hN : 0 < N := by dsimp [N]; positivity
  have hsq : Real.sqrt n ≤ (n : ℝ) := by
    have hs := Real.sq_sqrt (show (0 : ℝ) ≤ n by positivity)
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith [Real.sqrt_nonneg (n : ℝ)]
  have hbound : ∀ x ∈ K', ‖L x‖ ≤ (n : ℝ) := fun x hx =>
    (norm_le_sqrt_card_of_coordinate_le _ (hcoord x hx)).trans hsq
  have haBound : ‖L a‖ ≤ (n : ℝ) := by
    have hmem : -a ∈ K' := ⟨0, h0, by simp⟩
    simpa only [map_neg, norm_neg] using hbound (-a) hmem
  let A := (L.toLinearEquiv.trans
    (LinearEquiv.smulOfNeZero ℝ (Space n) (N ^ 2) (pow_ne_zero 2 hN.ne'))).toContinuousLinearEquiv
  have hA (x : Space n) : A x = N ^ 2 • L x := rfl
  let w : Space n := WithLp.toLp 2 (fun _ => 1 / N)
  let c : Space n := A a + N ^ 2 • w
  have hin : Metric.closedBall c 1 ⊆ A '' K := by
    intro z hz
    let b : Space n := (N ^ 2)⁻¹ • (z - c) + w
    have hb : b ∈ Metric.closedBall w (1 / N ^ 2) := by
      rw [Metric.mem_closedBall, dist_eq_norm]
      simp only [b, add_sub_cancel_right, norm_smul, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr (sq_pos_of_pos hN)), one_div]
      have hdist : ‖z - c‖ ≤ 1 := by simpa [Metric.mem_closedBall, dist_eq_norm] using hz
      exact (mul_le_mul_of_nonneg_left hdist (inv_nonneg.mpr (sq_nonneg N))).trans_eq (mul_one _)
    obtain ⟨hbpos, hbsum⟩ := simplex_ball_coordinates hn b hb
    have hqb : q b ∈ K' := by
      rw [hq]
      exact convex_sum_mem_le_one hcv' h0' b v hbpos hbsum hv
    obtain ⟨x, hx, hxb⟩ := hqb
    refine ⟨x, hx, ?_⟩
    have hLb : L x = b + L a := by
      have he := congrArg L hxb
      change L (x - a) = q.symm (q b) at he
      rw [map_sub, q.symm_apply_apply] at he
      exact eq_add_of_sub_eq he
    rw [hA, hLb, smul_add, show b = (N ^ 2)⁻¹ • (z - c) + w from rfl,
      smul_add, smul_smul, mul_inv_cancel₀ (pow_ne_zero 2 hN.ne'), one_smul]
    dsimp [c]
    rw [hA]
    abel
  have hout : A '' K ⊆ Metric.closedBall 0 (2 * ((n : ℝ) + 1) ^ 3) := by
    rintro z ⟨x, hx, rfl⟩
    have hxB := hbound (x - a) ⟨x, hx, rfl⟩
    have hLx : ‖L x‖ ≤ 2 * (n : ℝ) := by
      have he : L x = L (x - a) + L a := by rw [map_sub]; abel
      rw [he]
      exact (norm_add_le _ _).trans (by linarith)
    rw [Metric.mem_closedBall, dist_zero_right, hA, norm_smul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg N)]
    have he := mul_le_mul_of_nonneg_left hLx (sq_nonneg N)
    dsimp [N] at he ⊢
    nlinarith [sq_nonneg ((n : ℝ) + 1)]
  exact ⟨A, c, hin, hout, by
    simpa [Metric.mem_closedBall, dist_zero_right] using hout (hin (Metric.mem_closedBall_self (by norm_num)))⟩

/- The same intermediate normalization with the zero-dimensional convention
made explicit. Its radii are only used in compactness arguments. -/
theorem noncentered_body_normalization_all {n : ℕ}
    {K : Set (Space n)} (hK : IsCompact K) (hconv : Convex ℝ K)
    (hint : (interior K).Nonempty) (h0 : (0 : Space n) ∈ K) :
    ∃ (A : Space n ≃L[ℝ] Space n) (c : Space n),
      Metric.closedBall c 1 ⊆ A '' K ∧
      A '' K ⊆ Metric.closedBall 0 (2 * ((n : ℝ) + 1) ^ 3) ∧
      ‖c‖ ≤ 2 * ((n : ℝ) + 1) ^ 3 := by
  by_cases hn : 1 ≤ n
  · exact noncentered_body_normalization hn hK hconv hint h0
  · have hn0 : n = 0 := by omega
    subst n
    refine ⟨ContinuousLinearEquiv.refl ℝ _, 0, ?_, ?_, by norm_num⟩
    · intro x hx
      have he : x = 0 := Subsingleton.elim _ _
      subst x
      exact ⟨0, h0, rfl⟩
    · intro x hx
      have he : x = 0 := Subsingleton.elim _ _
      simp [he]

end AffineBernstein

end

end OAI
