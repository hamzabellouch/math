import Mathlib

namespace OAI

noncomputable section
open scoped ContDiff ENNReal Pointwise Classical

namespace PackingSufficiencySupport

abbrev Ambient (n : ℕ) := Fin n → ℂ

def capacity {n : ℕ} (z : Ambient n) : ℝ :=
  Real.pi * ∑ j, Complex.normSq (z j)

def closedBall (n : ℕ) (R : ℝ) : Set (Ambient n) :=
  {z | capacity z ≤ R}

def openBall (n : ℕ) (R : ℝ) : Set (Ambient n) :=
  {z | capacity z < R}

def standardForm {n : ℕ} (v w : Ambient n) : ℝ :=
  ∑ j, ((v j).re * (w j).im - (v j).im * (w j).re)

def IsBallEmbedding {n : ℕ} (r : ℝ) (f : Ambient n → Ambient n) : Prop :=
  ∃ U : Set (Ambient n), IsOpen U ∧ closedBall n r ⊆ U ∧
    ContDiffOn ℝ ∞ f U ∧
    Topology.IsEmbedding (fun x : U => f x) ∧
    ∀ x ∈ U, ∀ v w : Ambient n,
      standardForm (fderiv ℝ f x v) (fderiv ℝ f x w) = standardForm v w

def HasPacking (n k : ℕ) (R : ℝ) (r : Fin k → ℝ) : Prop :=
  ∃ f : Fin k → Ambient n → Ambient n,
    (∀ i, IsBallEmbedding (r i) (f i)) ∧
    (∀ i, f i '' closedBall n (r i) ⊆ openBall n R) ∧
    (∀ i j, i ≠ j → Disjoint (f i '' closedBall n (r i))
      (f j '' closedBall n (r j)))

theorem isBallEmbedding_id (n : ℕ) (r : ℝ) :
    IsBallEmbedding r (id : Ambient n → Ambient n) := by
  refine ⟨Set.univ, isOpen_univ, Set.subset_univ _, contDiff_id.contDiffOn, ?_, ?_⟩
  · simpa only [id_eq] using (Topology.IsEmbedding.subtypeVal (p := fun x : Ambient n => x ∈ (Set.univ : Set (Ambient n))))
  · intro x _ v w
    simp

def realCoordinates (n : ℕ) : Ambient n ≃ₗ[ℝ] ((Fin n ⊕ Fin n) → ℝ) where
  toFun z := Sum.elim (fun j => (z j).re) (fun j => (z j).im)
  invFun v := fun j => ⟨v (Sum.inl j), v (Sum.inr j)⟩
  left_inv z := by rfl
  right_inv v := by funext i; cases i <;> rfl
  map_add' z w := by funext i; cases i <;> rfl
  map_smul' r z := by funext i; cases i <;> simp

def realBasis (n : ℕ) : Module.Basis (Fin n ⊕ Fin n) ℝ (Ambient n) :=
  Module.Basis.ofEquivFun (realCoordinates n)

@[simp]
theorem realBasis_repr {n : ℕ} (v : Ambient n) (i : Fin n ⊕ Fin n) :
    (realBasis n).repr v i = realCoordinates n v i := by
  exact Module.Basis.ofEquivFun_repr_apply _ _ _

theorem matrix_J_pairing {n : ℕ} (A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ)
    (i j : Fin n ⊕ Fin n) :
    (A.transpose * Matrix.J (Fin n) ℝ * A) i j =
      ∑ k, (A (Sum.inr k) i * A (Sum.inl k) j -
        A (Sum.inl k) i * A (Sum.inr k) j) := by
  simp [Matrix.mul_apply, Matrix.J, Fintype.sum_sum_type, Matrix.fromBlocks,
    Matrix.one_apply, Finset.sum_add_distrib, sub_eq_add_neg]

theorem det_eq_one_of_preserves_standardForm {n : ℕ}
    (L : Ambient n →ₗ[ℝ] Ambient n)
    (hL : ∀ v w, standardForm (L v) (L w) = standardForm v w) :
    LinearMap.det L = 1 := by
  let b := realBasis n
  let M := LinearMap.toMatrix b b L
  have pair (T : Ambient n →ₗ[ℝ] Ambient n) (i j : Fin n ⊕ Fin n) :
      ((LinearMap.toMatrix b b T).transpose * Matrix.J (Fin n) ℝ *
        LinearMap.toMatrix b b T) i j = - standardForm (T (b i)) (T (b j)) := by
    rw [matrix_J_pairing]
    simp only [LinearMap.toMatrix_apply, b, realBasis_repr]
    change (∑ k, ((T (realBasis n i) k).im * (T (realBasis n j) k).re -
      (T (realBasis n i) k).re * (T (realBasis n j) k).im)) =
      -(∑ k, ((T (realBasis n i) k).re * (T (realBasis n j) k).im -
        (T (realBasis n i) k).im * (T (realBasis n j) k).re))
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hM : M ∈ Matrix.symplecticGroup (Fin n) ℝ := by
    apply SymplecticGroup.mem_iff'.mpr
    ext i j
    change (M.transpose * Matrix.J (Fin n) ℝ * M) i j = _
    rw [show (M.transpose * Matrix.J (Fin n) ℝ * M) i j =
      -standardForm (L (b i)) (L (b j)) from pair L i j, hL]
    simpa using (pair LinearMap.id i j).symm
  rw [← LinearMap.det_toMatrix b L]
  exact SymplecticGroup.det_eq_one hM

@[fun_prop]
theorem continuous_capacity (n : ℕ) : Continuous (capacity : Ambient n → ℝ) := by
  unfold capacity
  fun_prop

theorem closedBall_isClosed (n : ℕ) (R : ℝ) : IsClosed (closedBall n R) :=
  isClosed_le (continuous_capacity n) continuous_const

theorem openBall_isOpen (n : ℕ) (R : ℝ) : IsOpen (openBall n R) :=
  isOpen_lt (continuous_capacity n) continuous_const

theorem closedBall_isCompact (n : ℕ) (R : ℝ) : IsCompact (closedBall n R) := by
  apply (isCompact_closedBall (0 : Ambient n) (max R 0 + 1)).of_isClosed_subset
    (closedBall_isClosed n R)
  intro z hz
  rw [Metric.mem_closedBall, dist_zero_right]
  apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ max R 0 + 1)).mpr
  intro j
  have hj : Complex.normSq (z j) ≤ ∑ k, Complex.normSq (z k) :=
    Finset.single_le_sum (fun k _ => Complex.normSq_nonneg (z k)) (Finset.mem_univ j)
  have hj' := mul_le_mul_of_nonneg_left hj Real.pi_pos.le
  have hq : 0 ≤ Complex.normSq (z j) := Complex.normSq_nonneg (z j)
  have hs : (∑ k, Complex.normSq (z k)) * Real.pi ≤ R := by
    simpa [closedBall, capacity, mul_comm] using hz
  have hb : Complex.normSq (z j) ≤ max R 0 := by
    nlinarith [Real.pi_gt_three, le_max_left R 0]
  rw [Complex.normSq_eq_norm_sq] at hb
  have hm := le_max_right R 0
  nlinarith [sq_nonneg (‖z j‖ - 1)]

open MeasureTheory

theorem IsBallEmbedding.volume_image {n : ℕ} {r : ℝ}
    {f : Ambient n → Ambient n} (hf : IsBallEmbedding r f) :
    volume (f '' closedBall n r) = volume (closedBall n r) := by
  rcases hf with ⟨U, hU, hsub, hsmooth, hembed, hform⟩
  have hdiff : ∀ x ∈ closedBall n r,
      HasFDerivWithinAt f (fderiv ℝ f x) (closedBall n r) x := by
    intro x hx
    exact ((hsmooth.differentiableOn (by simp)).differentiableAt
      (hU.mem_nhds (hsub hx))).hasFDerivAt.hasFDerivWithinAt
  have hinj : Set.InjOn f (closedBall n r) := by
    intro x hx y hy hxy
    exact congrArg Subtype.val (hembed.injective
      (show f (⟨x, hsub hx⟩ : U) = f (⟨y, hsub hy⟩ : U) from hxy))
  have hs := (closedBall_isClosed n r).measurableSet
  calc
    volume (f '' closedBall n r) = ∫⁻ x in closedBall n r,
        ENNReal.ofReal |(fderiv ℝ f x).det| :=
      (lintegral_abs_det_fderiv_eq_addHaar_image volume hs hdiff hinj).symm
    _ = ∫⁻ _ in closedBall n r, (1 : ℝ≥0∞) := by
      apply setLIntegral_congr_fun hs
      intro x hx
      have hd := det_eq_one_of_preserves_standardForm (fderiv ℝ f x).toLinearMap
        (hform x (hsub hx))
      simp [show (fderiv ℝ f x).det = 1 from hd]
    _ = volume (closedBall n r) := by simp

@[simp]
theorem capacity_zero (n : ℕ) : capacity (0 : Ambient n) = 0 := by
  simp [capacity]

theorem capacity_smul {n : ℕ} (t : ℝ) (z : Ambient n) :
    capacity (t • z) = t ^ 2 * capacity z := by
  simp only [capacity, Pi.smul_apply, Complex.normSq_eq_norm_sq, norm_smul,
    Real.norm_eq_abs, mul_pow, sq_abs, ← Finset.mul_sum]
  ring

theorem closedBall_eq_smul {n : ℕ} {r : ℝ} (hr : 0 < r) :
    closedBall n r = Real.sqrt r • closedBall n 1 := by
  ext z
  constructor
  · intro hz
    refine ⟨(Real.sqrt r)⁻¹ • z, ?_, ?_⟩
    · change capacity ((Real.sqrt r)⁻¹ • z) ≤ 1
      rw [capacity_smul, inv_pow, Real.sq_sqrt hr.le, ← div_eq_inv_mul,
        div_le_iff₀ hr]
      simpa [closedBall] using hz
    · simp [smul_smul, ne_of_gt (Real.sqrt_pos.mpr hr)]
  · rintro ⟨w, hw, rfl⟩
    change capacity (Real.sqrt r • w) ≤ r
    rw [capacity_smul, Real.sq_sqrt hr.le]
    simpa using mul_le_mul_of_nonneg_left hw hr.le

theorem volume_closedBall {n : ℕ} {r : ℝ} (hr : 0 < r) :
    volume (closedBall n r) = ENNReal.ofReal (r ^ n) * volume (closedBall n 1) := by
  rw [closedBall_eq_smul hr, Measure.addHaar_smul]
  have hd : Module.finrank ℝ (Ambient n) = 2 * n := by
    simp [Ambient, Module.finrank_pi_fintype, Complex.finrank_real_complex, mul_comm]
  rw [hd, pow_mul, Real.sq_sqrt hr.le, abs_of_pos (pow_pos hr n)]

theorem capacity_nonneg {n : ℕ} (z : Ambient n) : 0 ≤ capacity z :=
  mul_nonneg Real.pi_pos.le (Finset.sum_nonneg fun j _ => Complex.normSq_nonneg (z j))

theorem unitBall_volume_pos (n : ℕ) : 0 < volume (closedBall n 1) := by
  have hp : 0 < volume (openBall n 1) :=
    (openBall_isOpen n 1).measure_pos volume ⟨0, by simp [openBall]⟩
  exact hp.trans_le (measure_mono (fun _ hx => (show capacity _ < 1 from hx).le))

theorem unitBall_volume_ne_top (n : ℕ) : volume (closedBall n 1) ≠ ⊤ :=
  (closedBall_isCompact n 1).measure_lt_top.ne

theorem IsBallEmbedding.closedBall_continuousOn {n : ℕ} {r : ℝ}
    {f : Ambient n → Ambient n} (hf : IsBallEmbedding r f) :
    ContinuousOn f (closedBall n r) := by
  rcases hf with ⟨U, _, hsub, hsmooth, _, _⟩
  exact hsmooth.continuousOn.mono hsub

theorem IsBallEmbedding.isCompact_image {n : ℕ} {r : ℝ}
    {f : Ambient n → Ambient n} (hf : IsBallEmbedding r f) :
    IsCompact (f '' closedBall n r) :=
  (closedBall_isCompact n r).image_of_continuousOn hf.closedBall_continuousOn

theorem HasPacking.exists_smaller_target {n k : ℕ} {R : ℝ} {r : Fin k → ℝ}
    (hR : 0 < R) (hp : HasPacking n k R r) :
    ∃ σ, 0 < σ ∧ σ < R ∧ HasPacking n k σ r := by
  rcases hp with ⟨f, hf, htarget, hdisj⟩
  let S : Set (Ambient n) := ⋃ i, f i '' closedBall n (r i)
  have hc : IsCompact (insert 0 S) :=
    (isCompact_iUnion (fun i => (hf i).isCompact_image)).insert 0
  obtain ⟨z, hz, hmax⟩ := hc.exists_isMaxOn (Set.insert_nonempty 0 S)
    (continuous_capacity n).continuousOn
  have hS : insert (0 : Ambient n) S ⊆ openBall n R := by
    intro y hy
    rcases hy with rfl | hy
    · simpa [openBall] using hR
    · rcases Set.mem_iUnion.mp hy with ⟨i, hi⟩
      exact htarget i hi
  have hzR : capacity z < R := hS hz
  refine ⟨(capacity z + R) / 2, ?_, ?_, f, hf, ?_, hdisj⟩
  · linarith [capacity_nonneg z]
  · linarith
  · intro i y hy
    have hm : capacity y ≤ capacity z := hmax (Set.mem_insert_of_mem 0
      (Set.mem_iUnion.mpr ⟨i, hy⟩))
    change capacity y < (capacity z + R) / 2
    linarith

theorem HasPacking.volume_le {n k : ℕ} {R : ℝ} {r : Fin k → ℝ}
    (hR : 0 < R) (hr : ∀ i, 0 < r i) (hp : HasPacking n k R r) :
    ∑ i, (r i) ^ n ≤ R ^ n := by
  rcases hp with ⟨f, hf, htarget, hdisj⟩
  have hm : volume (⋃ i, f i '' closedBall n (r i)) ≤ volume (closedBall n R) := by
    apply measure_mono
    intro z hz
    rcases Set.mem_iUnion.mp hz with ⟨i, hi⟩
    exact (show capacity z < R from htarget i hi).le
  rw [measure_iUnion hdisj (fun i => (hf i).isCompact_image.measurableSet),
    tsum_fintype] at hm
  simp_rw [(hf _).volume_image, volume_closedBall (hr _)] at hm
  rw [volume_closedBall hR, ← Finset.sum_mul] at hm
  have he := (ENNReal.mul_le_mul_iff_left (unitBall_volume_pos n).ne'
    (unitBall_volume_ne_top n)).mp hm
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => pow_nonneg (hr i).le n)] at he
  exact (ENNReal.ofReal_le_ofReal_iff (pow_nonneg hR.le n)).mp he

theorem HasPacking.volume_lt {n k : ℕ} {R : ℝ} {r : Fin k → ℝ}
    (hn : 0 < n) (hR : 0 < R) (hr : ∀ i, 0 < r i)
    (hp : HasPacking n k R r) : ∑ i, (r i) ^ n < R ^ n := by
  obtain ⟨σ, hσ, hσR, hpσ⟩ := hp.exists_smaller_target hR
  exact (hpσ.volume_le hσ hr).trans_lt (pow_lt_pow_left₀ hσR hσ.le hn.ne')

def dilation (n : ℕ) (t : ℝ) (ht : t ≠ 0) : Ambient n ≃L[ℝ] Ambient n :=
  (LinearEquiv.smulOfNeZero ℝ (Ambient n) t ht).toContinuousLinearEquiv

@[simp] theorem dilation_apply (n : ℕ) (t : ℝ) (ht : t ≠ 0) (z : Ambient n) :
    dilation n t ht z = t • z := rfl

@[simp] theorem dilation_symm_apply (n : ℕ) (t : ℝ) (ht : t ≠ 0) (z : Ambient n) :
    (dilation n t ht).symm z = t⁻¹ • z := rfl

theorem IsBallEmbedding.dilate {n : ℕ} {r t : ℝ} {f : Ambient n → Ambient n}
    (hf : IsBallEmbedding r f) (ht : t ≠ 0) :
    IsBallEmbedding (t ^ 2 * r) (fun z => t • f (t⁻¹ • z)) := by
  let e := dilation n t ht
  rcases hf with ⟨U, hU, hsub, hsmooth, hembed, hform⟩
  have hmaps : Set.MapsTo e.symm (e '' U) U := by
    rintro _ ⟨x, hx, rfl⟩
    simpa using hx
  refine ⟨e '' U, e.isOpenMap _ hU, ?_, ?_, ?_, ?_⟩
  · intro z hz
    refine ⟨e.symm z, hsub ?_, e.apply_symm_apply z⟩
    change capacity (t⁻¹ • z) ≤ r
    rw [capacity_smul, inv_pow, ← div_eq_inv_mul, div_le_iff₀ (sq_pos_of_ne_zero ht)]
    simpa [closedBall, mul_comm] using hz
  · exact (hsmooth.comp e.symm.contDiff.contDiffOn hmaps).const_smul t
  · exact e.toHomeomorph.isEmbedding.comp (hembed.comp (e.toHomeomorph.image U).symm.isEmbedding)
  · intro z hz v w
    have hd := ((hsmooth.differentiableOn (by simp)).differentiableAt
      (hU.mem_nhds (hmaps hz))).hasFDerivAt
    have hchain := (e.hasFDerivAt.comp z (hd.comp z e.symm.hasFDerivAt))
    have heq : e.toContinuousLinearMap.comp
        ((fderiv ℝ f (e.symm z)).comp e.symm.toContinuousLinearMap) =
        fderiv ℝ f (e.symm z) := by
      apply ContinuousLinearMap.ext
      intro a
      change t • (fderiv ℝ f (e.symm z) (t⁻¹ • a)) = _
      rw [map_smul, smul_smul, mul_inv_cancel₀ ht, one_smul]
    rw [heq] at hchain
    have hdg : fderiv ℝ (fun z => t • f (t⁻¹ • z)) z = fderiv ℝ f (e.symm z) :=
      hchain.fderiv
    rw [hdg]
    exact hform _ (hmaps hz) v w

theorem HasPacking.dilate {n k : ℕ} {R t : ℝ} {r : Fin k → ℝ}
    (hp : HasPacking n k R r) (ht : t ≠ 0) :
    HasPacking n k (t ^ 2 * R) (fun i => t ^ 2 * r i) := by
  rcases hp with ⟨f, hf, htarget, hdisj⟩
  have hsource {a : ℝ} {z : Ambient n} (hz : z ∈ closedBall n (t ^ 2 * a)) :
      t⁻¹ • z ∈ closedBall n a := by
    change capacity (t⁻¹ • z) ≤ a
    rw [capacity_smul, inv_pow, ← div_eq_inv_mul, div_le_iff₀ (sq_pos_of_ne_zero ht)]
    simpa [closedBall, mul_comm] using hz
  refine ⟨fun i z => t • f i (t⁻¹ • z), fun i => (hf i).dilate ht, ?_, ?_⟩
  · intro i z hz
    rcases hz with ⟨x, hx, rfl⟩
    change capacity (t • f i (t⁻¹ • x)) < t ^ 2 * R
    rw [capacity_smul]
    exact mul_lt_mul_of_pos_left (htarget i ⟨_, hsource hx, rfl⟩) (sq_pos_of_ne_zero ht)
  · intro i j hij
    apply Set.disjoint_left.mpr
    rintro z ⟨x, hx, rfl⟩ ⟨y, hy, heq⟩
    have heq' : f j (t⁻¹ • y) = f i (t⁻¹ • x) := by
      have := congrArg (fun z : Ambient n => t⁻¹ • z) heq
      simpa [smul_smul, ht] using this
    exact Set.disjoint_left.mp (hdisj i j hij)
      ⟨_, hsource hx, rfl⟩ ⟨_, hsource hy, heq'⟩

theorem hasPacking_normalize {n k : ℕ} {R : ℝ} {r : Fin k → ℝ} (hR : 0 < R) :
    HasPacking n k R r ↔ HasPacking n k 1 (fun i => r i / R) := by
  constructor
  · intro hp
    have ht : Real.sqrt R⁻¹ ≠ 0 := (Real.sqrt_pos.mpr (inv_pos.mpr hR)).ne'
    have h := hp.dilate ht
    simpa only [Real.sq_sqrt (inv_nonneg.mpr hR.le), inv_mul_cancel₀ hR.ne',
      div_eq_inv_mul] using h
  · intro hp
    have ht : Real.sqrt R ≠ 0 := (Real.sqrt_pos.mpr hR).ne'
    have h := hp.dilate ht
    simpa only [Real.sq_sqrt hR.le, mul_one, mul_div_cancel₀ _ hR.ne'] using h

theorem IsBallEmbedding.mono {n : ℕ} {r s : ℝ} {f : Ambient n → Ambient n}
    (hf : IsBallEmbedding r f) (hs : s ≤ r) : IsBallEmbedding s f := by
  rcases hf with ⟨U, hU, hsub, hsmooth, hembed, hform⟩
  exact ⟨U, hU, fun _ hx => hsub (le_trans hx hs), hsmooth, hembed, hform⟩

theorem HasPacking.mono {n k : ℕ} {R S : ℝ} {r s : Fin k → ℝ}
    (hp : HasPacking n k R r) (hR : R ≤ S) (hr : ∀ i, s i ≤ r i) :
    HasPacking n k S s := by
  rcases hp with ⟨f, hf, htarget, hdisj⟩
  have hsub (i) : closedBall n (s i) ⊆ closedBall n (r i) := fun _ hx => le_trans hx (hr i)
  refine ⟨f, fun i => (hf i).mono (hr i), ?_, ?_⟩
  · intro i z hz
    exact lt_of_lt_of_le (htarget i (Set.image_mono (hsub i) hz)) hR
  · intro i j hij
    exact (hdisj i j hij).mono (Set.image_mono (hsub i)) (Set.image_mono (hsub j))

theorem exists_larger_closedBall_subset {n : ℕ} {r : ℝ} {U : Set (Ambient n)}
    (hU : IsOpen U) (hsub : closedBall n r ⊆ U) :
    ∃ s, r < s ∧ closedBall n s ⊆ U := by
  let S := closedBall n (r + 1) ∩ Uᶜ
  have hc : IsCompact S := (closedBall_isCompact n (r + 1)).inter_right hU.isClosed_compl
  by_cases hne : S.Nonempty
  · obtain ⟨z, hz, hmin⟩ := hc.exists_isMinOn hne (continuous_capacity n).continuousOn
    have hzcap : r < capacity z := by
      by_contra h
      exact hz.2 (hsub (le_of_not_gt h))
    obtain ⟨s, hrs, hsm⟩ := exists_between (lt_min (by linarith : r < r + 1) hzcap)
    refine ⟨s, hrs, ?_⟩
    intro x hx
    by_contra hxU
    have hxS : x ∈ S := ⟨le_trans hx (min_le_left _ _ |>.trans' hsm.le), hxU⟩
    have := hmin hxS
    have hs : s < capacity z := hsm.trans_le (min_le_right _ _)
    exact (not_le_of_gt hs) (le_trans this hx)
  · refine ⟨r + 1, by linarith, ?_⟩
    intro x hx
    by_contra hxU
    exact hne ⟨x, hx, hxU⟩

theorem HasPacking.exists_larger_sources {n k : ℕ} {R : ℝ} {r : Fin k → ℝ}
    (hp : HasPacking n k R r) :
    ∃ s : Fin k → ℝ, (∀ i, r i < s i) ∧ HasPacking n k R s := by
  classical
  rcases hp with ⟨f, hf, htarget, hdisj⟩
  have hdf : Pairwise (fun i j => Disjoint
      (nhdsSet (f i '' closedBall n (r i))) (nhdsSet (f j '' closedBall n (r j)))) := by
    intro i j hij
    exact disjoint_nhdsSet_nhdsSet (hf i).isCompact_image.isClosed
      (hf j).isCompact_image.isClosed (hdisj i j hij)
  obtain ⟨O, hO, hOd⟩ := hdf.exists_mem_filter_basis_of_disjoint
    (fun i => hasBasis_nhdsSet (f i '' closedBall n (r i)))
  choose U hU hsub hsmooth hembed hform using hf
  let W (i : Fin k) := U i ∩ f i ⁻¹' (O i ∩ openBall n R)
  have hW (i : Fin k) : IsOpen (W i) :=
    (hsmooth i).continuousOn.isOpen_inter_preimage (hU i)
      ((hO i).1.inter (openBall_isOpen n R))
  have hWsub (i : Fin k) : closedBall n (r i) ⊆ W i := by
    intro z hz
    exact ⟨hsub i hz, (hO i).2 ⟨z, hz, rfl⟩, htarget i ⟨z, hz, rfl⟩⟩
  choose s hs hssub using fun i => exists_larger_closedBall_subset (hW i) (hWsub i)
  refine ⟨s, hs, f, ?_, ?_, ?_⟩
  · intro i
    exact ⟨U i, hU i, fun _ hx => (hssub i hx).1, hsmooth i, hembed i, hform i⟩
  · intro i z hz
    rcases hz with ⟨x, hx, rfl⟩
    exact (hssub i hx).2.2
  · intro i j hij
    apply (hOd hij).mono
    · rintro z ⟨x, hx, rfl⟩
      exact (hssub i hx).2.1
    · rintro z ⟨x, hx, rfl⟩
      exact (hssub j hx).2.1

theorem hasPacking_one_iff {n : ℕ} {R r : ℝ} (hn : 0 < n)
    (hR : 0 < R) (hr : 0 < r) :
    HasPacking n 1 R (fun _ => r) ↔ r < R := by
  constructor
  · intro hp
    have h := hp.volume_lt hn hR (fun _ => hr)
    simp only [Fin.sum_univ_one] at h
    exact lt_of_pow_lt_pow_left₀ n hR.le h
  · intro h
    refine ⟨fun _ => id, fun _ => isBallEmbedding_id n r, ?_, ?_⟩
    · intro i z hz
      rcases hz with ⟨x, hx, rfl⟩
      exact lt_of_le_of_lt hx h
    · intro i j hij
      exact False.elim (hij (Subsingleton.elim i j))

namespace Comparison

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def convexFunctionSet (S : Set E) (hS : Convex ℝ S) : Set C(S, ℝ) :=
  {f | ∀ (x y : S) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1),
    f ⟨a • (x : E) + b • (y : E), hS x.property y.property ha hb hab⟩ ≤
      a * f x + b * f y}

abbrev ConvexMaps (S : Set E) (hS : Convex ℝ S) := ↥(convexFunctionSet S hS)

theorem isClosed_convexFunctionSet (S : Set E) (hS : Convex ℝ S) :
    IsClosed (convexFunctionSet S hS) := by
  unfold convexFunctionSet
  simp only [Set.ofPred_forall]
  repeat' apply isClosed_iInter; intro
  exact isClosed_le (ContinuousMap.evalCLM ℝ _).continuous
    (((ContinuousMap.evalCLM ℝ _).continuous.const_mul _).add
      ((ContinuousMap.evalCLM ℝ _).continuous.const_mul _))

instance convexMaps_nonempty (S : Set E) (hS : Convex ℝ S) : Nonempty (ConvexMaps S hS) :=
  ⟨⟨0, by simp [convexFunctionSet]⟩⟩

instance convexMaps_completeSpace (S : Set E) (hS : Convex ℝ S) [CompactSpace S] :
    CompleteSpace (ConvexMaps S hS) :=
  (isClosed_convexFunctionSet S hS).isComplete.completeSpace_coe

def affineStep {S : Set E} {hS : Convex ℝ S} (lam : ℝ) (hlam : 0 ≤ lam)
    (Q F : ConvexMaps S hS) : ConvexMaps S hS :=
  ⟨lam • (F : C(S, ℝ)) + (Q : C(S, ℝ)), by
    intro x y a b ha hb hab
    have hF := mul_le_mul_of_nonneg_left (F.property x y a b ha hb hab) hlam
    have hQ := Q.property x y a b ha hb hab
    change lam * F.val _ + Q.val _ ≤ a * (lam * F.val x + Q.val x) +
      b * (lam * F.val y + Q.val y)
    nlinarith⟩

theorem exists_convex_fixedPoint {S : Set E} {hS : Convex ℝ S} [CompactSpace S]
    (Q : ConvexMaps S hS) (R : ConvexMaps S hS → ConvexMaps S hS)
    (hR : ∀ F G, dist (R F) (R G) ≤ dist F G)
    {lam : ℝ} (hlam : 0 ≤ lam) (hlam1 : lam < 1) :
    ∃ K : ConvexMaps S hS, R (affineStep lam hlam Q K) = K := by
  let T : ConvexMaps S hS → ConvexMaps S hS := fun F => R (affineStep lam hlam Q F)
  have hT : ContractingWith ⟨lam, hlam⟩ T := by
    refine ⟨hlam1, LipschitzWith.of_dist_le_mul ?_⟩
    intro F G
    apply (hR _ _).trans
    change dist (lam • (F : C(S, ℝ)) + (Q : C(S, ℝ)))
      (lam • (G : C(S, ℝ)) + (Q : C(S, ℝ))) ≤ lam * dist (F : C(S, ℝ)) (G : C(S, ℝ))
    rw [dist_add_right]
    simpa [Real.norm_eq_abs, abs_of_nonneg hlam] using dist_smul_le lam F.val G.val
  exact ⟨hT.fixedPoint T, hT.fixedPoint_isFixedPt⟩

theorem fixedPoint_negative_maximum {S : Set E} {hS : Convex ℝ S} [CompactSpace S]
    (h0 : (0 : E) ∈ S) (Q K : ConvexMaps S hS)
    (R : ConvexMaps S hS → ConvexMaps S hS) (μ : C(S, ℝ) →ₗ[ℝ] ℝ)
    (hμlower : ∀ (F : C(S, ℝ)) (c : ℝ), (∀ x, c ≤ F x) → c ≤ μ F)
    (hRmean : ∀ F, μ (R F).val = μ F.val)
    (hRmin : ∀ F x, (R F).val ⟨0, h0⟩ ≤ (R F).val x)
    (hRbound : ∀ F (c : ℝ), (∀ x, F.val x ≤ c) → ∀ x, (R F).val x ≤ c)
    {lam τ m d c MQ : ℝ} (hlam : 0 < lam) (hlam1 : lam < 1)
    (hτ : 0 < τ) (hτ1 : τ < 1) (hdc : d < c)
    (hμQ : μ Q.val = -m) (hQbound : ∀ x, Q.val x ≤ MQ)
    (houter : ∀ x : S, (x : E) ∉ τ • S → Q.val x ≤ -c)
    (hgap : (1 - lam) * (d + MQ) < lam * (1 - τ) * (m - d))
    (hfix : R (affineStep lam hlam.le Q K) = K) :
    ∀ x, K.val x < -d / (1 - lam) := by
  let : Nonempty S := ⟨⟨0, h0⟩⟩
  have hden : 0 < 1 - lam := sub_pos.mpr hlam1
  have hmean : μ K.val = -m / (1 - lam) := by
    have heq := congrArg (fun F : ConvexMaps S hS => μ F.val) hfix
    rw [hRmean] at heq
    change μ (lam • K.val + Q.val) = μ K.val at heq
    rw [map_add, map_smul, hμQ] at heq
    apply (eq_div_iff hden.ne').mpr
    change lam * μ K.val + -m = μ K.val at heq
    nlinarith
  have hzero : K.val ⟨0, h0⟩ ≤ μ K.val := by
    apply hμlower
    intro x
    rw [← hfix]
    exact hRmin _ x
  obtain ⟨z, _, hz⟩ := isCompact_univ.exists_isMaxOn
    (Set.univ_nonempty : (Set.univ : Set S).Nonempty) K.val.continuous.continuousOn
  have hmax (x : S) : K.val x ≤ K.val z := hz (Set.mem_univ x)
  have hmaxlt : K.val z < -d / (1 - lam) := by
    by_contra hh
    have hM : -d / (1 - lam) ≤ K.val z := le_of_not_gt hh
    have hlamM : lam * K.val z ≤ K.val z + d := by
      have := (div_le_iff₀ hden).mp hM
      nlinarith
    have hgap' : d + MQ < lam * ((1 - τ) * (m - d) / (1 - lam)) := by
      rw [← mul_div_assoc, lt_div_iff₀ hden]
      nlinarith [hgap]
    have hall (x : S) : (affineStep lam hlam.le Q K).val x < K.val z := by
      change lam * K.val x + Q.val x < K.val z
      by_cases hx : (x : E) ∈ τ • S
      · rcases hx with ⟨v, hv, hvx⟩
        have hcv : K.val x ≤ (1 - τ) * K.val ⟨0, h0⟩ + τ * K.val ⟨v, hv⟩ := by
          simpa [hvx] using K.property ⟨0, h0⟩ ⟨v, hv⟩ (1 - τ) τ
            (sub_nonneg.mpr hτ1.le) hτ.le (by ring)
        have hinner : K.val x ≤ K.val z - (1 - τ) * (m - d) / (1 - lam) := by
          calc
            K.val x ≤ (1 - τ) * (-m / (1 - lam)) + τ * K.val z :=
              hcv.trans (add_le_add
                (mul_le_mul_of_nonneg_left (hzero.trans_eq hmean) (sub_nonneg.mpr hτ1.le))
                (mul_le_mul_of_nonneg_left (hmax _) hτ.le))
            _ = K.val z - (1 - τ) * (K.val z + m / (1 - lam)) := by ring
            _ ≤ K.val z - (1 - τ) * ((m - d) / (1 - lam)) := by
              have hm : (m - d) / (1 - lam) ≤ K.val z + m / (1 - lam) := by
                rw [sub_div]
                have hM' := hM
                rw [neg_div] at hM'
                linarith
              exact sub_le_sub_left
                (mul_le_mul_of_nonneg_left hm (sub_nonneg.mpr hτ1.le)) _
            _ = _ := by ring
        have hxmul := mul_le_mul_of_nonneg_left hinner hlam.le
        have hqx := hQbound x
        nlinarith
      · have hxmul := mul_le_mul_of_nonneg_left (hmax x) hlam.le
        have hqx := houter x hx
        linarith
    obtain ⟨w, _, hw⟩ := isCompact_univ.exists_isMaxOn
      (Set.univ_nonempty : (Set.univ : Set S).Nonempty)
      (affineStep lam hlam.le Q K).val.continuous.continuousOn
    have hr := hRbound (affineStep lam hlam.le Q K)
      ((affineStep lam hlam.le Q K).val w) (fun x => hw (Set.mem_univ x)) z
    rw [hfix] at hr
    exact (not_lt_of_ge hr) (hall w)
  exact fun x => (hmax x).trans_lt hmaxlt

end Comparison
end PackingSufficiencySupport
end

end OAI
