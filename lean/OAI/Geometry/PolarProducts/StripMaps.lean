import OAI.Geometry.PolarProducts.LensBounds

namespace OAI

universe u55 u56 u57 u58 u59 u60

section LowerBoundInline
open Set Filter Function
open scoped Topology ContDiff NNReal
open Set Filter Metric
open scoped Topology ContDiff
open Set Filter Function MeasureTheory Metric
open scoped Topology ContDiff NNReal
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff NNReal
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped ContDiff Topology
open Set MeasureTheory
open scoped ContDiff Interval Topology
open Set
open scoped Topology ContDiff
open Set
open Set MeasureTheory
open scoped ContDiff Interval Topology
open Set Filter Complex
open scoped Topology ContDiff
open MeasureTheory intervalIntegral Set
open scoped Real

namespace PolarStrips
open Set Filter Asymptotics
open scoped Topology ContDiff
noncomputable section

variable {E : Type u55} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {ι : Type u56} [Fintype ι]

def domain (ℓ : ι → E →L[ℂ] ℂ) : Set E := {z | ∀ j, ℓ j z ∈ PlanarLens.D}

def tuple (ℓ : ι → E →L[ℂ] ℂ) (k : ℕ) (z : E) : EuclideanSpace ℂ ι :=
  (EuclideanSpace.equiv ι ℂ).symm (fun j => PlanarLens.g (ℓ j z)^k)

omit [Fintype ι] in
@[simp] theorem tuple_apply (ℓ : ι → E →L[ℂ] ℂ) (k : ℕ) (z : E) (j : ι) :
    tuple ℓ k z j = PlanarLens.g (ℓ j z)^k := rfl

theorem norm_tuple_sq (ℓ : ι → E →L[ℂ] ℂ) (k : ℕ) (z : E) :
    ‖tuple ℓ k z‖^2 = ∑ j, ‖PlanarLens.g (ℓ j z)‖^(2*k) := by
  rw [EuclideanSpace.norm_sq_eq]
  apply Finset.sum_congr rfl
  intro j _
  change ‖PlanarLens.g (ℓ j z)^k‖^2 = _
  rw [norm_pow, ← pow_mul, Nat.mul_comm k 2]

theorem isOpen_domain (ℓ : ι → E →L[ℂ] ℂ) : IsOpen (domain ℓ) := by
  have he : domain ℓ = ⋂ j, (ℓ j) ⁻¹' PlanarLens.D := by ext z; simp [domain]
  rw [he]
  exact isOpen_iInter_of_finite (fun j => PlanarLens.isOpen_D.preimage (ℓ j).continuous)

omit [Fintype ι] in
theorem zero_mem_domain (ℓ : ι → E →L[ℂ] ℂ) : (0 : E) ∈ domain ℓ := by
  intro j
  simpa using PlanarLens.zero_mem_D

theorem analyticOnNhd_tuple (ℓ : ι → E →L[ℂ] ℂ) (k : ℕ) :
    AnalyticOnNhd ℂ (tuple ℓ k) (domain ℓ) := by
  intro z hz
  apply ((EuclideanSpace.equiv ι ℂ).symm.toContinuousLinearMap.analyticAt _).comp
  exact AnalyticAt.pi (fun j => ((PlanarLens.analyticOnNhd_g _ (hz j)).comp ((ℓ j).analyticAt z)).pow k)

omit [Fintype ι] in
theorem tuple_zero_iff (ℓ : ι → E →L[ℂ] ℂ)
    (hℓ : Function.Injective (fun z => fun j => ℓ j z)) {k : ℕ} (hk : 1 ≤ k)
    {z : E} (hz : z ∈ domain ℓ) : tuple ℓ k z = 0 ↔ z = 0 := by
  constructor
  · intro hf
    apply hℓ
    funext j
    have hj := congrArg (fun w : EuclideanSpace ℂ ι => w j) hf
    have hg : PlanarLens.g (ℓ j z) = 0 := (pow_eq_zero_iff (by omega : k ≠ 0)).mp (by simpa using hj)
    simpa using (PlanarLens.g_eq_zero_iff (hz j)).mp hg
  · rintro rfl
    ext j
    simp only [tuple_apply, map_zero, PlanarLens.g_zero, zero_pow (by omega : k ≠ 0)]
    rfl

theorem tuple_order (ℓ : ι → E →L[ℂ] ℂ) (k : ℕ) :
    tuple ℓ k =O[𝓝 (0 : E)] (fun z : E => ‖z‖^k) := by
  have hc (j : ι) : (fun z => PlanarLens.g (ℓ j z)) =O[𝓝 (0 : E)] (fun z : E => ‖z‖) := by
    have ha : AnalyticAt ℂ (fun z => PlanarLens.g (ℓ j z)) (0 : E) :=
      (PlanarLens.analyticOnNhd_g _ (by simpa using PlanarLens.zero_mem_D)).comp ((ℓ j).analyticAt 0)
    have hh := ha.differentiableAt.isBigO_sub.norm_right
    simpa only [map_zero, PlanarLens.g_zero, sub_zero] using hh
  have hp : (fun z j => PlanarLens.g (ℓ j z)^k) =O[𝓝 (0 : E)] (fun z : E => ‖z‖^k) :=
    isBigO_pi.mpr (fun j => (hc j).pow k)
  exact ((EuclideanSpace.equiv ι ℂ).symm.toContinuousLinearMap.isBigO_comp
    (fun z j => PlanarLens.g (ℓ j z)^k) _).trans hp

variable [FiniteDimensional ℂ E]

omit [Fintype ι] in

theorem isBounded_domain (ℓ : ι → E →L[ℂ] ℂ)
    (hℓ : Function.Injective (fun z => fun j => ℓ j z)) : Bornology.IsBounded (domain ℓ) := by
  let L : E →L[ℂ] (ι → ℂ) := ContinuousLinearMap.pi ℓ
  have hL : Topology.IsClosedEmbedding L :=
    LinearMap.isClosedEmbedding_of_injective (LinearMap.ker_eq_bot.mpr hℓ)
  let C := PlanarLens.F '' Metric.closedBall (0 : ℂ) 1
  have hC : IsCompact C := (isCompact_closedBall (0 : ℂ) 1).image_of_continuousOn
    PlanarLens.continuousOn_F_closedBall
  have hc : IsCompact (L ⁻¹' {f : ι → ℂ | ∀ j, f j ∈ C}) :=
    hL.isCompact_preimage (isCompact_pi_infinite (fun _ => hC))
  apply hc.isBounded.subset
  intro z hz j
  exact image_mono Metric.ball_subset_closedBall (hz j)

omit [Fintype ι] in

theorem compact_inner_preimage (ℓ : ι → E →L[ℂ] ℂ)
    (hℓ : Function.Injective (fun z => fun j => ℓ j z)) {r : ℝ} (hr : r < 1) :
    IsCompact {z : E | ∀ j, ℓ j z ∈ PlanarLens.F '' Metric.closedBall (0 : ℂ) r} := by
  let L : E →L[ℂ] (ι → ℂ) := ContinuousLinearMap.pi ℓ
  have hL : Topology.IsClosedEmbedding L :=
    LinearMap.isClosedEmbedding_of_injective (LinearMap.ker_eq_bot.mpr hℓ)
  have hC : IsCompact (PlanarLens.F '' Metric.closedBall (0 : ℂ) r) :=
    (isCompact_closedBall (0 : ℂ) r).image_of_continuousOn
      (PlanarLens.continuousOn_F_closedBall.mono (Metric.closedBall_subset_closedBall hr.le))
  have hc := hL.isCompact_preimage (isCompact_pi_infinite (fun _ : ι => hC))
  exact hc

theorem compact_sublevel (ℓ : ι → E →L[ℂ] ℂ)
    (hℓ : Function.Injective (fun z => fun j => ℓ j z)) {k : ℕ} (hk : 1 ≤ k)
    {s : ℝ} (hs : 0 < s) (hs1 : s < 1) :
    IsCompact {z : E | z ∈ domain ℓ ∧ ‖tuple ℓ k z‖^2 ≤ s} := by
  have hk0 : 2*k ≠ 0 := by omega
  have hval : (s+1)/2 ∈ Icc ((0 : ℝ)^(2*k)) ((1 : ℝ)^(2*k)) := by
    simp only [zero_pow hk0, one_pow]
    constructor <;> linarith
  obtain ⟨r, hr, hre⟩ := intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1)
    (f := fun r : ℝ => r^(2*k)) (by fun_prop) hval
  dsimp only at hre
  have hr0 : 0 ≤ r := hr.1
  have hr1 : r < 1 := by
    by_contra hn
    have her : r = 1 := le_antisymm hr.2 (le_of_not_gt hn)
    rw [her, one_pow] at hre
    linarith
  let C := {z : E | ∀ j, ℓ j z ∈ PlanarLens.F '' Metric.closedBall (0 : ℂ) r}
  have hC : IsCompact C := compact_inner_preimage ℓ hℓ hr1
  have hCD : C ⊆ domain ℓ := by
    intro z hz j
    rcases hz j with ⟨w, hw, he⟩
    refine ⟨w, ?_, he⟩
    have hw' : ‖w‖ ≤ r := by simpa using hw
    simpa using hw'.trans_lt hr1
  have hsub : ∀ z ∈ domain ℓ, ‖tuple ℓ k z‖^2 ≤ s → z ∈ C := by
    intro z hz hzs j
    have hcoord : ‖PlanarLens.g (ℓ j z)‖^(2*k) ≤ ‖tuple ℓ k z‖^2 := by
      have hh := pow_le_pow_left₀ (norm_nonneg _) (PiLp.norm_apply_le (tuple ℓ k z) j) 2
      simpa only [tuple_apply, norm_pow, ← pow_mul, Nat.mul_comm k 2] using hh
    have hp : ‖PlanarLens.g (ℓ j z)‖^(2*k) ≤ r^(2*k) := by linarith
    have hn : ‖PlanarLens.g (ℓ j z)‖ ≤ r := (pow_le_pow_iff_left₀ (norm_nonneg _) hr0 hk0).mp hp
    exact ⟨PlanarLens.g (ℓ j z), by simpa using hn, PlanarLens.F_g (hz j)⟩
  let : CompactSpace C := isCompact_iff_compactSpace.mp hC
  have hcont : Continuous (fun z : C => ‖tuple ℓ k z‖^2) :=
    ((analyticOnNhd_tuple ℓ k).continuousOn.mono hCD).domRestrict.norm.pow 2
  have hclosed : IsClosed {z : C | ‖tuple ℓ k z‖^2 ≤ s} := isClosed_le hcont continuous_const
  have hc := hclosed.isCompact.image continuous_subtype_val
  convert hc using 1
  ext z
  constructor
  · intro hz
    exact ⟨⟨z, hsub z hz.1 hz.2⟩, hz.2, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨hCD z.2, hz⟩

end
end PolarStrips

namespace ComplexCoordinates
open scoped ComplexConjugate ContDiff
noncomputable section
variable {ι : Type u57} [Fintype ι]
abbrev R (ι : Type u58) := EuclideanSpace ℝ ι
abbrev C (ι : Type u59) := EuclideanSpace ℂ ι

def re : C ι →L[ℝ] R ι :=
  LinearMap.toContinuousLinearMap {
    toFun := fun z => (EuclideanSpace.equiv ι ℝ).symm (fun i => (z i).re)
    map_add' := by intro x y; ext i; simp
    map_smul' := by intro a x; ext i; simp }

def im : C ι →L[ℝ] R ι :=
  LinearMap.toContinuousLinearMap {
    toFun := fun z => (EuclideanSpace.equiv ι ℝ).symm (fun i => (z i).im)
    map_add' := by intro x y; ext i; simp
    map_smul' := by intro a x; ext i; simp }

@[simp] theorem re_apply (z : C ι) (i : ι) : re z i = (z i).re := rfl
@[simp] theorem im_apply (z : C ι) (i : ι) : im z i = (z i).im := rfl

def parts : C ι ≃L[ℝ] R ι × R ι :=
  LinearEquiv.toContinuousLinearEquiv {
    toFun := fun z => (re z, im z)
    invFun := fun p => (EuclideanSpace.equiv ι ℂ).symm (fun i => (p.1 i : ℂ)+(p.2 i : ℂ)*Complex.I)
    left_inv := by intro z; ext i; simp [Complex.re_add_im]
    right_inv := by intro p; ext i <;> simp
    map_add' := by intros; simp
    map_smul' := by intros; simp }

@[simp] theorem parts_apply (z : C ι) : parts z = (re z, im z) := rfl
@[simp] theorem parts_symm_apply (x y : R ι) (i : ι) :
    parts.symm (x,y) i = (x i : ℂ)+(y i : ℂ)*Complex.I := rfl

def functional (b : R ι) : C ι →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap {
    toFun := fun z => ∑ i, (b i : ℂ)*z i
    map_add' := by intro x y; simp [mul_add, Finset.sum_add_distrib]
    map_smul' := by intro a x; simp [mul_left_comm, Finset.mul_sum] }

@[simp] theorem functional_apply (b : R ι) (z : C ι) : functional b z = ∑ i, (b i : ℂ)*z i := rfl

theorem re_functional (b : R ι) (z : C ι) :
    (functional b z).re = inner (𝕜 := ℝ) b (re z) := by
  simp [functional_apply, EuclideanSpace.inner_eq_star_dotProduct, dotProduct, mul_comm]

theorem im_functional (b : R ι) (z : C ι) :
    (functional b z).im = inner (𝕜 := ℝ) b (im z) := by
  simp [functional_apply, EuclideanSpace.inner_eq_star_dotProduct, dotProduct, mul_comm]

theorem norm_sq_parts (z : C ι) : ‖z‖^2 = ‖re z‖^2+‖im z‖^2 := by
  simp only [EuclideanSpace.norm_sq_eq, re_apply, im_apply, Real.norm_eq_abs, sq_abs,
    Complex.sq_norm, Complex.normSq_apply, ← pow_two, Finset.sum_add_distrib]

theorem real_inner_parts (z w : C ι) :
    let : InnerProductSpace ℝ (C ι) := InnerProductSpace.complexToReal
    inner (𝕜 := ℝ) z w = inner (𝕜 := ℝ) (re z) (re w)+inner (𝕜 := ℝ) (im z) (im w) := by
  let : InnerProductSpace ℝ (C ι) := InnerProductSpace.complexToReal
  simp [real_inner_eq_re_inner, EuclideanSpace.inner_eq_star_dotProduct, dotProduct,
    Finset.sum_add_distrib]

@[simp] theorem re_I_smul (z : C ι) : re (Complex.I • z) = -im z := by
  ext i; simp [Complex.mul_re]
@[simp] theorem im_I_smul (z : C ι) : im (Complex.I • z) = re z := by
  ext i; simp [Complex.mul_im]

theorem functional_injective {κ : Type u60} (b : κ → R ι)
    (hb : Function.Injective (fun x : R ι => fun j => inner (𝕜 := ℝ) (b j) x)) :
    Function.Injective (fun z : C ι => fun j => functional (b j) z) := by
  intro z w h
  apply parts.injective
  apply Prod.ext
  · apply hb
    funext j
    have hh := congrArg Complex.re (congrFun h j)
    simpa only [re_functional, parts_apply] using hh
  · apply hb
    funext j
    have hh := congrArg Complex.im (congrFun h j)
    simpa only [im_functional, parts_apply] using hh

end
end ComplexCoordinates

namespace PlanarLens
open Set Filter Complex MeasureTheory
open scoped Topology ContDiff
noncomputable section

def primitive (k : ℕ) (z : ℂ) : ℝ := J k z.re z.im

theorem contDiffAt_primitive {z : ℂ} (hz : z ∈ D) (k : ℕ) :
    ContDiffAt ℝ ∞ (primitive k) z :=
  (contDiffOn_J k).contDiffAt (isOpen_D.mem_nhds hz)

theorem J_mono {v w t : ℝ} (hv : (v : ℂ)+(t : ℂ)*I ∈ D)
    (hw : (w : ℂ)+(t : ℂ)*I ∈ D) (hvw : v ≤ w) (k : ℕ) : J k v t ≤ J k w t := by
  have hi := (integrable_density hv k).symm.trans (integrable_density hw k)
  have he := intervalIntegral.integral_add_adjacent_intervals (integrable_density hv k) hi
  have hp : 0 ≤ ∫ h in v..w, density k ((h : ℂ)+(t : ℂ)*I) :=
    intervalIntegral.integral_nonneg hvw (fun _ _ => density_nonneg _ _)
  unfold J
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  linarith

theorem J_product_nonneg {v w t : ℝ} (hv : (v : ℂ)+(t : ℂ)*I ∈ D)
    (hw : (w : ℂ)+(t : ℂ)*I ∈ D) (k : ℕ) :
    0 ≤ (J k w t-J k v t)*(w-v) := by
  rcases le_total v w with h | h
  · exact mul_nonneg (sub_nonneg.mpr (J_mono hv hw h k)) (sub_nonneg.mpr h)
  · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr (J_mono hw hv h k)) (sub_nonpos.mpr h)

theorem fderiv_primitive_one {z : ℂ} (hz : z ∈ D) (k : ℕ) :
    fderiv ℝ (primitive k) z 1 = (k : ℝ)^2*density k z := by
  have hp := (contDiffAt_primitive hz k).differentiableAt (by simp)
  have hd : HasDerivAt (fun v : ℝ => (v : ℂ)+(z.im : ℂ)*I) 1 z.re :=
    by simpa using ((hasDerivAt_id (z.re : ℂ)).comp_ofReal.add_const ((z.im : ℂ)*I))
  have hp' : HasFDerivAt (primitive k) (fderiv ℝ (primitive k) z) ((z.re : ℂ)+(z.im : ℂ)*I) := by
    simpa only [Complex.re_add_im] using hp.hasFDerivAt
  have hh := hp'.comp_hasDerivAt z.re hd
  have hj := hasDerivAt_J (v := z.re) (t := z.im) (by simpa only [Complex.re_add_im] using hz) k
  have hh' : HasDerivAt (fun v => J k v z.im) (fderiv ℝ (primitive k) z 1) z.re := by
    simpa [primitive, Function.comp_def] using hh
  simpa only [Complex.re_add_im] using hh'.unique hj

theorem fderiv_primitive_apply {z : ℂ} (hz : z ∈ D) (k : ℕ) (h : ℂ) :
    fderiv ℝ (primitive k) z h =
      (k : ℝ)^2*density k z * h.re + fderiv ℝ (primitive k) z I * h.im := by
  have he : h = h.re • (1 : ℂ)+h.im • I := by apply Complex.ext <;> simp
  calc
    fderiv ℝ (primitive k) z h = fderiv ℝ (primitive k) z (h.re • (1 : ℂ)+h.im • I) := congrArg _ he
    _ = _ := by simp only [map_add, map_smul, smul_eq_mul, fderiv_primitive_one hz k]; ring

end
end PlanarLens

end LowerBoundInline

end OAI
