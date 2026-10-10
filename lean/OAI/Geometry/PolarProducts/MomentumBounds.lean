import OAI.Geometry.PolarProducts.StripEmbedding

namespace OAI

universe u70 u71 u72 u73

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
open Set Filter ComplexCoordinates
open scoped Topology ContDiff
noncomputable section
variable {ι : Type u70} {κ : Type u71} [Fintype ι] [Fintype κ]

theorem position_mem_interior (b : κ → R ι) (k : ℕ) {z : C ι}
    (hz : z ∈ domain (fun j => functional (b j))) :
    (phase b k z).1 ∈ interior (ConvexPolar.stripBody b) := by
  apply ConvexPolar.mem_interior_stripBody
  intro j
  change |inner (𝕜 := ℝ) (b j) (im z)| < 1
  rw [← im_functional]
  exact abs_lt.mpr (PlanarLens.im_mem_Ioo (hz j))

theorem norm_re_le (z : C ι) : ‖re z‖ ≤ ‖z‖ := by
  have hh := norm_sq_parts z
  nlinarith [sq_nonneg ‖im z‖, norm_nonneg (re z), norm_nonneg z]

theorem momentum_bound (b : κ → R ι) {k : ℕ} (hk : 1 ≤ k) {z : C ι}
    (hz : z ∈ domain (fun j => functional (b j))) {y : R ι}
    (hy : y ∈ ConvexPolar.stripBody b) {A B : ℝ}
    (hzA : ‖z‖ ≤ A) (hyB : ‖y‖ ≤ B) :
    inner (𝕜 := ℝ) y (phase b k z).2 / (k : ℝ) ≤
      A*B/(k : ℝ) + Real.pi/4*‖tuple (fun j => functional (b j)) k z‖^2 +
        (Fintype.card κ : ℝ)*PlanarLens.epsilon k := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (Nat.zero_lt_of_lt hk)
  have hu : inner (𝕜 := ℝ) y (-re z) ≤ A*B := by
    have hh := real_inner_le_norm y (-re z)
    rw [norm_neg] at hh
    have hm := mul_le_mul hyB ((norm_re_le z).trans hzA) (norm_nonneg _) (le_trans (norm_nonneg _) hyB)
    nlinarith
  have hj (j : κ) : -(PlanarLens.primitive k (functional (b j) z)*inner (𝕜 := ℝ) y (b j)) ≤
      |PlanarLens.primitive k (functional (b j) z)| := by
    have hh : |inner (𝕜 := ℝ) y (b j)| ≤ 1 := by rw [real_inner_comm]; exact hy j
    calc
      _ ≤ |PlanarLens.primitive k (functional (b j) z)*inner (𝕜 := ℝ) y (b j)| := neg_le_abs _
      _ = |PlanarLens.primitive k (functional (b j) z)| * |inner (𝕜 := ℝ) y (b j)| := abs_mul _ _
      _ ≤ _ := by simpa using mul_le_mul_of_nonneg_left hh (abs_nonneg (PlanarLens.primitive k (functional (b j) z)))
  have hsum : inner (𝕜 := ℝ) y (phase b k z).2 ≤ A*B+∑ j, |PlanarLens.primitive k (functional (b j) z)| := by
    have hh := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hj j)
    simp only [phase, inner_sub_right, inner_sum, real_inner_smul_right, Finset.sum_neg_distrib] at ⊢ hh
    linarith
  have hslice (j : κ) : |PlanarLens.primitive k (functional (b j) z)|/(k : ℝ) ≤
      Real.pi/4*‖PlanarLens.g (functional (b j) z)‖^(2*k)+PlanarLens.epsilon k := by
    simpa only [PlanarLens.primitive, Complex.re_add_im] using
      PlanarLens.uniform_slice hk (v := (functional (b j) z).re) (t := (functional (b j) z).im)
        (by simpa only [Complex.re_add_im] using hz j)
  calc
    _ ≤ (A*B+∑ j, |PlanarLens.primitive k (functional (b j) z)|)/(k : ℝ) :=
      div_le_div_of_nonneg_right hsum hkpos.le
    _ = A*B/(k : ℝ) + ∑ j, |PlanarLens.primitive k (functional (b j) z)|/(k : ℝ) := by
      rw [add_div, Finset.sum_div]
    _ ≤ A*B/(k : ℝ) + ∑ j, (Real.pi/4*‖PlanarLens.g (functional (b j) z)‖^(2*k)+PlanarLens.epsilon k) :=
      add_le_add le_rfl (Finset.sum_le_sum (fun j _ => hslice j))
    _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← norm_tuple_sq]; simp [add_assoc]

theorem exists_uniform_momentum_bound (b : κ → R ι)
    (hb : Function.Injective (fun x : R ι => fun j => inner (𝕜 := ℝ) (b j) x)) :
    ∃ C B : ℝ, 0 ≤ C ∧ 0 ≤ B ∧ (∀ y ∈ ConvexPolar.stripBody b, ‖y‖ ≤ B) ∧
      ∀ k : ℕ, 1 ≤ k → ∀ z ∈ domain (fun j => functional (b j)),
        ∀ y ∈ ConvexPolar.stripBody b,
          inner (𝕜 := ℝ) y (phase b k z).2 / (k : ℝ) ≤
            C/(k : ℝ)+Real.pi/4*‖tuple (fun j => functional (b j)) k z‖^2 +
              (Fintype.card κ : ℝ)*PlanarLens.epsilon k := by
  obtain ⟨A, hA⟩ := (isBounded_domain _ (functional_injective b hb)).exists_norm_le
  obtain ⟨B, hB⟩ := (ConvexPolar.isCompact_stripBody b hb).isBounded.exists_norm_le
  have hA0 : 0 ≤ A := (norm_nonneg (0 : C ι)).trans (hA 0 (zero_mem_domain _))
  have hB0 : 0 ≤ B := (norm_nonneg (0 : R ι)).trans (hB 0 (interior_subset (ConvexPolar.zero_mem_interior_stripBody b)))
  refine ⟨A*B, B, mul_nonneg hA0 hB0, hB0, hB, ?_⟩
  intro k hk z hz y hy
  exact momentum_bound b hk hz hy (hA z hz) (hB y hy)

theorem exists_scaled_image (b : κ → R ι)
    (hb : Function.Injective (fun x : R ι => fun j => inner (𝕜 := ℝ) (b j) x))
    {η : ℝ} (hη : 0 < η) :
    ∃ k : ℕ, 1 ≤ k ∧ ∀ z : C ι,
      z ∈ domain (fun j => functional (b j)) → ‖tuple (fun j => functional (b j)) k z‖^2 < 1 →
      (phase b k z).1 ∈ interior (ConvexPolar.stripBody b) ∧
        (((1+η)*Real.pi*(k : ℝ)/4)⁻¹ • (phase b k z).2) ∈ interior (ConvexPolar.polar (ConvexPolar.stripBody b)) := by
  obtain ⟨C, B, _hC, hB, hbound, hmoment⟩ := exists_uniform_momentum_bound b hb
  have ht : Tendsto (fun k : ℕ => C/(k : ℝ)+(Fintype.card κ : ℝ)*PlanarLens.epsilon k) atTop (𝓝 0) := by
    simpa using (tendsto_const_div_atTop_nhds_zero_nat C).add (PlanarLens.tendsto_epsilon.const_mul (Fintype.card κ : ℝ))
  have hsmall := ht.eventually (eventually_lt_nhds (show (0 : ℝ) < η*Real.pi/4 by positivity))
  obtain ⟨k, hk, hksmall⟩ := (eventually_ge_atTop (1 : ℕ)).and hsmall |>.exists
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (Nat.zero_lt_of_lt hk)
  let T := (1+η)*Real.pi/4
  have hT : 0 < T := by dsimp [T]; positivity
  have hTsmall : C/(k : ℝ)+Real.pi/4+(Fintype.card κ : ℝ)*PlanarLens.epsilon k < T := by dsimp [T]; nlinarith
  refine ⟨k, hk, fun z hz hτ => ⟨position_mem_interior b k hz, ?_⟩⟩
  apply ConvexPolar.mem_interior_polar_of_bound hB hbound
    (r := (C/(k : ℝ)+Real.pi/4+(Fintype.card κ : ℝ)*PlanarLens.epsilon k)/T)
  · exact (div_lt_one hT).mpr hTsmall
  · intro y hy
    have hh := hmoment k hk z hz y hy
    have hp : inner (𝕜 := ℝ) y (phase b k z).2/(k : ℝ) ≤
        C/(k : ℝ)+Real.pi/4+(Fintype.card κ : ℝ)*PlanarLens.epsilon k := by
      have hm := mul_le_mul_of_nonneg_left hτ.le (by positivity : (0 : ℝ) ≤ Real.pi/4)
      linarith
    have hd := div_le_div_of_nonneg_right hp hT.le
    calc
      _ = inner (𝕜 := ℝ) y (phase b k z).2/(k : ℝ)/T := by
        rw [real_inner_smul_right]
        dsimp only [T]
        field_simp
      _ ≤ _ := hd

end
end PolarStrips

open Set
open scoped ContDiff ENNReal

namespace SymmetricPolar

end SymmetricPolar

namespace LocalEmbedding
open Set Filter
open scoped Topology ContDiff
noncomputable section
variable {E : Type u72} {F : Type u73} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem open_image {U : Set E} (hU : IsOpen U) {f : E → F}
    (hf : ContDiffOn ℝ ∞ f U)
    (hD : ∀ x ∈ U, (fderiv ℝ f x).IsInvertible) : IsOpen (f '' U) := by
  rw [isOpen_iff_mem_nhds]
  rintro _ ⟨x, hx, rfl⟩
  have hs := hf.contDiffAt (hU.mem_nhds hx)
  obtain ⟨e, heq⟩ := hD x hx
  have he : HasFDerivAt f e.toContinuousLinearMap x := by
    rw [heq]
    exact (hs.differentiableAt (by simp)).hasFDerivAt
  rw [← (hs.hasStrictFDerivAt' he (by simp)).map_nhds_eq_of_equiv]
  change f ⁻¹' (f '' U) ∈ 𝓝 x
  exact mem_of_superset (hU.mem_nhds hx) (fun y hy => mem_image_of_mem f hy)

theorem isOpenEmbedding {U : Set E} (hU : IsOpen U) {f : E → F}
    (hf : ContDiffOn ℝ ∞ f U) (hi : InjOn f U)
    (hD : ∀ x ∈ U, (fderiv ℝ f x).IsInvertible) :
    Topology.IsOpenEmbedding (fun x : U => f x) := by
  apply Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap hf.continuousOn.domRestrict
  · intro x y h; exact Subtype.ext (hi x.2 y.2 h)
  · intro V hV
    have hUV : Subtype.val '' V ⊆ U := by rintro _ ⟨x, _, rfl⟩; exact x.2
    have huV : IsOpen (Subtype.val '' V) := hU.isOpenMap_subtype_val _ hV
    have ho := open_image huV (hf.mono hUV) (fun x hx => hD x (hUV hx))
    change IsOpen ((fun x : U => f x) '' V)
    rw [image_image] at ho
    exact ho

end
end LocalEmbedding

namespace SymmetricPolar
open Set Filter
open scoped ContDiff Topology
noncomputable section
variable {n : ℕ}

theorem isOpen_capacityBall (n : ℕ) (c : ℝ) : IsOpen (capacityBall n c) :=
  isOpen_lt (by fun_prop) continuous_const

def diagScale (a b : ℝ) : Phase n →L[ℝ] Phase n :=
  (a • ContinuousLinearMap.fst ℝ (Position n) (Position n)).prod
    (b • ContinuousLinearMap.snd ℝ (Position n) (Position n))

@[simp] theorem diagScale_apply (a b : ℝ) (z : Phase n) : diagScale a b z = (a • z.1, b • z.2) := rfl

theorem diagScale_injective {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) :
    Function.Injective (diagScale a b : Phase n → Phase n) := by
  intro x y h
  exact Prod.ext ((smul_right_injective _ ha) (congrArg Prod.fst h))
    ((smul_right_injective _ hb) (congrArg Prod.snd h))

theorem omega0_diagScale (a b : ℝ) (v w : Phase n) :
    omega0 (diagScale a b v) (diagScale a b w) = (a*b)*omega0 v w := by
  simp only [omega0, diagScale_apply, real_inner_smul_left, real_inner_smul_right]
  ring

theorem omega0_nondegenerate (v : Phase n) (h : ∀ w : Phase n, omega0 v w = 0) : v = 0 := by
  have hh := h (-v.2, v.1)
  simp only [omega0, inner_neg_left, real_inner_self_eq_norm_sq, sub_neg_eq_add] at hh
  have h1 : v.1 = 0 := norm_eq_zero.mp (by nlinarith [norm_nonneg v.1, sq_nonneg ‖v.2‖])
  have h2 : v.2 = 0 := norm_eq_zero.mp (by nlinarith [norm_nonneg v.2, sq_nonneg ‖v.1‖])
  exact Prod.ext h1 h2

theorem isInvertible_of_preserves_omega0 (L : Phase n →L[ℝ] Phase n)
    (hL : ∀ v w, omega0 (L v) (L w) = omega0 v w) : L.IsInvertible := by
  have hi : Function.Injective L := by
    intro v w hvw
    have hz : L (v-w) = 0 := by rw [map_sub, hvw, sub_self]
    apply sub_eq_zero.mp
    apply omega0_nondegenerate
    intro a
    rw [← hL, hz]
    simp [omega0]
  have hs : Function.Surjective L := LinearMap.surjective_of_injective hi
  exact ⟨ContinuousLinearEquiv.ofBijective L (LinearMap.ker_eq_bot.mpr hi)
    (LinearMap.range_eq_top.mpr hs), rfl⟩

theorem hasSymplecticEmbedding_of_injOn {U V : Set (Phase n)} (hU : IsOpen U)
    {e : Phase n → Phase n} (he : ContDiffOn ℝ ∞ e U) (hi : InjOn e U)
    (hm : MapsTo e U V) (hω : ∀ z ∈ U, ∀ v w,
      omega0 (fderiv ℝ e z v) (fderiv ℝ e z w) = omega0 v w) :
    HasSymplecticEmbedding U V := by
  refine ⟨e, he, ?_, hm, hω⟩
  exact (LocalEmbedding.isOpenEmbedding hU he hi (fun z hz => isInvertible_of_preserves_omega0 _ (hω z hz))).isEmbedding

theorem HasSymplecticEmbedding.mono_target {U V W : Set (Phase n)}
    (h : HasSymplecticEmbedding U V) (hVW : V ⊆ W) : HasSymplecticEmbedding U W := by
  rcases h with ⟨e, he, hi, hm, hω⟩
  exact ⟨e, he, hi, hm.mono_right hVW, hω⟩

theorem HasSymplecticEmbedding.injOn {U : Set (Phase n)} {e : Phase n → Phase n}
    (he : Topology.IsEmbedding (fun z : U => e z)) : InjOn e U := by
  intro x hx y hy h
  exact congrArg Subtype.val (he.injective (show e (⟨x,hx⟩ : U) = e (⟨y,hy⟩ : U) from h))

theorem mapsTo_scaled_ball {lam c : ℝ} (hlam : 0 < lam) :
    MapsTo (diagScale (Real.sqrt lam) (Real.sqrt lam) : Phase n → Phase n)
      (capacityBall n c) (capacityBall n (lam*c)) := by
  intro z hz
  change Real.pi*(‖Real.sqrt lam • z.1‖^2+‖Real.sqrt lam • z.2‖^2) < lam*c
  have hsq : |Real.sqrt lam|^2 = lam := by rw [sq_abs, Real.sq_sqrt hlam.le]
  simp only [norm_smul, Real.norm_eq_abs, mul_pow, hsq]
  have hh := mul_lt_mul_of_pos_left hz hlam
  nlinarith

theorem embedding_of_scaled_ball_map {lam c a b : ℝ} (hlam : 0 < lam) (hab : a*b = lam⁻¹)
    {V : Set (Phase n)} {e : Phase n → Phase n}
    (he : ContDiffOn ℝ ∞ e (capacityBall n (lam*c)))
    (hi : InjOn e (capacityBall n (lam*c)))
    (hm : MapsTo (fun z => diagScale a b (e z)) (capacityBall n (lam*c)) V)
    (hω : ∀ z ∈ capacityBall n (lam*c), ∀ v w,
      omega0 (fderiv ℝ e z v) (fderiv ℝ e z w) = omega0 v w) :
    HasSymplecticEmbedding (capacityBall n c) V := by
  let D : Phase n →L[ℝ] Phase n := diagScale (Real.sqrt lam) (Real.sqrt lam)
  let L : Phase n →L[ℝ] Phase n := diagScale a b
  let F : Phase n → Phase n := fun z => L (e (D z))
  have hD : MapsTo D (capacityBall n c) (capacityBall n (lam*c)) := mapsTo_scaled_ball hlam
  have hLinj : Function.Injective L := diagScale_injective (left_ne_zero_of_mul (by rw [hab]; exact inv_ne_zero hlam.ne'))
    (right_ne_zero_of_mul (by rw [hab]; exact inv_ne_zero hlam.ne'))
  have hDinj : Function.Injective D := diagScale_injective (Real.sqrt_pos.mpr hlam).ne' (Real.sqrt_pos.mpr hlam).ne'
  have hs (z : Phase n) (hz : z ∈ capacityBall n c) : ContDiffAt ℝ ∞ e (D z) :=
    he.contDiffAt ((isOpen_capacityBall _ _).mem_nhds (hD hz))
  apply hasSymplecticEmbedding_of_injOn (isOpen_capacityBall n c) (e := F)
  · intro z hz
    exact (L.contDiff.contDiffAt.comp z ((hs z hz).comp z D.contDiff.contDiffAt)).contDiffWithinAt
  · intro z hz w hw h
    exact hDinj (hi (hD hz) (hD hw) (hLinj h))
  · intro z hz
    exact hm (hD hz)
  · intro z hz v w
    have hd : HasFDerivAt F (L.comp ((fderiv ℝ e (D z)).comp D)) z :=
      L.hasFDerivAt.comp z (((hs z hz).differentiableAt (by simp)).hasFDerivAt.comp z D.hasFDerivAt)
    rw [hd.fderiv]
    change omega0 (diagScale a b (fderiv ℝ e (D z) (D v)))
      (diagScale a b (fderiv ℝ e (D z) (D w))) = _
    rw [omega0_diagScale, hω _ (hD hz), hab, omega0_diagScale]
    rw [← pow_two, Real.sq_sqrt hlam.le, ← mul_assoc, inv_mul_cancel₀ hlam.ne', one_mul]

end
end SymmetricPolar

end LowerBoundInline

end OAI
