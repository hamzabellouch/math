import Mathlib
import OAI.Geometry.BallPacking.Holder.BanachSpace
import OAI.Geometry.BallPacking.Rigidity.CompatibleStructures

namespace OAI

noncomputable section
namespace HigherDimensionalBallPacking.Rigidity

section
open scoped ContDiff Topology Manifold
open Set Function Filter


theorem exists_smooth_cutoff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {K U : Set E} (hK : IsCompact K) (hU : IsOpen U)
    (hKU : K ⊆ U) : ∃ χ : E → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
      tsupport χ ⊆ U ∧ (∀ᶠ x in 𝓝ˢ K, χ x = 1) ∧ ∀ x, χ x ∈ Icc 0 1 := by
  obtain ⟨L,hL,hKL,hLU⟩ := exists_compact_between hK hU hKU
  obtain ⟨χ,hχ1,hχ0,hχrange⟩ :=
    exists_contMDiffMap_one_nhds_of_subset_interior 𝓘(ℝ,E) hK.isClosed hKL (n := ⊤)
  have hs : tsupport (χ : E → ℝ) ⊆ L := by
    apply closure_minimal _ hL.isClosed
    intro x hx
    by_contra hn
    exact hx (hχ0 x hn)
  exact ⟨χ,χ.contMDiff.contDiff,hL.of_isClosed_subset (isClosed_tsupport _) hs,
    hs.trans hLU,hχ1,hχrange⟩

def localizeJ {n : ℕ} (V : Set (Phase n)) (J : Phase n → End n)
    (χ : Phase n → ℝ) (x : Phase n) : End n := by
  classical
  exact if x ∈ V then interpolateJ (J x) (χ x) else standardJ n

theorem localizeJ_compatible {n : ℕ} {V : Set (Phase n)} {J : Phase n → End n}
    {χ : Phase n → ℝ} (hJ : ∀ x ∈ V, Compatible (J x))
    (hχ : ∀ x, χ x ∈ Icc (0 : ℝ) 1) (x : Phase n) :
    Compatible (localizeJ V J χ x) := by
  classical
  by_cases hx : x ∈ V
  · simpa only [localizeJ, ite_eq_left hx] using compatible_interpolateJ (hJ x hx) (hχ x)
  · simpa only [localizeJ, ite_eq_right hx] using compatible_standardJ n

theorem localizeJ_eq_standard {n : ℕ} {V : Set (Phase n)} {J : Phase n → End n}
    {χ : Phase n → ℝ} (hJ : ∀ x ∈ V, Compatible (J x)) {x : Phase n}
    (hx : χ x = 0) : localizeJ V J χ x = standardJ n := by
  classical
  by_cases hV : x ∈ V
  · simp only [localizeJ, ite_eq_left hV, hx, interpolateJ_zero (hJ x hV)]
  · simp only [localizeJ, ite_eq_right hV]

theorem localizeJ_smooth {n : ℕ} {V : Set (Phase n)} (hV : IsOpen V)
    {J : Phase n → End n} (hJs : ContDiffOn ℝ ∞ J V)
    (hJ : ∀ x ∈ V, Compatible (J x)) {χ : Phase n → ℝ}
    (hχs : ContDiff ℝ ∞ χ) (hχV : tsupport χ ⊆ V)
    (hχ : ∀ x, χ x ∈ Icc (0 : ℝ) 1) : ContDiff ℝ ∞ (localizeJ V J χ) := by
  classical
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x ∈ V
  · apply (contDiffAt_interpolateJ (hJs.contDiffAt (hV.mem_nhds hx)) hχs.contDiffAt
      (hJ x hx) (hχ x)).congr_of_eventuallyEq
    filter_upwards [hV.mem_nhds hx] with y hy
    simp only [localizeJ, ite_eq_left hy]
  · have hn : x ∉ tsupport χ := fun h => hx (hχV h)
    apply (contDiffAt_const (c := standardJ n)).congr_of_eventuallyEq
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hn] with y hy
    exact localizeJ_eq_standard hJ hy

theorem localizeJ_eqOn {n : ℕ} {V K : Set (Phase n)} {J : Phase n → End n}
    {χ : Phase n → ℝ} (hKV : K ⊆ V) (hJ : ∀ x ∈ V, Compatible (J x))
    (hχ : ∀ x ∈ K, χ x = 1) : EqOn (localizeJ V J χ) J K := by
  classical
  intro x hx
  simp only [localizeJ, ite_eq_left (hKV hx), hχ x hx, interpolateJ_one (hJ x (hKV hx))]

theorem extend_two_compatible {n : ℕ} {K₀ K₁ V₀ V₁ W : Set (Phase n)}
    (hK₀ : IsCompact K₀) (hK₁ : IsCompact K₁) (hdis : Disjoint K₀ K₁)
    (hV₀ : IsOpen V₀) (hV₁ : IsOpen V₁) (hW : IsOpen W)
    (hKV₀ : K₀ ⊆ V₀) (hKV₁ : K₁ ⊆ V₁) (hKW₀ : K₀ ⊆ W) (hKW₁ : K₁ ⊆ W)
    {J₀ J₁ : Phase n → End n} (hJ₀s : ContDiffOn ℝ ∞ J₀ V₀)
    (hJ₁s : ContDiffOn ℝ ∞ J₁ V₁) (hJ₀ : ∀ x ∈ V₀, Compatible (J₀ x))
    (hJ₁ : ∀ x ∈ V₁, Compatible (J₁ x)) :
    ∃ J : Phase n → End n, ContDiff ℝ ∞ J ∧ (∀ x, Compatible (J x)) ∧
      (∀ᶠ x in 𝓝ˢ K₀, J x = J₀ x) ∧ (∀ᶠ x in 𝓝ˢ K₁, J x = J₁ x) ∧
      HasCompactSupport (fun x => J x - standardJ n) ∧
      tsupport (fun x => J x - standardJ n) ⊆ W := by
  obtain ⟨O₀,O₁,hO₀,hO₁,hKO₀,hKO₁,hOdis⟩ :=
    normal_separation hK₀.isClosed hK₁.isClosed hdis
  let A₀ := O₀ ∩ V₀ ∩ W
  let A₁ := O₁ ∩ V₁ ∩ W
  have hA₀ : IsOpen A₀ := (hO₀.inter hV₀).inter hW
  have hA₁ : IsOpen A₁ := (hO₁.inter hV₁).inter hW
  have hKA₀ : K₀ ⊆ A₀ := fun x hx => ⟨⟨hKO₀ hx,hKV₀ hx⟩,hKW₀ hx⟩
  have hKA₁ : K₁ ⊆ A₁ := fun x hx => ⟨⟨hKO₁ hx,hKV₁ hx⟩,hKW₁ hx⟩
  obtain ⟨χ₀,hχ₀s,hχ₀c,hχ₀A,hχ₀one,hχ₀I⟩ := exists_smooth_cutoff hK₀ hA₀ hKA₀
  obtain ⟨χ₁,hχ₁s,hχ₁c,hχ₁A,hχ₁one,hχ₁I⟩ := exists_smooth_cutoff hK₁ hA₁ hKA₁
  have hχdis : Disjoint (tsupport χ₀) (tsupport χ₁) :=
    hOdis.mono (fun _ hx => (hχ₀A hx).1.1) (fun _ hx => (hχ₁A hx).1.1)
  have hA₀V : A₀ ⊆ V₀ := fun _ hx => hx.1.2
  have hA₁V : A₁ ⊆ V₁ := fun _ hx => hx.1.2
  have hJ₀A : ∀ x ∈ A₀, Compatible (J₀ x) := fun _ hx => hJ₀ _ (hA₀V hx)
  have hJ₁A : ∀ x ∈ A₁, Compatible (J₁ x) := fun _ hx => hJ₁ _ (hA₁V hx)
  let L₀ := localizeJ A₀ J₀ χ₀
  let L₁ := localizeJ A₁ J₁ χ₁
  have hL₀s : ContDiff ℝ ∞ L₀ :=
    localizeJ_smooth hA₀ (hJ₀s.mono hA₀V) hJ₀A hχ₀s hχ₀A hχ₀I
  have hL₁s : ContDiff ℝ ∞ L₁ :=
    localizeJ_smooth hA₁ (hJ₁s.mono hA₁V) hJ₁A hχ₁s hχ₁A hχ₁I
  have hL₀ (x) : Compatible (L₀ x) := localizeJ_compatible hJ₀A hχ₀I x
  have hL₁ (x) : Compatible (L₁ x) := localizeJ_compatible hJ₁A hχ₁I x
  have hL₀out (x) (hx : x ∉ tsupport χ₀) : L₀ x = standardJ n :=
    localizeJ_eq_standard hJ₀A (image_eq_zero_of_notMem_tsupport hx)
  have hL₁out (x) (hx : x ∉ tsupport χ₁) : L₁ x = standardJ n :=
    localizeJ_eq_standard hJ₁A (image_eq_zero_of_notMem_tsupport hx)
  let J := fun x => L₀ x + L₁ x - standardJ n
  have hJs : ContDiff ℝ ∞ J := (hL₀s.add hL₁s).sub contDiff_const
  have hJ (x) : Compatible (J x) := by
    by_cases hx : x ∈ tsupport χ₀
    · have hx₁ : x ∉ tsupport χ₁ := fun hh => disjoint_left.mp hχdis hx hh
      simpa only [J,hL₁out x hx₁,add_sub_cancel_right] using hL₀ x
    · simpa only [J,hL₀out x hx,add_sub_cancel_left] using hL₁ x
  have hzero (x) (hx : x ∉ tsupport χ₀ ∪ tsupport χ₁) : J x - standardJ n = 0 := by
    have hx₀ : x ∉ tsupport χ₀ := fun hh => hx (Or.inl hh)
    have hx₁ : x ∉ tsupport χ₁ := fun hh => hx (Or.inr hh)
    simp only [J,hL₀out x hx₀,hL₁out x hx₁,add_sub_cancel_right,sub_self]
  have hsupport : tsupport (fun x => J x - standardJ n) ⊆ tsupport χ₀ ∪ tsupport χ₁ := by
    apply closure_minimal _ ((isClosed_tsupport χ₀).union (isClosed_tsupport χ₁))
    intro x hx
    by_contra hn
    exact hx (hzero x hn)
  refine ⟨J,hJs,hJ,?_,?_,(hχ₀c.union hχ₁c).of_isClosed_subset (isClosed_tsupport _) hsupport,
    fun x hx => ?_⟩
  · filter_upwards [hχ₀one] with x hx
    have hx₀ : x ∈ tsupport χ₀ := subset_tsupport χ₀ (by simp [mem_support,hx])
    have hx₁ : x ∉ tsupport χ₁ := fun hh => disjoint_left.mp hχdis hx₀ hh
    have hL : L₀ x = J₀ x := by
      classical
      simp only [L₀,localizeJ,ite_eq_left (hχ₀A hx₀),hx,
        interpolateJ_one (hJ₀A x (hχ₀A hx₀))]
    simp only [J,hL,hL₁out x hx₁,add_sub_cancel_right]
  · filter_upwards [hχ₁one] with x hx
    have hx₁ : x ∈ tsupport χ₁ := subset_tsupport χ₁ (by simp [mem_support,hx])
    have hx₀ : x ∉ tsupport χ₀ := fun hh => disjoint_left.mp hχdis hh hx₁
    have hL : L₁ x = J₁ x := by
      classical
      simp only [L₁,localizeJ,ite_eq_left (hχ₁A hx₁),hx,
        interpolateJ_one (hJ₁A x (hχ₁A hx₁))]
    simp only [J,hL₀out x hx₀,hL,add_sub_cancel_left]
  · rcases hsupport hx with h | h
    · exact (hχ₀A h).2
    · exact (hχ₁A h).2

@[fun_prop]
theorem continuous_capacity (n : ℕ) : Continuous (capacity : Phase n → ℝ) := by
  unfold capacity
  fun_prop

theorem closedBall_isClosed (n : ℕ) (R : ℝ) : IsClosed (closedBall n R) :=
  isClosed_le (continuous_capacity n) continuous_const

theorem openBall_isOpen (n : ℕ) (R : ℝ) : IsOpen (openBall n R) :=
  isOpen_lt (continuous_capacity n) continuous_const

theorem closedBall_isCompact (n : ℕ) (R : ℝ) : IsCompact (closedBall n R) := by
  apply (isCompact_closedBall (0 : Phase n) (max R 0 + 1)).of_isClosed_subset
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

theorem adapt_two_ball_images {n : ℕ} {a b R : ℝ}
    {U₀ U₁ : Set (Phase n)} {f₀ f₁ : Phase n → Phase n}
    (hsub₀ : closedBall n a ⊆ U₀) (hsub₁ : closedBall n b ⊆ U₁)
    (hf₀ : SymplecticOn U₀ f₀) (hf₁ : SymplecticOn U₁ f₁)
    (ht₀ : MapsTo f₀ (closedBall n a) (openBall n R))
    (ht₁ : MapsTo f₁ (closedBall n b) (openBall n R))
    (hdis : Disjoint (f₀ '' closedBall n a) (f₁ '' closedBall n b)) :
    ∃ J : Phase n → End n, ContDiff ℝ ∞ J ∧ (∀ x, Compatible (J x)) ∧
      (∀ᶠ x in 𝓝ˢ (f₀ '' closedBall n a), J x = imageJ U₀ f₀ x) ∧
      (∀ᶠ x in 𝓝ˢ (f₁ '' closedBall n b), J x = imageJ U₁ f₁ x) ∧
      HasCompactSupport (fun x => J x - standardJ n) ∧
      tsupport (fun x => J x - standardJ n) ⊆ openBall n R := by
  exact extend_two_compatible
    ((closedBall_isCompact n a).image_of_continuousOn (hf₀.2.1.continuousOn.mono hsub₀))
    ((closedBall_isCompact n b).image_of_continuousOn (hf₁.2.1.continuousOn.mono hsub₁))
    hdis (symplecticOn_open_image hf₀) (symplecticOn_open_image hf₁) (openBall_isOpen n R)
    (image_mono hsub₀) (image_mono hsub₁) (image_subset_iff.mpr ht₀) (image_subset_iff.mpr ht₁)
    (imageJ_smooth hf₀) (imageJ_smooth hf₁)
    (fun _ hx => imageJ_compatible hf₀ hx) (fun _ hx => imageJ_compatible hf₁ hx)

theorem packing_two_has_adapted_structure {n : ℕ} {a b R : ℝ}
    (hp : HasPacking n 2 R ![a,b]) :
    ∃ (U : Fin 2 → Set (Phase n)) (f : Fin 2 → Phase n → Phase n)
      (J : Phase n → End n),
      (∀ i, closedBall n (![a,b] i) ⊆ U i ∧ SymplecticOn (U i) (f i) ∧
        MapsTo (f i) (closedBall n (![a,b] i)) (openBall n R)) ∧
      (∀ i j, i ≠ j → Disjoint (f i '' closedBall n (![a,b] i))
        (f j '' closedBall n (![a,b] j))) ∧
      ContDiff ℝ ∞ J ∧ (∀ x, Compatible (J x)) ∧
      (∀ i, ∀ᶠ x in 𝓝ˢ (f i '' closedBall n (![a,b] i)), J x = imageJ (U i) (f i) x) ∧
      HasCompactSupport (fun x => J x - standardJ n) ∧
      tsupport (fun x => J x - standardJ n) ⊆ openBall n R := by
  obtain ⟨U,f,hf,hd⟩ := hp
  obtain ⟨J,hJs,hJ,hJ₀,hJ₁,hJc,hJsupp⟩ := adapt_two_ball_images
    (hf 0).1 (hf 1).1 (hf 0).2.1 (hf 1).2.1 (hf 0).2.2 (hf 1).2.2
    (hd 0 1 (by decide))
  refine ⟨U,f,J,hf,hd,hJs,hJ,?_,hJc,hJsupp⟩
  intro i
  fin_cases i
  · exact hJ₀
  · exact hJ₁


end

section
open scoped ContDiff Topology
open Set Function Filter

def AffineLineCurve {n : ℕ} (J : Phase n → End n) (p q : Phase n)
    (u : ℂ → Phase n) : Prop :=
  ContDiff ℝ ∞ u ∧ (∀ z, PseudoHolomorphicAt J u z) ∧ u 0 = p ∧ u 1 = q ∧
    ∃ v : Phase n, v ≠ 0 ∧ Tendsto (fun z : ℂ => z⁻¹ • u z) (cocompact ℂ) (𝓝 v)

theorem pseudoHolomorphicAt_standard_of_complex {n : ℕ} {u : ℂ → Phase n} {z : ℂ}
    (hu : DifferentiableAt ℂ u z) :
    PseudoHolomorphicAt (fun _ => standardJ n) u z := by
  refine ⟨hu.restrictScalars ℝ,?_⟩
  intro w
  rw [(hu.hasFDerivAt.restrictScalars ℝ).fderiv]
  change fderiv ℂ u z (Complex.I • w) = Complex.I • fderiv ℂ u z w
  exact map_smul (fderiv ℂ u z) Complex.I w

theorem standard_affine_line {n : ℕ} (p q : Phase n) (hpq : p ≠ q) :
    AffineLineCurve (fun _ => standardJ n) p q (fun z : ℂ => p + z • (q-p)) := by
  have hs : ContDiff ℂ ∞ (fun z : ℂ => p + z • (q-p)) :=
    contDiff_const.add (contDiff_id.smul contDiff_const)
  refine ⟨hs.restrict_scalars ℝ,fun z =>
    pseudoHolomorphicAt_standard_of_complex (hs.differentiable (by simp) z),by simp,by simp,?_,?_⟩
  · exact q-p
  · refine ⟨sub_ne_zero.mpr hpq.symm,?_⟩
    have hi : Tendsto (fun z : ℂ => z⁻¹) (cocompact ℂ) (𝓝 0) := by
      simpa only [←Metric.cobounded_eq_cocompact] using (tendsto_inv₀_cobounded (α := ℂ))
    have ht : Tendsto (fun z : ℂ => z⁻¹ • p + (q-p)) (cocompact ℂ) (𝓝 (q-p)) := by
      simpa only [zero_smul, zero_add] using (hi.smul_const p).add_const (q-p)
    apply ht.congr'
    filter_upwards [(isCompact_singleton (x := (0:ℂ))).compl_mem_cocompact] with z hz
    have hz0 : z ≠ 0 := by simpa only [mem_compl_iff, mem_singleton_iff] using hz
    simp only [smul_add, smul_smul, inv_mul_cancel₀ hz0, one_smul]

theorem interpolateJ_standard {n : ℕ} {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    interpolateJ (standardJ n) t = standardJ n := by
  have ha : 0 < 1+t := by linarith [ht.1]
  have hb : 0 ≤ 1-t := by linarith [ht.2]
  obtain ⟨e,he⟩ := cayleyP_invertible (compatible_standardJ n) ha hb
  apply ContinuousLinearMap.ext
  intro v
  obtain ⟨x,rfl⟩ := e.surjective v
  change standardJ n (cayleyOperator (standardJ n) (1+t) (1-t) ((e : End n) x)) =
    standardJ n ((e : End n) x)
  rw [he,cayleyOperator_on_denominator ⟨e,he⟩]
  congr 1
  simp only [cayleyP_apply,relativeOperator_apply,standardJ_sq,neg_neg]
  module

def lineHomotopy {n : ℕ} (J : Phase n → End n) (t : ℝ) (x : Phase n) : End n :=
  interpolateJ (J x) t

theorem lineHomotopy_compatible {n : ℕ} {J : Phase n → End n}
    (hJ : ∀ x, Compatible (J x)) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) (x : Phase n) :
    Compatible (lineHomotopy J t x) := compatible_interpolateJ (hJ x) ht

theorem lineHomotopy_smooth {n : ℕ} {J : Phase n → End n}
    (hJs : ContDiff ℝ ∞ J) (hJ : ∀ x, Compatible (J x)) :
    ContDiffOn ℝ ∞ (fun y : ℝ × Phase n => lineHomotopy J y.1 y.2)
      ((Icc (0:ℝ) 1) ×ˢ univ) := by
  intro y hy
  exact (contDiffAt_interpolateJ (hJs.contDiffAt.comp y contDiffAt_snd)
    contDiffAt_fst (hJ y.2) hy.1).contDiffWithinAt

@[simp] theorem lineHomotopy_zero {n : ℕ} {J : Phase n → End n}
    (hJ : ∀ x, Compatible (J x)) (x : Phase n) : lineHomotopy J 0 x = standardJ n :=
  interpolateJ_zero (hJ x)

@[simp] theorem lineHomotopy_one {n : ℕ} {J : Phase n → End n}
    (hJ : ∀ x, Compatible (J x)) (x : Phase n) : lineHomotopy J 1 x = J x :=
  interpolateJ_one (hJ x)

theorem lineHomotopy_support {n : ℕ} (J : Phase n → End n)
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    tsupport (fun x => lineHomotopy J t x - standardJ n) ⊆
      tsupport (fun x => J x - standardJ n) := by
  apply closure_minimal _ (isClosed_tsupport _)
  intro x hx
  by_contra hn
  have hzero := image_eq_zero_of_notMem_tsupport hn
  have hJx : J x = standardJ n := sub_eq_zero.mp hzero
  apply hx
  change interpolateJ (J x) t - standardJ n = 0
  rw [hJx,interpolateJ_standard ht,sub_self]

theorem lineHomotopy_compact {n : ℕ} {J : Phase n → End n}
    (hJc : HasCompactSupport (fun x => J x - standardJ n))
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    HasCompactSupport (fun x => lineHomotopy J t x - standardJ n) :=
  hJc.of_isClosed_subset (isClosed_tsupport _) (lineHomotopy_support J ht)


end

open scoped ContDiff Topology
open Set Function Filter MeasureTheory

def radialSwitch (σ τ t : ℝ) : ℝ := Real.smoothTransition ((t-σ)/(τ-σ))

theorem radialSwitch_smooth (σ τ : ℝ) : ContDiff ℝ ∞ (radialSwitch σ τ) :=
  Real.smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).div_const _)

theorem radialSwitch_nonneg (σ τ t : ℝ) : 0 ≤ radialSwitch σ τ t :=
  Real.smoothTransition.nonneg _

theorem radialSwitch_le_one (σ τ t : ℝ) : radialSwitch σ τ t ≤ 1 :=
  Real.smoothTransition.le_one _

theorem radialSwitch_zero {σ τ t : ℝ} (hστ : σ < τ) (ht : t ≤ σ) :
    radialSwitch σ τ t = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr ht) (sub_pos.mpr hστ).le

theorem radialSwitch_one {σ τ t : ℝ} (hστ : σ < τ) (ht : τ ≤ t) :
    radialSwitch σ τ t = 1 := by
  apply Real.smoothTransition.one_of_one_le
  apply (le_div_iff₀ (sub_pos.mpr hστ)).mpr
  linarith

def radialOffset (σ τ t : ℝ) : ℝ := ∫ s in σ..t, radialSwitch σ τ s

theorem radialOffset_hasDerivAt (σ τ t : ℝ) :
    HasDerivAt (radialOffset σ τ) (radialSwitch σ τ t) t := by
  have hc := (radialSwitch_smooth σ τ).continuous
  exact intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable _ _)
    hc.stronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt

theorem radialOffset_smooth (σ τ : ℝ) : ContDiff ℝ ∞ (radialOffset σ τ) := by
  apply contDiff_infty_iff_deriv.mpr
  refine ⟨fun t => (radialOffset_hasDerivAt σ τ t).differentiableAt,?_⟩
  have he : deriv (radialOffset σ τ) = radialSwitch σ τ :=
    funext (fun t => (radialOffset_hasDerivAt σ τ t).deriv)
  rw [he]
  exact radialSwitch_smooth σ τ

theorem radialOffset_zero {σ τ t : ℝ} (hστ : σ < τ) (ht : t ≤ σ) :
    radialOffset σ τ t = 0 := by
  unfold radialOffset
  calc
    (∫ s in σ..t, radialSwitch σ τ s) = ∫ s in σ..t, (0:ℝ) := by
      apply intervalIntegral.integral_congr
      intro s hs
      exact radialSwitch_zero hστ ((uIcc_of_ge ht ▸ hs).2)
    _ = 0 := by simp

theorem radialOffset_nonneg {σ τ : ℝ} (hστ : σ < τ) (t : ℝ) :
    0 ≤ radialOffset σ τ t := by
  by_cases ht : t ≤ σ
  · rw [radialOffset_zero hστ ht]
  · exact intervalIntegral.integral_nonneg (le_of_not_ge ht)
      (fun s _ => radialSwitch_nonneg σ τ s)

def radialShift (σ τ : ℝ) : ℝ := 1 + radialOffset σ τ τ - τ

theorem radialShift_pos {σ τ : ℝ} (hστ : σ < τ) (hτ : τ < 1) :
    0 < radialShift σ τ := by
  have hn := radialOffset_nonneg hστ τ
  unfold radialShift
  linarith

theorem radialOffset_after {σ τ t : ℝ} (hστ : σ < τ) (ht : τ ≤ t) :
    1 + radialOffset σ τ t = t + radialShift σ τ := by
  have hc := (radialSwitch_smooth σ τ).continuous
  have he := intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable (μ := volume) σ τ) (hc.intervalIntegrable τ t)
  have hI : (∫ s in τ..t, radialSwitch σ τ s) = t-τ := by
    calc
      _ = ∫ s in τ..t, (1:ℝ) := by
        apply intervalIntegral.integral_congr
        intro s hs
        exact radialSwitch_one hστ ((uIcc_of_le ht ▸ hs).1)
      _ = t-τ := by simp
  rw [hI] at he
  change radialOffset σ τ τ + (t-τ) = radialOffset σ τ t at he
  unfold radialShift
  linarith

def radialCoefficient (σ τ t : ℝ) : ℝ := (1 + radialOffset σ τ t)⁻¹

theorem radialCoefficient_pos {σ τ : ℝ} (hστ : σ < τ) (t : ℝ) :
    0 < radialCoefficient σ τ t :=
  inv_pos.mpr (by linarith [radialOffset_nonneg hστ t])

theorem radialCoefficient_smooth {σ τ : ℝ} (hστ : σ < τ) :
    ContDiff ℝ ∞ (radialCoefficient σ τ) :=
  (contDiff_const.add (radialOffset_smooth σ τ)).inv
    (fun t => ne_of_gt (by linarith [radialOffset_nonneg hστ t]))

theorem radialCoefficient_hasDerivAt {σ τ : ℝ} (hστ : σ < τ) (t : ℝ) :
    HasDerivAt (radialCoefficient σ τ)
      (-radialSwitch σ τ t / (1 + radialOffset σ τ t)^2) t := by
  have hd : HasDerivAt (fun x : ℝ => 1 + radialOffset σ τ x) (radialSwitch σ τ t) t :=
    (radialOffset_hasDerivAt σ τ t).const_add 1
  exact hd.inv (ne_of_gt (by linarith [radialOffset_nonneg hστ t]))

theorem radialCoefficient_one {σ τ t : ℝ} (hστ : σ < τ) (ht : t ≤ σ) :
    radialCoefficient σ τ t = 1 := by
  simp only [radialCoefficient,radialOffset_zero hστ ht,add_zero,inv_one]

theorem radialCoefficient_after {σ τ t : ℝ} (hστ : σ < τ) (ht : τ ≤ t) :
    radialCoefficient σ τ t = (t + radialShift σ τ)⁻¹ := by
  rw [radialCoefficient,radialOffset_after hστ ht]

def radialMoment (σ τ t : ℝ) : ℝ := t * radialCoefficient σ τ t

theorem radialMoment_hasDerivAt {σ τ : ℝ} (hστ : σ < τ) (t : ℝ) :
    HasDerivAt (radialMoment σ τ)
      ((1 + radialOffset σ τ t - t * radialSwitch σ τ t) /
        (1 + radialOffset σ τ t)^2) t := by
  have hd : HasDerivAt (radialMoment σ τ)
      (1 * radialCoefficient σ τ t + t * (-radialSwitch σ τ t /
        (1 + radialOffset σ τ t)^2)) t :=
    (hasDerivAt_id t).mul (radialCoefficient_hasDerivAt hστ t)
  have hn : 1 + radialOffset σ τ t ≠ 0 :=
    ne_of_gt (by linarith [radialOffset_nonneg hστ t])
  have he : 1 * radialCoefficient σ τ t + t * (-radialSwitch σ τ t /
        (1 + radialOffset σ τ t)^2) =
      (1 + radialOffset σ τ t - t * radialSwitch σ τ t) /
        (1 + radialOffset σ τ t)^2 := by
    simp only [one_mul,radialCoefficient]
    field_simp
    ring
  rw [←he]
  exact hd

theorem radialMoment_derivative_pos {σ τ : ℝ} (hστ : σ < τ) (hτ : τ < 1) (t : ℝ) :
    0 < (1 + radialOffset σ τ t - t * radialSwitch σ τ t) /
      (1 + radialOffset σ τ t)^2 := by
  apply div_pos _ (sq_pos_of_pos (by linarith [radialOffset_nonneg hστ t]))
  by_cases htσ : t ≤ σ
  · rw [radialOffset_zero hστ htσ,radialSwitch_zero hστ htσ]
    norm_num
  by_cases htτ : t ≤ τ
  · have ht1 : t < 1 := htτ.trans_lt hτ
    have hs0 := radialSwitch_nonneg σ τ t
    have hs1 := radialSwitch_le_one σ τ t
    have hφ := radialOffset_nonneg hστ t
    have hm : t * radialSwitch σ τ t < 1 := by
      by_cases ht0 : 0 ≤ t
      · exact (mul_le_mul_of_nonneg_left hs1 ht0).trans_lt (by simpa using ht1)
      · exact (mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge ht0) hs0).trans_lt zero_lt_one
    linarith
  · have htτ' : τ ≤ t := le_of_not_ge htτ
    rw [radialOffset_after hστ htτ',radialSwitch_one hστ htτ',mul_one]
    linarith [radialShift_pos hστ hτ]

@[simp] theorem radialMoment_zero {σ τ : ℝ} : radialMoment σ τ 0 = 0 := by
  simp [radialMoment]

theorem radialMoment_before {σ τ t : ℝ} (hστ : σ < τ) (ht : t ≤ σ) :
    radialMoment σ τ t = t := by
  rw [radialMoment,radialCoefficient_one hστ ht,mul_one]

theorem radialMoment_after {σ τ t : ℝ} (hστ : σ < τ) (ht : τ ≤ t) :
    radialMoment σ τ t = t / (t + radialShift σ τ) := by
  rw [radialMoment, radialCoefficient_after hστ ht,div_eq_mul_inv]

theorem radialMoment_tendsto_one {σ τ : ℝ} (hστ : σ < τ) :
    Tendsto (radialMoment σ τ) atTop (𝓝 1) := by
  have ht : Tendsto (fun t : ℝ => t + radialShift σ τ) atTop atTop :=
    Filter.tendsto_atTop_add_const_right _ _ tendsto_id
  have hc : Tendsto (fun t : ℝ => radialShift σ τ / (t + radialShift σ τ))
      atTop (𝓝 0) := tendsto_const_nhds.div_atTop ht
  have hl : Tendsto (fun t : ℝ => 1 - radialShift σ τ / (t + radialShift σ τ))
      atTop (𝓝 1) := by simpa using tendsto_const_nhds.sub hc
  apply hl.congr'
  filter_upwards [eventually_ge_atTop τ, eventually_gt_atTop (-radialShift σ τ)] with t htτ ht0
  rw [radialMoment_after hστ htτ]
  have hn : t + radialShift σ τ ≠ 0 := by linarith
  field_simp
  ring



end HigherDimensionalBallPacking.Rigidity
end

end OAI
