import Mathlib

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
section ProfileForms
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
abbrev ProfileForm (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] := E →L[ℝ] E →L[ℝ] ℝ

def profileTrace (H : ProfileForm E) (a v : E) : ℝ := H a a + (1 + ‖a‖ ^ 2) * H v v

def profileStrict (H : ProfileForm E) (a : E) : Prop :=
  ∃ v : E, ‖v‖ = 1 ∧ inner ℝ a v = 0 ∧ 0 < profileTrace H a v

def profileFull (H : ProfileForm E) (a : E) : Prop :=
  ∀ v : E, ‖v‖ = 1 → inner ℝ a v = 0 → 0 < profileTrace H a v

omit [FiniteDimensional ℝ E] in
lemma continuous_profileTrace : Continuous (fun p : (ProfileForm E × E) × E =>
    profileTrace p.1.1 p.1.2 p.2) := by
  have hH : Continuous (fun p : (ProfileForm E × E) × E => p.1.1) := continuous_fst.fst
  have ha : Continuous (fun p : (ProfileForm E × E) × E => p.1.2) := continuous_fst.snd
  have hv : Continuous (fun p : (ProfileForm E × E) × E => p.2) := continuous_snd
  exact (hH.clm_apply ha |>.clm_apply ha).add
    ((continuous_const.add (ha.norm.pow 2)).mul (hH.clm_apply hv |>.clm_apply hv))

omit [FiniteDimensional ℝ E] in

theorem profileStrict_eventually {H : ProfileForm E} {a : E} (ha : a ≠ 0)
    (hs : profileStrict H a) : ∀ᶠ p : ProfileForm E × E in 𝓝 (H,a), profileStrict p.1 p.2 := by
  obtain ⟨v,hv,hav,hpos⟩ := hs
  let w : ProfileForm E × E → E := fun p => v - (inner ℝ p.2 v / ‖p.2‖ ^ 2) • p.2
  have han : ‖a‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr ha)
  have hsnd : Continuous (fun p : ProfileForm E × E => p.2) := continuous_snd
  have hw : ContinuousAt w (H,a) := by
    exact continuousAt_const.sub (((hsnd.inner continuous_const).continuousAt.div
      (hsnd.norm.pow 2).continuousAt han).smul hsnd.continuousAt)
  have hwa : w (H,a) = v := by simp [w,hav]
  let z : ProfileForm E × E → E := fun p => ‖w p‖⁻¹ • w p
  have hz : ContinuousAt z (H,a) :=
    (hw.norm.inv₀ (by rw [hwa,hv]; norm_num)).smul hw
  have hza : z (H,a) = v := by simp [z,hwa,hv]
  have hp : ∀ᶠ p : ProfileForm E × E in 𝓝 (H,a), 0 < profileTrace p.1 p.2 (z p) := by
    have hc := continuous_profileTrace.continuousAt.comp
      (continuousAt_id.prodMk hz)
    apply hc.eventually (Ioi_mem_nhds ?_)
    simpa [hza] using hpos
  have hane : ∀ᶠ p : ProfileForm E × E in 𝓝 (H,a), p.2 ≠ 0 :=
    continuous_snd.continuousAt.eventually_ne ha
  have hwne : ∀ᶠ p : ProfileForm E × E in 𝓝 (H,a), w p ≠ 0 :=
    hw.eventually_ne (by rw [hwa]; exact norm_ne_zero_iff.mp (by rw [hv]; norm_num))
  filter_upwards [hp,hane,hwne] with p hp hpa hpw
  refine ⟨z p,?_,?_,hp⟩
  · simp [z,norm_smul,norm_ne_zero_iff.mpr hpw]
  · have hpn : ‖p.2‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hpa)
    have hwperp : inner ℝ p.2 (w p) = 0 := by
      simp only [w, inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq]
      field_simp
      ring
    simp [z,inner_smul_right,hwperp]

theorem isOpen_profileFull : IsOpen {p : ProfileForm E × E | profileFull p.1 p.2} := by
  let S : Set E := sphere 0 1
  let : CompactSpace S := isCompact_iff_compactSpace.mp (isCompact_sphere 0 1)
  let B : Set ((ProfileForm E × E) × S) := {p | inner ℝ p.1.2 (p.2 : E) = 0 ∧
    profileTrace p.1.1 p.1.2 p.2 ≤ 0}
  have hB : IsClosed B := by
    apply IsClosed.inter
    · exact isClosed_eq (continuous_fst.snd.inner (continuous_subtype_val.comp continuous_snd)) continuous_const
    · exact isClosed_le
        (continuous_profileTrace.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))) continuous_const
  have hC : IsClosed (Prod.fst '' B) := isClosedMap_fst_of_compactSpace _ hB
  convert hC.isOpen_compl using 1
  ext p
  simp only [mem_ofPred_eq, mem_compl_iff, mem_image, B]
  constructor
  · intro hp
    rintro ⟨y,hy,hyp⟩
    subst p
    exact (not_le_of_gt (hp y.2 (by simpa only [S, mem_sphere_zero_iff_norm] using y.2.property) hy.1)) hy.2
  · intro hp v hv hav
    by_contra hh
    apply hp
    exact ⟨(p,⟨v,by simpa [S,mem_sphere_zero_iff_norm] using hv⟩),⟨hav,not_lt.mp hh⟩,rfl⟩
end ProfileForms

variable {X : Type*} [TopologicalSpace X]

theorem compact_positive_linear_penalty {K : Set X} (hK : IsCompact K)
    {A B : X → ℝ} (hA : Continuous A) (hB : Continuous B)
    (hAn : ∀ x, 0 ≤ A x) (hker : ∀ x ∈ K, A x = 0 → 0 < B x) :
    ∃ n : ℕ, ∀ x ∈ K, 0 < B x + n * A x := by
  let U : ℕ → Set X := fun n => {x | 0 < B x + n * A x}
  have ho : ∀ n, IsOpen (U n) := fun n => isOpen_lt continuous_const (hB.add (continuous_const.mul hA))
  have hc : K ⊆ ⋃ n, U n := by
    intro x hx
    by_cases ha : A x = 0
    · exact mem_iUnion.mpr ⟨0,by simpa [U,ha] using hker x hx ha⟩
    · have hap : 0 < A x := lt_of_le_of_ne (hAn x) (Ne.symm ha)
      obtain ⟨n,hn⟩ := exists_nat_gt ((-B x) / A x)
      refine mem_iUnion.mpr ⟨n,?_⟩
      change 0 < B x + n * A x
      have hh := (div_lt_iff₀ hap).mp hn
      linarith
  have hd : Directed (· ⊆ ·) U := by
    intro i j
    refine ⟨max i j,?_,?_⟩ <;> intro x hx
    · change 0 < B x + i * A x at hx
      change 0 < B x + (max i j : ℕ) * A x
      have hh : (i : ℝ) * A x ≤ (max i j : ℕ) * A x := mul_le_mul_of_nonneg_right (by exact_mod_cast le_max_left i j) (hAn x)
      linarith
    · change 0 < B x + j * A x at hx
      change 0 < B x + (max i j : ℕ) * A x
      have hh : (j : ℝ) * A x ≤ (max i j : ℕ) * A x := mul_le_mul_of_nonneg_right (by exact_mod_cast le_max_right i j) (hAn x)
      linarith
  exact hK.elim_directed_cover U ho hc hd

end

section
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

def profileRankOne (l : E →L[ℝ] ℝ) : ProfileForm E := l.smulRight l

omit [FiniteDimensional ℝ E] in
@[simp] lemma profileRankOne_apply (l : E →L[ℝ] ℝ) (v w : E) :
    profileRankOne l v w = l v * l w := rfl

omit [FiniteDimensional ℝ E] in
lemma profileTrace_add_rankOne (H : ProfileForm E) (a v : E)
    (l : E →L[ℝ] ℝ) (c : ℝ) :
    profileTrace (H + c • profileRankOne l) a v =
      profileTrace H a v + c * ((l a)^2 + (1 + ‖a‖^2) * (l v)^2) := by
  change H a a + c * (l a * l a) + (1 + ‖a‖^2) * (H v v + c * (l v * l v)) =
    H a a + (1 + ‖a‖^2) * H v v + c * ((l a)^2 + (1 + ‖a‖^2) * (l v)^2)
  ring

omit [FiniteDimensional ℝ E] in
lemma profileStrict_rankOne (H : ProfileForm E) (a : E) (l : E →L[ℝ] ℝ)
    (ha : l a = 0) (hv : ∃ v, ‖v‖ = 1 ∧ inner ℝ a v = 0 ∧ l v = 0 ∧
      0 < profileTrace H a v) (c : ℝ) : profileStrict (H + c • profileRankOne l) a := by
  obtain ⟨v,hv,hav,hlv,hpos⟩ := hv
  refine ⟨v,hv,hav,?_⟩
  simpa [profileTrace_add_rankOne,ha,hlv] using hpos

omit [FiniteDimensional ℝ E] in
theorem isOpen_profileStrict_nonzero :
    IsOpen {p : ProfileForm E × E | p.2 ≠ 0 ∧ profileStrict p.1 p.2} := by
  rw [isOpen_iff_mem_nhds]
  intro p hp
  exact (continuous_snd.continuousAt.eventually_ne hp.1).and
    (profileStrict_eventually hp.1 hp.2)

omit [FiniteDimensional ℝ E] in
theorem compact_strict_profile_stability {K : Set (ProfileForm E × E)}
    (hK : IsCompact K) (hs : ∀ p ∈ K, p.2 ≠ 0 ∧ profileStrict p.1 p.2) :
    ∃ ε > 0, ∀ p ∈ K, ∀ q : ProfileForm E × E, dist q p < ε →
      q.2 ≠ 0 ∧ profileStrict q.1 q.2 := by
  let : PseudoEMetricSpace (ProfileForm E × E) :=
    (inferInstance : PseudoMetricSpace (ProfileForm E × E)).toPseudoEMetricSpace
  let U : Set (ProfileForm E × E) := {p | p.2 ≠ 0 ∧ profileStrict p.1 p.2}
  have hU : IsOpen U := isOpen_profileStrict_nonzero
  have hKU : K ⊆ U := hs
  obtain ⟨ε,hε,he⟩ := hK.exists_thickening_subset_open hU hKU
  refine ⟨ε,hε,?_⟩
  intro p hp q hq
  exact he (mem_thickening_iff.mpr ⟨p,hp,hq⟩)

theorem compact_full_profile_stability {K : Set (ProfileForm E × E)}
    (hK : IsCompact K) (hs : ∀ p ∈ K, profileFull p.1 p.2) :
    ∃ ε > 0, ∀ p ∈ K, ∀ q : ProfileForm E × E, dist q p < ε →
      profileFull q.1 q.2 := by
  let : PseudoEMetricSpace (ProfileForm E × E) :=
    (inferInstance : PseudoMetricSpace (ProfileForm E × E)).toPseudoEMetricSpace
  let U : Set (ProfileForm E × E) := {p | profileFull p.1 p.2}
  have hU : IsOpen U := isOpen_profileFull
  have hKU : K ⊆ U := hs
  obtain ⟨ε,hε,he⟩ := hK.exists_thickening_subset_open hU hKU
  refine ⟨ε,hε,?_⟩
  intro p hp q hq
  exact he (mem_thickening_iff.mpr ⟨p,hp,hq⟩)

theorem preparation_rankOne_full {X : Type*} [TopologicalSpace X]
    {K : Set X} (hK : IsCompact K) (H : X → ProfileForm E) (a : X → E)
    (l : X → E →L[ℝ] ℝ) (hH : Continuous H) (ha : Continuous a) (hl : Continuous l)
    (hker : ∀ x ∈ K, ∀ v, ‖v‖ = 1 → inner ℝ (a x) v = 0 → l x v = 0 →
      0 < profileTrace (H x) (a x) v) :
    ∃ C : ℕ, ∀ x ∈ K, ∀ c : ℝ, C ≤ c → profileFull (H x + c • profileRankOne (l x)) (a x) := by
  let S : Set (X × E) := {p | p.1 ∈ K ∧ ‖p.2‖ = 1 ∧ inner ℝ (a p.1) p.2 = 0}
  have hS : IsCompact S := by
    have heq : S = (K ×ˢ sphere (0 : E) 1) ∩ {p | inner ℝ (a p.1) p.2 = 0} := by
      ext p
      simp only [S,mem_ofPred_eq,mem_inter_iff, mem_prod,mem_sphere_zero_iff_norm]
      tauto
    rw [heq]
    exact (hK.prod (isCompact_sphere 0 1)).inter_right
      (isClosed_eq ((ha.comp continuous_fst).inner continuous_snd) continuous_const)
  let A : X × E → ℝ := fun p => (l p.1 (a p.1))^2 + (1 + ‖a p.1‖^2) * (l p.1 p.2)^2
  let B : X × E → ℝ := fun p => profileTrace (H p.1) (a p.1) p.2
  have hA : Continuous A := by
    exact (((hl.comp continuous_fst).clm_apply (ha.comp continuous_fst)).pow 2).add
      ((continuous_const.add ((ha.comp continuous_fst).norm.pow 2)).mul
        (((hl.comp continuous_fst).clm_apply continuous_snd).pow 2))
  have hB : Continuous B := continuous_profileTrace.comp
    (((hH.prodMk ha).comp continuous_fst).prodMk continuous_snd)
  have hAn : ∀ p, 0 ≤ A p := by intro p; dsimp [A]; positivity
  have hAk : ∀ p ∈ S, A p = 0 → 0 < B p := by
    intro p hp heq
    have hsq : (l p.1 p.2)^2 = 0 := by
      have hh : 0 < 1 + ‖a p.1‖^2 := by positivity
      dsimp [A] at heq
      nlinarith [sq_nonneg (l p.1 (a p.1)),sq_nonneg (l p.1 p.2)]
    exact hker p.1 hp.1 p.2 hp.2.1 hp.2.2 (sq_eq_zero_iff.mp hsq)
  obtain ⟨C,hC⟩ := compact_positive_linear_penalty hS hA hB hAn hAk
  refine ⟨C,?_⟩
  intro x hx c hc v hv hav
  rw [profileTrace_add_rankOne]
  have hh := hC (x,v) ⟨hx,hv,hav⟩
  have hm := mul_le_mul_of_nonneg_right hc (hAn (x,v))
  change 0 < B (x,v) + c * A (x,v)
  linarith

end

open Set Filter Function Metric
open scoped Topology
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem compact_full_profile_margin {X : Type*} [TopologicalSpace X]
    {K : Set X} (hK : IsCompact K) (H : X → ProfileForm E) (a : X → E)
    (hH : Continuous H) (ha : Continuous a)
    (hfull : ∀ x ∈ K, profileFull (H x) (a x)) :
    ∃ m : ℝ, 0 < m ∧ m ≤ 1 ∧ ∀ x ∈ K, ∀ v,
      ‖v‖ = 1 → inner ℝ (a x) v = 0 → m ≤ profileTrace (H x) (a x) v := by
  let S : Set (X × E) := {p | p.1 ∈ K ∧ ‖p.2‖ = 1 ∧ inner ℝ (a p.1) p.2 = 0}
  have hS : IsCompact S := by
    have heq : S = (K ×ˢ sphere (0 : E) 1) ∩ {p | inner ℝ (a p.1) p.2 = 0} := by
      ext p
      simp only [S, mem_ofPred_eq, mem_inter_iff, mem_prod, mem_sphere_zero_iff_norm]
      tauto
    rw [heq]
    exact (hK.prod (isCompact_sphere 0 1)).inter_right
      (isClosed_eq ((ha.comp continuous_fst).inner continuous_snd) continuous_const)
  let B : X × E → ℝ := fun p => profileTrace (H p.1) (a p.1) p.2
  have hB : Continuous B := continuous_profileTrace.comp
    (((hH.prodMk ha).comp continuous_fst).prodMk continuous_snd)
  by_cases hne : S.Nonempty
  · obtain ⟨p, hp, hmin⟩ := hS.exists_isMinOn hne hB.continuousOn
    have hpB : 0 < B p := hfull p.1 hp.1 p.2 hp.2.1 hp.2.2
    refine ⟨min (B p) 1, lt_min hpB zero_lt_one, min_le_right _ _, ?_⟩
    intro x hx v hv hav
    have hh : B p ≤ B (x,v) := hmin (show (x,v) ∈ S from ⟨hx, hv, hav⟩)
    exact (min_le_left _ _).trans hh
  · refine ⟨1, zero_lt_one, le_rfl, ?_⟩
    intro x hx v hv hav
    exact (hne ⟨(x,v), hx, hv, hav⟩).elim

omit [FiniteDimensional ℝ E] in

lemma profileForm_diag_sub_bound (H : ProfileForm E) (a b : E) :
    |H a a - H b b| ≤ ‖H‖ * (‖a‖ + ‖b‖) * ‖a-b‖ := by
  have he : H a a - H b b = H (a-b) a + H b (a-b) := by
    simp only [map_sub, sub_apply]
    ring
  rw [he]
  calc
    _ ≤ ‖H (a-b) a‖ + ‖H b (a-b)‖ := norm_add_le _ _
    _ ≤ ‖H‖ * ‖a-b‖ * ‖a‖ + ‖H‖ * ‖b‖ * ‖a-b‖ :=
      add_le_add (H.le_opNorm₂ _ _) (H.le_opNorm₂ _ _)
    _ = _ := by ring

omit [FiniteDimensional ℝ E] in

theorem exists_transverse_unit_near (a a' v : E) (ha : a ≠ 0)
    (hv : ‖v‖ = 1) (hav : inner ℝ a' v = 0)
    (hsmall : ‖a'-a‖ ≤ ‖a‖ / 2) :
    ∃ w : E, ‖w‖ = 1 ∧ inner ℝ a w = 0 ∧
      ‖v-w‖ ≤ 2 * ‖a'-a‖ / ‖a‖ := by
  have han : 0 < ‖a‖ := norm_pos_iff.mpr ha
  let c := inner ℝ a v / ‖a‖^2
  let z := v - c • a
  have haz : inner ℝ a z = 0 := by
    dsimp [z,c]
    rw [inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq]
    field_simp
    ring
  have hinner : |inner ℝ a v| ≤ ‖a'-a‖ := by
    have he : inner ℝ a v = inner ℝ (a-a') v := by
      rw [inner_sub_left, hav, sub_zero]
    rw [he]
    simpa [hv, norm_sub_rev] using abs_real_inner_le_norm (a-a') v
  have hcv : ‖c • a‖ ≤ ‖a'-a‖ / ‖a‖ := by
    calc
      _ = |inner ℝ a v| / ‖a‖ := by
        simp only [norm_smul, Real.norm_eq_abs, c, abs_div, abs_pow, abs_norm]
        field_simp
      _ ≤ _ := div_le_div_of_nonneg_right hinner han.le
  have hcvhalf : ‖c • a‖ ≤ 1/2 := hcv.trans ((div_le_iff₀ han).mpr (by linarith))
  have hzlower : 1/2 ≤ ‖z‖ := by
    have hh : ‖v‖ ≤ ‖z‖ + ‖c • a‖ := by
      simpa only [z, sub_add_cancel] using norm_add_le (v-c • a) (c • a)
    rw [hv] at hh
    linarith
  have hzn : z ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt (by linarith : 0 < ‖z‖))
  let w := ‖z‖⁻¹ • z
  have hw : ‖w‖ = 1 := by
    simp [w, norm_smul, norm_ne_zero_iff.mpr hzn]
  have hdw : ‖w-z‖ ≤ ‖v-z‖ := by
    calc
      _ = |1-‖z‖| := by
        rw [show w-z = (‖z‖⁻¹-1) • z by dsimp [w]; rw [sub_smul, one_smul]]
        rw [norm_smul, Real.norm_eq_abs]
        calc
          _ = |(‖z‖⁻¹-1)*‖z‖| := by rw [abs_mul, abs_norm]
          _ = _ := by rw [sub_mul, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hzn), one_mul]
      _ ≤ _ := by simpa [hv] using abs_norm_sub_norm_le v z
  have hvz : ‖v-z‖ ≤ ‖a'-a‖ / ‖a‖ := by
    simpa [z] using hcv
  refine ⟨w,hw,?_,?_⟩
  · simp [w,inner_smul_right,haz]
  · calc
      _ ≤ ‖v-z‖ + ‖z-w‖ := norm_sub_le_norm_sub_add_norm_sub v z w
      _ = ‖v-z‖ + ‖w-z‖ := by rw [norm_sub_rev z w]
      _ ≤ ‖a'-a‖ / ‖a‖ + ‖a'-a‖ / ‖a‖ := add_le_add hvz (hdw.trans hvz)
      _ = _ := by ring
omit [FiniteDimensional ℝ E] in
lemma profileTrace_abs_bound (H : ProfileForm E) (a v : E) (R : ℝ)
    (ha : ‖a‖ ≤ R) (hv : ‖v‖ = 1) :
    |profileTrace H a v| ≤ ‖H‖ * (1 + 2*R^2) := by
  have hR : 0 ≤ R := (norm_nonneg _).trans ha
  have haa : |H a a| ≤ ‖H‖ * R^2 := by
    calc
      _ ≤ ‖H‖ * ‖a‖ * ‖a‖ := H.le_opNorm₂ a a
      _ ≤ ‖H‖ * R * R := mul_le_mul
        (mul_le_mul_of_nonneg_left ha (norm_nonneg H)) ha
        (norm_nonneg _) (mul_nonneg (norm_nonneg H) hR)
      _ = _ := by ring
  have hvv : |H v v| ≤ ‖H‖ := by simpa [hv] using H.le_opNorm₂ v v
  have hsq : ‖a‖^2 ≤ R^2 := sq_le_sq₀ (norm_nonneg _) hR |>.mpr ha
  calc
    _ ≤ |H a a| + |(1+‖a‖^2) * H v v| := abs_add_le _ _
    _ = |H a a| + (1+‖a‖^2)*|H v v| := by
      rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 1+‖a‖^2)]
    _ ≤ ‖H‖*R^2 + (1+R^2)*‖H‖ := add_le_add haa
      (mul_le_mul (by linarith) hvv (abs_nonneg _) (by positivity))
    _ = _ := by ring

omit [FiniteDimensional ℝ E] in
lemma profileTrace_sub_bound (H : ProfileForm E) (a a' v w : E) (R : ℝ)
    (ha : ‖a‖ ≤ R) (ha' : ‖a'‖ ≤ R) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) :
    |profileTrace H a' v - profileTrace H a w| ≤
      4*‖H‖*R*‖a'-a‖ + 2*‖H‖*(1+R^2)*‖v-w‖ := by
  have hR : 0 ≤ R := (norm_nonneg _).trans ha
  have hdiag : |H a' a' - H a a| ≤ 2*‖H‖*R*‖a'-a‖ := by
    calc
      _ ≤ ‖H‖*(‖a'‖+‖a‖)*‖a'-a‖ := profileForm_diag_sub_bound H a' a
      _ ≤ ‖H‖*(R+R)*‖a'-a‖ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (add_le_add ha' ha) (norm_nonneg H)) (norm_nonneg _)
      _ = _ := by ring
  have hsq : |‖a'‖^2-‖a‖^2| ≤ 2*R*‖a'-a‖ := by
    rw [show ‖a'‖^2-‖a‖^2 = (‖a'‖-‖a‖)*(‖a'‖+‖a‖) by ring,
      abs_mul, abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
    calc
      _ ≤ ‖a'-a‖*(R+R) := mul_le_mul (abs_norm_sub_norm_le _ _) (add_le_add ha' ha)
        (by positivity) (norm_nonneg _)
      _ = _ := by ring
  have hvv : |H v v| ≤ ‖H‖ := by simpa [hv] using H.le_opNorm₂ v v
  have hvw : |H v v - H w w| ≤ 2*‖H‖*‖v-w‖ := by
    simpa [hv,hw,show (1:ℝ)+1=2 by norm_num,mul_comm,mul_left_comm]
      using profileForm_diag_sub_bound H v w
  have hsqa : ‖a‖^2 ≤ R^2 := (sq_le_sq₀ (norm_nonneg _) hR).mpr ha
  have he : profileTrace H a' v - profileTrace H a w =
      (H a' a'-H a a)+(‖a'‖^2-‖a‖^2)*H v v+
        (1+‖a‖^2)*(H v v-H w w) := by unfold profileTrace; ring
  rw [he]
  calc
    _ ≤ |H a' a'-H a a| + |(‖a'‖^2-‖a‖^2)*H v v| +
        |(1+‖a‖^2)*(H v v-H w w)| := (abs_add_le _ _).trans
      (add_le_add (abs_add_le _ _) le_rfl)
    _ = |H a' a'-H a a| + |‖a'‖^2-‖a‖^2| * |H v v| +
        (1+‖a‖^2)*|H v v-H w w| := by
      rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : 0 ≤ 1+‖a‖^2)]
    _ ≤ 2*‖H‖*R*‖a'-a‖ + (2*R*‖a'-a‖)*‖H‖ +
        (1+R^2)*(2*‖H‖*‖v-w‖) := add_le_add
      (add_le_add hdiag (mul_le_mul hsq hvv (abs_nonneg _) (by positivity)))
      (mul_le_mul (by linarith) hvw (abs_nonneg _) (by positivity))
    _ = _ := by ring

omit [FiniteDimensional ℝ E] in

theorem profileTrace_base_lower (H : ProfileForm E) (a a' v : E)
    (m α B R : ℝ) (hm : m ≤ 1) (hα : 0 < α) (ha0 : α ≤ ‖a‖)
    (hH : ‖H‖ ≤ B) (ha : ‖a‖ ≤ R) (ha' : ‖a'‖ ≤ R)
    (hv : ‖v‖ = 1) (hav : inner ℝ a' v = 0)
    (hmargin : ∀ w, ‖w‖ = 1 → inner ℝ a w = 0 → m ≤ profileTrace H a w) :
    m - (4*B*R + 4*B*(1+R^2)/α + 2*(1+B*(1+2*R^2))/α) * ‖a'-a‖ ≤
      profileTrace H a' v := by
  have hB : 0 ≤ B := (norm_nonneg H).trans hH
  have hR : 0 ≤ R := (norm_nonneg _).trans ha
  have han : 0 < ‖a‖ := hα.trans_le ha0
  have haN : a ≠ 0 := norm_pos_iff.mp han
  let C₁ : ℝ := 4*B*R+4*B*(1+R^2)/α
  let C₂ : ℝ := 2*(1+B*(1+2*R^2))/α
  have hC₁ : 0 ≤ C₁ := by dsimp [C₁]; positivity
  have hC₂ : 0 ≤ C₂ := by dsimp [C₂]; positivity
  change m-(C₁+C₂)*‖a'-a‖ ≤ _
  by_cases hsmall : ‖a'-a‖ ≤ ‖a‖/2
  · obtain ⟨w,hw,haw,hdw⟩ := exists_transverse_unit_near a a' v haN hv hav hsmall
    have hdw' : ‖v-w‖ ≤ 2*‖a'-a‖/α := hdw.trans
      (div_le_div_of_nonneg_left (by positivity) hα ha0)
    have hdiff : |profileTrace H a' v-profileTrace H a w| ≤ C₁*‖a'-a‖ := by
      calc
        _ ≤ 4*‖H‖*R*‖a'-a‖+2*‖H‖*(1+R^2)*‖v-w‖ :=
          profileTrace_sub_bound H a a' v w R ha ha' hv hw
        _ ≤ 4*B*R*‖a'-a‖+2*B*(1+R^2)*(2*‖a'-a‖/α) := add_le_add
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hH (by norm_num)) hR) (norm_nonneg _))
          (mul_le_mul (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hH (by norm_num)) (by positivity))
            hdw' (norm_nonneg _) (by positivity))
        _ = _ := by dsimp [C₁]; ring
    have hh := neg_abs_le (profileTrace H a' v-profileTrace H a w)
    have hmm := hmargin w hw haw
    have hmore := mul_nonneg hC₂ (norm_nonneg (a'-a))
    nlinarith only [hdiff,hh,hmm,hmore]
  · have hd : α/2 ≤ ‖a'-a‖ := by linarith [not_le.mp hsmall]
    have hlarge : 1+B*(1+2*R^2) ≤ C₂*‖a'-a‖ := by
      calc
        _ = C₂*(α/2) := by dsimp [C₂]; field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_left hd hC₂
    have hbound : |profileTrace H a' v| ≤ B*(1+2*R^2) :=
      (profileTrace_abs_bound H a' v R ha' hv).trans
        (mul_le_mul_of_nonneg_right hH (by positivity))
    have hn := neg_abs_le (profileTrace H a' v)
    have hmore := mul_nonneg hC₁ (norm_nonneg (a'-a))
    nlinarith only [hm,hlarge,hbound,hn,hmore]

theorem compact_profileTrace_base_lower {X : Type*} [TopologicalSpace X]
    {K : Set X} (hK : IsCompact K) (H : X → ProfileForm E) (a : X → E)
    (hH : Continuous H) (ha : Continuous a)
    (hfull : ∀ x ∈ K, profileFull (H x) (a x))
    (hane : ∀ x ∈ K, a x ≠ 0) (R : ℝ) (hR : ∀ x ∈ K, ‖a x‖ ≤ R) :
    ∃ m C : ℝ, 0 < m ∧ 0 < C ∧ ∀ x ∈ K, ∀ a' v,
      ‖a'‖ ≤ R → ‖v‖ = 1 → inner ℝ a' v = 0 →
      m-C*‖a'-a x‖ ≤ profileTrace (H x) a' v := by
  obtain ⟨m,hm,hm1,hmargin⟩ := compact_full_profile_margin hK H a hH ha hfull
  by_cases hne : K.Nonempty
  · obtain ⟨p,hp,hmin⟩ := hK.exists_isMinOn hne ha.norm.continuousOn
    let α := ‖a p‖
    have hα : 0 < α := norm_pos_iff.mpr (hane p hp)
    have hαa : ∀ x ∈ K, α ≤ ‖a x‖ := fun x hx => hmin hx
    obtain ⟨B',hB'⟩ := hK.exists_bound_of_continuousOn (f := H) hH.continuousOn
    let B := |B'|
    have hB : 0 ≤ B := abs_nonneg _
    have hBH : ∀ x ∈ K, ‖H x‖ ≤ B := fun x hx => (hB' x hx).trans (le_abs_self _)
    have hR0 : 0 ≤ R := (norm_nonneg _).trans (hR p hp)
    let C := 4*B*R+4*B*(1+R^2)/α+2*(1+B*(1+2*R^2))/α
    have hC : 0 < C := by dsimp [C]; positivity
    refine ⟨m,C,hm,hC,?_⟩
    intro x hx a' v ha' hv hav
    exact profileTrace_base_lower (H x) (a x) a' v m α B R hm1 hα (hαa x hx)
      (hBH x hx) (hR x hx) ha' hv hav (hmargin x hx)
  · refine ⟨m,1,hm,zero_lt_one,?_⟩
    intro x hx
    exact (hne ⟨x,hx⟩).elim



end YauCounterexamples
end

end OAI
