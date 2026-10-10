import OAI.Combinatorics.SparsestCut.ContractionBounds

namespace OAI

universe u1 u2 u3 u4 u5 u6 u7 u8 u9 u10

open scoped BigOperators Topology NNReal RealInnerProductSpace InnerProductSpace Matrix ContDiff ENNReal
open MeasureTheory ProbabilityTheory Set Filter Matrix

noncomputable section

namespace UniformSparsestCut.InterfaceStep
variable {ι : Type u1} {V : Type u2} [DecidableEq ι] [AddCommGroup V]

lemma telescoping_events (s : Finset ι) (t : ι → ℝ) (ht : Set.InjOn t s)
    (F : Finset ι → V) :
    (∑ i ∈ s, (F (s.filter (fun j => t j ≤ t i))-F (s.filter (fun j => t j < t i)))) =
      F s-F ∅ := by
  revert ht
  induction s using Finset.strongInductionOn with
  | _ s ih =>
    intro ht
    by_cases hs : s.Nonempty
    · obtain ⟨a,ha,hmax⟩ := s.exists_max_image t hs
      let r := s.erase a
      have hr : r ⊂ s := Finset.erase_ssubset ha
      have htr : Set.InjOn t (↑r : Set ι) := ht.mono (by intro i hi; exact Finset.mem_of_mem_erase hi)
      have hind := ih r hr htr
      have hle : s.filter (fun j => t j ≤ t a) = s := by
        apply Finset.filter_eq_self.mpr; intro j hj; exact hmax j hj
      have hlt : s.filter (fun j => t j < t a) = r := by
        ext j
        simp only [Finset.mem_filter, r, Finset.mem_erase]
        constructor
        · rintro ⟨hj,h⟩; exact ⟨fun he => by simp [he] at h,hj⟩
        · rintro ⟨hne,hj⟩
          exact ⟨hj,lt_of_le_of_ne (hmax j hj) (fun he => hne (ht hj ha he))⟩
      have hfilters (i : ι) (hi : i ∈ r) :
          s.filter (fun j => t j ≤ t i) = r.filter (fun j => t j ≤ t i) ∧
          s.filter (fun j => t j < t i) = r.filter (fun j => t j < t i) := by
        have hia : t i < t a := (Finset.mem_filter.mp (show i ∈ s.filter (fun j => t j < t a) by rw [hlt]; exact hi)).2
        constructor <;> (ext j; simp only [Finset.mem_filter, r, Finset.mem_erase]; constructor)
        · rintro ⟨hj,hji⟩
          exact ⟨⟨fun he => by subst j; linarith,hj⟩,hji⟩
        · rintro ⟨⟨_,hj⟩,hji⟩; exact ⟨hj,hji⟩
        · rintro ⟨hj,hji⟩
          exact ⟨⟨fun he => by subst j; linarith,hj⟩,hji⟩
        · rintro ⟨⟨_,hj⟩,hji⟩; exact ⟨hj,hji⟩
      rw [← Finset.sum_erase_add _ _ ha, hle,hlt]
      change (∑ i ∈ r, _) + (F s-F r) = _
      have he : (∑ i ∈ r, (F (s.filter (fun j => t j ≤ t i))-F (s.filter (fun j => t j < t i)))) =
          ∑ i ∈ r, (F (r.filter (fun j => t j ≤ t i))-F (r.filter (fun j => t j < t i))) := by
        apply Finset.sum_congr rfl; intro i hi; rw [(hfilters i hi).1,(hfilters i hi).2]
      rw [he,hind]
      abel
    · simp [Finset.not_nonempty_iff_eq_empty.mp hs]

lemma threshold_decomposition (s : Finset ι) (t : ι → ℝ) (ht : Set.InjOn t s)
    (F : Finset ι → V) (x : ℝ) :
    F (s.filter (fun i => t i < x)) = F ∅+
      ∑ i ∈ s, if t i < x then
        F (s.filter (fun j => t j ≤ t i))-F (s.filter (fun j => t j < t i)) else 0 := by
  let r := s.filter (fun i => t i < x)
  have htr : Set.InjOn t (↑r : Set ι) := ht.mono (by intro i hi; exact (Finset.mem_filter.mp hi).1)
  have h := telescoping_events r t htr F
  have hfilters (i : ι) (hi : i ∈ r) :
      r.filter (fun j => t j ≤ t i) = s.filter (fun j => t j ≤ t i) ∧
      r.filter (fun j => t j < t i) = s.filter (fun j => t j < t i) := by
    have hix : t i < x := (Finset.mem_filter.mp hi).2
    constructor <;> (ext j; simp only [r,Finset.mem_filter]; constructor)
    · rintro ⟨⟨hj,_⟩,hji⟩; exact ⟨hj,hji⟩
    · rintro ⟨hj,hji⟩; exact ⟨⟨hj,lt_of_le_of_lt hji hix⟩,hji⟩
    · rintro ⟨⟨hj,_⟩,hji⟩; exact ⟨hj,hji⟩
    · rintro ⟨hj,hji⟩; exact ⟨⟨hj,hji.trans hix⟩,hji⟩
  have he : (∑ i ∈ r, (F (r.filter (fun j => t j ≤ t i))-F (r.filter (fun j => t j < t i)))) =
      ∑ i ∈ r, (F (s.filter (fun j => t j ≤ t i))-F (s.filter (fun j => t j < t i))) := by
    apply Finset.sum_congr rfl; intro i hi; rw [(hfilters i hi).1,(hfilters i hi).2]
  rw [he] at h
  rw [← Finset.sum_filter]
  change F r = F ∅+_
  rw [h]
  abel

section Integral
variable {W : Type u3} [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]

lemma integral_deriv_eq_zero {φ : ℝ → ℝ} (hφ : ContDiff ℝ 1 φ)
    (hc : HasCompactSupport φ) : ∫ x, deriv φ x = 0 := by
  apply integral_eq_zero_of_hasDerivAt_of_integrable
    (fun x => (hφ.differentiable one_ne_zero x).hasDerivAt)
  · exact (hφ.continuous_deriv le_rfl).integrable_of_hasCompactSupport hc.deriv
  · exact hφ.continuous.integrable_of_hasCompactSupport hc

lemma threshold_integral_deriv (s : Finset ι) (t : ι → ℝ) (ht : Set.InjOn t s)
    (F : Finset ι → W) {φ : ℝ → ℝ} (hφ : ContDiff ℝ 1 φ)
    (hc : HasCompactSupport φ) :
    (∫ x, deriv φ x • F (s.filter (fun i => t i < x))) =
      -∑ i ∈ s, φ (t i) •
        (F (s.filter (fun j => t j ≤ t i))-F (s.filter (fun j => t j < t i))) := by
  let Δ := fun i => F (s.filter (fun j => t j ≤ t i))-F (s.filter (fun j => t j < t i))
  have hd : Integrable (deriv φ) :=
    (hφ.continuous_deriv le_rfl).integrable_of_hasCompactSupport hc.deriv
  have hi (i : ι) : Integrable (fun x => deriv φ x • (if t i < x then Δ i else 0)) := by
    have he : (fun x => deriv φ x • (if t i < x then Δ i else 0)) =
        (Ioi (t i)).indicator (fun x => deriv φ x • Δ i) := by
      funext x; by_cases hx : t i < x <;> simp [hx]
    rw [he]
    exact (hd.smul_const _).indicator measurableSet_Ioi
  have he (x : ℝ) : deriv φ x • F (s.filter (fun i => t i < x)) =
      deriv φ x • F ∅ + ∑ i ∈ s, deriv φ x • (if t i < x then Δ i else 0) := by
    rw [threshold_decomposition s t ht F x, smul_add, Finset.smul_sum]
  simp_rw [he]
  rw [integral_add (hd.smul_const _) (integrable_finsetSum _ (fun i _ => hi i)),
    integral_smul_const, integral_deriv_eq_zero hφ hc, zero_smul, zero_add,
    integral_finsetSum _ (fun i _ => hi i), ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i hi'
  have he : (fun x => deriv φ x • (if t i < x then Δ i else 0)) =
      (Ioi (t i)).indicator (fun x => deriv φ x • Δ i) := by
    funext x; by_cases hx : t i < x <;> simp [hx]
  rw [he, integral_indicator measurableSet_Ioi, integral_smul_const,
    hc.integral_Ioi_deriv_eq hφ, neg_smul]
end Integral

section MovingEvents
variable {X : Type u4} [MeasurableSpace X]

lemma measurable_filter_apply (s : Finset ι) (P : ι → X → Prop)
    [∀ i, DecidablePred (P i)] (hP : ∀ i, MeasurableSet {x | P i x})
    (F : Finset ι → ℝ) : Measurable (fun x => F (s.filter (fun i => P i x))) := by
  classical
  induction s using Finset.induction_on generalizing F with
  | empty => simp
  | @insert i s hi ih =>
    have h₁ := ih (fun a => F (insert i a))
    have h₂ := ih F
    have h : Measurable (fun x => if P i x then F (insert i (s.filter (fun j => P j x))) else F (s.filter (fun j => P j x))) := Measurable.ite (hP i) h₁ h₂
    convert h using 1
    funext x
    by_cases hx : P i x <;> simp [Finset.filter_insert, hx]

end MovingEvents

section ContinuousEvents
variable [Fintype ι] {X : Type u5} [TopologicalSpace X] [FirstCountableTopology X]

omit [DecidableEq ι] [Fintype ι] [FirstCountableTopology X] in
lemma eventually_threshold_eq (s : Finset ι) (t : ι → X → ℝ) {y : X} {x : ℝ}
    (ht : ∀ i ∈ s, ContinuousAt (t i) y) (hx : ∀ i ∈ s, x ≠ t i y) :
    ∀ᶠ z in 𝓝 y, s.filter (fun i => t i z < x) = s.filter (fun i => t i y < x) := by
  have hi (i : ι) (hi : i ∈ s) : ∀ᶠ z in 𝓝 y, (t i z < x ↔ t i y < x) := by
    rcases lt_or_gt_of_ne (hx i hi) with h | h
    · filter_upwards [(ht i hi).eventually (lt_mem_nhds h)] with z hz
      exact iff_of_false (not_lt.mpr hz.le) (not_lt.mpr h.le)
    · filter_upwards [(ht i hi).eventually (gt_mem_nhds h)] with z hz
      exact iff_of_true hz h
  filter_upwards [s.eventually_all.mpr hi] with z hz
  ext i
  simp only [Finset.mem_filter]
  exact and_congr_right (fun hi => hz i hi)

lemma continuousAt_threshold_integral (s : Finset ι) (t : ι → X → ℝ) (F : Finset ι → ℝ)
    {y : X} (ht : ∀ i ∈ s, ContinuousAt (t i) y) {φ : ℝ → ℝ} (hφ : Integrable φ) :
    ContinuousAt (fun z => ∫ x, φ x * F (s.filter (fun i => t i z < x))) y := by
  let M : ℝ := ∑ a : Finset ι, |F a|
  have hM (a : Finset ι) : |F a| ≤ M := by
    exact Finset.single_le_sum (f := fun a : Finset ι => |F a|) (fun _ _ => abs_nonneg _) (Finset.mem_univ a)
  apply continuousAt_of_dominated (bound := fun x => |φ x| * M)
  · apply Filter.Eventually.of_forall
    intro z
    exact hφ.aestronglyMeasurable.mul ((measurable_filter_apply s
      (fun i x => t i z < x) (fun _ => measurableSet_Ioi) F).aestronglyMeasurable)
  · exact Filter.Eventually.of_forall (fun z => ae_of_all _ (fun x => by
      simp only [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_left (hM _) (abs_nonneg _)))
  · exact hφ.abs.mul_const M
  · have hn : ∀ᵐ x : ℝ, ∀ i : ι, x ≠ t i y := ae_all_iff.mpr (fun i => volume.ae_ne (t i y))
    filter_upwards [hn] with x hx
    have he := eventually_threshold_eq s t ht (fun i _ => hx i)
    apply ContinuousAt.congr_of_eventuallyEq (by fun_prop : ContinuousAt (fun _ : X => φ x * F (s.filter (fun i => t i y < x))) y)
    filter_upwards [he] with z hz
    rw [hz]

omit [Fintype ι] in
lemma threshold_integral (s : Finset ι) (t : ι → ℝ) (ht : Set.InjOn t s)
    (F : Finset ι → ℝ) {φ : ℝ → ℝ} (hφ : Integrable φ) :
    (∫ x, φ x * F (s.filter (fun i => t i < x))) =
      (∫ x, φ x)*F ∅ + ∑ i ∈ s, (∫ x in Ioi (t i), φ x) *
        (F (s.filter (fun j => t j ≤ t i))-F (s.filter (fun j => t j < t i))) := by
  let Δ := fun i => F (s.filter (fun j => t j ≤ t i))-F (s.filter (fun j => t j < t i))
  have hi (i : ι) : Integrable (fun x => φ x * (if t i < x then Δ i else 0)) := by
    have he : (fun x => φ x * (if t i < x then Δ i else 0)) =
        (Ioi (t i)).indicator (fun x => φ x * Δ i) := by
      funext x; by_cases hx : t i < x <;> simp [hx]
    rw [he]
    exact (hφ.mul_const _).indicator measurableSet_Ioi
  have he (x : ℝ) : φ x * F (s.filter (fun i => t i < x)) =
      φ x * F ∅ + ∑ i ∈ s, φ x * (if t i < x then Δ i else 0) := by
    rw [threshold_decomposition s t ht F x, mul_add, Finset.mul_sum]
  simp_rw [he]
  rw [integral_add (hφ.mul_const _) (integrable_finsetSum _ (fun i _ => hi i)),
    integral_mul_const, integral_finsetSum _ (fun i _ => hi i)]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi'
  have he : (fun x => φ x * (if t i < x then Δ i else 0)) =
      (Ioi (t i)).indicator (fun x => φ x * Δ i) := by
    funext x; by_cases hx : t i < x <;> simp [hx]
  rw [he, integral_indicator measurableSet_Ioi, integral_mul_const]

lemma tail_integral_hasDerivAt {φ : ℝ → ℝ} (hφ : Integrable φ) (hc : Continuous φ) (x : ℝ) :
    HasDerivAt (fun t => ∫ z in Ioi t, φ z) (-φ x) x := by
  have he (t : ℝ) : (∫ z in Ioi t, φ z) = (∫ z in Ioi (0:ℝ), φ z)-(∫ z in (0:ℝ)..t, φ z) := by
    rw [← intervalIntegral.integral_Ioi_sub_Ioi' hφ.integrableOn hφ.integrableOn]
    ring
  rw [show (fun t => ∫ z in Ioi t, φ z) = (fun t => (∫ z in Ioi (0:ℝ), φ z)-(∫ z in (0:ℝ)..t, φ z)) from funext he]
  exact (intervalIntegral.integral_hasDerivAt_right (hφ.intervalIntegrable) hc.stronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt).const_sub _
end ContinuousEvents

section Slope
variable [Fintype ι]

omit [Fintype ι] in
lemma eventually_order_eq {X : Type u6} [TopologicalSpace X] (s : Finset ι) (t : ι → X → ℝ) {y : X}
    (ht : ∀ i ∈ s, ContinuousAt (t i) y) (hi : Set.InjOn (fun i => t i y) s) :
    ∀ᶠ z in 𝓝 y, Set.InjOn (fun i => t i z) s ∧
      ∀ i ∈ s, s.filter (fun j => t j z ≤ t i z) = s.filter (fun j => t j y ≤ t i y) ∧
        s.filter (fun j => t j z < t i z) = s.filter (fun j => t j y < t i y) := by
  have hp (i : ι) (his : i ∈ s) (j : ι) (hjs : j ∈ s) :
      ∀ᶠ z in 𝓝 y, (t i z < t j z ↔ t i y < t j y) := by
    by_cases hij : i = j
    · subst j; simp
    have hne : t i y ≠ t j y := fun he => hij (hi his hjs he)
    rcases hne.lt_or_gt with h | h
    · filter_upwards [(ht i his).eventually_lt (ht j hjs) h] with z hz
      exact iff_of_true hz h
    · filter_upwards [(ht j hjs).eventually_lt (ht i his) h] with z hz
      exact iff_of_false (not_lt.mpr hz.le) (not_lt.mpr h.le)
  have hall : ∀ᶠ z in 𝓝 y, ∀ i ∈ s, ∀ j ∈ s, (t i z < t j z ↔ t i y < t j y) :=
    s.eventually_all.mpr (fun i his => s.eventually_all.mpr (fun j hjs => hp i his j hjs))
  filter_upwards [hall] with z hz
  refine ⟨?_,?_⟩
  · intro i his j hjs he
    change t i z=t j z at he
    apply hi his hjs
    apply le_antisymm
    · apply not_lt.mp
      intro h
      have := (hz j hjs i his).mpr h
      rw [he] at this
      exact (lt_irrefl _ this)
    · apply not_lt.mp
      intro h
      have := (hz i his j hjs).mpr h
      rw [he] at this
      exact (lt_irrefl _ this)
  · intro i his
    constructor <;> ext j <;> simp only [Finset.mem_filter]
    · apply and_congr_right
      intro hjs
      simp only [← not_lt, hz i his j hjs]
    · exact and_congr_right (fun hjs => hz j hjs i his)

omit [Fintype ι] in
lemma moving_threshold_integral_hasDerivAt (s : Finset ι) (t : ι → ℝ → ℝ)
    (F : Finset ι → ℝ) {y : ℝ} (t' : ι → ℝ)
    (ht : ∀ i ∈ s, HasDerivAt (t i) (t' i) y) (hi : Set.InjOn (fun i => t i y) s)
    {φ : ℝ → ℝ} (hφ : Integrable φ) (hc : Continuous φ) :
    HasDerivAt (fun z => ∫ x, φ x * F (s.filter (fun i => t i z < x)))
      (-∑ i ∈ s, t' i * φ (t i y) *
        (F (s.filter (fun j => t j y ≤ t i y))-F (s.filter (fun j => t j y < t i y)))) y := by
  let Δ := fun i => F (s.filter (fun j => t j y ≤ t i y))-F (s.filter (fun j => t j y < t i y))
  have he : (fun z => ∫ x, φ x * F (s.filter (fun i => t i z < x))) =ᶠ[𝓝 y]
      (fun z => (∫ x, φ x)*F ∅ + ∑ i ∈ s, (∫ x in Ioi (t i z), φ x)*Δ i) := by
    filter_upwards [eventually_order_eq s t (fun i his => (ht i his).continuousAt) hi] with z hz
    rw [threshold_integral s (fun i => t i z) hz.1 F hφ]
    congr 1
    apply Finset.sum_congr rfl
    intro i his
    rw [(hz.2 i his).1,(hz.2 i his).2]
  have hd (i : ι) (his : i ∈ s) : HasDerivAt (fun z => (∫ x in Ioi (t i z), φ x)*Δ i)
      (-(t' i * φ (t i y)*Δ i)) y := by
    convert ((tail_integral_hasDerivAt hφ hc (t i y)).comp y (ht i his)).mul_const (Δ i) using 1 <;> try rfl
    ring
  have hs := (HasDerivAt.sum (fun i his => hd i his)).const_add ((∫ x, φ x)*F ∅)
  simp only [Finset.sum_neg_distrib, Finset.sum_apply] at hs
  exact hs.congr_of_eventuallyEq he

end Slope

section Weak
variable [Fintype ι]

lemma integral_deriv_zero_off_countable {f f' : ℝ → ℝ}
    (hf : Continuous f) (hs : HasCompactSupport f) (hs' : HasCompactSupport f')
    (hi : Integrable f') {bad : Set ℝ} (hb : bad.Countable)
    (hd : ∀ x ∉ bad, HasDerivAt f (f' x) x) : ∫ x, f' x = 0 := by
  obtain ⟨R,hR,hbound⟩ := (hs.isCompact.union hs'.isCompact).isBounded.exists_pos_norm_lt
  have hf0 {x : ℝ} (hx : R ≤ |x|) : f x=0 := by
    apply image_eq_zero_of_notMem_tsupport
    intro hm
    have := hbound x (Or.inl hm)
    simpa only [Real.norm_eq_abs] using not_lt.mpr hx this
  have hf'0 {x : ℝ} (hx : R ≤ |x|) : f' x=0 := by
    apply image_eq_zero_of_notMem_tsupport
    intro hm
    have := hbound x (Or.inr hm)
    simpa only [Real.norm_eq_abs] using not_lt.mpr hx this
  have hI := integral_eq_of_hasDerivAt_off_countable_of_le f f' (by linarith : -R ≤ R)
    hb hf.continuousOn (fun x hx => hd x hx.2) hi.intervalIntegrable
  rw [hf0 (by rw [abs_of_pos hR]), hf0 (by rw [abs_neg,abs_of_pos hR]),sub_self,
    intervalIntegral.integral_of_le (by linarith)] at hI
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => hf'0 (by
    simp only [mem_Ioc,not_and_or,not_lt,not_le] at hx
    rcases hx with hx | hx
    · exact (neg_le_abs x).trans' (by linarith)
    · exact (le_abs_self x).trans' hx.le))] at hI
  exact hI

omit [DecidableEq ι] in
lemma affine_collisions_countable (s : Finset ι) (a b : ι → ℝ)
    (hab : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → a i ≠ a j ∨ b i ≠ b j) :
    {y : ℝ | ¬ Set.InjOn (fun i => a i*y+b i) s}.Countable := by
  classical
  have hp (i j : ι) : {y : ℝ | i ∈ s ∧ j ∈ s ∧ i ≠ j ∧ a i*y+b i=a j*y+b j}.Subsingleton := by
    intro x hx y hy
    have h := hab i hx.1 j hx.2.1 hx.2.2.1
    rcases h with h | h
    · have he : (a i-a j)*(x-y)=0 := by nlinarith [hx.2.2.2,hy.2.2.2]
      exact sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_left (sub_ne_zero.mpr h))
    · by_cases ha : a i=a j
      · exfalso; apply h; have he := hx.2.2.2; rw [ha] at he; linarith
      · have he : (a i-a j)*(x-y)=0 := by nlinarith [hx.2.2.2,hy.2.2.2]
        exact sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_left (sub_ne_zero.mpr ha))
  apply (countable_iUnion (fun i => countable_iUnion (fun j => (hp i j).countable))).mono
  intro y hy
  simp only [mem_ofPred_eq,Set.InjOn,not_forall] at hy
  obtain ⟨i,hi,j,hj,he,hne⟩ := hy
  exact mem_iUnion.mpr ⟨i,mem_iUnion.mpr ⟨j,hi,hj,hne,he⟩⟩

lemma moving_threshold_weak (s : Finset ι) (a b : ι → ℝ)
    (hab : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → a i ≠ a j ∨ b i ≠ b j)
    (F : Finset ι → ℝ) {φ χ χ' : ℝ → ℝ}
    (hφ : Integrable φ) (hcφ : Continuous φ) (hcχ : Continuous χ)
    (hsχ : HasCompactSupport χ) (hsχ' : HasCompactSupport χ')
    (hdχ : ∀ y, HasDerivAt χ (χ' y) y)
    (hi₁ : Integrable (fun y => χ' y * ∫ x, φ x * F (s.filter (fun i => a i*y+b i < x))))
    (hi₂ : Integrable (fun y => χ y * ∑ i ∈ s, a i * φ (a i*y+b i) *
      (F (s.filter (fun j => a j*y+b j ≤ a i*y+b i))-F (s.filter (fun j => a j*y+b j < a i*y+b i))))) :
    (∫ y, χ' y * ∫ x, φ x * F (s.filter (fun i => a i*y+b i < x))) =
      ∫ y, χ y * ∑ i ∈ s, a i * φ (a i*y+b i) *
      (F (s.filter (fun j => a j*y+b j ≤ a i*y+b i))-F (s.filter (fun j => a j*y+b j < a i*y+b i))) := by
  let H := fun y => ∫ x, φ x * F (s.filter (fun i => a i*y+b i < x))
  let D := fun y => ∑ i ∈ s, a i * φ (a i*y+b i) *
      (F (s.filter (fun j => a j*y+b j ≤ a i*y+b i))-F (s.filter (fun j => a j*y+b j < a i*y+b i)))
  have hH : Continuous H := continuous_iff_continuousAt.mpr (fun y =>
    continuousAt_threshold_integral s (fun i y => a i*y+b i) F (fun _ _ => by fun_prop) hφ)
  have hprod : HasCompactSupport (fun y => χ y * H y) := hsχ.mul_right
  have hder : HasCompactSupport (fun y => χ' y * H y-χ y * D y) :=
    hsχ'.mul_right.sub hsχ.mul_right
  have hzero := integral_deriv_zero_off_countable (hcχ.mul hH) hprod hder (hi₁.sub hi₂)
    (affine_collisions_countable s a b hab) (fun y hy => by
      have hdy := moving_threshold_integral_hasDerivAt s (fun i y => a i*y+b i) F a
        (fun i _ => by simpa using ((hasDerivAt_id y).const_mul (a i)).add_const (b i))
        (not_not.mp hy) hφ hcφ
      convert (hdχ y).mul hdy using 1
      dsimp [D]
      ring)
  rw [integral_sub hi₁ hi₂,sub_eq_zero] at hzero
  exact hzero

end Weak

section Lipschitz
variable [Fintype ι]

lemma threshold_integrable (s : Finset ι) (t : ι → ℝ) (F : Finset ι → ℝ)
    {φ : ℝ → ℝ} (hφ : Integrable φ) :
    Integrable (fun x => φ x * F (s.filter (fun i => t i < x))) := by
  classical
  let M := ∑ a : Finset ι, |F a|
  apply hφ.mul_bdd (measurable_filter_apply s (fun i x => t i < x)
      (fun _ => measurableSet_Ioi) F).aestronglyMeasurable
  apply ae_of_all
  intro x
  exact Finset.single_le_sum (f := fun a : Finset ι => |F a|) (fun _ _ => abs_nonneg _) (Finset.mem_univ _)

lemma threshold_pointwise_bound (s : Finset ι) (t u : ι → ℝ) (F : Finset ι → ℝ)
    {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ a, |F a| ≤ M) (x : ℝ) :
    |F (s.filter (fun i => t i < x))-F (s.filter (fun i => u i < x))| ≤
      2*M*∑ i ∈ s, (uIoc (t i) (u i)).indicator (fun _ => (1:ℝ)) x := by
  classical
  have hn (i : ι) : 0 ≤ (uIoc (t i) (u i)).indicator (fun _ => (1:ℝ)) x := by
    by_cases hx : x ∈ uIoc (t i) (u i) <;> simp [hx]
  by_cases he : ∀ i ∈ s, t i < x ↔ u i < x
  · have he' : s.filter (fun i => t i < x) = s.filter (fun i => u i < x) := by
      ext i; simp only [Finset.mem_filter]; exact and_congr_right (he i)
    rw [he',sub_self,abs_zero]
    exact mul_nonneg (by positivity) (Finset.sum_nonneg (fun i _ => hn i))
  · simp only [not_forall] at he
    obtain ⟨i,his,hi⟩ := he
    have hx : x ∈ uIoc (t i) (u i) := by
      change min (t i) (u i) < x ∧ x ≤ max (t i) (u i)
      rcases lt_or_ge (t i) x with ht | ht <;> rcases lt_or_ge (u i) x with hu | hu
      · exact False.elim (hi (iff_of_true ht hu))
      · exact ⟨(min_le_left _ _).trans_lt ht,hu.trans (le_max_right _ _)⟩
      · exact ⟨(min_le_right _ _).trans_lt hu,ht.trans (le_max_left _ _)⟩
      · exact False.elim (hi (iff_of_false (not_lt.mpr ht) (not_lt.mpr hu)))
    have hs : 1 ≤ ∑ i ∈ s, (uIoc (t i) (u i)).indicator (fun _ => (1:ℝ)) x := by
      have hh := Finset.single_le_sum (fun j _ => hn j) his
      simpa [hx] using hh
    calc
      _ ≤ |F (s.filter (fun i => t i < x))|+|F (s.filter (fun i => u i < x))| := abs_sub _ _
      _ ≤ 2*M := by linarith [hM (s.filter (fun i => t i < x)),hM (s.filter (fun i => u i < x))]
      _ ≤ _ := le_mul_of_one_le_right (by positivity) hs

lemma threshold_integral_diff_bound (s : Finset ι) (t u : ι → ℝ) (F : Finset ι → ℝ)
    {φ : ℝ → ℝ} (hφ : Integrable φ) {M C : ℝ} (hM0 : 0 ≤ M) (hC : 0 ≤ C)
    (hM : ∀ a, |F a| ≤ M) (hφC : ∀ x, |φ x| ≤ C) :
    |(∫ x, φ x * F (s.filter (fun i => t i < x)))-
      (∫ x, φ x * F (s.filter (fun i => u i < x)))| ≤
      2*M*C*∑ i ∈ s, |u i-t i| := by
  classical
  let I := fun i x => (uIoc (t i) (u i)).indicator (fun _ => (1:ℝ)) x
  have hi (i : ι) : Integrable (I i) := by
    exact (integrable_indicator_iff measurableSet_uIoc).mpr (integrableOn_const (μ := volume) (s := uIoc (t i) (u i)) (C := (1:ℝ)) (by rw [Real.volume_uIoc]; exact ENNReal.ofReal_ne_top))
  have hiS : Integrable (fun x => 2*M*C*∑ i ∈ s, I i x) :=
    (integrable_finsetSum s (fun i _ => hi i)).const_mul _
  have hbound (x : ℝ) : ‖φ x*(F (s.filter (fun i => t i < x))-F (s.filter (fun i => u i < x)))‖ ≤
      2*M*C*∑ i ∈ s, I i x := by
    rw [Real.norm_eq_abs,abs_mul]
    have hp := mul_le_mul (hφC x) (threshold_pointwise_bound s t u F hM0 hM x) (abs_nonneg _) hC
    dsimp [I]
    convert hp using 1
    first | rfl | ring
  rw [← integral_sub (threshold_integrable s t F hφ) (threshold_integrable s u F hφ)]
  simp_rw [← mul_sub]
  calc
    _ ≤ ∫ x, 2*M*C*∑ i ∈ s, I i x := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_of_norm_le hiS (ae_of_all _ hbound)
    _ = 2*M*C*∑ i ∈ s, |u i-t i| := by
      rw [integral_const_mul,integral_finsetSum s (fun i _ => hi i)]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      dsimp [I]
      change (∫ x, (uIoc (t i) (u i)).indicator (1 : ℝ → ℝ) x) = _
      rw [integral_indicator_one measurableSet_uIoc,measureReal_def,Real.volume_uIoc,ENNReal.toReal_ofReal (abs_nonneg _)]

end Lipschitz

section FDeriv
variable [Fintype ι]
variable {X : Type u7} [NormedAddCommGroup X] [NormedSpace ℝ X]

omit [Fintype ι] in
lemma moving_threshold_integral_hasFDerivAt (s : Finset ι) (t : ι → X → ℝ)
    (F : Finset ι → ℝ) {y : X} (t' : ι → X →L[ℝ] ℝ)
    (ht : ∀ i ∈ s, HasFDerivAt (t i) (t' i) y) (hi : Set.InjOn (fun i => t i y) s)
    {φ : ℝ → ℝ} (hφ : Integrable φ) (hc : Continuous φ) :
    HasFDerivAt (fun z => ∫ x, φ x * F (s.filter (fun i => t i z < x)))
      (∑ i ∈ s, (-(φ (t i y) *
        (F (s.filter (fun j => t j y ≤ t i y))-F (s.filter (fun j => t j y < t i y))))) • t' i) y := by
  let Δ := fun i => F (s.filter (fun j => t j y ≤ t i y))-F (s.filter (fun j => t j y < t i y))
  have he : (fun z => ∫ x, φ x * F (s.filter (fun i => t i z < x))) =ᶠ[𝓝 y]
      (fun z => (∫ x, φ x)*F ∅ + ∑ i ∈ s, (∫ x in Ioi (t i z), φ x)*Δ i) := by
    filter_upwards [eventually_order_eq s t (fun i his => (ht i his).continuousAt) hi] with z hz
    rw [threshold_integral s (fun i => t i z) hz.1 F hφ]
    congr 1
    apply Finset.sum_congr rfl
    intro i his
    rw [(hz.2 i his).1,(hz.2 i his).2]
  have hd (i : ι) (his : i ∈ s) : HasFDerivAt (fun z => (∫ x in Ioi (t i z), φ x)*Δ i)
      (-(φ (t i y)*Δ i) • t' i) y := by
    convert ((tail_integral_hasDerivAt hφ hc (t i y)).comp_hasFDerivAt y (ht i his)).mul_const (Δ i) using 1 <;> try rfl
    simp only [smul_smul]
    congr 1; ring
  have hs := (HasFDerivAt.sum (fun i his => hd i his)).const_add ((∫ x, φ x)*F ∅)
  simp only [Finset.sum_apply] at hs
  exact hs.congr_of_eventuallyEq he

lemma affine_threshold_lipschitz (s : Finset ι) (L : ι → X →L[ℝ] ℝ) (b : ι → ℝ)
    (F : Finset ι → ℝ) {φ : ℝ → ℝ} (hφ : Integrable φ)
    {M C : ℝ} (hM0 : 0 ≤ M) (hC : 0 ≤ C) (hM : ∀ a, |F a| ≤ M) (hφC : ∀ x, |φ x| ≤ C) :
    LipschitzWith (Real.nnabs (2*M*C*∑ i ∈ s, ‖L i‖))
      (fun y => ∫ x, φ x * F (s.filter (fun i => L i y+b i < x))) := by
  apply LipschitzWith.of_dist_le_mul
  intro y z
  simp only [dist_eq_norm]
  have hb := threshold_integral_diff_bound s (fun i => L i y+b i) (fun i => L i z+b i) F hφ hM0 hC hM hφC
  simp only [Real.norm_eq_abs] at ⊢
  refine hb.trans ?_
  have hs : (∑ i ∈ s, |L i z+b i-(L i y+b i)|) ≤ (∑ i ∈ s, ‖L i‖)*‖y-z‖ := by
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro i _
    have ht := (L i).le_opNorm (z-y)
    simpa only [map_sub, Real.norm_eq_abs, add_sub_add_right_eq_sub, norm_sub_rev z y] using ht
  exact mul_le_mul_of_nonneg_left hs (by positivity) |>.trans_eq (by simp only [Real.coe_nnabs, abs_of_nonneg (show 0 ≤ 2*M*C*∑ i ∈ s, ‖L i‖ by positivity)]; ring)

end FDeriv

end UniformSparsestCut.InterfaceStep

namespace UniformSparsestCut.InterfaceStep
open MeasureTheory Set
open scoped BigOperators Topology
variable {ι : Type u8} {X : Type u9} {Z : Type u10} [DecidableEq ι] [Fintype ι]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [MeasurableSpace Z]

lemma averaged_threshold_derivative (s : Finset ι) (L : ι → X →L[ℝ] ℝ)
    (b : ι → Z → ℝ) (hb : ∀ i, Measurable (b i)) (F : Finset ι → ℝ)
    {φ : ℝ → ℝ} (hφ : Integrable φ) (hc : Continuous φ)
    {M C : ℝ} (hM0 : 0 ≤ M) (hC : 0 ≤ C) (hM : ∀ a, |F a| ≤ M) (hφC : ∀ x, |φ x| ≤ C)
    (μ : Measure Z) [IsFiniteMeasure μ] (y : X)
    (hi : ∀ᵐ z ∂μ, Set.InjOn (fun i => L i y+b i z) s) :
    HasFDerivAt (fun y => ∫ z, (∫ x, φ x * F (s.filter (fun i => L i y+b i z < x))) ∂μ)
      (∑ i ∈ s, (∫ z, -(φ (L i y+b i z) *
        (F (s.filter (fun j => L j y+b j z ≤ L i y+b i z))-
          F (s.filter (fun j => L j y+b j z < L i y+b i z)))) ∂μ) • L i) y := by
  let H : X → Z → ℝ := fun y z => ∫ x, φ x * F (s.filter (fun i => L i y+b i z < x))
  let c : ι → Z → ℝ := fun i z => -(φ (L i y+b i z) *
    (F (s.filter (fun j => L j y+b j z ≤ L i y+b i z))-
      F (s.filter (fun j => L j y+b j z < L i y+b i z))))
  have hmH (y : X) : StronglyMeasurable (H y) := by
    apply StronglyMeasurable.integral_prod_right
    apply Measurable.stronglyMeasurable
    exact (hc.measurable.comp measurable_snd).mul (measurable_filter_apply s
      (fun i (p : Z × ℝ) => L i y+b i p.1 < p.2)
      (fun i => measurableSet_lt ((measurable_const.add ((hb i).comp measurable_fst))) measurable_snd) F)
  have hmC (i : ι) : Measurable (c i) := by
    apply Measurable.neg
    apply Measurable.mul (hc.measurable.comp (measurable_const.add (hb i)))
    exact (measurable_filter_apply s (fun j z => L j y+b j z ≤ L i y+b i z)
      (fun j => measurableSet_le (measurable_const.add (hb j)) (measurable_const.add (hb i))) F).sub
      (measurable_filter_apply s (fun j z => L j y+b j z < L i y+b i z)
      (fun j => measurableSet_lt (measurable_const.add (hb j)) (measurable_const.add (hb i))) F)
  have hcB (i : ι) (z : Z) : ‖c i z‖ ≤ C*(2*M) := by
    dsimp [c]
    simp only [abs_neg,abs_mul]
    have hd := abs_sub_le (F (s.filter (fun j => L j y+b j z ≤ L i y+b i z))) 0
      (F (s.filter (fun j => L j y+b j z < L i y+b i z)))
    simp only [sub_zero,zero_sub,abs_neg] at hd
    apply mul_le_mul (hφC _) _ (abs_nonneg _) hC
    linarith [hM (s.filter (fun j => L j y+b j z ≤ L i y+b i z)),
      hM (s.filter (fun j => L j y+b j z < L i y+b i z))]
  have hiC (i : ι) : Integrable (c i) μ :=
    (integrable_const (C*(2*M))).mono' (hmC i).aestronglyMeasurable (ae_of_all _ (hcB i))
  have hiH : Integrable (H y) μ := by
    apply (integrable_const (∫ x, |φ x| * M)).mono' (hmH y).aestronglyMeasurable
    filter_upwards with z
    apply norm_integral_le_of_norm_le (hφ.abs.mul_const M)
    filter_upwards with x
    rw [Real.norm_eq_abs,abs_mul]
    exact mul_le_mul_of_nonneg_left (hM _) (abs_nonneg _)
  let K : NNReal := Real.nnabs (2*M*C*∑ i ∈ s, ‖L i‖)
  have hLip (z : Z) : LipschitzWith K (fun y => H y z) :=
    affine_threshold_lipschitz s L (fun i => b i z) F hφ hM0 hC hM hφC
  have hD : ∀ᵐ z ∂μ, HasFDerivAt (fun y => H y z) (∑ i ∈ s, c i z • L i) y := by
    filter_upwards [hi] with z hz
    exact moving_threshold_integral_hasFDerivAt s (fun i y => L i y+b i z) F L
      (fun i _ => (L i).hasFDerivAt.add_const _) hz hφ hc
  have hres := hasFDerivAt_integral_of_dominated_loc_of_lip (μ := μ) (F := H)
    (s := Set.univ) (bound := fun _ => (K : ℝ)) (F' := fun z => ∑ i ∈ s, c i z • L i)
    (Filter.univ_mem) (Filter.Eventually.of_forall (fun x => (hmH x).aestronglyMeasurable)) hiH
    (by
      have hm := (Finset.stronglyMeasurable_sum s (fun i _ => (hmC i).stronglyMeasurable.smul_const (L i))).aestronglyMeasurable (μ := μ)
      have he : (∑ i ∈ s, (fun z => c i z • L i)) = (fun z => ∑ i ∈ s, c i z • L i) := by
        funext z; exact Finset.sum_apply z s _
      rw [he] at hm
      exact hm)
    (ae_of_all _ (fun z => by simpa using (hLip z).lipschitzOnWith (s := Set.univ)))
    (integrable_const _) hD
  rw [integral_finsetSum s (fun i _ => (hiC i).smul_const (L i))] at hres
  simp only [integral_smul_const] at hres
  exact hres.2

end UniformSparsestCut.InterfaceStep

end

end OAI
