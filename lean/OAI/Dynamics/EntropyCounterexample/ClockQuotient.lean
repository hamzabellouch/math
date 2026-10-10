import OAI.Dynamics.EntropyCounterexample.ClockPeriodization

namespace OAI

noncomputable section

open Set Filter Function
open scoped Topology

namespace Problem340
namespace ClockQuotient

variable {E F : Type*}

def periodize [AddCommMonoid F] (P : ℝ) (f : ℝ × E → F) (x : ℝ × E) : F :=
  ∑ᶠ k : ℤ, f (x.1 - (k : ℝ) * P, x.2)

lemma periodic_periodize [AddCommMonoid F] (P : ℝ) (f : ℝ × E → F) (z : E) :
    Periodic (fun t => periodize P f (t, z)) P := by
  intro t
  unfold periodize
  refine finsum_eq_of_bijective (fun k : ℤ => k - 1) ?_ ?_
  · constructor
    · intro a b h
      dsimp at h
      omega
    · intro a
      exact ⟨a + 1, by simp⟩
  · intro k
    apply congrArg f
    apply Prod.ext
    · simp only [Int.cast_sub, Int.cast_one]
      ring
    · rfl

lemma locallyFinite_translated_strips [TopologicalSpace E]
    {P : ℝ} (hP : 0 < P) (a b : ℝ) :
    LocallyFinite (fun k : ℤ =>
      {x : ℝ × E | x.1 - (k : ℝ) * P ∈ Icc a b}) := by
  have hl := (ClockPeriodization.locallyFinite_clockIntervals hP a b).preimage_continuous
    (continuous_fst : Continuous (Prod.fst : ℝ × E → ℝ))
  refine hl.subset ?_
  intro k x hx
  change (k : ℝ) * P + a ≤ x.1 ∧ x.1 ≤ (k : ℝ) * P + b
  exact ⟨by linarith [hx.1], by linarith [hx.2]⟩

lemma locallyFinite_translated_supports [TopologicalSpace E] [Zero F]
    {P a b : ℝ} {f : ℝ × E → F} (hP : 0 < P)
    (hsupp : ∀ x, f x ≠ 0 → x.1 ∈ Icc a b) :
    LocallyFinite (fun k : ℤ => support (fun x : ℝ × E =>
      f (x.1 - (k : ℝ) * P, x.2))) := by
  refine (locallyFinite_translated_strips hP a b).subset ?_
  intro k x hx
  exact hsupp _ hx

lemma continuous_periodize [TopologicalSpace E]
    [AddCommMonoid F] [TopologicalSpace F] [ContinuousAdd F]
    {P a b : ℝ} {f : ℝ × E → F}
    (hP : 0 < P) (hf : Continuous f)
    (hsupp : ∀ x, f x ≠ 0 → x.1 ∈ Icc a b) :
    Continuous (periodize P f) := by
  exact continuous_finsum
    (fun k => hf.comp ((continuous_fst.sub continuous_const).prodMk continuous_snd))
    (locallyFinite_translated_supports hP hsupp)

lemma periodize_eq_tsum [TopologicalSpace E]
    [AddCommMonoid F] [TopologicalSpace F]
    {P a b : ℝ} {f : ℝ × E → F}
    (hP : 0 < P) (hsupp : ∀ x, f x ≠ 0 → x.1 ∈ Icc a b) (x : ℝ × E) :
    periodize P f x = ∑' k : ℤ, f (x.1 - (k : ℝ) * P, x.2) := by
  exact (tsum_eq_finsum
    ((locallyFinite_translated_supports hP hsupp).point_finite x)).symm

lemma periodize_eq_on_fundamental_strip [AddCommMonoid F]
    {P : ℝ} {f : ℝ × E → F} (hP : 0 < P)
    (hsupp : ∀ x, f x ≠ 0 → x.1 ∈ Ioo 0 P)
    {t : ℝ} (ht : t ∈ Icc 0 P) (z : E) :
    periodize P f (t, z) = f (t, z) := by
  unfold periodize
  have hzero : ∀ k : ℤ, k ≠ 0 → f (t - (k : ℝ) * P, z) = 0 := by
    intro k hk
    by_contra hne
    have hi := hsupp (t - (k : ℝ) * P, z) hne
    rcases lt_or_gt_of_ne hk with hkneg | hkpos
    · have hk1 : (k : ℝ) ≤ -1 := by exact_mod_cast (show k ≤ -1 by omega)
      have hmul := mul_le_mul_of_nonneg_right hk1 hP.le
      linarith [hi.2, ht.1]
    · have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
      have hmul := mul_le_mul_of_nonneg_right hk1 hP.le
      linarith [hi.1, ht.2]
  simpa using finsum_eq_single (fun k : ℤ => f (t - (k : ℝ) * P, z)) 0 hzero

lemma periodize_eq_toIcoMod [AddCommMonoid F]
    {P : ℝ} {f : ℝ × E → F} (hP : 0 < P)
    (hsupp : ∀ x, f x ≠ 0 → x.1 ∈ Ioo 0 P) (t : ℝ) (z : E) :
    periodize P f (t, z) = f (toIcoMod hP 0 t, z) := by
  have hm := toIcoMod_mem_Ico' hP t
  have hp := (periodic_periodize P f z).sub_zsmul_eq (x := t) (toIcoDiv hP 0 t)
  rw [self_sub_toIcoDiv_zsmul] at hp
  rw [← hp]
  exact periodize_eq_on_fundamental_strip hP hsupp ⟨hm.1, hm.2.le⟩ z

lemma periodize_mem_Icc [TopologicalSpace E]
    {P a b : ℝ} {f : ℝ × E → ℝ} (hP : 0 < P)
    (hsupp : ∀ x, f x ≠ 0 → x.1 ∈ Ioo 0 P)
    (hbound : ∀ x, f x ∈ Icc a b) (x : ℝ × E) :
    periodize P f x ∈ Icc a b := by
  rw [periodize_eq_toIcoMod hP hsupp]
  exact hbound _

def liftPeriodic {P : ℝ} (f : ℝ × E → F)
    (hf : ∀ z, Periodic (fun t => f (t, z)) P) (x : AddCircle P × E) : F :=
  (hf x.2).lift x.1

@[simp] lemma liftPeriodic_coe {P : ℝ} (f : ℝ × E → F)
    (hf : ∀ z, Periodic (fun t => f (t, z)) P) (t : ℝ) (z : E) :
    liftPeriodic f hf ((t : AddCircle P), z) = f (t, z) :=
  (hf z).lift_coe t

lemma continuous_liftPeriodic [TopologicalSpace E] [TopologicalSpace F]
    {P : ℝ} {f : ℝ × E → F}
    (hf : ∀ z, Periodic (fun t => f (t, z)) P) (hc : Continuous f) :
    Continuous (liftPeriodic f hf) := by
  have hq : IsOpenQuotientMap
      (fun x : ℝ × E => ((x.1 : AddCircle P), x.2)) :=
    QuotientAddGroup.isOpenQuotientMap_mk.prodMap IsOpenQuotientMap.id
  rw [← hq.continuous_comp_iff]
  simpa only [Function.comp_def, liftPeriodic_coe] using hc

lemma liftPeriodic_eq_liftIco {P : ℝ} [Fact (0 < P)] (f : ℝ × E → F)
    (hf : ∀ z, Periodic (fun t => f (t, z)) P) (x : AddCircle P × E) :
    liftPeriodic f hf x = AddCircle.liftIco P 0 (fun t => f (t, x.2)) x.1 := by
  let r := AddCircle.equivIco P 0 x.1
  have he : ((r : ℝ) : AddCircle P) = x.1 := AddCircle.coe_equivIco
  calc
    liftPeriodic f hf x = liftPeriodic f hf (((r : ℝ) : AddCircle P), x.2) := by rw [he]
    _ = f ((r : ℝ), x.2) := liftPeriodic_coe f hf _ _
    _ = AddCircle.liftIco P 0 (fun t => f (t, x.2)) x.1 := rfl

lemma continuous_liftIco_of_periodic [TopologicalSpace E] [TopologicalSpace F]
    {P : ℝ} [Fact (0 < P)] {f : ℝ × E → F}
    (hf : ∀ z, Periodic (fun t => f (t, z)) P) (hc : Continuous f) :
    Continuous (fun x : AddCircle P × E =>
      AddCircle.liftIco P 0 (fun t => f (t, x.2)) x.1) :=
  (continuous_liftPeriodic hf hc).congr (liftPeriodic_eq_liftIco f hf)

def liftPeriodize [AddCommMonoid F] (P : ℝ) (f : ℝ × E → F) : AddCircle P × E → F :=
  liftPeriodic (periodize P f) (periodic_periodize P f)

@[simp] lemma liftPeriodize_coe [AddCommMonoid F]
    (P : ℝ) (f : ℝ × E → F) (t : ℝ) (z : E) :
    liftPeriodize P f ((t : AddCircle P), z) = periodize P f (t, z) :=
  liftPeriodic_coe _ _ _ _

lemma continuous_liftPeriodize [TopologicalSpace E]
    [AddCommMonoid F] [TopologicalSpace F] [ContinuousAdd F]
    {P a b : ℝ} {f : ℝ × E → F}
    (hP : 0 < P) (hf : Continuous f)
    (hsupp : ∀ x, f x ≠ 0 → x.1 ∈ Icc a b) :
    Continuous (liftPeriodize P f) :=
  continuous_liftPeriodic _ (continuous_periodize hP hf hsupp)

lemma liftPeriodize_eq_liftIco [AddCommMonoid F]
    {P : ℝ} [Fact (0 < P)] {f : ℝ × E → F}
    (hsupp : ∀ x, f x ≠ 0 → x.1 ∈ Ioo 0 P) (x : AddCircle P × E) :
    liftPeriodize P f x = AddCircle.liftIco P 0 (fun t => f (t, x.2)) x.1 := by
  let r := AddCircle.equivIco P 0 x.1
  have hr : (r : ℝ) ∈ Icc 0 P := by
    have h := r.property
    simp only [zero_add] at h
    exact ⟨h.1, h.2.le⟩
  have he : ((r : ℝ) : AddCircle P) = x.1 := AddCircle.coe_equivIco
  calc
    liftPeriodize P f x = liftPeriodize P f (((r : ℝ) : AddCircle P), x.2) := by
      rw [he]
    _ = f ((r : ℝ), x.2) := by
      rw [liftPeriodize_coe]
      exact periodize_eq_on_fundamental_strip Fact.out hsupp hr x.2
    _ = AddCircle.liftIco P 0 (fun t => f (t, x.2)) x.1 := rfl

lemma continuous_liftIco_of_strip_support [TopologicalSpace E]
    [AddCommMonoid F] [TopologicalSpace F] [ContinuousAdd F]
    {P : ℝ} [Fact (0 < P)] {f : ℝ × E → F}
    (hf : Continuous f) (hsupp : ∀ x, f x ≠ 0 → x.1 ∈ Ioo 0 P) :
    Continuous (fun x : AddCircle P × E =>
      AddCircle.liftIco P 0 (fun t => f (t, x.2)) x.1) := by
  have hsupp' : ∀ x, f x ≠ 0 → x.1 ∈ Icc 0 P :=
    fun x hx => ⟨(hsupp x hx).1.le, (hsupp x hx).2.le⟩
  exact (continuous_liftPeriodize Fact.out hf hsupp').congr
    (liftPeriodize_eq_liftIco hsupp)

end ClockQuotient
end Problem340

end

end OAI
