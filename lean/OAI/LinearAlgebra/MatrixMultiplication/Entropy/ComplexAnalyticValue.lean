import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Convex.Topology
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Order.Monotone
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace OAI

/-! Finite entropy, rate estimates and ordered asymptotic limits. -/

noncomputable section

open Set Filter
open scoped Topology BigOperators

namespace MatrixMultiplication.Foundation

theorem unitInterval_subset_closure_rat :
    Icc (0 : ℝ) 1 ⊆ closure (((↑) : ℚ → ℝ) '' Icc 0 1) := by
  have hinterior : Ioo (0 : ℝ) 1 ⊆ closure (((↑) : ℚ → ℝ) '' Icc 0 1) := by
    intro x hx
    rw [mem_closure_iff]
    intro U hU hxU
    obtain ⟨z, hz, hzrat⟩ := Rat.denseRange_cast.inter_open_nonempty
      (U ∩ Ioo (0 : ℝ) 1) (hU.inter isOpen_Ioo) ⟨x, hxU, hx⟩
    obtain ⟨q, rfl⟩ := hzrat
    refine ⟨(q : ℝ), hz.1, q, ?_, rfl⟩
    constructor
    · exact Rat.cast_nonneg.mp hz.2.1.le
    · exact Rat.cast_le.mp (by simpa using hz.2.2.le)
  have hclosed := closure_minimal hinterior isClosed_closure
  simpa only [closure_Ioo (show (0 : ℝ) ≠ 1 by norm_num)] using hclosed

structure FiniteConstructionRates where
  occurrences : ℕ
  multiplicity : ℕ
  auxiliaryRank : ℕ
  volume : ℕ
  occurrences_pos : 0 < occurrences
  multiplicity_pos : 0 < multiplicity
  auxiliaryRank_pos : 0 < auxiliaryRank
  volume_pos : 0 < volume

def FiniteConstructionRates.score (r : FiniteConstructionRates) (β : ℝ) : ℝ :=
  (Real.log r.multiplicity - Real.log r.auxiliaryRank +
    (β / 3) * Real.log r.volume) / r.occurrences

structure AttainableFamily (C X : Type*) where
  law : C → X
  score : C → ℝ

def finiteConstructionFamily {C X : Type*} (β : ℝ) (law : C → X)
    (rates : C → FiniteConstructionRates) : AttainableFamily C X :=
  ⟨law, fun c => (rates c).score β⟩

namespace AttainableFamily

variable {C X : Type*} [TopologicalSpace X] (A : AttainableFamily C X)

def pairs : Set (X × ℝ) :=
  {p | ∃ c, A.law c = p.1 ∧ p.2 ≤ A.score c}

def closedPairs : Set (X × ℝ) := closure A.pairs

def fiber (x : X) : Set ℝ := {t | (x, t) ∈ A.closedPairs}

def value (x : X) : ℝ := sSup (A.fiber x)

theorem finite_mem_closedPairs (c : C) : (A.law c, A.score c) ∈ A.closedPairs :=
  subset_closure ⟨c, rfl, le_rfl⟩

theorem closedPairs_law_mem_of_isClosed {s : Set X} (hs : IsClosed s)
    (hlaw : ∀ c, A.law c ∈ s) : ∀ p ∈ A.closedPairs, p.1 ∈ s := by
  apply closure_minimal
  · rintro p ⟨c, hc, _⟩
    change p.1 ∈ s
    rw [← hc]
    exact hlaw c
  · exact hs.preimage continuous_fst

theorem closedPairs_downward {x : X} {u v : ℝ}
    (hu : (x, u) ∈ A.closedPairs) (hvu : v ≤ u) :
    (x, v) ∈ A.closedPairs := by
  let T : X × ℝ → X × ℝ := fun p => (p.1, p.2 - (u - v))
  have hT : Continuous T :=
    continuous_fst.prodMk (continuous_snd.sub continuous_const)
  have himage : T '' A.pairs ⊆ A.pairs := by
    rintro _ ⟨p, ⟨c, hc, hscore⟩, rfl⟩
    exact ⟨c, hc, by dsimp [T]; linarith⟩
  have hmem : T (x, u) ∈ closure (T '' A.pairs) :=
    image_closure_subset_closure_image hT ⟨(x, u), hu, rfl⟩
  have := closure_mono himage hmem
  simpa [T, closedPairs] using this

theorem isClosed_fiber (x : X) : IsClosed (A.fiber x) :=
  isClosed_closure.preimage (continuous_const.prodMk continuous_id)

theorem value_mem_closedPairs (x : X) (hne : (A.fiber x).Nonempty)
    (hbound : BddAbove (A.fiber x)) : (x, A.value x) ∈ A.closedPairs :=
  (A.isClosed_fiber x).csSup_mem hne hbound

theorem mem_closedPairs_iff_le_value (x : X) (hne : (A.fiber x).Nonempty)
    (hbound : BddAbove (A.fiber x)) (t : ℝ) :
    (x, t) ∈ A.closedPairs ↔ t ≤ A.value x := by
  constructor
  · exact fun ht => le_csSup hbound ht
  · exact fun ht => A.closedPairs_downward (A.value_mem_closedPairs x hne hbound) ht

theorem closedPairs_le_continuous_cap (H : X → ℝ) (hH : Continuous H)
    (hcap : ∀ c, A.score c ≤ H (A.law c)) :
    ∀ p ∈ A.closedPairs, p.2 ≤ H p.1 := by
  apply closure_minimal
  · rintro p ⟨c, hc, ht⟩
    exact ht.trans (hc ▸ hcap c)
  · exact isClosed_le continuous_snd (hH.comp continuous_fst)

theorem value_le_continuous_cap (H : X → ℝ) (hH : Continuous H)
    (hcap : ∀ c, A.score c ≤ H (A.law c)) (x : X)
    (hne : (A.fiber x).Nonempty) : A.value x ≤ H x :=
  csSup_le hne (fun _ ht => A.closedPairs_le_continuous_cap H hH hcap _ ht)

theorem value_nonneg (x : X) (hzero : (x, 0) ∈ A.closedPairs)
    (hbound : BddAbove (A.fiber x)) : 0 ≤ A.value x :=
  le_csSup hbound hzero

theorem upperSemicontinuous_value
    (hne : ∀ x, (A.fiber x).Nonempty) (hbound : ∀ x, BddAbove (A.fiber x)) :
    UpperSemicontinuous A.value := by
  intro x b hb
  have hnot : (x, b) ∉ A.closedPairs := by
    intro hmem
    exact (not_le_of_gt hb)
      ((A.mem_closedPairs_iff_le_value x (hne x) (hbound x) b).mp hmem)
  have hclosed : IsClosed {y : X | (y, b) ∈ A.closedPairs} :=
    isClosed_closure.preimage (continuous_id.prodMk continuous_const)
  have hnear : ∀ᶠ y in 𝓝 x, (y, b) ∉ A.closedPairs :=
    hclosed.isOpen_compl.mem_nhds hnot
  filter_upwards [hnear] with y hy
  exact lt_of_not_ge (fun hle =>
    hy ((A.mem_closedPairs_iff_le_value y (hne y) (hbound y) b).mpr hle))

theorem upperSemicontinuous_value_comp {Y : Type*} [TopologicalSpace Y]
    (α : Y → X) (hα : Continuous α)
    (hne : ∀ y, (A.fiber (α y)).Nonempty)
    (hbound : ∀ y, BddAbove (A.fiber (α y))) :
    UpperSemicontinuous (fun y => A.value (α y)) := by
  intro y b hb
  have hnot : (α y, b) ∉ A.closedPairs := by
    intro hmem
    exact (not_le_of_gt hb)
      ((A.mem_closedPairs_iff_le_value (α y) (hne y) (hbound y) b).mp hmem)
  have hclosed : IsClosed {z : Y | (α z, b) ∈ A.closedPairs} :=
    isClosed_closure.preimage (hα.prodMk continuous_const)
  have hnear : ∀ᶠ z in 𝓝 y, (α z, b) ∉ A.closedPairs :=
    hclosed.isOpen_compl.mem_nhds hnot
  filter_upwards [hnear] with z hz
  exact lt_of_not_ge (fun hle =>
    hz ((A.mem_closedPairs_iff_le_value (α z) (hne z) (hbound z) b).mpr hle))

theorem exists_finite_in_open_gt {x : X} {b : ℝ} (hne : (A.fiber x).Nonempty)
    (hb : b < A.value x) {U : Set X} (hU : IsOpen U) (hx : x ∈ U) :
    ∃ c, A.law c ∈ U ∧ b < A.score c := by
  obtain ⟨t, ht, hbt⟩ := exists_lt_of_lt_csSup hne hb
  have hopen : IsOpen (U ×ˢ Ioi b) := hU.prod isOpen_Ioi
  obtain ⟨p, hpU, hpA⟩ := mem_closure_iff.mp ht (U ×ˢ Ioi b) hopen ⟨hx, hbt⟩
  obtain ⟨c, hc, hscore⟩ := hpA
  refine ⟨c, hc.symm ▸ hpU.1, lt_of_lt_of_le hpU.2 hscore⟩

theorem exists_finite_gt {x : X} {b : ℝ} (hne : (A.fiber x).Nonempty)
    (hb : b < A.value x) : ∃ c, b < A.score c := by
  obtain ⟨c, _, hc⟩ := A.exists_finite_in_open_gt hne hb isOpen_univ (mem_univ x)
  exact ⟨c, hc⟩

section Concavity

variable [AddCommGroup X] [Module ℝ X]

theorem concaveOn_value (s : Set X) (hs : Convex ℝ s)
    (hne : ∀ x ∈ s, (A.fiber x).Nonempty)
    (hbound : ∀ x ∈ s, BddAbove (A.fiber x))
    (hmix : Convex ℝ A.closedPairs) : ConcaveOn ℝ s A.value := by
  refine ⟨hs, ?_⟩
  intro x hx y hy a b ha hb hab
  have hpair := hmix (A.value_mem_closedPairs x (hne x hx) (hbound x hx))
    (A.value_mem_closedPairs y (hne y hy) (hbound y hy)) ha hb hab
  exact le_csSup (hbound _ (hs hx hy ha hb hab)) hpair

end Concavity

section RationalMixtures

variable [AddCommGroup X] [Module ℝ X] [ContinuousAdd X] [ContinuousSMul ℝ X]

theorem closedPairs_convex_of_rational_mixing
    (hmix : ∀ c d : C, ∀ q : ℚ, q ∈ Icc 0 1 →
      (q : ℝ) • (A.law c, A.score c) +
        (1 - (q : ℝ)) • (A.law d, A.score d) ∈ A.pairs) :
    Convex ℝ A.closedPairs := by
  have hfull : ∀ c d : C, ∀ t : ℝ, t ∈ Icc 0 1 →
      t • (A.law c, A.score c) + (1 - t) • (A.law d, A.score d) ∈
        A.closedPairs := by
    intro c d t ht
    let T : ℝ → X × ℝ := fun u =>
      u • (A.law c, A.score c) + (1 - u) • (A.law d, A.score d)
    have hT : Continuous T :=
      (continuous_id.smul continuous_const).add
        ((continuous_const.sub continuous_id).smul continuous_const)
    have himage : T '' (((↑) : ℚ → ℝ) '' Icc 0 1) ⊆ A.pairs := by
      rintro _ ⟨_, ⟨q, hq, rfl⟩, rfl⟩
      exact hmix c d q hq
    exact closure_mono himage
      (image_closure_subset_closure_image hT ⟨t, unitInterval_subset_closure_rat ht, rfl⟩)
  intro x hx y hy a b ha hb hab
  have hb_eq : b = 1 - a := by linarith
  subst b
  have ha1 : a ≤ 1 := by linarith
  let T : (X × ℝ) → (X × ℝ) → X × ℝ := fun p q => a • p + (1 - a) • q
  have hT : Continuous (Function.uncurry T) := by
    change Continuous (fun p : (X × ℝ) × (X × ℝ) => a • p.1 + (1 - a) • p.2)
    have hfst : Continuous (fun p : (X × ℝ) × (X × ℝ) => a • p.1) :=
      continuous_fst.const_smul a
    have hsnd : Continuous (fun p : (X × ℝ) × (X × ℝ) => (1 - a) • p.2) :=
      continuous_snd.const_smul (1 - a)
    exact hfst.add hsnd
  have hseed : ∀ p ∈ A.pairs, ∀ q ∈ A.pairs, T p q ∈ A.closedPairs := by
    rintro p ⟨c, hc, hp⟩ q ⟨d, hd, hq⟩
    have h := hfull c d a ⟨ha, ha1⟩
    have hlaw : a • A.law c + (1 - a) • A.law d =
        a • p.1 + (1 - a) • q.1 := by rw [hc, hd]
    have hscore : a * p.2 + (1 - a) * q.2 ≤
        a * A.score c + (1 - a) * A.score d :=
      add_le_add (mul_le_mul_of_nonneg_left hp ha)
        (mul_le_mul_of_nonneg_left hq hb)
    change (a • A.law c + (1 - a) • A.law d,
      a * A.score c + (1 - a) * A.score d) ∈ A.closedPairs at h
    rw [hlaw] at h
    exact A.closedPairs_downward h hscore
  have hresult : T x y ∈ closure A.closedPairs := map_mem_closure₂ hT hx hy hseed
  simpa only [closedPairs, closure_closure] using hresult

end RationalMixtures
end AttainableFamily

private abbrev realSimplex (ι : Type*) [Fintype ι] : Set (ι → ℝ) :=
  {weights | (∀ index, 0 ≤ weights index) ∧ ∑ index, weights index = 1}

private theorem convex_realSimplex (ι : Type*) [Fintype ι] :
    Convex ℝ (realSimplex ι) := by
  intro left hleft right hright leftWeight rightWeight hleftWeight hrightWeight hsum
  refine ⟨fun index => add_nonneg (mul_nonneg hleftWeight (hleft.1 index))
    (mul_nonneg hrightWeight (hright.1 index)), ?_⟩
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
    ← Finset.mul_sum, hleft.2, hright.2, mul_one, hsum]

theorem simplex_residual {ι : Type*} [Fintype ι] {x y : ι → ℝ}
    (hx : x ∈ realSimplex ι) (hy : y ∈ realSimplex ι)
    {ε : ℝ} (hε : 0 < ε) (hdom : ∀ i, (1 - ε) * x i ≤ y i) :
    (fun i => (y i - (1 - ε) * x i) / ε) ∈ realSimplex ι := by
  refine ⟨fun i => div_nonneg (sub_nonneg.mpr (hdom i)) hε.le, ?_⟩
  rw [← Finset.sum_div, Finset.sum_sub_distrib, ← Finset.mul_sum, hx.2, hy.2]
  field_simp [ne_of_gt hε]
  ring

theorem concave_simplex_domination {ι : Type*} [Fintype ι] {F : (ι → ℝ) → ℝ}
    (hF : ConcaveOn ℝ (realSimplex ι) F)
    (hzero : ∀ x ∈ realSimplex ι, 0 ≤ F x)
    {x y : ι → ℝ} (hx : x ∈ realSimplex ι) (hy : y ∈ realSimplex ι)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hdom : ∀ i, (1 - ε) * x i ≤ y i) : (1 - ε) * F x ≤ F y := by
  let r : ι → ℝ := fun i => (y i - (1 - ε) * x i) / ε
  have hr : r ∈ realSimplex ι := simplex_residual hx hy hε hdom
  have hmix : (1 - ε) • x + ε • r = y := by
    funext i
    dsimp [r]
    field_simp [ne_of_gt hε]
    ring
  have hconc := hF.2 hx hr (sub_nonneg.mpr hε1) hε.le (by ring)
  rw [hmix] at hconc
  change (1 - ε) * F x + ε * F r ≤ F y at hconc
  exact le_trans (le_add_of_nonneg_right (mul_nonneg hε.le (hzero r hr))) hconc

theorem lowerSemicontinuousOn_nonneg_concave_simplex {ι : Type*} [Fintype ι]
    {F : (ι → ℝ) → ℝ} (hF : ConcaveOn ℝ (realSimplex ι) F)
    (hzero : ∀ x ∈ realSimplex ι, 0 ≤ F x) :
    LowerSemicontinuousOn F (realSimplex ι) := by
  intro x hx b hb
  by_cases hb0 : b < 0
  · filter_upwards [self_mem_nhdsWithin] with y hy
    exact lt_of_lt_of_le hb0 (hzero y hy)
  have hbnonneg : 0 ≤ b := le_of_not_gt hb0
  have hxpos : 0 < F x := lt_of_le_of_lt hbnonneg hb
  let ε : ℝ := (F x - b) / (2 * F x)
  have hden : 0 < 2 * F x := mul_pos (by norm_num) hxpos
  have hε : 0 < ε := div_pos (sub_pos.mpr hb) hden
  have hε1 : ε ≤ 1 := by
    apply (div_le_iff₀ hden).2
    linarith
  have hεeq : ε * (2 * F x) = F x - b := div_mul_cancel₀ _ (ne_of_gt hden)
  have hgap : b < (1 - ε) * F x := by nlinarith
  have hdom : ∀ᶠ y in 𝓝[realSimplex ι] x, ∀ i, (1 - ε) * x i ≤ y i := by
    apply Filter.eventually_all.2
    intro i
    by_cases hxi : x i = 0
    · filter_upwards [self_mem_nhdsWithin] with y hy
      simpa [hxi] using hy.1 i
    have hxipos : 0 < x i := lt_of_le_of_ne (hx.1 i) (Ne.symm hxi)
    have hlt : (1 - ε) * x i < x i := by nlinarith
    have hev : ∀ᶠ y : ι → ℝ in 𝓝 x, (1 - ε) * x i < y i :=
      (continuous_apply i).continuousAt.eventually (lt_mem_nhds hlt)
    exact (hev.filter_mono nhdsWithin_le_nhds).mono (fun _ h => h.le)
  filter_upwards [self_mem_nhdsWithin, hdom] with y hy hdomy
  exact lt_of_lt_of_le hgap (concave_simplex_domination hF hzero hx hy hε hε1 hdomy)

theorem lowerSemicontinuous_comp_of_mem {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {s : Set X} {F : X → ℝ}
    (hF : LowerSemicontinuousOn F s) (α : Y → X) (hα : Continuous α)
    (hmem : ∀ y, α y ∈ s) : LowerSemicontinuous (fun y => F (α y)) := by
  intro y b hb
  have ht : Tendsto α (𝓝 y) (𝓝[s] α y) :=
    tendsto_nhdsWithin_iff.mpr ⟨hα.continuousAt, Eventually.of_forall hmem⟩
  exact ht.eventually (hF (α y) (hmem y) b hb)

theorem AttainableFamily.continuous_value_on_simplex_chart {C Y ι : Type*}
    [TopologicalSpace Y] [Fintype ι] (A : AttainableFamily C (ι → ℝ))
    (hzero : ∀ x ∈ realSimplex ι, (x, 0) ∈ A.closedPairs)
    (hbound : ∀ x ∈ realSimplex ι, BddAbove (A.fiber x))
    (hmix : Convex ℝ A.closedPairs)
    (α : Y → (ι → ℝ)) (hα : Continuous α)
    (hmem : ∀ y, α y ∈ realSimplex ι) :
    Continuous (fun y => A.value (α y)) := by
  have hne : ∀ x ∈ realSimplex ι, (A.fiber x).Nonempty :=
    fun x hx => ⟨0, hzero x hx⟩
  have hconc := A.concaveOn_value _ (convex_realSimplex ι) hne hbound hmix
  have hnonneg : ∀ x ∈ realSimplex ι, 0 ≤ A.value x :=
    fun x hx => A.value_nonneg x (hzero x hx) (hbound x hx)
  exact continuous_iff_lower_upperSemicontinuous.mpr
    ⟨lowerSemicontinuous_comp_of_mem
      (lowerSemicontinuousOn_nonneg_concave_simplex hconc hnonneg) α hα hmem,
      A.upperSemicontinuous_value_comp α hα
        (fun y => hne _ (hmem y)) (fun y => hbound _ (hmem y))⟩

end MatrixMultiplication.Foundation

end

end OAI
