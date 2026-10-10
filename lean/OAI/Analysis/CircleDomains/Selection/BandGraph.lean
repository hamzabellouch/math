import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.Topology.Algebra.Order.Field

namespace OAI

/-!+# Compact interval-band graphs for bounded real coordinates

Take the closure of the physical graph and fill the interval between
cluster values in each fiber. This constructs a compact band graph;
on the open physical domain it is exactly the original graph. Its
projection modulo one consequently gives compact level sets with the
correct physical fibers.
-/

open Set

namespace CircleDomainRigidity

def clusterGraph {X : Type*} [TopologicalSpace X] (G : Set X) (f : X → ℝ) : Set (X × ℝ) :=
  closure ((fun x => (x, f x)) '' G)

def intervalFiberHull {X : Type*} (K : Set (X × ℝ)) : Set (X × ℝ) :=
  (fun p : (X × ℝ) × (X × ℝ) × ℝ =>
    (p.1.1, (1 - p.2.2) * p.1.2 + p.2.2 * p.2.1.2)) ''
      ((K ×ˢ (K ×ˢ Icc 0 1)) ∩ {p | p.1.1 = p.2.1.1})

theorem isCompact_clusterGraph {X : Type*} [TopologicalSpace X] [CompactSpace X]
    {G : Set X} {f : X → ℝ} {M : ℝ} (hM : ∀ x ∈ G, |f x| ≤ M) :
    IsCompact (clusterGraph G f) := by
  apply (isCompact_univ.prod (isCompact_Icc : IsCompact (Icc (-M) M))).of_isClosed_subset
    isClosed_closure
  apply closure_minimal _ (isClosed_univ.prod isClosed_Icc)
  rintro _ ⟨x, hx, rfl⟩
  exact ⟨mem_univ x, abs_le.mp (hM x hx)⟩

theorem isCompact_intervalFiberHull {X : Type*} [TopologicalSpace X] [T2Space X]
    {K : Set (X × ℝ)} (hK : IsCompact K) : IsCompact (intervalFiberHull K) := by
  apply ((hK.prod (hK.prod isCompact_Icc)).inter_right
    (isClosed_eq (continuous_fst.fst) (continuous_snd.fst.fst))).image
  exact continuous_fst.fst.prodMk
    (((continuous_const.sub continuous_snd.snd).mul continuous_fst.snd).add
      (continuous_snd.snd.mul continuous_snd.fst.snd))

theorem mem_intervalFiberHull_iff {X : Type*} {K : Set (X × ℝ)} {x : X} {t : ℝ} :
    (x, t) ∈ intervalFiberHull K ↔
      ∃ a b s : ℝ, (x, a) ∈ K ∧ (x, b) ∈ K ∧ s ∈ Icc 0 1 ∧
        t = (1 - s) * a + s * b := by
  constructor
  · rintro ⟨⟨⟨y, a⟩, ⟨z, b⟩, s⟩, ⟨⟨ha, hb, hs⟩, heq⟩, hout⟩
    obtain ⟨rfl, ht⟩ := Prod.mk.inj hout
    change y = z at heq
    subst z
    exact ⟨a, b, s, ha, hb, hs, ht.symm⟩
  · rintro ⟨a, b, s, ha, hb, hs, rfl⟩
    exact ⟨((x, a), (x, b), s), ⟨⟨ha, hb, hs⟩, rfl⟩, rfl⟩

theorem subset_intervalFiberHull {X : Type*} (K : Set (X × ℝ)) :
    K ⊆ intervalFiberHull K := by
  rintro ⟨x, t⟩ ht
  apply mem_intervalFiberHull_iff.mpr
  exact ⟨t, t, 0, ht, ht, by norm_num, by ring⟩

theorem isCompact_real_fiber {X : Type*} [TopologicalSpace X] [T2Space X]
    {K : Set (X × ℝ)} (hK : IsCompact K) (x : X) :
    IsCompact {t : ℝ | (x, t) ∈ K} := by
  have hc : IsCompact (Prod.snd '' (K ∩ {p | p.1 = x})) :=
    (hK.inter_right (isClosed_eq continuous_fst continuous_const)).image continuous_snd
  convert hc using 1
  ext t
  constructor
  · intro ht
    exact ⟨(x, t), ⟨ht, rfl⟩, rfl⟩
  · rintro ⟨⟨y, a⟩, ⟨ha, heq⟩, rfl⟩
    change y = x at heq
    change (x, a) ∈ K
    simpa only [heq] using ha

/-- The interpolated fiber is exactly the interval between the smallest
and largest cluster values, with the endpoints attained in the compact
original fiber. -/
theorem intervalFiberHull_fiber_eq_Icc
    {X : Type*} [TopologicalSpace X] [T2Space X] {K : Set (X × ℝ)}
    (hK : IsCompact K) (x : X) (hne : {t : ℝ | (x, t) ∈ K}.Nonempty) :
    {t : ℝ | (x, t) ∈ intervalFiberHull K} =
      Icc (sInf {t : ℝ | (x, t) ∈ K}) (sSup {t : ℝ | (x, t) ∈ K}) := by
  let F : Set ℝ := {t | (x, t) ∈ K}
  have hlo := (isCompact_real_fiber hK x).isLeast_sInf hne
  have hhi := (isCompact_real_fiber hK x).isGreatest_sSup hne
  ext t
  constructor
  · intro ht
    obtain ⟨a, b, s, ha, hb, hs, rfl⟩ := mem_intervalFiberHull_iff.mp ht
    constructor
    · nlinarith [mul_nonneg (sub_nonneg.mpr hs.2) (sub_nonneg.mpr (hlo.2 ha)),
        mul_nonneg hs.1 (sub_nonneg.mpr (hlo.2 hb))]
    · nlinarith [mul_nonneg (sub_nonneg.mpr hs.2) (sub_nonneg.mpr (hhi.2 ha)),
        mul_nonneg hs.1 (sub_nonneg.mpr (hhi.2 hb))]
  · intro ht
    apply mem_intervalFiberHull_iff.mpr
    by_cases heq : sInf F = sSup F
    · have htEq : t = sInf F := le_antisymm (ht.2.trans_eq heq.symm) ht.1
      refine ⟨sInf F, sSup F, 0, hlo.1, hhi.1, by norm_num, ?_⟩
      rw [htEq]
      ring
    · have hlt : sInf F < sSup F := lt_of_le_of_ne (hlo.2 hhi.1) heq
      have hd : 0 < sSup F - sInf F := sub_pos.mpr hlt
      refine ⟨sInf F, sSup F, (t - sInf F) / (sSup F - sInf F), hlo.1, hhi.1,
        ⟨div_nonneg (sub_nonneg.mpr ht.1) hd.le, (div_le_one hd).mpr (by linarith [ht.2])⟩, ?_⟩
      field_simp
      ring

theorem clusterGraph_fiber_nonempty_of_mem_closure
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    {G : Set X} {f : X → ℝ} {M : ℝ} (hM : ∀ x ∈ G, |f x| ≤ M)
    {x : X} (hx : x ∈ closure G) : {t : ℝ | (x, t) ∈ clusterGraph G f}.Nonempty := by
  have hsub : closure G ⊆ Prod.fst '' clusterGraph G f := by
    apply closure_minimal _ ((isCompact_clusterGraph hM).image continuous_fst).isClosed
    intro y hy
    exact ⟨(y, f y), subset_closure ⟨y, hy, rfl⟩, rfl⟩
  obtain ⟨⟨y, t⟩, ht, heq⟩ := hsub hx
  change y = x at heq
  exact ⟨t, heq ▸ ht⟩

theorem clusterGraph_fiber_eq_of_continuousAt
    {X : Type*} [TopologicalSpace X] {G : Set X} {f : X → ℝ} {x : X}
    (hf : ContinuousAt f x) {t : ℝ} (ht : (x, t) ∈ clusterGraph G f) : t = f x := by
  have hc : ContinuousAt (fun p : X × ℝ => p.2 - f p.1) (x, t) :=
    continuousAt_snd.sub (hf.comp continuousAt_fst)
  have hz : t - f x ∈ closure ({0} : Set ℝ) := hc.continuousWithinAt.mem_closure ht (by
    rintro _ ⟨y, hy, rfl⟩
    simp)
  simpa only [closure_singleton, mem_singleton_iff, sub_eq_zero] using hz

theorem intervalFiberHull_clusterGraph_on_open
    {X : Type*} [TopologicalSpace X] {G : Set X} (hG : IsOpen G) {f : X → ℝ}
    (hf : ContinuousOn f G) {x : X} (hx : x ∈ G) {t : ℝ} :
    (x, t) ∈ intervalFiberHull (clusterGraph G f) ↔ t = f x := by
  constructor
  · intro ht
    obtain ⟨a, b, s, ha, hb, _, ht⟩ := mem_intervalFiberHull_iff.mp ht
    have hfx := hf.continuousAt (hG.mem_nhds hx)
    rw [clusterGraph_fiber_eq_of_continuousAt hfx ha,
      clusterGraph_fiber_eq_of_continuousAt hfx hb] at ht
    nlinarith [ht]
  · rintro rfl
    exact subset_intervalFiberHull _ (subset_closure ⟨x, hx, rfl⟩)

def circleBandGraph {X : Type*} [TopologicalSpace X] (G : Set X) (f : X → ℝ) :
    Set (X × AddCircle (1 : ℝ)) :=
  (fun p : X × ℝ => (p.1, (p.2 : AddCircle (1 : ℝ)))) ''
    intervalFiberHull (clusterGraph G f)

theorem isCompact_circleBandGraph {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [T2Space X] {G : Set X} {f : X → ℝ} {M : ℝ} (hM : ∀ x ∈ G, |f x| ≤ M) :
    IsCompact (circleBandGraph G f) := by
  exact (isCompact_intervalFiberHull (isCompact_clusterGraph hM)).image
    (continuous_fst.prodMk ((AddCircle.continuous_mk' (1 : ℝ)).comp continuous_snd))

theorem circleBandGraph_on_open {X : Type*} [TopologicalSpace X]
    {G : Set X} (hG : IsOpen G) {f : X → ℝ} (hf : ContinuousOn f G)
    {x : X} (hx : x ∈ G) {t : AddCircle (1 : ℝ)} :
    (x, t) ∈ circleBandGraph G f ↔ (f x : AddCircle (1 : ℝ)) = t := by
  constructor
  · rintro ⟨⟨y, a⟩, ha, hout⟩
    obtain ⟨rfl, ht⟩ := Prod.mk.inj hout
    rwa [(intervalFiberHull_clusterGraph_on_open hG hf hx).mp ha] at ht
  · intro ht
    exact ⟨(x, f x), (intervalFiberHull_clusterGraph_on_open hG hf hx).mpr rfl,
      Prod.ext rfl ht⟩

theorem isCompact_circleBandLevel {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [T2Space X] {G : Set X} {f : X → ℝ} {M : ℝ} (hM : ∀ x ∈ G, |f x| ≤ M)
    (t : AddCircle (1 : ℝ)) : IsCompact {x | (x, t) ∈ circleBandGraph G f} :=
  ((isCompact_circleBandGraph hM).isClosed.preimage (continuous_id.prodMk continuous_const)).isCompact

theorem isCompact_circleBandIncidence {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [T2Space X] {G : Set X} {f : X → ℝ} {M : ℝ} (hM : ∀ x ∈ G, |f x| ≤ M)
    (x : X) : IsCompact {t : AddCircle (1 : ℝ) | (x, t) ∈ circleBandGraph G f} :=
  ((isCompact_circleBandGraph hM).isClosed.preimage (continuous_const.prodMk continuous_id)).isCompact

end CircleDomainRigidity

end OAI
