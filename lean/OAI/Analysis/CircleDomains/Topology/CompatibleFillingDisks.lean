import OAI.Analysis.CircleDomains.Topology.FillingDisks
import OAI.Analysis.CircleDomains.Transfer.GridObstacles
import OAI.Analysis.CircleDomains.Selection.TerminalCounts

namespace OAI

/-!
# Filling disks for the actual free/flagged grid setup

The levels below are the actual equally spaced circle levels of the compact
band graph. At a free point a singleton real band gives one level per label.
At a flagged point outside the terminal collision set, two distinct label
grids cannot occur. The pair family may represent each unordered pair in
either orientation. These facts discharge the lower-obstacle premise of
the descending contour construction.
-/

open Set Function
open scoped Topology Manifold ContDiff

namespace CircleDomainRigidity.FiniteTransfer

def reciprocalBandLevel {X : Type*} [TopologicalSpace X]
    (G : Set X) (f : X → ℝ) (θ : ℝ) (N : ℕ) (k : Fin (N + 1)) : Set X :=
  {x | (x, ((θ + (k.val : ℝ) * reciprocalGridStep N : ℝ) : UnitAddCircle)) ∈
    circleBandGraph G f}

/-- The manuscript's ordered compatibility: a new label meets no
nontrivial component formed using only earlier labels at a free point. -/
def OrderedBandGridCompatibility {X S : Type*} [TopologicalSpace X] {n : ℕ}
    (G : Set X) (f : Fin n → X → ℝ) (θ : Fin n → ℝ) (N : ℕ)
    (A : Set X) (σ : S → X) : Prop :=
  ∀ x ∈ A, x ∉ range σ → ∀ j : Fin n,
    x ∈ ⋃ k, reciprocalBandLevel G (f j) (θ j) N k →
    ∀ I : Finset (Fin n), (∀ i ∈ I, i.val < j.val) → ∀ k : Fin n → Fin (N + 1),
      ¬ (connectedComponentIn
        (⋃ i ∈ I, reciprocalBandLevel G (f i) (θ i) N (k i)) x).Nontrivial

theorem isClosed_reciprocalBandLevel
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    {G : Set X} {f : X → ℝ} {M : ℝ} (hf : ∀ x ∈ G, |f x| ≤ M)
    (θ : ℝ) (N : ℕ) (k : Fin (N + 1)) :
    IsClosed (reciprocalBandLevel G f θ N k) :=
  (isCompact_circleBandLevel hf _).isClosed

theorem reciprocal_circle_levels_injective (θ : ℝ) (N : ℕ) :
    Injective (fun k : Fin (N + 1) =>
      ((θ + (k.val : ℝ) * reciprocalGridStep N : ℝ) : UnitAddCircle)) := by
  intro k l hkl
  obtain ⟨m, hm⟩ := (addCircle_eq_iff_exists_int 1 _ _).mp hkl
  have hh := reciprocalGridStep_pos N
  have hden := reciprocalGridStep_mul_denominator N
  have hbound (i : Fin (N + 1)) : 0 ≤ (i.val : ℝ) * reciprocalGridStep N ∧
      (i.val : ℝ) * reciprocalGridStep N < 1 := by
    refine ⟨mul_nonneg (Nat.cast_nonneg _) hh.le, ?_⟩
    have hi : (i.val : ℝ) < (N : ℝ) + 1 := by exact_mod_cast i.isLt
    nlinarith [mul_pos (sub_pos.mpr hi) hh]
  have hmlo : (-1 : ℤ) < m := by
    have : (-1 : ℝ) < (m : ℝ) := by linarith [(hbound k).1, (hbound l).2]
    exact_mod_cast this
  have hmhi : m < (1 : ℤ) := by
    have : (m : ℝ) < 1 := by linarith [(hbound k).2, (hbound l).1]
    exact_mod_cast this
  have hm0 : m = 0 := by omega
  subst m
  simp only [Int.cast_zero, zero_mul, add_zero] at hm
  apply Fin.ext
  have hk : (k.val : ℝ) = (l.val : ℝ) := by nlinarith
  exact_mod_cast hk

theorem reciprocalBandLevel_unique_of_singleton_fiber
    {X : Type*} [TopologicalSpace X] {G : Set X} {f : X → ℝ}
    {θ : ℝ} {N : ℕ} {x : X} {v : ℝ}
    (htrace : {r : ℝ | (x, r) ∈ intervalFiberHull (clusterGraph G f)} = {v})
    {k l : Fin (N + 1)} (hk : x ∈ reciprocalBandLevel G f θ N k)
    (hl : x ∈ reciprocalBandLevel G f θ N l) : k = l := by
  have hlevel (i : Fin (N + 1)) (hi : x ∈ reciprocalBandLevel G f θ N i) :
      (v : UnitAddCircle) = ((θ + (i.val : ℝ) * reciprocalGridStep N : ℝ) : UnitAddCircle) := by
    have hi' : ((θ + (i.val : ℝ) * reciprocalGridStep N : ℝ) : UnitAddCircle) ∈
        ((↑) : ℝ → UnitAddCircle) '' {r : ℝ | (x, r) ∈ intervalFiberHull (clusterGraph G f)} := by
      rw [← circleBandGraph_fiber_eq_image_realFiber]
      exact hi
    rw [htrace] at hi'
    have heq : ((θ + (i.val : ℝ) * reciprocalGridStep N : ℝ) : UnitAddCircle) =
        (v : UnitAddCircle) := by
      simpa only [image_singleton, mem_singleton_iff] using hi'
    exact heq.symm
  exact reciprocal_circle_levels_injective θ N ((hlevel k hk).symm.trans (hlevel l hl))

theorem latticeBandIncidence_of_reciprocalBandLevel
    {X : Type*} [TopologicalSpace X] {G : Set X} {f : X → ℝ}
    {θ a b : ℝ} {N : ℕ} {x : X}
    (hband : {r : ℝ | (x, r) ∈ intervalFiberHull (clusterGraph G f)} = Icc a b)
    {k : Fin (N + 1)} (hk : x ∈ reciprocalBandLevel G f θ N k) :
    θ ∈ latticeBandIncidence (reciprocalGridStep N) a b := by
  have hk' : ((θ + (k.val : ℝ) * reciprocalGridStep N : ℝ) : UnitAddCircle) ∈
      ((↑) : ℝ → UnitAddCircle) '' Icc a b := by
    rw [← hband, ← circleBandGraph_fiber_eq_image_realFiber]
    exact hk
  obtain ⟨r, hr, heq⟩ := hk'
  obtain ⟨m, hm⟩ := (addCircle_eq_iff_exists_int 1 _ _).mp heq
  refine ⟨(k.val : ℤ) + m * (N + 1), ?_⟩
  have hden : ((N : ℝ) + 1) * reciprocalGridStep N = 1 := by
    simpa only [mul_comm] using reciprocalGridStep_mul_denominator N
  have hval : θ + (((k.val : ℤ) + m * (N + 1) : ℤ) : ℝ) * reciprocalGridStep N = r := by
    push_cast
    calc
      _ = θ + (k.val : ℝ) * reciprocalGridStep N +
          (m : ℝ) * (((N : ℝ) + 1) * reciprocalGridStep N) := by ring
      _ = r := by rw [hden]; simpa only [mul_one] using hm.symm
  exact hval.symm ▸ hr

/-- Actual collision terminals exclude every pair of distinct flagged grids. -/
theorem no_two_flagged_grids_outside_terminals
    {n N : ℕ} {P S X : Type*} [TopologicalSpace X]
    (G : Set X) (f : Fin n → X → ℝ) (σ : S → X)
    (a b : Fin n → S → ℝ) (θ : Fin n → ℝ)
    (pairs : P → Fin n × Fin n)
    (hpairs : ∀ i j : Fin n, i ≠ j → ∃ p, pairs p = (i, j) ∨ pairs p = (j, i))
    (F : Set S)
    (hband : ∀ i s, {r : ℝ | (σ s, r) ∈ intervalFiberHull (clusterGraph G (f i))} =
      Icc (a i s) (b i s))
    {s : S} (hs : s ∉ gridTerminalIndices F (reciprocalGridStep N) pairs a b θ)
    {i j : Fin n} (hij : i ≠ j)
    (hi : σ s ∈ ⋃ k, reciprocalBandLevel G (f i) (θ i) N k)
    (hj : σ s ∈ ⋃ k, reciprocalBandLevel G (f j) (θ j) N k) : False := by
  obtain ⟨p, hp⟩ := hpairs i j hij
  obtain ⟨k, hk⟩ := mem_iUnion.mp hi
  obtain ⟨l, hl⟩ := mem_iUnion.mp hj
  apply hs
  right
  refine ⟨p, ?_⟩
  change θ (pairs p).1 ∈ latticeBandIncidence _ _ _ ∧
    θ (pairs p).2 ∈ latticeBandIncidence _ _ _
  rcases hp with hp | hp
  · rw [hp]
    exact ⟨latticeBandIncidence_of_reciprocalBandLevel (hband i s) hk,
      latticeBandIncidence_of_reciprocalBandLevel (hband j s) hl⟩
  · rw [hp]
    exact ⟨latticeBandIncidence_of_reciprocalBandLevel (hband j s) hl,
      latticeBandIncidence_of_reciprocalBandLevel (hband i s) hk⟩

theorem lower_obstacle_singleton_of_compatible_bands
    {n N : ℕ} {P S X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (G : Set X) (f : Fin n → X → ℝ) (M : Fin n → ℝ)
    (hbounded : ∀ i x, x ∈ G → |f i x| ≤ M i)
    (σ : S → X) (a b : Fin n → S → ℝ) (θ : Fin n → ℝ)
    (pairs : P → Fin n × Fin n)
    (hpairs : ∀ i j : Fin n, i ≠ j → ∃ p, pairs p = (i, j) ∨ pairs p = (j, i))
    (F : Set S)
    (hband : ∀ i s, {r : ℝ | (σ s, r) ∈ intervalFiberHull (clusterGraph G (f i))} =
      Icc (a i s) (b i s))
    {B A : Set X} (hB : IsClosed B) (hTD : IsTotallyDisconnected B) (hAB : A ⊆ B)
    (hnoterm : Disjoint A (σ '' gridTerminalIndices F (reciprocalGridStep N) pairs a b θ))
    (hfree : ∀ x ∈ A, x ∉ range σ → ∀ i,
      ∃ v : ℝ, {r : ℝ | (x, r) ∈ intervalFiberHull (clusterGraph G (f i))} = {v})
    (hcompat : OrderedBandGridCompatibility G f θ N A σ)
    (j : Fin n) {x : X}
    (hx : x ∈ A ∩ ⋃ k, reciprocalBandLevel G (f j) (θ j) N k) :
    connectedComponentIn
      (B ∪ ⋃ i : Fin n, ⋃ (_ : i.val < j.val), ⋃ k,
        reciprocalBandLevel G (f i) (θ i) N k) x = {x} := by
  let L : Fin n → Fin (N + 1) → Set X := fun i k =>
    reciprocalBandLevel G (f i) (θ i) N k
  have hL (i : Fin n) (k : Fin (N + 1)) : IsClosed (L i k) :=
    isClosed_reciprocalBandLevel (hbounded i) (θ i) N k
  by_cases hflag : x ∈ range σ
  · obtain ⟨s, rfl⟩ := hflag
    have hs : s ∉ gridTerminalIndices F (reciprocalGridStep N) pairs a b θ := by
      intro hs
      exact Set.disjoint_left.mp hnoterm hx.1 ⟨s, hs, rfl⟩
    have hlower : σ s ∉ ⋃ i : Fin n, ⋃ (_ : i.val < j.val), ⋃ k, L i k := by
      intro h
      obtain ⟨i, hi⟩ := mem_iUnion.mp h
      obtain ⟨hij, hi⟩ := mem_iUnion.mp hi
      exact no_two_flagged_grids_outside_terminals G f σ a b θ pairs hpairs F hband hs
        (fun heq => (ne_of_lt hij) (congrArg Fin.val heq)) hi hx.2
    rw [union_comm]
    apply component_union_dust_eq_singleton
      (isClosed_iUnion_of_finite (fun i => isClosed_iUnion_of_finite
        (fun _ => isClosed_iUnion_of_finite (hL i)))) hB hTD (Or.inr (hAB hx.1))
    exact fun h => (hlower h).elim
  · let e : Fin j.val → Fin n := fun i => ⟨i.val, i.isLt.trans j.isLt⟩
    have heq : (⋃ i : Fin j.val, ⋃ k, L (e i) k) =
        ⋃ i : Fin n, ⋃ (_ : i.val < j.val), ⋃ k, L i k := by
      ext y
      constructor
      · rintro ⟨_, ⟨i, hi, rfl⟩, hy⟩
        exact mem_iUnion₂.mpr ⟨e i, i.isLt, hy⟩
      · intro hy
        obtain ⟨i, hi, hy⟩ := mem_iUnion₂.mp hy
        exact mem_iUnion.mpr ⟨⟨i.val, hi⟩, hy⟩
    have hwhole : connectedComponentIn ((⋃ i : Fin j.val, ⋃ k, L (e i) k) ∪ B) x = {x} := by
      apply component_lower_grid_union_dust_eq_singleton (fun i k => L (e i) k)
        (fun i k => hL (e i) k) hB hTD (hAB hx.1)
      · intro i k l hk hl
        obtain ⟨v, hv⟩ := hfree x hx.1 hflag (e i)
        exact reciprocalBandLevel_unique_of_singleton_fiber hv hk hl
      · intro I k hnon
        let k' : Fin n → Fin (N + 1) := fun i => if hi : i.val < j.val then k ⟨i.val, hi⟩ else 0
        have hsmall : ∀ i ∈ I.image e, i.val < j.val := by
          intro i hi
          obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp hi
          exact r.isLt
        apply hcompat x hx.1 hflag j hx.2 (I.image e) hsmall k'
        apply hnon.mono (connectedComponentIn_mono x ?_)
        intro y hy
        obtain ⟨i, hi, hy⟩ := mem_iUnion₂.mp hy
        apply mem_iUnion₂.mpr
        refine ⟨e i, Finset.mem_image.mpr ⟨i, hi, rfl⟩, ?_⟩
        simpa only [k', e, dite_eq_left i.isLt] using hy
    rw [union_comm, ← heq]
    exact hwhole

/-- Compact band grids admit filling disks by free-point compatibility
and the selected collision terminals. -/
theorem exists_filling_disks_of_compatible_bands
    (hsard : SmoothPlanarSard) (hschoenflies : PlanarSchoenflies)
    (G : Set Sphere) (π : Sphere → Sphere) (hπ : Continuous π)
    (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔
      x = y ∨ (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x))
    {n N : ℕ} {P S : Type*} (U : Set Sphere) (f : Fin n → Sphere → ℝ)
    (M : Fin n → ℝ) (hbounded : ∀ i x, x ∈ U → |f i x| ≤ M i)
    (σ : S → Sphere) (a b : Fin n → S → ℝ) (θ : Fin n → ℝ)
    (pairs : P → Fin n × Fin n)
    (hpairs : ∀ i j : Fin n, i ≠ j → ∃ p, pairs p = (i, j) ∨ pairs p = (j, i))
    (F : Set S)
    (hband : ∀ i s, {r : ℝ | (σ s, r) ∈ intervalFiberHull (clusterGraph U (f i))} =
      Icc (a i s) (b i s))
    {B A W : Set Sphere} (hB : IsClosed B) (hTD : IsTotallyDisconnected B)
    (hA : IsCompact A) (hAB : A ⊆ B) (hBA : IsClosed (B \ A))
    (hW : IsOpen W) (hAW : A ⊆ W) (hinfty : π OnePoint.infty ∉ A)
    (hbad : ∀ p ∈ Gᶜ, π p ∈ B)
    (hnoterm : Disjoint A (σ '' gridTerminalIndices F (reciprocalGridStep N) pairs a b θ))
    (hfree : ∀ x ∈ A, x ∉ range σ → ∀ i,
      ∃ v : ℝ, {r : ℝ | (x, r) ∈ intervalFiberHull (clusterGraph U (f i))} = {v})
    (hcompat : OrderedBandGridCompatibility U f θ N A σ) :
    ∃ (m : ℕ) (H : Fin m → ℂ ≃ₜ ℂ) (γ : Fin m → Circle → ℂ),
      ((fun z : ℂ => π (z : Sphere)) ⁻¹' A ⊆ ⋃ i, jordanInterior (H i)) ∧
      Pairwise (Disjoint on fun i => closure (jordanInterior (H i))) ∧
      ∀ i, closure (jordanInterior (H i)) ⊆ (fun z : ℂ => π (z : Sphere)) ⁻¹' W ∧
        ContMDiff (𝓡 1) (𝓘(ℝ, ℂ)) ∞ (γ i) ∧ Topology.IsEmbedding (γ i) ∧
        frontier (jordanInterior (H i)) = range (γ i) ∧
        (∀ z ∈ frontier (jordanInterior (H i)), (z : Sphere) ∈ G ∧ π (z : Sphere) ∉ B) ∧
        ∃ k : ℕ, ∀ j : Fin n, j.val ≠ k →
          Disjoint (frontier (jordanInterior (H i)))
            ((fun z : ℂ => π (z : Sphere)) ⁻¹' (⋃ l, reciprocalBandLevel U (f j) (θ j) N l)) := by
  classical
  let L : Fin n → Set Sphere := fun j => ⋃ k, reciprocalBandLevel U (f j) (θ j) N k
  let J : ℕ → Set Sphere := fun j => if hj : j < n then L ⟨j, hj⟩ else ∅
  have hJ (j : ℕ) : IsClosed (J j) := by
    by_cases hj : j < n
    · simpa only [J, dite_eq_left hj] using
        (isClosed_iUnion_of_finite (fun k =>
          isClosed_reciprocalBandLevel (hbounded ⟨j, hj⟩) (θ ⟨j, hj⟩) N k))
    · simp only [J, dite_eq_right hj, isClosed_empty]
  have hlower (j : Fin n) : (⋃ k ∈ Finset.range j.val, J k) =
      ⋃ i : Fin n, ⋃ (_ : i.val < j.val), L i := by
    ext x
    constructor
    · intro hx
      obtain ⟨k, hk, hx⟩ := mem_iUnion₂.mp hx
      have hkj := Finset.mem_range.mp hk
      have hkn := hkj.trans j.isLt
      exact mem_iUnion₂.mpr ⟨⟨k, hkn⟩, hkj, by simpa only [J, dite_eq_left hkn] using hx⟩
    · intro hx
      obtain ⟨i, hi, hx⟩ := mem_iUnion₂.mp hx
      exact mem_iUnion₂.mpr ⟨i.val, Finset.mem_range.mpr hi,
        by simpa only [J, dite_eq_left i.isLt] using hx⟩
  have hsingle (j : ℕ) (hj : j < n) (x : Sphere) (hx : x ∈ A ∩ J j) :
      connectedComponentIn (B ∪ ⋃ k ∈ Finset.range j, J k) x = {x} := by
    rw [hlower ⟨j, hj⟩]
    apply lower_obstacle_singleton_of_compatible_bands U f M hbounded σ a b θ pairs
      hpairs F hband hB hTD hAB hnoterm hfree hcompat ⟨j, hj⟩
    simpa only [J, dite_eq_left hj] using hx
  obtain ⟨m, H, γ, hc, hd, hcurves⟩ := exists_finite_filling_disks hsard hschoenflies
    G π hπ hclosed hsurj hr hB hTD J hJ hbad n hA hAB hBA hW hAW hinfty hsingle
  refine ⟨m, H, γ, hc, hd, ?_⟩
  intro i
  obtain ⟨hi, hsm, hemb, hfront, hb, k, hk⟩ := hcurves i
  refine ⟨hi, hsm, hemb, hfront, hb, k, ?_⟩
  intro j hj
  simpa only [J, dite_eq_left j.isLt] using hk j.val j.isLt hj

end CircleDomainRigidity.FiniteTransfer

end OAI
