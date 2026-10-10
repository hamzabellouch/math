import Mathlib

namespace OAI

/-! Equicontinuity and finite-dimensionality of holomorphic sections on compact manifolds. -/

noncomputable section
open Bundle Set Filter
open scoped Manifold Bundle Topology BoundedContinuousFunction

namespace CompactSections

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

theorem equicontinuousAt_of_ball_bound {ι : Type*} (f : ι → E → F)
    (x : E) {r C : ℝ} (hr : 0 < r)
    (hd : ∀ i, DifferentiableOn ℂ (f i) (Metric.ball x r))
    (hb : ∀ i y, y ∈ Metric.ball x r → ‖f i y‖ ≤ C) :
    EquicontinuousAt f x := by
  apply Metric.equicontinuousAt_iff.mpr
  intro ε hε
  let D := 2 * max C 0 / r
  have hD : 0 ≤ D := div_nonneg (mul_nonneg (by norm_num) (le_max_right _ _)) hr.le
  refine ⟨min r (ε / (D + 1)), lt_min hr (div_pos hε (by positivity)), ?_⟩
  intro y hy i
  have hyr : y ∈ Metric.ball x r := hy.trans_le (min_le_left _ _)
  have hmap : MapsTo (f i) (Metric.ball x r) (Metric.closedBall (f i x) (2 * max C 0)) := by
    intro z hz
    change dist (f i z) (f i x) ≤ _
    calc
      dist (f i z) (f i x) ≤ ‖f i z‖ + ‖f i x‖ := dist_le_norm_add_norm _ _
      _ ≤ C + C := add_le_add (hb i z hz) (hb i x (Metric.mem_ball_self hr))
      _ ≤ 2 * max C 0 := by linarith [le_max_left C 0]
  have hSchwarz := Complex.dist_le_div_mul_dist_of_mapsTo_ball (hd i) hmap hyr
  rw [dist_comm] at hSchwarz
  apply hSchwarz.trans_lt
  have hyε : dist y x < ε / (D + 1) := hy.trans_le (min_le_right _ _)
  have hstrict : (D + 1) * dist y x < ε := by
    nlinarith [(lt_div_iff₀ (show 0 < D + 1 by positivity)).mp hyε]
  change D * dist y x < ε
  nlinarith [dist_nonneg (α := E) (x := y) (y := x)]

 

theorem equicontinuousAt_clm_apply {X ι : Type*} [TopologicalSpace X]
    (f : ι → X → F) (A : X → F →L[ℂ] F) (x : X)
    (hf : EquicontinuousAt f x) (hA : ContinuousAt A x)
    {C : ℝ} (hb : ∀ i, ‖f i x‖ ≤ C) :
    EquicontinuousAt (fun i y => A y (f i y)) x := by
  apply Metric.equicontinuousAt_iff_right.mpr
  intro ε hε
  let K := ‖A x‖ + 1
  let L := max C 0 + 1
  have hK : 0 < K := by dsimp [K]; positivity
  have hL : 0 < L := by dsimp [L]; positivity
  have hsmall := (Metric.equicontinuousAt_iff_right.mp hf)
    (ε / 2 / K) (div_pos (half_pos hε) hK)
  have hopen : ∀ᶠ y in 𝓝 x, ‖A y - A x‖ < min 1 (ε / 2 / L) := by
    simpa only [dist_eq_norm] using
      (Metric.tendsto_nhds.mp hA _ (lt_min zero_lt_one (div_pos (half_pos hε) hL)))
  filter_upwards [hsmall, hopen] with y hy hAy
  intro i
  have hnorm : ‖A y‖ ≤ K := by
    have := norm_le_norm_add_norm_sub (A x) (A y)
    rw [norm_sub_rev] at this
    dsimp [K]
    linarith [lt_of_lt_of_le hAy (min_le_left _ _)]
  have h₁ : dist (A y (f i y)) (A y (f i x)) < ε / 2 := by
    calc
      dist (A y (f i y)) (A y (f i x)) ≤ ‖A y‖ * dist (f i y) (f i x) :=
        (A y).dist_le_opNorm _ _
      _ ≤ K * dist (f i x) (f i y) := by rw [dist_comm]; gcongr
      _ < ε / 2 := by
        have := (lt_div_iff₀ hK).mp (hy i)
        nlinarith
  have h₂ : dist (A y (f i x)) (A x (f i x)) < ε / 2 := by
    calc
      dist (A y (f i x)) (A x (f i x)) = ‖(A y - A x) (f i x)‖ := by
        rw [dist_eq_norm]; rfl
      _ ≤ ‖A y - A x‖ * ‖f i x‖ := (A y - A x).le_opNorm _
      _ ≤ ‖A y - A x‖ * L := by
        gcongr
        exact (hb i).trans (by dsimp [L]; linarith [le_max_left C 0])
      _ < ε / 2 := by
        have := (lt_div_iff₀ hL).mp (lt_of_lt_of_le hAy (min_le_right _ _))
        exact this
  rw [dist_comm]
  exact (dist_triangle _ (A y (f i x)) _).trans_lt (by linarith)

section ManifoldLocal
variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℂ, E) (⊤ : WithTop ℕ∞) M]

theorem equicontinuousAt_of_local_holomorphic_bound {ι : Type*} (f : ι → M → F)
    {U : Set M} (hU : IsOpen U) {x : M} (hx : x ∈ U) {C : ℝ}
    (hd : ∀ i, MDifferentiableOn 𝓘(ℂ, E) 𝓘(ℂ, F) (f i) U)
    (hb : ∀ i y, y ∈ U → ‖f i y‖ ≤ C) :
    EquicontinuousAt f x := by
  let e := extChartAt 𝓘(ℂ, E) x
  have het : IsOpen e.target := isOpen_extChartAt_target x
  have hex : e x ∈ e.target := mem_extChartAt_target x
  have hec : ContinuousAt e.symm (e x) :=
    (contMDiffOn_extChartAt_symm (I := 𝓘(ℂ, E)) (n := (⊤ : WithTop ℕ∞)) x).continuousOn.continuousAt
      (het.mem_nhds hex)
  have hpre : e.symm ⁻¹' U ∈ 𝓝 (e x) := by
    apply hec.preimage_mem_nhds
    simpa only [e, extChartAt_to_inv] using hU.mem_nhds hx
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (inter_mem (het.mem_nhds hex) hpre)
  have heq : EquicontinuousAt (fun i => f i ∘ e.symm) (e x) := by
    refine equicontinuousAt_of_ball_bound (C := C) _ _ hr ?_ ?_
    · intro i y hy
      have hyt := (hball hy).1
      have hyU := (hball hy).2
      have hemd : MDifferentiableAt 𝓘(ℂ, E) 𝓘(ℂ, E) e.symm y :=
        ((contMDiffOn_extChartAt_symm (I := 𝓘(ℂ, E))
          (n := (⊤ : WithTop ℕ∞)) x y hyt).contMDiffAt (het.mem_nhds hyt)).mdifferentiableAt (by simp)
      exact (mdifferentiableAt_iff_differentiableAt.mp
        (((hd i _ hyU).mdifferentiableAt (hU.mem_nhds hyU)).comp y hemd)).differentiableWithinAt
    · intro i y hy
      exact hb i _ (hball hy).2
  apply Metric.equicontinuousAt_iff_right.mpr
  intro ε hε
  have hε' := (Metric.equicontinuousAt_iff_right.mp heq ε hε)
  have hecont : ContinuousAt e x :=
    (contMDiffAt_extChartAt (I := 𝓘(ℂ, E)) (n := (⊤ : WithTop ℕ∞))).continuousAt
  filter_upwards [hecont hε', extChartAt_source_mem_nhds (I := 𝓘(ℂ, E)) x] with y hy hys
  intro i
  simpa only [Function.comp_apply, e.left_inv hys, e, extChartAt_to_inv] using hy i

end ManifoldLocal

section CompactCover
variable [FiniteDimensional ℂ E] [FiniteDimensional ℂ F]
  {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) (⊤ : WithTop ℕ∞) M]
  (V : M → Type*) [TopologicalSpace (TotalSpace F V)]
  [∀ x, TopologicalSpace (V x)] [∀ x, AddCommGroup (V x)] [∀ x, Module ℂ (V x)]
  [FiberBundle F V] [VectorBundle ℂ F V]
  [ContMDiffVectorBundle (⊤ : WithTop ℕ∞) F V 𝓘(ℂ, E)]
  {ι : Type*} [Fintype ι]
  (e : ι → Trivialization F (TotalSpace.proj : TotalSpace F V → M))
  [∀ i, MemTrivializationAtlas (e i)]
  (K : ι → Set M) (hK : ∀ i, IsCompact (K i)) (hsub : ∀ i, K i ⊆ (e i).baseSet)

abbrev HolSections := ContMDiffSection 𝓘(ℂ, E) F (⊤ : WithTop ℕ∞) V

 
def sectionProfile : HolSections (E := E) (F := F) V →ₗ[ℂ] (∀ i, K i →ᵇ F) where
  toFun s i := by
    letI : CompactSpace (K i) := (isCompact_iff_compactSpace.mp (hK i))
    exact BoundedContinuousFunction.mkOfCompact
      ⟨(fun x => (e i ⟨x.1, s x.1⟩).2),
        (((e i).contMDiffOn_section_baseSet_iff.mp s.contMDiff.contMDiffOn).continuousOn.mono
          (hsub i)).domRestrict⟩
  map_add' s t := by
    funext i
    apply BoundedContinuousFunction.ext
    intro x
    exact ((e i).linearEquivAt ℂ x.1 (hsub i x.2)).map_add (s x.1) (t x.1)
  map_smul' c s := by
    funext i
    apply BoundedContinuousFunction.ext
    intro x
    exact ((e i).linearEquivAt ℂ x.1 (hsub i x.2)).map_smul c (s x.1)

omit [FiniteDimensional ℂ E] [FiniteDimensional ℂ F] [T2Space M]
  [IsManifold 𝓘(ℂ, E) ⊤ M] [Fintype ι] in
theorem sectionProfile_injective (hcover : ∀ x, ∃ i, x ∈ interior (K i)) :
    Function.Injective (sectionProfile (E := E) V e K hK hsub) := by
  intro s t h
  ext x
  obtain ⟨i, hi⟩ := hcover x
  have hxK := interior_subset hi
  apply ((e i).linearEquivAt ℂ x (hsub i hxK)).injective
  exact congrArg (fun f : ∀ i, K i →ᵇ F => f i ⟨x, hxK⟩) h

include hsub in
 

omit [FiniteDimensional ℂ E] [FiniteDimensional ℂ F] [T2Space M] [Fintype ι] in
theorem sectionProfiles_equicontinuous {S : Type*}
    (s : S → HolSections (E := E) (F := F) V)
    (hcover : ∀ x, ∃ i, x ∈ interior (K i)) {C : ℝ}
    (hb : ∀ t i x, x ∈ K i → ‖(e i ⟨x, s t x⟩).2‖ ≤ C) (i : ι) :
    Equicontinuous (fun t (x : K i) => (e i ⟨x.1, s t x.1⟩).2) := by
  intro x
  obtain ⟨j, hj⟩ := hcover x.1
  have hlocal : EquicontinuousAt (fun t y => (e j ⟨y, s t y⟩).2) x.1 := by
    refine equicontinuousAt_of_local_holomorphic_bound (E := E) (C := C) _ isOpen_interior hj ?_ ?_
    · intro t
      exact (((e j).contMDiffOn_section_baseSet_iff.mp
        (s t).contMDiff.contMDiffOn).mdifferentiableOn (by simp)).mono
          (interior_subset.trans (hsub j))
    · intro t y hy
      exact hb t j y (interior_subset hy)
  let A : M → F →L[ℂ] F := fun y => (e j).coordChangeL ℂ (e i) y
  have hxbase : x.1 ∈ (e j).baseSet ∩ (e i).baseSet :=
    ⟨hsub j (interior_subset hj), hsub i x.2⟩
  have hopen : IsOpen ((e j).baseSet ∩ (e i).baseSet) :=
    (e j).open_baseSet.inter (e i).open_baseSet
  have hA : ContinuousAt A x.1 :=
    (continuousOn_coordChange ℂ (e j) (e i)).continuousAt (hopen.mem_nhds hxbase)
  have heqc := equicontinuousAt_clm_apply _ A x.1 hlocal hA
    (fun t => hb t j x.1 (interior_subset hj))
  have hid (t : S) (y : M) (hy : y ∈ (e j).baseSet ∩ (e i).baseSet) :
      A y ((e j ⟨y, s t y⟩).2) = (e i ⟨y, s t y⟩).2 := by
    dsimp [A]
    rw [(e j).coordChangeL_apply (e i) hy, (e j).symm_apply_apply_mk hy.1]
  apply Metric.equicontinuousAt_iff_right.mpr
  intro ε hε
  have hev := (Metric.equicontinuousAt_iff_right.mp heqc ε hε).and
    (hopen.mem_nhds hxbase)
  have hev' := (continuous_subtype_val.continuousAt (x := x)) hev
  filter_upwards [hev'] with y hy
  intro t
  simpa only [hid t x.1 hxbase, hid t y.1 hy.2] using hy.1 t

include e hK hsub in
omit [FiniteDimensional ℂ E] [T2Space M] in
theorem finiteDimensional_of_compact_cover
    (hcover : ∀ x, ∃ i, x ∈ interior (K i)) :
    FiniteDimensional ℂ (HolSections (E := E) (F := F) V) := by
  classical
  let H := HolSections (E := E) (F := F) V
  let P := ∀ i, K i →ᵇ F
  let p : H →ₗ[ℂ] P := sectionProfile (E := E) V e K hK hsub
  have hp : Function.Injective p := sectionProfile_injective V e K hK hsub hcover
  let : NormedAddCommGroup H := NormedAddCommGroup.induced H P p hp
  let : NormedSpace ℂ H := NormedSpace.induced ℂ H P p
  have hiso : Isometry p := AddMonoidHomClass.isometry_of_norm p (fun _ => rfl)
  let B : Set H := Metric.closedBall 0 1
  have hb (s : B) (i : ι) (x : M) (hx : x ∈ K i) : ‖(e i ⟨x, s.1 x⟩).2‖ ≤ 1 := by
    calc
      ‖(e i ⟨x, s.1 x⟩).2‖ = ‖p s.1 i ⟨x, hx⟩‖ := rfl
      _ ≤ ‖p s.1 i‖ := (p s.1 i).norm_coe_le_norm _
      _ ≤ ‖p s.1‖ := norm_le_pi_norm _ i
      _ ≤ 1 := by
        change ‖s.1‖ ≤ 1
        simpa only [B, Metric.mem_closedBall, dist_zero_right] using s.2
  let A : ∀ i, Set (K i →ᵇ F) := fun i => (fun s : H => p s i) '' B
  have hcompact (i : ι) : IsCompact (closure (A i)) := by
    let : CompactSpace (K i) := isCompact_iff_compactSpace.mp (hK i)
    refine BoundedContinuousFunction.arzela_ascoli (Metric.closedBall 0 1)
      (isCompact_closedBall _ _) (A i) ?_ ?_
    · intro f x hf
      obtain ⟨s, hs, rfl⟩ := hf
      rw [Metric.mem_closedBall, dist_zero_right]
      exact hb ⟨s, hs⟩ i x.1 x.2
    · have heq := sectionProfiles_equicontinuous V e K hsub
        (fun s : B => s.1) hcover hb i
      intro x
      apply Metric.equicontinuousAt_iff_right.mpr
      intro ε hε
      filter_upwards [Metric.equicontinuousAt_iff_right.mp (heq x) ε hε] with y hy
      intro f
      obtain ⟨s, hs, hsf⟩ := f.2
      change dist (f.1 x) (f.1 y) < ε
      rw [← hsf]
      exact hy ⟨s, hs⟩
  have htotal : TotallyBounded (p '' B) := by
    apply (isCompact_pi_infinite hcompact).totallyBounded.subset
    rintro _ ⟨s, hs, rfl⟩ i
    exact subset_closure ⟨s, hs, rfl⟩
  exact FiniteDimensional.of_totallyBounded_nhds_zero ℂ
    (Metric.closedBall_mem_nhds (0 : H) (by norm_num : (0 : ℝ) < 1))
    ((totallyBounded_image_iff hiso.isUniformInducing).mp htotal)

end CompactCover

variable [FiniteDimensional ℂ E] [FiniteDimensional ℂ F]
  {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) (⊤ : WithTop ℕ∞) M]
  (V : M → Type*) [TopologicalSpace (TotalSpace F V)]
  [∀ x, TopologicalSpace (V x)] [∀ x, AddCommGroup (V x)] [∀ x, Module ℂ (V x)]
  [FiberBundle F V] [VectorBundle ℂ F V]
  [ContMDiffVectorBundle (⊤ : WithTop ℕ∞) F V 𝓘(ℂ, E)]

 

omit [FiniteDimensional ℂ E] in
theorem finiteDimensional_holomorphic_sections :
    FiniteDimensional ℂ (ContMDiffSection 𝓘(ℂ, E) F (⊤ : WithTop ℕ∞) V) := by
  classical
  have hex (x : M) : ∃ K : Set M, IsCompact K ∧ x ∈ interior K ∧
      K ⊆ (trivializationAt F V x).baseSet :=
    exists_compact_subset (trivializationAt F V x).open_baseSet
      (mem_baseSet_trivializationAt F V x)
  choose K hK hxK hsub using hex
  obtain ⟨I, hI⟩ := isCompact_univ.elim_finite_subcover (fun x => interior (K x))
    (fun _ => isOpen_interior) (fun x _ => mem_iUnion.mpr ⟨x, hxK x⟩)
  let e (i : I) := trivializationAt F V i.1
  let (i : I) : MemTrivializationAtlas (e i) := inferInstanceAs
    (MemTrivializationAtlas (trivializationAt F V i.1))
  apply finiteDimensional_of_compact_cover (E := E) V e (fun i => K i.1)
    (fun i => hK i.1) (fun i => hsub i.1)
  intro x
  obtain ⟨i, hi, hx⟩ := mem_iUnion₂.mp (hI (mem_univ x))
  exact ⟨⟨i, hi⟩, hx⟩

end CompactSections

end

end OAI
