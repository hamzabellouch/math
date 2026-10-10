import Mathlib
import OAI.Analysis.AffineBernstein.ModelLimit
import OAI.Analysis.AffineBernstein.SupportCoordinates
import OAI.Analysis.AffineBernstein.ThinSlices

namespace OAI

noncomputable section

namespace AffineBernstein

open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
open Filter Metric
open scoped Topology Pointwise
open scoped Pointwise
open scoped Pointwise

open Filter Metric
open scoped Topology Pointwise

variable {k m d : ℕ}

/- Transverse coordinate changes preserve the literal model conditions. -/
theorem IsModelShape.transverse_image {C : Set (Space k × Space m)}
    (hC : IsModelShape C) (A : Space m ≃L[ℝ] Space m) :
    IsModelShape (((ContinuousLinearEquiv.refl ℝ (Space k)).prodCongr A) '' C) := by
  let B := (ContinuousLinearEquiv.refl ℝ (Space k)).prodCongr A
  have cap (T : ℝ) : (B '' C) ∩ {p | ∑ i, p.1 i ≤ T} =
      B '' (C ∩ {p | ∑ i, p.1 i ≤ T}) := by
    ext p
    constructor
    · rintro ⟨⟨q, hq, rfl⟩, ht⟩
      exact ⟨q, ⟨hq, ht⟩, rfl⟩
    · rintro ⟨q, ⟨hq, ht⟩, rfl⟩
      exact ⟨⟨q, hq, rfl⟩, ht⟩
  refine ⟨B.toHomeomorph.isClosedMap _ hC.closed,
    hC.convex.linear_image B.toLinearMap, ?_, ?_, ?_, ?_⟩
  · change (interior (B.toHomeomorph '' C)).Nonempty
    rw [← B.toHomeomorph.image_interior]
    exact hC.interior_nonempty.image B
  · intro s hs
    exact ⟨(s, 0), hC.orthant s hs, by simp⟩
  · rintro p ⟨q, hq, rfl⟩
    exact hC.support q hq
  · intro T hT
    change IsCompact ((B '' C) ∩ _)
    rw [cap]
    exact (hC.compact_cap T hT).image B.continuous

@[simp] theorem fiber_transverse_image {C : Set (Space k × Space m)}
    (A : Space m ≃L[ℝ] Space m) (s : Space k) :
    modelFiber (((ContinuousLinearEquiv.refl ℝ (Space k)).prodCongr A) '' C) s =
      A '' modelFiber C s := by
  ext y
  constructor
  · rintro ⟨p, hp, he⟩
    have hs : p.1 = s := congrArg Prod.fst he
    have hy : A p.2 = y := congrArg Prod.snd he
    exact ⟨p.2, by simpa only [modelFiber, mem_ofPred_eq, ← hs, Prod.mk.eta] using hp, hy⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨(s,z), hz, rfl⟩

/- The actual support-coordinate change gives precisely the split model to
which the thin-slice construction applies. -/
theorem IsModelShape.supported_split {C : Set (Space k × Space m)}
    (hC : IsModelShape C) (A : Space m ≃L[ℝ] ℝ × Space d)
    (hs : ∀ p ∈ C, 0 ≤ (A p.2).1)
    (hi : (1,0) ∈ interior (A '' modelFiber C (WithLp.toLp 2 (fun _ : Fin k => (1:ℝ))))) :
    IsSupportedSplitModel (((ContinuousLinearEquiv.refl ℝ (Space k)).prodCongr A) '' C) := by
  let B := (ContinuousLinearEquiv.refl ℝ (Space k)).prodCongr A
  have cap (T : ℝ) : (B '' C) ∩ {p | ∑ i, p.1 i ≤ T} =
      B '' (C ∩ {p | ∑ i, p.1 i ≤ T}) := by
    ext p
    constructor
    · rintro ⟨⟨q, hq, rfl⟩, ht⟩
      exact ⟨q, ⟨hq, ht⟩, rfl⟩
    · rintro ⟨q, ⟨hq, ht⟩, rfl⟩
      exact ⟨⟨q, hq, rfl⟩, ht⟩
  refine ⟨B.toHomeomorph.isClosedMap _ hC.closed,
    hC.convex.linear_image B.toLinearMap, ?_, ?_, ?_, ?_, ?_⟩
  · intro s hs
    exact ⟨(s,0), hC.orthant s hs, by simp [Prod.zero_eq_mk]⟩
  · rintro p ⟨q,hq,rfl⟩
    exact hC.support q hq
  · rintro p ⟨q,hq,rfl⟩
    exact hs q hq
  · intro T hT
    change IsCompact ((B '' C) ∩ _)
    rw [cap]
    exact (hC.compact_cap T hT).image B.continuous
  · convert hi using 1
    congr 1
    ext y
    constructor
    · rintro ⟨p,hp,he⟩
      have he1 : p.1 = WithLp.toLp 2 (fun _ : Fin k => (1:ℝ)) := congrArg Prod.fst he
      have he2 := congrArg Prod.snd he
      refine ⟨p.2, ?_, he2⟩
      simpa only [modelFiber, mem_ofPred_eq, ← he1, Prod.mk.eta] using hp
    · rintro ⟨z,hz,rfl⟩
      exact ⟨(_,z),hz,rfl⟩

/- The rescaling is genuinely an invertible linear image, not an abstract
limit operation. -/
def thinRescalingEquiv (k d : ℕ) (ε : ℝ) (hε : ε ≠ 0)
    (A : Space d ≃L[ℝ] Space d) :
    (Space k × (ℝ × Space d)) ≃L[ℝ] (Space k × (ℝ × Space d)) :=
  (ContinuousLinearEquiv.refl ℝ (Space k)).prodCongr
    (((LinearEquiv.smulOfNeZero ℝ ℝ ε hε).symm.toContinuousLinearEquiv).prodCongr A)

theorem thinRescaling_eq_image {C : Set (Space k × (ℝ × Space d))}
    {ε : ℝ} (hε : ε ≠ 0) (A : Space d ≃L[ℝ] Space d) :
    thinRescaling C ε A = thinRescalingEquiv k d ε hε A '' C := by
  ext p
  change p ∈ thinRescaling C ε A ↔ p ∈ (thinRescalingEquiv k d ε hε A).toEquiv '' C
  rw [Set.mem_image_equiv]
  rfl

/- Reindexing the limiting (s,r) orthant gives the manuscript's exact
(k+1)-model, including the case of no remaining transverse coordinates. -/
theorem modelShape_reorder {C : Set (Space k × (ℝ × Space d))}
    (hc : IsClosed C) (hv : Convex ℝ C) (hi : (interior C).Nonempty)
    (ho : ∀ s : Space k, (∀ i, 0 ≤ s i) → ∀ r : ℝ, 0 ≤ r → (s,(r,0)) ∈ C)
    (hs : ∀ p ∈ C, (∀ i, 0 ≤ p.1 i) ∧ 0 ≤ p.2.1)
    (hcap : ∀ T : ℝ, 0 ≤ T → IsCompact (C ∩ {p | (∑ i,p.1 i)+p.2.1 ≤ T})) :
    IsModelShape (reorderThinEquiv k d '' C) := by
  let B := reorderThinEquiv k d
  refine ⟨B.toHomeomorph.isClosedMap _ hc, hv.linear_image B.toLinearMap, ?_, ?_, ?_, ?_⟩
  · change (interior (B.toHomeomorph '' C)).Nonempty
    rw [← B.toHomeomorph.image_interior]
    exact hi.image B
  · intro s hs'
    let p := B.symm (s,0)
    have he : B p = (s,0) := B.apply_symm_apply _
    have he0 : p.2.2 = 0 := congrArg Prod.snd he
    have he1 (i : Fin k) : p.1 i = s i.succ := by
      simpa [B] using congrArg (fun q : Space (k+1) × Space d => q.1 i.succ) he
    have he2 : p.2.1 = s 0 := by
      simpa [B] using congrArg (fun q : Space (k+1) × Space d => q.1 0) he
    refine ⟨p, ?_, he⟩
    have hm := ho p.1 (fun i => by rw [he1]; exact hs' _) p.2.1 (by rw [he2]; exact hs' _)
    simpa only [← he0, Prod.mk.eta] using hm
  · rintro p ⟨q,hq,rfl⟩ i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact (hs q hq).2
    · exact (hs q hq).1 j
  · intro T hT
    have he : (B '' C) ∩ {p | ∑ i,p.1 i ≤ T} =
        B '' (C ∩ {p | (∑ i,p.1 i)+p.2.1 ≤ T}) := by
      ext p
      constructor
      · rintro ⟨⟨q,hq,rfl⟩,ht⟩
        refine ⟨q,⟨hq,?_⟩,rfl⟩
        simpa only [B, mem_ofPred_eq, reorderThin_sum] using ht
      · rintro ⟨q,⟨hq,ht⟩,rfl⟩
        refine ⟨⟨q,hq,rfl⟩,?_⟩
        simpa only [B, mem_ofPred_eq, reorderThin_sum] using ht
    change IsCompact ((B '' C) ∩ _)
    rw [he]
    exact (hcap T hT).image B.continuous

/- A supported thin-slice model produces an actual model with one additional
nonnegative direction in the original affine local-limit family. All normalizers,
subsequences and limiting sets are constructed here. -/
theorem IsSupportedSplitModel.exists_next_model
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    {D : Set E} (hD : IsClosed D) (hneD : D.Nonempty)
    {C : Set (Space k × (ℝ × Space d))} (hC : IsSupportedSplitModel C)
    (hf : InAffineLimitFamily D C) :
    ∃ C' : Set (Space (k+1) × Space d), IsModelShape C' ∧ InAffineLimitFamily D C' := by
  classical
  let ε : ℕ → ℝ := fun j => (1 / ((j:ℝ)+1)) / 4
  have hepos : ∀ j, 0 < ε j := by intro j; dsimp [ε]; positivity
  have he2 : ∀ j, 2 * ε j ≤ 1 := by
    intro j
    have hi : 1 / ((j:ℝ)+1) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith [Nat.cast_nonneg (α := ℝ) j])
    dsimp [ε]
    linarith
  have he1 : ∀ j, ε j ≤ 1 := fun j => by linarith [he2 j, hepos j]
  have het : Tendsto ε atTop (𝓝 0) := by
    simpa [ε] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).div_const 4
  have hnorm : ∀ j, ∃ (A : Space d ≃L[ℝ] Space d) (c : Space d),
      closedBall c 1 ⊆ A '' thinSlice C (ε j) ∧
      A '' thinSlice C (ε j) ⊆ closedBall 0 (2 * ((d:ℝ)+1)^3) ∧
      ‖c‖ ≤ 2 * ((d:ℝ)+1)^3 := by
    intro j
    have hi := hC.slice_interior_zero (hepos j) (he1 j)
    exact noncentered_body_normalization_all (hC.slice_compact _) (hC.slice_convex _)
      ⟨0,hi⟩ (interior_subset hi)
  choose A cj hin hout hcb using hnorm
  obtain ⟨c,hcB,φ,hφ,hct⟩ := (isCompact_closedBall (0 : Space d) (2*((d:ℝ)+1)^3)).tendsto_subseq
    (x := cj) (fun j => by simpa [mem_closedBall,dist_zero_right] using hcb j)
  let Cj : ℕ → Set (Space k × (ℝ × Space d)) := fun j => thinRescaling C (ε (φ j)) (A (φ j))
  have hz : ∀ j, (0 : Space k × (ℝ × Space d)) ∈ Cj j := by
    intro j
    simpa [Cj,thinRescaling,Prod.zero_eq_mk] using hC.zero_mem
  have hcl : ∀ j, IsClosed (Cj j) := fun j => hC.rescaling_closed _ _
  have hcv : ∀ j, Convex ℝ (Cj j) := fun j => hC.rescaling_convex _ _
  obtain ⟨C₀,ψ,hψ,hclosed,hne,hconv,hlim⟩ := exists_convex_local_limit hcl hcv
    (fun j => ⟨0,hz j⟩) (R := 0) (fun j => by rw [infDist_zero_of_mem (hz j)])
  have hp := hlim.thin_limit hC (fun j => hepos (φ (ψ j))) (fun j => he2 (φ (ψ j)))
    (het.comp (hφ.tendsto_atTop.comp hψ.tendsto_atTop)) (fun j => A (φ (ψ j)))
    hclosed hconv hne (hct.comp hψ.tendsto_atTop)
    (fun j => hin (φ (ψ j))) (fun j => hout (φ (ψ j)))
  have hfj : ∀ j, InAffineLimitFamily D (Cj j) := by
    intro j
    have hh := hf.affine_image hD hneD
      (thinRescalingEquiv k d (ε (φ j)) (hepos _).ne' (A (φ j))).toContinuousAffineEquiv
    simpa only [Cj,thinRescaling_eq_image (hepos _).ne',
      ContinuousLinearEquiv.coe_toContinuousAffineEquiv] using hh
  have hf₀ : InAffineLimitFamily D C₀ :=
    InAffineLimitFamily.diagonal_closure (fun j => hfj (ψ j)) hlim hclosed hconv hp.2.2.1
  exact ⟨reorderThinEquiv k d '' C₀,
    modelShape_reorder hclosed hconv hp.2.2.1 hp.1 hp.2.1 hp.2.2.2,
    hf₀.affine_image hD hneD (reorderThinEquiv k d).toContinuousAffineEquiv⟩

/- Boundary zero in the fiber is incompatible with maximality of the number
of model directions: the missing new model is actually produced, not assumed. -/
theorem IsModelShape.exists_next_model_of_zero_boundary
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    {D : Set E} (hD : IsClosed D) (hneD : D.Nonempty)
    {C : Set (Space k × Space m)} (hC : IsModelShape C) (hf : InAffineLimitFamily D C)
    (hz : (0 : Space m) ∉ interior (modelFiber C (WithLp.toLp 2 (fun _ : Fin k => (1:ℝ))))) :
    ∃ (d : ℕ) (C' : Set (Space (k+1) × Space d)),
      m = d+1 ∧ IsModelShape C' ∧ InAffineLimitFamily D C' := by
  obtain ⟨ell,hell,hs⟩ := hC.exists_global_support_of_zero_boundary hz
  obtain ⟨d,A,hd,hsA,hiA⟩ := exists_support_coordinates
    (hC.fiber_interior_nonempty (s := WithLp.toLp 2 (fun _ : Fin k => (1:ℝ))) (by simp)) ell hell
    (fun y hy => hs (_,y) hy)
  have hsupport : ∀ p ∈ C, 0 ≤ (A p.2).1 := by
    -- Coordinate construction yields the sign globally by contraction into
    -- the exact fiber; this avoids relying on implementation details of A.
    let f : Space m →L[ℝ] ℝ := (ContinuousLinearMap.fst ℝ ℝ (Space d)).comp A.toContinuousLinearMap
    exact hC.support_from_fiber f hsA
  let B := (ContinuousLinearEquiv.refl ℝ (Space k)).prodCongr A
  obtain ⟨C',hc',hf'⟩ := (hC.supported_split A hsupport hiA).exists_next_model hD hneD
    (hf.affine_image hD hneD B.toContinuousAffineEquiv)
  exact ⟨d,C',hd,hc',hf'⟩

/- Dilation of a convex body containing zero is monotone for nonnegative
radii. This includes a zero inner radius. -/
theorem convex_smul_set_mono {F : Set (Space m)} (hv : Convex ℝ F) (hz : (0 : Space m) ∈ F)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : 0 < b) : a • F ⊆ b • F := by
  rintro x ⟨y,hy,rfl⟩
  refine mem_smul_set.mpr ⟨(a/b) • y, hv.smul_mem_of_zero_mem hz hy
    ⟨div_nonneg ha hb.le,(div_le_one hb).mpr hab⟩, ?_⟩
  rw [smul_smul, mul_div_cancel₀ _ hb.ne']

/- Centering is unaffected by any invertible linear transverse change. -/
theorem centering_image_iff (A : Space m ≃L[ℝ] Space m) (F : Set (Space m)) (a : ℝ) :
    -(A '' F) ⊆ a • (A '' F) ↔ -F ⊆ a • F := by
  constructor
  · intro h x hx
    have hm : A x ∈ -(A '' F) := by
      change -(A x) ∈ A '' F
      exact ⟨-x,hx,by simp⟩
    obtain ⟨y,⟨z,hz,rfl⟩,he⟩ := mem_smul_set.mp (h hm)
    refine mem_smul_set.mpr ⟨z,hz,A.injective ?_⟩
    simpa only [map_smul] using he
  · intro h x hx
    change -x ∈ A '' F at hx
    obtain ⟨y,hy,he⟩ := hx
    have hm : -y ∈ -F := by simpa using hy
    obtain ⟨z,hz,hz'⟩ := mem_smul_set.mp (h hm)
    refine mem_smul_set.mpr ⟨A z,⟨z,hz,rfl⟩,?_⟩
    have hh := congrArg A hz'
    rw [map_smul,map_neg,he] at hh
    simpa using hh

/- Uniform centering for every distinguished fiber in a maximal model
family. The single maximality hypothesis rules out actual (k+1)-models;
it carries no centering estimate and is discharged by choosing maximal k. -/
theorem uniform_centering_at_one
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    {D : Set E} (hD : IsClosed D) (hneD : D.Nonempty)
    (hmax : ∀ (d : ℕ), m = d+1 → ∀ C' : Set (Space (k+1) × Space d),
      IsModelShape C' → InAffineLimitFamily D C' → False) :
    ∃ a : ℝ, 1 ≤ a ∧ ∀ C : Set (Space k × Space m),
      IsModelShape C → InAffineLimitFamily D C →
      -(modelFiber C (WithLp.toLp 2 (fun _ : Fin k => (1:ℝ)))) ⊆
        a • modelFiber C (WithLp.toLp 2 (fun _ : Fin k => (1:ℝ))) := by
  classical
  let e : Space k := WithLp.toLp 2 (fun _ => 1)
  by_contra h
  push Not at h
  have hbad : ∀ j : ℕ, ∃ C : Set (Space k × Space m), IsModelShape C ∧
      InAffineLimitFamily D C ∧ ¬ -(modelFiber C e) ⊆ ((j:ℝ)+1) • modelFiber C e := by
    intro j
    obtain ⟨C,hC,hf,hfail⟩ := h ((j:ℝ)+1) (by linarith [Nat.cast_nonneg (α := ℝ) j])
    exact ⟨C,hC,hf,hfail⟩
  choose C hC hf hfail using hbad
  have hn : ∀ j, ∃ (A : Space m ≃L[ℝ] Space m) (c : Space m),
      closedBall c 1 ⊆ A '' modelFiber (C j) e ∧
      A '' modelFiber (C j) e ⊆ closedBall 0 (2*((m:ℝ)+1)^3) ∧ ‖c‖ ≤ 2*((m:ℝ)+1)^3 := by
    intro j
    exact noncentered_body_normalization_all
      ((hC j).fiber_compact (s := e) (by simp [e])) ((hC j).fiber_convex e)
      ((hC j).fiber_interior_nonempty (by simp [e])) ((hC j).fiber_zero (by simp [e]))
  choose A cj hin hout hcb using hn
  let Cj : ℕ → Set (Space k × Space m) := fun j =>
    ((ContinuousLinearEquiv.refl ℝ (Space k)).prodCongr (A j)) '' C j
  have hmod : ∀ j, IsModelShape (Cj j) := fun j => (hC j).transverse_image (A j)
  have hfam : ∀ j, InAffineLimitFamily D (Cj j) := fun j =>
    (hf j).affine_image hD hneD ((ContinuousLinearEquiv.refl ℝ (Space k)).prodCongr (A j)).toContinuousAffineEquiv
  have hinner : ∀ j, closedBall (cj j) 1 ⊆ modelFiber (Cj j) e := by
    intro j
    simpa only [Cj,fiber_transverse_image] using hin j
  have houter : ∀ j, modelFiber (Cj j) e ⊆ closedBall 0 (2*((m:ℝ)+1)^3) := by
    intro j
    simpa only [Cj,fiber_transverse_image] using hout j
  have hassym : ∀ j, ¬ -(modelFiber (Cj j) e) ⊆ ((j:ℝ)+1) • modelFiber (Cj j) e := by
    intro j hj
    apply hfail j
    apply (centering_image_iff (A j) _ _).mp
    simpa only [Cj,fiber_transverse_image] using hj
  obtain ⟨c,hcB,φ,hφ,hct⟩ := (isCompact_closedBall (0 : Space m) (2*((m:ℝ)+1)^3)).tendsto_subseq
    (x := cj) (fun j => by simpa [mem_closedBall,dist_zero_right] using hcb j)
  obtain ⟨C₀,ψ,hψ,hclosed,hne,hconv,hlim⟩ := exists_convex_local_limit
    (fun j => (hmod (φ j)).closed) (fun j => (hmod (φ j)).convex)
    (fun j => ⟨0,(hmod (φ j)).zero_mem⟩) (R := 0)
    (fun j => by rw [infDist_zero_of_mem (hmod (φ j)).zero_mem])
  have hmod₀ := hlim.isModelShape_of_normalized (fun j => hmod (φ (ψ j)))
    hclosed hconv hne (hct.comp hψ.tendsto_atTop)
    (fun j => hinner (φ (ψ j))) (fun j => houter (φ (ψ j)))
  have hf₀ : InAffineLimitFamily D C₀ := InAffineLimitFamily.diagonal_closure
    (fun j => hfam (φ (ψ j))) hlim hclosed hconv hmod₀.interior_nonempty
  have hfail' : ∀ j : ℕ, 1 ≤ j →
      ¬ -(modelFiber (Cj (φ (ψ j))) e) ⊆ (j:ℝ) • modelFiber (Cj (φ (ψ j))) e := by
    intro j hj hh
    apply hassym (φ (ψ j))
    apply hh.trans
    apply convex_smul_set_mono ((hmod _).fiber_convex e) ((hmod _).fiber_zero (by simp [e]))
      (Nat.cast_nonneg j) _ (by positivity)
    have hle : j ≤ φ (ψ j) := (hψ.id_le j).trans (hφ.id_le (ψ j))
    have hle' : (j:ℝ) ≤ φ (ψ j) := by exact_mod_cast hle
    linarith
  have hfront := hlim.zero_mem_frontier_fiber_of_asymmetry (fun j => hmod (φ (ψ j)))
    hmod₀ (fun j => houter (φ (ψ j))) hfail'
  have hz : (0 : Space m) ∉ interior (modelFiber C₀ e) := hfront.2
  obtain ⟨d,C',hd,hc',hf'⟩ := hmod₀.exists_next_model_of_zero_boundary hD hneD hf₀ hz
  exact hmax d hd C' hc' hf'

/- The positive diagonal base change sending s to the all-ones base point. -/
def positiveBaseEquiv (s : Space k) (hs : ∀ i, 0 < s i) : Space k ≃L[ℝ] Space k :=
  LinearEquiv.toContinuousLinearEquiv
  { toFun := fun x => WithLp.toLp 2 (fun i => x i / s i)
    invFun := fun x => WithLp.toLp 2 (fun i => s i * x i)
    left_inv := by intro x; ext i; exact mul_div_cancel₀ _ (hs i).ne'
    right_inv := by intro x; ext i; exact mul_div_cancel_left₀ _ (hs i).ne'
    map_add' := by intro x y; ext i; exact add_div _ _ _
    map_smul' := by intro a x; ext i; exact mul_div_assoc _ _ _ }

@[simp] theorem positiveBaseEquiv_apply (s : Space k) (hs : ∀ i, 0 < s i) (x : Space k) (i : Fin k) :
    positiveBaseEquiv s hs x i = x i / s i := rfl

@[simp] theorem positiveBaseEquiv_symm_apply (s : Space k) (hs : ∀ i, 0 < s i) (x : Space k) (i : Fin k) :
    (positiveBaseEquiv s hs).symm x i = s i * x i := rfl

@[simp] theorem positiveBaseEquiv_self (s : Space k) (hs : ∀ i, 0 < s i) :
    positiveBaseEquiv s hs s = WithLp.toLp 2 (fun _ : Fin k => (1:ℝ)) := by
  ext i
  exact div_self (hs i).ne'

/- Positive diagonal choices of the distinguished directions preserve all
model properties, in particular compactness of caps. -/
theorem IsModelShape.positive_base_image {C : Set (Space k × Space m)}
    (hC : IsModelShape C) (s : Space k) (hs : ∀ i, 0 < s i) :
    IsModelShape (((positiveBaseEquiv s hs).prodCongr (ContinuousLinearEquiv.refl ℝ (Space m))) '' C) := by
  let B := (positiveBaseEquiv s hs).prodCongr (ContinuousLinearEquiv.refl ℝ (Space m))
  refine ⟨B.toHomeomorph.isClosedMap _ hC.closed,
    hC.convex.linear_image B.toLinearMap, ?_, ?_, ?_, ?_⟩
  · change (interior (B.toHomeomorph '' C)).Nonempty
    rw [← B.toHomeomorph.image_interior]
    exact hC.interior_nonempty.image B
  · intro t ht
    refine ⟨((positiveBaseEquiv s hs).symm t,0),hC.orthant _ (fun i => mul_nonneg (hs i).le (ht i)),?_⟩
    simp
  · rintro p ⟨q,hq,rfl⟩ i
    exact div_nonneg (hC.support q hq i) (hs i).le
  · intro T hT
    have hclosed : IsClosed ((B '' C) ∩ {p | ∑ i,p.1 i ≤ T}) :=
      (B.toHomeomorph.isClosedMap _ hC.closed).inter (isClosed_le (by fun_prop) continuous_const)
    have hcompact := (hC.compact_cap ((∑ i,s i)*T)
      (mul_nonneg (Finset.sum_nonneg (fun i _ => (hs i).le)) hT)).image B.continuous
    apply hcompact.of_isClosed_subset hclosed
    rintro p ⟨⟨q,hq,rfl⟩,hTq⟩
    refine ⟨q,⟨hq,?_⟩,rfl⟩
    change ∑ i,q.1 i ≤ (∑ i,s i)*T
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro i hi
    have hnon : ∀ j : Fin k, 0 ≤ (B q).1 j := fun j => div_nonneg (hC.support q hq j) (hs j).le
    have hle : (B q).1 i ≤ T :=
      (Finset.single_le_sum (fun j _ => hnon j) (Finset.mem_univ i)).trans hTq
    change q.1 i / s i ≤ T at hle
    exact (div_le_iff₀ (hs i)).mp hle |>.trans_eq (mul_comm _ _)

@[simp] theorem fiber_positive_base_image {C : Set (Space k × Space m)}
    (s : Space k) (hs : ∀ i, 0 < s i) :
    modelFiber (((positiveBaseEquiv s hs).prodCongr (ContinuousLinearEquiv.refl ℝ (Space m))) '' C)
      (WithLp.toLp 2 (fun _ : Fin k => (1:ℝ))) = modelFiber C s := by
  ext y
  constructor
  · rintro ⟨p,hp,he⟩
    have he1 : positiveBaseEquiv s hs p.1 = positiveBaseEquiv s hs s := by
      simpa using congrArg Prod.fst he
    have he2 : p.2 = y := congrArg Prod.snd he
    have hp1 := (positiveBaseEquiv s hs).injective he1
    simpa only [modelFiber, mem_ofPred_eq, ← hp1, ← he2, Prod.mk.eta] using hp
  · intro hy
    exact ⟨(s,y),hy, by simp⟩

/- Geometry.tex Proposition 2.7: the centering constant is uniform over all
models, positive fibers, and admissible distinguished coordinates of a maximal
family. Zero-dimensional transverse fibers are included. -/
theorem uniform_centering
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    {D : Set E} (hD : IsClosed D) (hneD : D.Nonempty)
    (hmax : ∀ (d : ℕ), m = d+1 → ∀ C' : Set (Space (k+1) × Space d),
      IsModelShape C' → InAffineLimitFamily D C' → False) :
    ∃ a : ℝ, 1 ≤ a ∧ ∀ C : Set (Space k × Space m),
      IsModelShape C → InAffineLimitFamily D C → ∀ s : Space k, (∀ i, 0 < s i) →
      -(modelFiber C s) ⊆ a • modelFiber C s := by
  obtain ⟨a,ha,hcenter⟩ := uniform_centering_at_one hD hneD hmax
  refine ⟨a,ha,?_⟩
  intro C hC hf s hs
  have hh := hcenter _ (hC.positive_base_image s hs)
    (hf.affine_image hD hneD
      ((positiveBaseEquiv s hs).prodCongr (ContinuousLinearEquiv.refl ℝ (Space m))).toContinuousAffineEquiv)
  simpa only [ContinuousLinearEquiv.coe_toContinuousAffineEquiv,fiber_positive_base_image] using hh

end AffineBernstein

end

end OAI
