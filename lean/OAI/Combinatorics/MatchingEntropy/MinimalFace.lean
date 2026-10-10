import OAI.Combinatorics.MatchingEntropy.Pointwise

namespace OAI

noncomputable section

open scoped BigOperators Topology
open Filter

universe uV uE uI uJ uA uB uC uW uF uD uι

namespace MatchingEntropyBounds.Refined

variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

def minimalFace (G : LooplessGraph V E) (x : E → ℝ) : Set (E → ℝ) :=
  {y | y ∈ G.polytope ∧ (∀ e, x e = 0 → y e = 0) ∧
    ∀ S : Finset V, Odd S.card → G.cutMass x S = 1 → G.cutMass y S = 1}

def faceDimension (G : LooplessGraph V E) (x : E → ℝ) : ℕ :=
  Module.finrank ℝ (affineSpan ℝ (minimalFace G x)).direction

theorem even_of_mem (G : LooplessGraph V E) {x : E → ℝ} (hx : x ∈ G.polytope) :
    Even (Fintype.card V) := by
  obtain ⟨M⟩ := matching_nonempty_of_mem G hx
  rw [← G.matching_card_twice M]
  exact even_two_mul _

omit [Fintype V] in
theorem self_mem_minimalFace (G : LooplessGraph V E) {x : E → ℝ} (hx : x ∈ G.polytope) :
    x ∈ minimalFace G x := ⟨hx, fun _ h => h, fun _ _ h => h⟩

omit [Fintype V] in
theorem minimalFace_sub_direction (G : LooplessGraph V E) {x y : E → ℝ}
    (hx : x ∈ G.polytope) (hy : y ∈ minimalFace G x) :
    y - x ∈ (G.faceSpace x).map (LooplessGraph.positiveExtension x) := by
  let u : {e // 0 < x e} → ℝ := fun e => y e.val - x e.val
  have hext : LooplessGraph.positiveExtension x u = y - x := by
    ext e
    by_cases he : 0 < x e
    · simp [LooplessGraph.positiveExtension, he, u]
    · have hz : x e = 0 := le_antisymm (le_of_not_gt he) ((G.polytope_subset_constraintPolytope hx).1 e)
      simp [LooplessGraph.positiveExtension, hz, hy.2.1 e hz]
  refine ⟨u, ?_, hext⟩
  rw [LooplessGraph.faceSpace]
  change G.degreeLinear (LooplessGraph.positiveExtension x u) = 0 ∧ _
  rw [hext]
  constructor
  · rw [map_sub]
    ext v
    change G.degree y v - G.degree x v = 0
    rw [(G.polytope_subset_constraintPolytope hy.1).2.1,
      (G.polytope_subset_constraintPolytope hx).2.1, sub_self]
  · intro S hS ht
    rw [map_sub]
    change G.cutMass y S - G.cutMass x S = 0
    rw [hy.2.2 S hS ht, ht, sub_self]

theorem direction_eventually_minimalFace (G : LooplessGraph V E) {x : E → ℝ}
    (hx : x ∈ G.polytope) {u : E → ℝ}
    (hu : u ∈ (G.faceSpace x).map (LooplessGraph.positiveExtension x)) :
    ∀ᶠ t : ℝ in 𝓝 0, x + t • u ∈ minimalFace G x := by
  obtain ⟨v, hv, rfl⟩ := hu
  have hline := G.faceSpace_eventually_line (G.polytope_subset_constraintPolytope hx) hv
  rw [← G.polytope_eq_constraints (even_of_mem G hx)] at hline
  filter_upwards [hline] with t ht
  refine ⟨ht, ?_, ?_⟩
  · intro e he
    simp [he, LooplessGraph.positiveExtension_zero x v he]
  · intro S hS hcut
    change G.cutLinear S (x + t • LooplessGraph.positiveExtension x v) = 1
    rw [map_add, map_smul, hv.2 S hS hcut, smul_zero, add_zero]
    exact hcut

theorem minimalFace_spec (G : LooplessGraph V E) {x : E → ℝ} (hx : x ∈ G.polytope) :
    x ∈ minimalFace G x ∧ Convex ℝ (minimalFace G x) ∧
    IsExtreme ℝ G.polytope (minimalFace G x) ∧
    ∀ A : Set (E → ℝ), IsExtreme ℝ G.polytope A → x ∈ A → minimalFace G x ⊆ A := by
  refine ⟨self_mem_minimalFace G hx, ?_, ?_, ?_⟩
  · intro y hy z hz a b ha hb hab
    refine ⟨(convex_convexHull ℝ _ ) hy.1 hz.1 ha hb hab, ?_, ?_⟩
    · intro e he
      simp [hy.2.1 e he, hz.2.1 e he]
    · intro S hS ht
      rw [G.cutMass_linear, hy.2.2 S hS ht, hz.2.2 S hS ht]
      simpa using hab
  · refine ⟨fun _ h => h.1, ?_⟩
    intro y hy z hz w hw hseg
    obtain ⟨a, b, ha, hb, hab, rfl⟩ := hseg
    have hyc := G.polytope_subset_constraintPolytope hy
    have hzc := G.polytope_subset_constraintPolytope hz
    refine ⟨hy, ?_, ?_⟩
    · intro e he
      have h := hw.2.1 e he
      change a * y e + b * z e = 0 at h
      have hn := mul_nonneg hb.le (hzc.1 e)
      have hyn := hyc.1 e
      nlinarith
    · intro S hS ht
      have h := hw.2.2 S hS ht
      rw [G.cutMass_linear] at h
      have hyn := hyc.2.2 S hS
      have hzn := hzc.2.2 S hS
      nlinarith
  · intro A hA hxA y hy
    have hline := direction_eventually_minimalFace G hx (minimalFace_sub_direction G hx hy)
    have hneg : ∀ᶠ t : ℝ in 𝓝 0, x + (-t) • (y - x) ∈ minimalFace G x :=
      (show Tendsto (fun t : ℝ => -t) (𝓝 0) (𝓝 0) by
        simpa using continuous_neg.tendsto (0 : ℝ)).eventually hline
    have hh : ∀ᶠ t : ℝ in 𝓝[>] 0, (x + (-t) • (y-x) ∈ minimalFace G x) ∧ 0 < t :=
      (hneg.filter_mono nhdsWithin_le_nhds).and eventually_mem_nhdsWithin
    obtain ⟨a, ha, ha0⟩ := hh.exists
    apply hA.left_mem_of_mem_openSegment hy.1 ha.1 hxA
    refine ⟨a / (1+a), 1 / (1+a), div_pos ha0 (by linarith),
      div_pos (by norm_num) (by linarith), ?_, ?_⟩
    · field_simp
      ring
    · ext e
      simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      field_simp
      ring

theorem minimalFace_direction (G : LooplessGraph V E) {x : E → ℝ} (hx : x ∈ G.polytope) :
    (affineSpan ℝ (minimalFace G x)).direction =
      (G.faceSpace x).map (LooplessGraph.positiveExtension x) := by
  apply le_antisymm
  · have hle : affineSpan ℝ (minimalFace G x) ≤
        AffineSubspace.mk' x ((G.faceSpace x).map (LooplessGraph.positiveExtension x)) := by
      apply affineSpan_le.mpr
      intro y hy
      exact (AffineSubspace.mem_mk').mpr (minimalFace_sub_direction G hx hy)
    simpa using AffineSubspace.direction_le hle
  · intro u hu
    have he := direction_eventually_minimalFace G hx hu
    have hh : ∀ᶠ t : ℝ in 𝓝[>] 0, (x + t • u ∈ minimalFace G x) ∧ 0 < t :=
      (he.filter_mono nhdsWithin_le_nhds).and eventually_mem_nhdsWithin
    obtain ⟨a, ha, ha0⟩ := hh.exists
    have hd := AffineSubspace.vsub_mem_direction
      (subset_affineSpan ℝ _ ha) (subset_affineSpan ℝ _ (self_mem_minimalFace G hx))
    have hd' : a • u ∈ (affineSpan ℝ (minimalFace G x)).direction := by
      simpa using hd
    have hh := (affineSpan ℝ (minimalFace G x)).direction.smul_mem a⁻¹ hd'
    simpa [smul_smul, ne_of_gt ha0] using hh

omit [Fintype E] [DecidableEq E] in
theorem positiveExtension_injective (x : E → ℝ) :
    Function.Injective (LooplessGraph.positiveExtension x) := by
  intro u v h
  ext e
  simpa using congrFun h e.val

theorem faceDimension_eq (G : LooplessGraph V E) {x : E → ℝ} (hx : x ∈ G.polytope) :
    faceDimension G x = Module.finrank ℝ (G.faceSpace x) := by
  rw [faceDimension, minimalFace_direction G hx]
  exact (Submodule.equivMapOfInjective _ (positiveExtension_injective x) _).finrank_eq.symm

theorem minimalFace_rank (G : LooplessGraph V E) (m : ℕ)
    (hm : 0 < m) (hV : Fintype.card V = 2 * m) {x : E → ℝ} (hx : x ∈ G.polytope) :
    Fintype.card {e // 0 < x e} + 2 ≤ faceDimension G x + 3 * m := by
  have hr := sharp_face_rank G m hm hV hx
  have hd := (G.faceSpace x).finrank_quotient_add_finrank
  rw [Module.finrank_pi] at hd
  rw [faceDimension_eq G hx]
  dsimp only [LooplessGraph.faceCodimension] at hr
  omega

def IsFractional (x : E → ℝ) (e : E) : Prop := 0 < x e ∧ x e < 1

end MatchingEntropyBounds.Refined

end

end OAI
