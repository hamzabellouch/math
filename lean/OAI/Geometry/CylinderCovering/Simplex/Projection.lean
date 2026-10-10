import OAI.Geometry.CylinderCovering.Simplex.ProjectionDefinitions
import OAI.Geometry.CylinderCovering.Convexity.AffineSimplexChord
import OAI.Geometry.CylinderCovering.Simplex.LayerCake
import OAI.Geometry.CylinderCovering.Ruled.Fubini
import OAI.Geometry.CylinderCovering.Simplex.DiameterBridge

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped InnerProductSpace

namespace CylinderCovering

lemma orthogonalProjection_add {d : ℕ} (u x y : Euclidean d) :
    orthogonalProjection u (x + y) =
      orthogonalProjection u x + orthogonalProjection u y := by
  simp only [orthogonalProjection, inner_add_right, add_smul]
  abel

lemma orthogonalProjection_smul {d : ℕ} (u x : Euclidean d) (r : ℝ) :
    orthogonalProjection u (r • x) = r • orthogonalProjection u x := by
  simp only [orthogonalProjection, inner_smul_right, smul_sub, smul_smul]

lemma orthogonalProjection_sub {d : ℕ} (u x y : Euclidean d) :
    orthogonalProjection u (x - y) =
      orthogonalProjection u x - orthogonalProjection u y := by
  simp only [orthogonalProjection, inner_sub_right, sub_smul]
  abel

lemma orthogonalProjection_homothety {d : ℕ} (u p x : Euclidean d) (r : ℝ) :
    orthogonalProjection u (AffineMap.homothety p r x) =
      AffineMap.homothety (orthogonalProjection u p) r (orthogonalProjection u x) := by
  simp only [AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add,
    orthogonalProjection_add, orthogonalProjection_smul, orthogonalProjection_sub]

lemma projection_image_homothety {d : ℕ} (u p : Euclidean d) (r : ℝ)
    (S : Set (Euclidean d)) :
    orthogonalProjection u '' (AffineMap.homothety p r '' S) =
      AffineMap.homothety (orthogonalProjection u p) r ''
        (orthogonalProjection u '' S) := by
  simp only [Set.image_image]
  congr 1
  funext x
  exact orthogonalProjection_homothety u p x r

theorem projected_homothety_measure {d : ℕ} (u p : Euclidean d) {r : ℝ}
    (hr : r ≠ 0) (S : Set (Euclidean d)) :
    Measure.euclideanHausdorffMeasure (d - 1)
        (orthogonalProjection u '' (AffineMap.homothety p r '' S)) =
      ‖r‖₊ ^ (d - 1) • Measure.euclideanHausdorffMeasure (d - 1)
        (orthogonalProjection u '' S) := by
  rw [projection_image_homothety]
  exact euclideanHausdorffMeasure_homothety_image (d - 1) _ hr _

lemma projected_homothety_area {d : ℕ} (u p : Euclidean d) {r : ℝ}
    (hr : 0 < r) (S : Set (Euclidean d)) :
    (Measure.euclideanHausdorffMeasure (d - 1)
        (orthogonalProjection u '' (AffineMap.homothety p r '' S))).toReal =
      r ^ (d - 1) * (Measure.euclideanHausdorffMeasure (d - 1)
        (orthogonalProjection u '' S)).toReal := by
  rw [projected_homothety_measure u p (ne_of_gt hr) S]
  simp [ENNReal.smul_def, ENNReal.toReal_mul, ENNReal.toReal_pow,
    Real.norm_eq_abs, abs_of_pos hr]

theorem projected_intersection_area {d : ℕ} (u p : Euclidean d)
    (S : Set (Euclidean d)) {s L : ℝ} (hL : 0 < L) (hs : s < L)
    (hgeom : {x | x ∈ S ∧ x + s • u ∈ S} =
      AffineMap.homothety p (1 - s / L) '' S) :
    (Measure.euclideanHausdorffMeasure (d - 1)
      (orthogonalProjection u '' {x | x ∈ S ∧ x + s • u ∈ S})).toReal =
    (1 - s / L) ^ (d - 1) *
      (Measure.euclideanHausdorffMeasure (d - 1) (orthogonalProjection u '' S)).toReal := by
  rw [hgeom]
  apply projected_homothety_area
  exact sub_pos.mpr ((div_lt_one hL).mpr hs)

lemma real_fiber_length_iff {F : Set ℝ} (hF : IsCompact F) (hcv : Convex ℝ F)
    {s : ℝ} (hs : 0 < s) :
    s ≤ volume.real F ↔ ∃ t ∈ F, t + s ∈ F := by
  by_cases hne : F.Nonempty
  · have hconn : IsConnected F := ⟨hne, hcv.isPreconnected⟩
    have heq := eq_Icc_of_connected_compact hconn hF
    have hab : sInf F ≤ sSup F := csInf_le_csSup hne hF.bddBelow hF.bddAbove
    rw [heq, Real.volume_real_Icc_of_le hab]
    constructor
    · intro h
      refine ⟨sInf F, ⟨le_rfl, hab⟩, ?_⟩
      constructor <;> linarith
    · rintro ⟨t, ht, hts⟩
      linarith [ht.1, hts.2]
  · have heq : F = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    simp [heq, not_le.mpr hs]

def lineFiber {d : ℕ} (S : Set (Euclidean d)) (u y : Euclidean d) : Set ℝ :=
  {t | y + t • u ∈ S}

lemma lineFiber_isometry {d : ℕ} {u : Euclidean d} (hu : ‖u‖ = 1)
    (y : Euclidean d) : Isometry (fun t : ℝ => y + t • u) := by
  apply isometry_iff_dist_eq.mpr
  intro a b
  rw [dist_eq_norm, dist_eq_norm]
  simp only [add_sub_add_left_eq_sub, ← sub_smul, norm_smul, hu, mul_one]

lemma lineFiber_compact {d : ℕ} {S : Set (Euclidean d)} (hS : IsCompact S)
    {u : Euclidean d} (hu : ‖u‖ = 1) (y : Euclidean d) :
    IsCompact (lineFiber S u y) :=
  (lineFiber_isometry hu y).isClosedEmbedding.isCompact_preimage hS

lemma lineFiber_convex {d : ℕ} {S : Set (Euclidean d)} (hS : Convex ℝ S)
    (u y : Euclidean d) : Convex ℝ (lineFiber S u y) := by
  intro a ha b hb c e hc he hce
  change y + (c * a + e * b) • u ∈ S
  have h := hS ha hb hc he hce
  convert h using 1
  calc
    y + (c * a + e * b) • u =
        (c + e) • y + (c * a + e * b) • u := by rw [hce, one_smul]
    _ = c • (y + a • u) + e • (y + b • u) := by module

lemma projection_mem_normal {d : ℕ} {u : Euclidean d} (hu : ‖u‖ = 1)
    (x : Euclidean d) : inner ℝ u (orthogonalProjection u x) = 0 := by
  simp [orthogonalProjection, inner_sub_right, inner_smul_right,
    hu]

lemma projection_line {d : ℕ} {u y : Euclidean d} (hu : ‖u‖ = 1)
    (hy : inner ℝ u y = 0) (t : ℝ) :
    orthogonalProjection u (y + t • u) = y := by
  simp [orthogonalProjection, inner_add_right, inner_smul_right, hy,
    hu]

lemma projection_reconstruct {d : ℕ} (u x : Euclidean d) :
    orthogonalProjection u x + inner ℝ u x • u = x := by
  simp [orthogonalProjection]

theorem fiber_superlevel_iff {d : ℕ} {S : Set (Euclidean d)}
    (hS : IsCompact S) (hcv : Convex ℝ S) {u y : Euclidean d}
    (hu : ‖u‖ = 1) (hy : inner ℝ u y = 0) {s : ℝ} (hs : 0 < s) :
    s ≤ volume.real (lineFiber S u y) ↔
      y ∈ orthogonalProjection u '' {x | x ∈ S ∧ x + s • u ∈ S} := by
  rw [real_fiber_length_iff (lineFiber_compact hS hu y) (lineFiber_convex hcv u y) hs]
  constructor
  · rintro ⟨t, ht, hts⟩
    refine ⟨y + t • u, ⟨ht, ?_⟩, projection_line hu hy t⟩
    simpa only [lineFiber, Set.mem_ofPred_eq, add_smul, add_assoc] using hts
  · rintro ⟨x, ⟨hx, hxs⟩, hxy⟩
    refine ⟨inner ℝ u x, ?_, ?_⟩
    · change y + inner ℝ u x • u ∈ S
      rw [← hxy, projection_reconstruct]
      exact hx
    · change y + (inner ℝ u x + s) • u ∈ S
      rw [add_smul, ← add_assoc, ← hxy, projection_reconstruct]
      exact hxs

lemma simplex_normalPlane_rank {d : ℕ} {u : Euclidean d} (hu : ‖u‖ = 1) :
    Module.finrank ℝ ((ℝ ∙ u)ᗮ) = d - 1 := by
  have hun : u ≠ 0 := by intro h; simp [h] at hu
  have h := (ℝ ∙ u).finrank_add_finrank_orthogonal
  rw [finrank_span_singleton hun] at h
  have hr : Module.finrank ℝ (Euclidean d) = d := by simp
  rw [hr] at h
  omega

theorem fiber_superlevel_measure {d : ℕ} {S : Set (Euclidean d)}
    (hS : IsCompact S) (hcv : Convex ℝ S) {u : Euclidean d}
    (hu : ‖u‖ = 1) {s : ℝ} (hs : 0 < s) :
    Measure.euclideanHausdorffMeasure (d - 1)
      (orthogonalProjection u '' {x | x ∈ S ∧ x + s • u ∈ S}) =
    volume {y : ((ℝ ∙ u)ᗮ) | s ≤ volume.real (lineFiber S u y)} := by
  let T : Set ((ℝ ∙ u)ᗮ) := {y | s ≤ volume.real (lineFiber S u y)}
  have himage : (Subtype.val : ((ℝ ∙ u)ᗮ) → Euclidean d) '' T =
      orthogonalProjection u '' {x | x ∈ S ∧ x + s • u ∈ S} := by
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (fiber_superlevel_iff hS hcv hu
        (Submodule.mem_orthogonal_singleton_iff_inner_right.mp y.property) hs).mp hy
    · intro hz
      have hzperp : z ∈ ((ℝ ∙ u)ᗮ) := by
        obtain ⟨x, _, rfl⟩ := hz
        exact Submodule.mem_orthogonal_singleton_iff_inner_right.mpr
          (projection_mem_normal hu x)
      refine ⟨⟨z, hzperp⟩, ?_, rfl⟩
      exact (fiber_superlevel_iff hS hcv hu
        (Submodule.mem_orthogonal_singleton_iff_inner_right.mp hzperp) hs).mpr hz
  rw [← himage, isometry_subtype_coe.euclideanHausdorffMeasure_image]
  have hmeasure : (Measure.euclideanHausdorffMeasure (d - 1) : Measure ((ℝ ∙ u)ᗮ)) =
      volume := by
    simpa only [simplex_normalPlane_rank hu] using
      (InnerProductSpace.euclideanHausdorffMeasure_eq_volume (V := ((ℝ ∙ u)ᗮ)))
  rw [hmeasure]

theorem fiber_distribution_of_intersection {d : ℕ} {S : Set (Euclidean d)}
    (hS : IsCompact S) (hcv : Convex ℝ S) {u : Euclidean d}
    (hu : ‖u‖ = 1) (p : Euclidean d) {s L : ℝ}
    (hL : 0 < L) (hs : 0 < s) (hsL : s < L)
    (hgeom : {x | x ∈ S ∧ x + s • u ∈ S} =
      AffineMap.homothety p (1 - s / L) '' S) :
    volume.real {y : ((ℝ ∙ u)ᗮ) | s ≤ volume.real (lineFiber S u y)} =
      (1 - s / L) ^ (d - 1) *
        (Measure.euclideanHausdorffMeasure (d - 1) (orthogonalProjection u '' S)).toReal := by
  change (volume {y : ((ℝ ∙ u)ᗮ) | s ≤ volume.real (lineFiber S u y)}).toReal = _
  rw [← fiber_superlevel_measure hS hcv hu hs]
  exact projected_intersection_area u p S hL hsL hgeom

def simplexAffineBasis {d : ℕ} (v : Fin (d + 1) → Euclidean d)
    (hv : AffineIndependent ℝ v) : AffineBasis (Fin (d + 1)) ℝ (Euclidean d) where
  toFun := v
  ind' := hv
  tot' := hv.affineSpan_eq_top_iff_card_eq_finrank_add_one.mpr (by simp)

theorem simplex_chord_data {d : ℕ} (v : Fin (d + 1) → Euclidean d)
    (hv : AffineIndependent ℝ v) {u : Euclidean d} (hu : ‖u‖ = 1) :
    0 < longestChord (simplexCarrier v) u ∧
    (∀ x ∈ simplexCarrier v, ∀ s : ℝ, 0 ≤ s →
      x + s • u ∈ simplexCarrier v → s ≤ longestChord (simplexCarrier v) u) ∧
    ∃ p ∈ simplexCarrier v, ∀ s : ℝ, 0 ≤ s →
      s < longestChord (simplexCarrier v) u →
      {x | x ∈ simplexCarrier v ∧ x + s • u ∈ simplexCarrier v} =
        AffineMap.homothety p (1 - s / longestChord (simplexCarrier v) u) ''
          simplexCarrier v := by
  let p := simplexAffineBasis v hv
  have hpv : (p : Fin (d + 1) → Euclidean d) = v := rfl
  have hu0 : u ≠ 0 := by intro h; simp [h] at hu
  let c : ℝ := ∑ i, max 0 (-(p.coord i).linear u)
  obtain ⟨hc, hex, hbound⟩ := SimplexChord.affine_maximal_chord p hu0
  change 0 < c at hc
  have hgreat : IsGreatest {r : ℝ | 0 ≤ r ∧
      ∃ x ∈ simplexCarrier v, x + r • u ∈ simplexCarrier v} (1 / c) := by
    constructor
    · exact ⟨one_div_nonneg.mpr hc.le, hex⟩
    · intro r hr
      obtain ⟨hr0, x, hx, hxr⟩ := hr
      exact hbound x r hr0 hx hxr
  have hL : longestChord (simplexCarrier v) u = 1 / c := hgreat.csSup_eq
  refine ⟨?_, ?_, ?_⟩
  · rw [hL]; positivity
  · intro x hx s hs hxs
    rw [hL]
    exact hbound x s hs hx hxs
  · obtain ⟨q, hq, _, hhom⟩ := SimplexChord.affine_intersection_homothety p hu0
    refine ⟨q, hq, ?_⟩
    intro s hs hsL
    rw [hL] at hsL ⊢
    have hsc : s * c < 1 := (lt_div_iff₀ hc).mp hsL
    have h := hhom s hs hsc
    rw [hpv] at h
    simpa only [one_div, div_inv_eq_mul, c, simplexCarrier] using h

lemma measurable_lineFiber_volume {d : ℕ} {S : Set (Euclidean d)}
    (hS : MeasurableSet S) (u : Euclidean d) :
    Measurable (fun y : ((ℝ ∙ u)ᗮ) => volume (lineFiber S u y)) := by
  let T : Set (((ℝ ∙ u)ᗮ) × ℝ) :=
    {p | (p.1 : Euclidean d) + p.2 • u ∈ S}
  have hT : MeasurableSet T := hS.preimage
    ((continuous_subtype_val.comp continuous_fst).add
      (continuous_snd.smul continuous_const)).measurable
  exact measurable_measure_prodMk_left hT

lemma integrable_lineFiber_length {d : ℕ} {S : Set (Euclidean d)}
    (hS : IsCompact S) {u : Euclidean d} (hu : ‖u‖ = 1) :
    Integrable (fun y : ((ℝ ∙ u)ᗮ) => volume.real (lineFiber S u y)) := by
  have hm := measurable_lineFiber_volume hS.measurableSet u
  have hf : (∫⁻ y : ((ℝ ∙ u)ᗮ), volume (lineFiber S u y)) ≠ ⊤ := by
    unfold lineFiber
    rw [← OrthogonalFubini.volume_directionalSlices u hu hS.measurableSet]
    exact hS.measure_lt_top.ne
  exact (integrable_toReal_iff hm.aemeasurable
    ((ae_lt_top hm hf).mono fun _ h => h.ne)).mpr hf

lemma real_volume_eq_integral_lineFiber {d : ℕ} {S : Set (Euclidean d)}
    (hS : IsCompact S) {u : Euclidean d} (hu : ‖u‖ = 1) :
    volume.real S = ∫ y : ((ℝ ∙ u)ᗮ), volume.real (lineFiber S u y) := by
  have hm := measurable_lineFiber_volume hS.measurableSet u
  have hf : (∫⁻ y : ((ℝ ∙ u)ᗮ), volume (lineFiber S u y)) ≠ ⊤ := by
    unfold lineFiber
    rw [← OrthogonalFubini.volume_directionalSlices u hu hS.measurableSet]
    exact hS.measure_lt_top.ne
  rw [Measure.real, OrthogonalFubini.volume_directionalSlices u hu hS.measurableSet]
  exact (integral_toReal hm.aemeasurable (ae_lt_top hm hf)).symm

lemma lineFiber_length_le_of_chord_bound {d : ℕ} {S : Set (Euclidean d)}
    (hS : IsCompact S) (hcv : Convex ℝ S) {u : Euclidean d}
    (hu : ‖u‖ = 1) {L : ℝ} (hL : 0 ≤ L)
    (hchord : ∀ x ∈ S, ∀ s : ℝ, 0 ≤ s → x + s • u ∈ S → s ≤ L)
    (y : Euclidean d) : volume.real (lineFiber S u y) ≤ L := by
  by_cases hpos : 0 < volume.real (lineFiber S u y)
  · obtain ⟨t, ht, hts⟩ :=
      (real_fiber_length_iff (lineFiber_compact hS hu y) (lineFiber_convex hcv u y) hpos).mp le_rfl
    apply hchord (y + t • u) ht _ hpos.le
    simpa only [lineFiber, Set.mem_ofPred_eq, add_smul, add_assoc] using hts
  · exact (le_of_not_gt hpos).trans hL

theorem simplex_chord_projection_product {d : ℕ} (hd : 2 ≤ d)
    (v : Fin (d + 1) → Euclidean d) (hv : AffineIndependent ℝ v)
    {u : Euclidean d} (hu : ‖u‖ = 1) :
    simplexShadowArea v u * longestChord (simplexCarrier v) u =
      (d : ℝ) * volume.real (simplexCarrier v) := by
  have hS : IsCompact (simplexCarrier v) := (finite_range v).isCompact_convexHull ℝ
  have hcv : Convex ℝ (simplexCarrier v) := convex_convexHull ℝ _
  obtain ⟨hL, hchord, p, hp, hhom⟩ := simplex_chord_data v hv hu
  have hbound :
      (fun y : ((ℝ ∙ u)ᗮ) => volume.real (lineFiber (simplexCarrier v) u y)) ≤ᵐ[volume]
        fun _ => longestChord (simplexCarrier v) u :=
    Filter.Eventually.of_forall fun y =>
      lineFiber_length_le_of_chord_bound hS hcv hu hL.le hchord y
  have hprofile : ∀ s ∈ Ioo (0 : ℝ) (longestChord (simplexCarrier v) u),
      volume.real {y : ((ℝ ∙ u)ᗮ) | s ≤ volume.real (lineFiber (simplexCarrier v) u y)} =
      simplexShadowArea v u * (1 - s / longestChord (simplexCarrier v) u) ^ (d - 1) := by
    intro s hs
    simpa only [simplexShadowArea, mul_comm] using
      fiber_distribution_of_intersection hS hcv hu p hL hs.1 hs.2
        (hhom s hs.1.le hs.2)
  have hcalc := SimplexLayerCake.integral_eq_area_mul_length_div volume
    (fun y : ((ℝ ∙ u)ᗮ) => volume.real (lineFiber (simplexCarrier v) u y))
    (simplexShadowArea v u) (longestChord (simplexCarrier v) u) hL (d - 1)
    (integrable_lineFiber_length hS hu)
    (Filter.Eventually.of_forall fun _ => ENNReal.toReal_nonneg) hbound hprofile
  rw [← real_volume_eq_integral_lineFiber hS hu] at hcalc
  have hdreal : ((d - 1 : ℕ) : ℝ) + 1 = (d : ℝ) := by
    exact_mod_cast (Nat.sub_add_cancel (by omega : 1 ≤ d))
  rw [hdreal] at hcalc
  have hdne : (d : ℝ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
  have hmul := (eq_div_iff hdne).mp hcalc
  nlinarith only [hmul]

theorem simplex_chord_projection : SimplexChordProjectionStatement :=
  simplexChordProjection_of_products fun _ hd v hv _ hu =>
    simplex_chord_projection_product hd v hv hu

theorem tetrahedron_edge_minimizer : TetrahedronEdgeMinimizerStatement :=
  tetrahedronEdgeMinimizer_of_simplexChordProjection simplex_chord_projection

end CylinderCovering

end

end OAI
