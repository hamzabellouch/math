import OAI.MathematicalPhysics.NavierStokes.BalancedTransport.Elementary

namespace OAI

noncomputable section
namespace BalancedTransport.Geometry
open MeasureTheory Filter Set
open scoped Topology ENNReal NNReal
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

omit [NormedSpace ℝ F] in
lemma SpatiallySupported.hasCompactSupport {K : Set Space} (hK : IsCompact K)
    {v : Field F} (hs : SpatiallySupported K v) (t : ℝ) : HasCompactSupport (v t) := by
  apply hK.of_isClosed_subset (isClosed_tsupport _)
  exact closure_minimal (fun x hx => by
    by_contra hn
    exact hx (hs t x hn)) hK.isClosed

lemma JointSmooth.memLp {K : Set Space} (hK : IsCompact K) {v : Field F}
    (hv : JointSmooth v) (hs : SpatiallySupported K v) (t : ℝ) :
    MemLp (v t) 2 (volume : Measure Space) :=
  (hv.slice t).continuous.memLp_of_hasCompactSupport (hs.hasCompactSupport hK t)

def supportedL2Curve {K : Set Space} (hK : IsCompact K) {v : Field F}
    (hv : JointSmooth v) (hs : SpatiallySupported K v) : ℝ → Lp F 2 (volume : Measure Space) :=
  fun t => (hv.memLp hK hs t).toLp (v t)

lemma supportedL2Curve_coe {K : Set Space} (hK : IsCompact K) {v : Field F}
    (hv : JointSmooth v) (hs : SpatiallySupported K v) (t : ℝ) :
    (supportedL2Curve hK hv hs t : Space → F) =ᵐ[volume] v t := MemLp.coeFn_toLp _

def supportL2Size (K : Set Space) (hK : IsCompact K) : ℝ :=
  ‖indicatorConstLp (μ := (volume : Measure Space)) 2 hK.measurableSet hK.measure_lt_top.ne (1 : ℝ)‖

lemma supportL2Size_nonneg (K : Set Space) (hK : IsCompact K) : 0 ≤ supportL2Size K hK :=
  norm_nonneg _

omit [NormedSpace ℝ F] in
lemma lp_norm_bound_of_support {K : Set Space} (hK : IsCompact K)
    {f : Lp F 2 (volume : Measure Space)} {g : Space → F} {C : ℝ}
    (he : (f : Space → F) =ᵐ[volume] g) (hs : ∀ x, x ∉ K → g x = 0)
    (hb : ∀ x, ‖g x‖ ≤ C) : ‖f‖ ≤ C * supportL2Size K hK := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [he, indicatorConstLp_coeFn (p := 2) (μ := (volume : Measure Space))
      (hs := hK.measurableSet) (hμs := hK.measure_lt_top.ne) (c := (1 : ℝ))] with x hfx hix
  rw [hfx, hix]
  by_cases hx : x ∈ K
  · simpa only [indicator_of_mem hx, norm_one, mul_one] using hb x
  · simp only [indicator_of_notMem hx, hs x hx, norm_zero, mul_zero, le_refl]

lemma time_difference_bound {v : Field F} (hv : JointSmooth v) {C : ℝ}
    (hb : ∀ t, 0 ≤ t → ∀ x, ‖fullTimeD v t x‖ ≤ C)
    {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (x : Space) :
    ‖v s x - v t x‖ ≤ C * ‖s - t‖ :=
  (convex_Ici (0 : ℝ)).norm_image_sub_le_of_norm_deriv_le
    (fun r _ => (hv.timeSlice x).differentiable (by simp) r)
    (fun r hr => hb r hr x) ht hs

lemma time_remainder_bound {v : Field F} (hv : JointSmooth v) {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ t, 0 ≤ t → ∀ x, ‖fullTimeD (fullTimeD v) t x‖ ≤ B)
    {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (x : Space) :
    ‖v s x - v t x - (s - t) • fullTimeD v t x‖ ≤ B * ‖s - t‖ * ‖s - t‖ := by
  let r : ℝ → F := fun q => v q x - v t x - (q - t) • fullTimeD v t x
  have hdr (q : ℝ) : HasDerivAt r (fullTimeD v q x - fullTimeD v t x) q := by
    convert (((hv.timeSlice x).differentiable (by simp) q).hasDerivAt.sub_const (v t x)).sub
        (((hasDerivAt_id q).sub_const t).smul_const (fullTimeD v t x)) using 1 <;>
      simp only [r, fullTimeD, id_eq, one_smul]
    rfl
  have hbound (q : ℝ) (hq : q ∈ uIcc t s) :
      ‖deriv r q‖ ≤ B * ‖s - t‖ := by
    rw [(hdr q).deriv]
    have hq₀ : 0 ≤ q := (le_min ht hs).trans hq.1
    refine (time_difference_bound hv.fullTimeD hb hq₀ ht x).trans ?_
    apply mul_le_mul_of_nonneg_left _ hB
    simpa only [Real.dist_eq, ← Real.norm_eq_abs, norm_sub_rev] using
      Real.dist_left_le_of_mem_uIcc hq
  have h := (convex_uIcc t s).norm_image_sub_le_of_norm_deriv_le
    (fun q _ => (hdr q).differentiableAt) hbound (left_mem_uIcc) (right_mem_uIcc)
  simpa only [r, sub_self, zero_smul, sub_zero] using h

lemma supportedL2Curve_difference_bound {K : Set Space} (hK : IsCompact K)
    {v : Field F} (hv : JointSmooth v) (hs : SpatiallySupported K v) {C : ℝ}
    (hb : ∀ t, 0 ≤ t → ∀ x, ‖fullTimeD v t x‖ ≤ C)
    {s t : ℝ} (hs₀ : 0 ≤ s) (ht₀ : 0 ≤ t) :
    ‖supportedL2Curve hK hv hs s - supportedL2Curve hK hv hs t‖ ≤
      C * ‖s - t‖ * supportL2Size K hK := by
  apply lp_norm_bound_of_support hK
  · exact (Lp.coeFn_sub _ _).trans ((supportedL2Curve_coe hK hv hs s).sub
      (supportedL2Curve_coe hK hv hs t))
  · intro x hx
    change v s x - v t x = 0
    simp only [hs s x hx, hs t x hx, sub_self]
  · exact fun x => time_difference_bound hv hb hs₀ ht₀ x

lemma supportedL2Curve_continuousOn {K : Set Space} (hK : IsCompact K)
    {v : Field F} (hv : JointSmooth v) (hs : SpatiallySupported K v) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ t, 0 ≤ t → ∀ x, ‖fullTimeD v t x‖ ≤ C) :
    ContinuousOn (supportedL2Curve hK hv hs) (Ici 0) := by
  let L : ℝ≥0 := ⟨C * supportL2Size K hK, mul_nonneg hC (supportL2Size_nonneg K hK)⟩
  apply LipschitzOnWith.continuousOn (K := L)
  apply LipschitzOnWith.of_dist_le_mul
  intro s hs₀ t ht₀
  simp only [dist_eq_norm]
  change ‖supportedL2Curve hK hv hs s - supportedL2Curve hK hv hs t‖ ≤
    C * supportL2Size K hK * ‖s - t‖
  convert supportedL2Curve_difference_bound hK hv hs hb hs₀ ht₀ using 1
  ring

lemma supportedL2Curve_hasDerivWithinAt {K : Set Space} (hK : IsCompact K)
    {v : Field F} (hv : JointSmooth v) (hs : SpatiallySupported K v) {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ t, 0 ≤ t → ∀ x, ‖fullTimeD (fullTimeD v) t x‖ ≤ B)
    {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (supportedL2Curve hK hv hs)
      (supportedL2Curve hK hv.fullTimeD hs.fullTimeD t) (Ici 0) t := by
  let V := supportedL2Curve hK hv hs
  let W := supportedL2Curve hK hv.fullTimeD hs.fullTimeD
  have hrem (s : ℝ) (hs₀ : 0 ≤ s) :
      ‖V s - V t - (s-t) • W t‖ ≤ B * ‖s-t‖ * ‖s-t‖ * supportL2Size K hK := by
    apply lp_norm_bound_of_support hK
    · exact (Lp.coeFn_sub _ _).trans (((Lp.coeFn_sub _ _).trans
        ((supportedL2Curve_coe hK hv hs s).sub (supportedL2Curve_coe hK hv hs t))).sub
        ((Lp.coeFn_smul _ _).trans ((supportedL2Curve_coe hK hv.fullTimeD hs.fullTimeD t).const_smul _)))
    · intro x hx
      change v s x - v t x - (s-t) • fullTimeD v t x = 0
      simp only [hs s x hx, hs t x hx, hs.fullTimeD t x hx, sub_self, smul_zero]
    · exact fun x => time_remainder_bound hv hB hb hs₀ ht x
  apply HasDerivWithinAt.of_isLittleO
  apply Asymptotics.IsLittleO.of_bound
  intro ε hε
  have hc : ContinuousAt (fun s : ℝ => B * supportL2Size K hK * ‖s-t‖) t := by fun_prop
  have hn : ∀ᶠ s in 𝓝[Ici 0] t, B * supportL2Size K hK * ‖s-t‖ < ε :=
    mem_nhdsWithin_of_mem_nhds (hc.eventually (gt_mem_nhds (by simpa using hε)))
  filter_upwards [self_mem_nhdsWithin, hn] with s hs₀ hsε
  exact (hrem s hs₀).trans (by nlinarith [norm_nonneg (s-t)])

lemma spatialD_eq_fullMixedD (a : List (Fin 3)) (v : Field F) :
    spatialD a v = fullMixedD (a.map some) v := by
  induction a with
  | nil => rfl
  | cons i a ha => simp only [spatialD, List.map_cons, fullMixedD, ha]

theorem CH_of_compact_boundedMixed {K : Set Space} (hK : IsCompact K)
    {v : Field F} (hv : JointSmooth v) (hs : SpatiallySupported K v) (hb : BoundedMixed v)
    (k : ℕ) : CH k v := by
  intro a _
  let d := fullMixedD (a.map some) v
  have hd : JointSmooth d := hv.fullMixedD _
  have hds : SpatiallySupported K d := hs.fullMixedD hK.isClosed _
  obtain ⟨C, hC, hbound⟩ := hb (none :: a.map some)
  have he (t : ℝ) (ht : 0 ≤ t) (x : Space) :
      fullTimeD d t x = mixedD (none :: a.map some) v t x :=
    fullMixedD_eq_mixedD hv (none :: a.map some) t ht x
  have hb' : ∀ t, 0 ≤ t → ∀ x, ‖fullTimeD d t x‖ ≤ C := by
    intro t ht x
    rw [he t ht x]
    exact hbound t ht x
  refine ⟨supportedL2Curve hK hd hds,
    supportedL2Curve_continuousOn hK hd hds hC hb', fun t _ => ?_⟩
  simpa only [spatialD_eq_fullMixedD] using supportedL2Curve_coe hK hd hds t

theorem C1L2_of_compact_boundedMixed {K : Set Space} (hK : IsCompact K)
    {v : Field F} (hv : JointSmooth v) (hs : SpatiallySupported K v) (hb : BoundedMixed v) :
    C1L2 v := by
  obtain ⟨C, hC, hc⟩ := hb [none]
  obtain ⟨B, hB, hb'⟩ := hb [none, none]
  have hc' : ∀ t, 0 ≤ t → ∀ x, ‖fullTimeD v t x‖ ≤ C := by
    intro t ht x
    rw [show fullTimeD v t x = mixedD [none] v t x from fullMixedD_eq_mixedD hv [none] t ht x]
    exact hc t ht x
  have hb'' : ∀ t, 0 ≤ t → ∀ x, ‖fullTimeD (fullTimeD v) t x‖ ≤ B := by
    intro t ht x
    rw [show fullTimeD (fullTimeD v) t x = mixedD [none,none] v t x from
      fullMixedD_eq_mixedD hv [none, none] t ht x]
    exact hb' t ht x
  refine ⟨supportedL2Curve hK hv hs, supportedL2Curve hK hv.fullTimeD hs.fullTimeD,
    supportedL2Curve_continuousOn hK hv hs hC hc',
    supportedL2Curve_continuousOn hK hv.fullTimeD hs.fullTimeD hB hb'', fun t ht => ?_⟩
  refine ⟨supportedL2Curve_coe hK hv hs t, ?_,
    supportedL2Curve_hasDerivWithinAt hK hv hs hB hb'' ht⟩
  apply (supportedL2Curve_coe hK hv.fullTimeD hs.fullTimeD t).trans
  exact Eventually.of_forall (fun x => fullMixedD_eq_mixedD hv [none] t ht x)

lemma boundedOnFiniteSlabs_of_boundedMixed {v : Velocity} (hv : BoundedMixed v) :
    BoundedOnFiniteSlabs v := by
  obtain ⟨C, hC, hb⟩ := hv []
  have hd : ∀ i : Fin 3, ∃ D : ℝ, 0 ≤ D ∧ ∀ t, 0 ≤ t → ∀ x, ‖spaceD i v t x‖ ≤ D :=
    fun i => hv [some i]
  choose D hD hd using hd
  intro T _
  refine ⟨C + ∑ i, D i, add_nonneg hC (Finset.sum_nonneg (fun i _ => hD i)), ?_⟩
  intro t ht x
  constructor
  · exact (hb t ht.1 x).trans (le_add_of_nonneg_right (Finset.sum_nonneg (fun i _ => hD i)))
  · intro i
    exact (hd i t ht.1 x).trans
      ((Finset.single_le_sum (fun j _ => hD j) (Finset.mem_univ i)).trans (le_add_of_nonneg_left hC))

lemma spatialD_zero (a : List (Fin 3)) : spatialD a (0 : Field F) = 0 := by
  induction a with
  | nil => rfl
  | cons i a ha =>
    simp only [spatialD, ha]
    ext t x
    simp [spaceD]

lemma CH_zero (k : ℕ) : CH k (0 : Field F) := by
  intro a _
  refine ⟨0, continuousOn_const, fun t _ => ?_⟩
  rw [spatialD_zero]
  exact Lp.coeFn_zero F 2 (volume : Measure Space)

theorem comparisonClass_of_compact_boundedMixed {K : Set Space} (hK : IsCompact K)
    {v : Velocity} (hv : JointSmooth v) (hs : SpatiallySupported K v) (hb : BoundedMixed v) :
    ComparisonClass v (fun _ _ => 0) := by
  refine ⟨CH_of_compact_boundedMixed hK hv hs hb 2,
    C1L2_of_compact_boundedMixed hK hv hs hb,
    boundedOnFiniteSlabs_of_boundedMixed hb, fun _ => 0, ?_⟩
  convert CH_zero (F := ℝ) 1 using 1
  ext t x
  exact sub_zero 0

end BalancedTransport.Geometry
end

end OAI
