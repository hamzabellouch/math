import OAI.Geometry.ProjectionBodies.CosineCalculus

namespace OAI

universe uU

noncomputable section
open Set MeasureTheory Metric Filter Topology Function
open scoped ENNReal NNReal RealInnerProductSpace Gradient
namespace PettyProjection
open Spherical (Sphere norm_coe)

lemma support_gradient_of_active {n : ℕ} {C : Set (Space n)}
    (hC : IsCompact C) {x y : Space n} (hy : y ∈ C)
    (hxy : support C x = ⟪x,y⟫)
    (hd : DifferentiableAt ℝ (support C) x) : ∇ (support C) x = y := by
  let l : Space n →L[ℝ] ℝ := InnerProductSpace.toDual ℝ (Space n) y
  have he (z : Space n) : l z = ⟪z,y⟫ := by
    change ⟪y,z⟫ = ⟪z,y⟫
    exact real_inner_comm z y
  have hl : IsLocalMin (fun z => support C z-l z) x := by
    apply Eventually.of_forall
    intro z
    dsimp only
    rw [he,he,hxy,sub_self]
    exact sub_nonneg.mpr (inner_le_support hC hy z)
  have hz := hl.hasFDerivAt_eq_zero (hd.hasFDerivAt.sub l.hasFDerivAt)
  have hd' : fderiv ℝ (support C) x = l := sub_eq_zero.mp hz
  apply ext_inner_right ℝ
  intro z
  rw [inner_gradient_left,hd',he]
  exact real_inner_comm _ _

lemma wulff_gradient_of_active {n : ℕ} [NeZero n] (s : C(Sphere n,ℝ))
    (hs : ∀ u, 0 < s u) {x : Space n} {u : Sphere n}
    (hu : wulffMax s x = ⟪x,(u : Space n)⟫ / s u)
    (hd : DifferentiableAt ℝ (gauge (wulff s)) x) :
    ∇ (gauge (wulff s)) x = (s u)⁻¹ • (u : Space n) := by
  have he : gauge (wulff s) = support (wulffCoefficients s) :=
    funext (gauge_wulff_eq_max s hs)
  rw [he] at hd ⊢
  apply support_gradient_of_active (wulffCoefficients_compact s hs) (mem_range_self u) _ hd
  simpa only [real_inner_smul_right,div_eq_inv_mul,wulffMax] using hu

lemma wulff_active_unique {n : ℕ} [NeZero n] (s : C(Sphere n,ℝ))
    (hs : ∀ u, 0 < s u) {x : Space n} (hd : DifferentiableAt ℝ (gauge (wulff s)) x)
    {u v : Sphere n} (hu : wulffMax s x = ⟪x,(u : Space n)⟫/s u)
    (hv : wulffMax s x = ⟪x,(v : Space n)⟫/s v) : u = v := by
  have he := (wulff_gradient_of_active s hs hu hd).symm.trans (wulff_gradient_of_active s hs hv hd)
  have hn := congrArg norm he
  simp only [norm_smul,norm_coe,mul_one,Real.norm_eq_abs,abs_inv,abs_of_pos (hs u),
    abs_of_pos (hs v)] at hn
  have hsuv : s u = s v := inv_injective hn
  apply Subtype.ext
  rw [hsuv] at he
  exact (smul_right_injective _ (inv_ne_zero (hs v).ne')) he

end PettyProjection
end

noncomputable section
open Set Filter Topology
namespace PettyProjection

/-- Convergence of maximizers at a unique maximum, with a compact parameter
space and joint continuity only at the limiting parameter. -/
lemma selected_max_tendsto {U : Type uU} [TopologicalSpace U] [CompactSpace U]
    {f : ℝ → U → ℝ} {a : ℝ → U} {u₀ : U}
    (hc : ∀ u : U, ContinuousAt (fun p : ℝ × U => f p.1 p.2) (0,u))
    (hm : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ u, f t u ≤ f t (a t))
    (hu : ∀ u, (∀ v, f 0 v ≤ f 0 u) → u = u₀) :
    Tendsto a (𝓝 0) (𝓝 u₀) := by
  apply tendsto_nhds_of_unique_mapClusterPt
  intro u hu'
  obtain ⟨l,hl,hat⟩ := mapClusterPt_iff_ultrafilter.mp hu'
  apply hu
  intro v
  have ht : Tendsto (fun t : ℝ => t) (l : Filter ℝ) (𝓝 0) := hl
  have hv : Tendsto (fun t => f t v) (l : Filter ℝ) (𝓝 (f 0 v)) :=
    (hc v).tendsto.comp (ht.prodMk_nhds tendsto_const_nhds)
  have hav : Tendsto (fun t => f t (a t)) (l : Filter ℝ) (𝓝 (f 0 u)) :=
    (hc u).tendsto.comp (ht.prodMk_nhds hat)
  exact le_of_tendsto_of_tendsto hv hav (hl (hm.mono (fun t h => h v)))

lemma quotient_bounds {a b z t : ℝ} (ht : t ≠ 0) (hl : t*a ≤ z) (hh : z ≤ t*b) :
    min a b ≤ z/t ∧ z/t ≤ max a b := by
  have he : z/t*t = z := div_mul_cancel₀ z ht
  rcases lt_or_gt_of_ne ht with ht | ht
  · have hb : b ≤ z/t := by nlinarith
    have ha : z/t ≤ a := by nlinarith
    exact ⟨(min_le_right a b).trans hb,ha.trans (le_max_left a b)⟩
  · have ha : a ≤ z/t := by nlinarith
    have hb : z/t ≤ b := by nlinarith
    exact ⟨(min_le_left a b).trans ha,hb.trans (le_max_right a b)⟩

/-- Envelope differentiation from an exact continuous difference quotient.
The statement does not require a smooth boundary or a smooth maximizer. -/
lemma hasDerivAt_selected_max {U : Type uU} [TopologicalSpace U] [CompactSpace U]
    {f d : ℝ → U → ℝ} {q : ℝ → ℝ} {a : ℝ → U} {u₀ : U}
    (hc : ∀ u : U, ContinuousAt (fun p : ℝ × U => f p.1 p.2) (0,u))
    (hd : ContinuousAt (fun p : ℝ × U => d p.1 p.2) (0,u₀))
    (hq : ∀ᶠ t in 𝓝 (0 : ℝ), q t = f t (a t) ∧ ∀ u, f t u ≤ q t)
    (hq₀ : q 0 = f 0 u₀) (hm₀ : ∀ u, f 0 u ≤ q 0)
    (hu : ∀ u, (∀ v, f 0 v ≤ f 0 u) → u = u₀)
    (he : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ u, f t u-f 0 u = t*d t u) :
    HasDerivAt q (d 0 u₀) 0 := by
  have ha : Tendsto a (𝓝 0) (𝓝 u₀) := selected_max_tendsto hc
    (hq.mono (fun t h u => h.1 ▸ h.2 u)) hu
  have hd₀ : Tendsto (fun t => d t u₀) (𝓝 0) (𝓝 (d 0 u₀)) :=
    hd.tendsto.comp (tendsto_id.prodMk_nhds tendsto_const_nhds)
  have hda : Tendsto (fun t => d t (a t)) (𝓝 0) (𝓝 (d 0 u₀)) :=
    hd.tendsto.comp (tendsto_id.prodMk_nhds ha)
  have hlo : Tendsto (fun t => min (d t u₀) (d t (a t))) (𝓝 0) (𝓝 (d 0 u₀)) := by
    simpa only [min_self] using hd₀.min hda
  have hhi : Tendsto (fun t => max (d t u₀) (d t (a t))) (𝓝 0) (𝓝 (d 0 u₀)) := by
    simpa only [max_self] using hd₀.max hda
  rw [hasDerivAt_iff_tendsto_slope_zero]
  simp only [zero_add,smul_eq_mul,← div_eq_inv_mul]
  have hb : ∀ᶠ t in 𝓝[≠] (0 : ℝ), min (d t u₀) (d t (a t)) ≤ (q t-q 0)/t ∧
      (q t-q 0)/t ≤ max (d t u₀) (d t (a t)) := by
    filter_upwards [hq.filter_mono nhdsWithin_le_nhds,he.filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with t ht he ht0
    have htn : t ≠ 0 := ht0
    have hl : t*d t u₀ ≤ q t-q 0 := by
      rw [← he u₀,hq₀]
      exact sub_le_sub_right (ht.2 u₀) _
    have hh : q t-q 0 ≤ t*d t (a t) := by
      rw [← he (a t),ht.1]
      exact sub_le_sub_left (hm₀ (a t)) _
    exact quotient_bounds htn hl hh
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (hlo.mono_left nhdsWithin_le_nhds) (hhi.mono_left nhdsWithin_le_nhds)
    (hb.mono (fun _ h => h.1)) (hb.mono (fun _ h => h.2))

end PettyProjection
end

noncomputable section
open Set MeasureTheory Metric Filter Topology Function
open scoped ENNReal NNReal RealInnerProductSpace Gradient
namespace PettyProjection
open Spherical (Sphere norm_coe)

lemma positive_constraints_eventually {n : ℕ} [NeZero n]
    (s φ : C(Sphere n,ℝ)) (hs : ∀ u, 0 < s u) :
    ∃ m M : ℝ, 0 < m ∧ 0 < M ∧
      (∀ᶠ t in 𝓝 (0 : ℝ), ∀ u, m ≤ (s+t • φ) u ∧ (s+t • φ) u ≤ M) := by
  obtain ⟨a,b,ha,hb,hab⟩ := positive_constraint_bounds s hs
  refine ⟨a/2,b+a/2,by positivity,by positivity,?_⟩
  have ht : ∀ᶠ t in 𝓝 (0 : ℝ), |t| *(‖φ‖+1) < a/2 := by
    have h : Tendsto (fun t : ℝ => |t| *(‖φ‖+1)) (𝓝 0) (𝓝 0) := by
      simpa using (continuous_abs.tendsto (0:ℝ)).mul_const (‖φ‖+1)
    exact h.eventually (eventually_lt_nhds (by positivity))
  filter_upwards [ht] with t ht u
  have hφ : |φ u| ≤ ‖φ‖ := φ.norm_coe_le_norm u
  have hbound : |t*φ u| ≤ |t| *(‖φ‖+1) := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hφ.trans (by linarith)) (abs_nonneg _)
  have hlo := neg_abs_le (t*φ u)
  have hhi := le_abs_self (t*φ u)
  have hh := hab u
  change a/2 ≤ s u+t*φ u ∧ s u+t*φ u ≤ b+a/2
  constructor <;> linarith

lemma positive_constraints_nhds {n : ℕ} [NeZero n]
    (s φ : C(Sphere n,ℝ)) (hs : ∀ u, 0 < s u) :
    ∀ᶠ t in 𝓝 (0 : ℝ), ∀ u, 0 < (s+t • φ) u := by
  obtain ⟨m,M,hm,_,he⟩ := positive_constraints_eventually s φ hs
  exact he.mono (fun _ h u => hm.trans_le (h u).1)

lemma wulff_derivative_active {n : ℕ} [NeZero n]
    (s φ : C(Sphere n,ℝ)) (hs : ∀ u, 0 < s u) {x : Space n}
    (hd : DifferentiableAt ℝ (gauge (wulff s)) x) {u₀ : Sphere n}
    (hu₀ : wulffMax s x = ⟪x,(u₀ : Space n)⟫/s u₀) :
    HasDerivAt (fun t : ℝ => gauge (wulff ⇑(s+t • φ)) x)
      (-(gauge (wulff s) x)*φ u₀/s u₀) 0 := by
  classical
  let f : ℝ → Sphere n → ℝ := fun t u => ⟪x,(u : Space n)⟫/(s u+t*φ u)
  let d : ℝ → Sphere n → ℝ := fun t u => -(⟪x,(u : Space n)⟫*φ u)/(s u*(s u+t*φ u))
  let a : ℝ → Sphere n := fun t => if hp : ∀ u, 0 < (s+t • φ) u then
    (wulffMax_attained (s+t • φ) hp x).choose else u₀
  have hpos := positive_constraints_nhds s φ hs
  have hq : ∀ᶠ t in 𝓝 (0 : ℝ), gauge (wulff ⇑(s+t • φ)) x = f t (a t) ∧
      ∀ u, f t u ≤ gauge (wulff ⇑(s+t • φ)) x := by
    filter_upwards [hpos] with t ht
    rw [gauge_wulff_eq_max (s+t • φ) ht]
    constructor
    · dsimp only [a]
      rw [dite_eq_left ht]
      exact (wulffMax_attained (s+t • φ) ht x).choose_spec
    · intro u; exact le_wulffMax (s+t • φ) ht x u
  have hq0 : gauge (wulff (s+(0:ℝ) • φ)) x = f 0 u₀ := by
    simpa only [zero_smul,add_zero,f,zero_mul] using (gauge_wulff_eq_max s hs x).trans hu₀
  have hm0 : ∀ u, f 0 u ≤ gauge (wulff (s+(0:ℝ) • φ)) x := by
    intro u
    simpa only [zero_smul,add_zero,f,zero_mul,gauge_wulff_eq_max s hs x] using le_wulffMax s hs x u
  have hc (u : Sphere n) : ContinuousAt (fun p : ℝ × Sphere n => f p.1 p.2) (0,u) := by
    apply ContinuousAt.div
    · fun_prop
    · fun_prop
    · simpa using (hs u).ne'
  have hdc : ContinuousAt (fun p : ℝ × Sphere n => d p.1 p.2) (0,u₀) := by
    apply ContinuousAt.div
    · fun_prop
    · fun_prop
    · simpa using mul_ne_zero (hs u₀).ne' (hs u₀).ne'
  have hu : ∀ u, (∀ v, f 0 v ≤ f 0 u) → u = u₀ := by
    intro u h
    apply wulff_active_unique s hs hd _ hu₀
    apply le_antisymm
    · simpa only [f,zero_mul,add_zero,← hu₀] using h u₀
    · exact le_wulffMax s hs x u
  have he : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ u, f t u-f 0 u = t*d t u := by
    filter_upwards [hpos] with t ht u
    have hst : s u+t*φ u ≠ 0 := (ht u).ne'
    dsimp only [f,d]
    simp only [zero_mul,add_zero]
    field_simp [hst,(hs u).ne']
    ring
  have h := hasDerivAt_selected_max hc hdc hq hq0 hm0 hu he
  have he0 : d 0 u₀ = -(gauge (wulff s) x)*φ u₀/s u₀ := by
    rw [gauge_wulff_eq_max s hs x,hu₀]
    dsimp [d]
    ring
  rwa [he0] at h

/-- Wulff variation against an actual continuous positively homogeneous test.
No symmetry or boundary smoothness is assumed. -/
theorem wulff_derivative {n : ℕ} [NeZero n] (s : C(Sphere n,ℝ))
    (hs : ∀ u, 0 < s u) (φ : Space n → ℝ) (hφ : Continuous φ)
    (hh : ∀ (a : ℝ), 0 < a → ∀ x, φ (a • x) = a*φ x)
    {x : Space n} (hd : DifferentiableAt ℝ (gauge (wulff s)) x) :
    HasDerivAt (fun t : ℝ => gauge (wulff (s+t • (⟨fun u : Sphere n => φ u,
      hφ.comp continuous_subtype_val⟩ : C(Sphere n,ℝ)))) x)
      (-(gauge (wulff s) x)*φ (∇ (gauge (wulff s)) x)) 0 := by
  obtain ⟨u,hu⟩ := wulffMax_attained s hs x
  have he := wulff_gradient_of_active s hs hu hd
  have h := wulff_derivative_active s ⟨fun u : Sphere n => φ u,hφ.comp continuous_subtype_val⟩ hs hd hu
  rw [he,hh _ (inv_pos.mpr (hs u))]
  convert h using 1
  dsimp
  ring

end PettyProjection
end

noncomputable section
open Set MeasureTheory Metric Filter Topology Function
open scoped ENNReal NNReal RealInnerProductSpace
namespace PettyProjection
open Spherical (Sphere norm_coe surface sigma mean)

lemma kappa_pos (n : ℕ) : 0 < kappa n := by
  unfold kappa unitBall
  exact ENNReal.toReal_pos (measure_closedBall_pos volume 0 (by norm_num)).ne'
    (measure_closedBall_lt_top.ne)

lemma surface_real_univ (n : ℕ) [NeZero n] : (surface n).real univ = n*kappa n := by
  rw [surface,Measure.toSphere_real_apply_univ]
  simp only [finrank_euclideanSpace_fin]
  congr 1
  exact congrArg ENNReal.toReal (Measure.addHaar_closedBall_eq_addHaar_ball volume (0 : Space n) (1:ℝ)).symm

/-- Polar integration of an arbitrary convex neighborhood of zero; the body
need not be symmetric or have a smooth boundary. -/
lemma gauge_volume_lintegral {n : ℕ} [NeZero n] {K : Set (Space n)}
    (hc : Convex ℝ K) (h0 : K ∈ 𝓝 (0 : Space n))
    (hp : ∀ u : Sphere n, 0 < gauge K (u : Space n)) :
    volume K = ∫⁻ u : Sphere n, ENNReal.ofReal ((gauge K (u : Space n))⁻¹ ^ n / n)
      ∂surface n := by
  let ν := Measure.volumeIoiPow (Module.finrank ℝ (Space n)-1)
  let A : Set ({0}ᶜ : Set (Space n)) := Subtype.val ⁻¹' interior K
  let S : Set (Sphere n × Ioi (0:ℝ)) :=
    {z | z.2.1 < (gauge K (z.1 : Space n))⁻¹}
  have hA : MeasurableSet A := isOpen_interior.measurableSet.preimage measurable_subtype_coe
  have hS : MeasurableSet S := by
    apply isOpen_lt (by fun_prop) ?_ |>.measurableSet
    exact ((continuous_gauge hc h0).comp (continuous_subtype_val.comp continuous_fst)).inv₀
      (fun z => (hp z.1).ne')
  have he : (homeomorphUnitSphereProd (Space n)).symm ⁻¹' A = S := by
    ext z
    change (↑((homeomorphUnitSphereProd (Space n)).symm z) : Space n) ∈ interior K ↔ _
    rw [homeomorphUnitSphereProd_symm_apply_coe,← gauge_lt_one_iff_mem_interior hc h0,
      gauge_smul_of_nonneg (α := ℝ) z.2.property.le]
    change (z.2 : ℝ)*gauge K (z.1 : Space n) < 1 ↔ (z.2 : ℝ) < (gauge K (z.1 : Space n))⁻¹
    rw [inv_eq_one_div,lt_div_iff₀ (hp z.1)]
  have hm := ((volume : Measure (Space n)).measurePreserving_homeomorphUnitSphereProd).symm
    (homeomorphUnitSphereProd (Space n)).toMeasurableEquiv
  have hm' := hm.measure_preimage hA.nullMeasurableSet
  change (surface n).prod ν ((homeomorphUnitSphereProd (Space n)).symm ⁻¹' A) = _ at hm'
  rw [he, ((MeasurableEmbedding.subtype_coe (measurableSet_singleton (0 : Space n)).compl)).comap_apply] at hm'
  have hi : Subtype.val '' A = interior K \ {0} := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩; exact ⟨hy,y.property⟩
    · intro hx; exact ⟨⟨x,hx.2⟩,hx.1,rfl⟩
  rw [hi,measure_sdiff_null (measure_singleton _),
    measure_interior_of_null_frontier (hc.addHaar_frontier volume)] at hm'
  rw [← hm',Measure.prod_apply hS]
  apply lintegral_congr
  intro u
  have hu : Prod.mk u ⁻¹' S = Iio (⟨(gauge K (u : Space n))⁻¹,inv_pos.mpr (hp u)⟩ : Ioi (0:ℝ)) := rfl
  rw [hu,Measure.volumeIoiPow_apply_Iio]
  have hn : n-1+1 = n := Nat.sub_add_cancel (NeZero.one_le : 1 ≤ n)
  have hnR := congrArg (fun j : ℕ => (j : ℝ)) hn
  simp only [Nat.cast_add,Nat.cast_one] at hnR
  simp only [finrank_euclideanSpace_fin,hn,hnR]

lemma gauge_volume {n : ℕ} [NeZero n] {K : Set (Space n)}
    (hc : Convex ℝ K) (h0 : K ∈ 𝓝 (0 : Space n))
    (hp : ∀ u : Sphere n, 0 < gauge K (u : Space n)) :
    volume.real K = kappa n * mean (fun u : Sphere n => (gauge K (u : Space n))⁻¹ ^ n) := by
  have hcont : Continuous (fun u : Sphere n => (gauge K (u : Space n))⁻¹ ^ n) :=
    (((continuous_gauge hc h0).comp continuous_subtype_val).inv₀ (fun u => (hp u).ne')).pow n
  have hnn : ∀ u : Sphere n, 0 ≤ (gauge K (u : Space n))⁻¹ ^ n := fun u => pow_nonneg (inv_nonneg.mpr (hp u).le) n
  have hv := congrArg ENNReal.toReal (gauge_volume_lintegral hc h0 hp)
  rw [← ofReal_integral_eq_lintegral_ofReal (hcont.div_const n |>.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)) (Eventually.of_forall (fun u => div_nonneg (hnn u) (Nat.cast_nonneg n))),
    ENNReal.toReal_ofReal (integral_nonneg (fun u => div_nonneg (hnn u) (Nat.cast_nonneg n))),
    integral_div] at hv
  change volume.real K = _ at hv
  rw [hv,mean,sigma,integral_smul_measure,ENNReal.toReal_inv,smul_eq_mul]
  change _ = kappa n * (((surface n).real univ)⁻¹ * _)
  rw [surface_real_univ]
  field_simp [(kappa_pos n).ne',(Nat.cast_pos.mpr (NeZero.pos n) : (0:ℝ)<n).ne']

lemma wulff_volume {n : ℕ} [NeZero n] (s : C(Sphere n,ℝ)) (hs : ∀ u, 0 < s u) :
    volume.real (wulff s) = kappa n * mean (fun u : Sphere n => (gauge (wulff s) (u : Space n))⁻¹ ^ n) := by
  apply gauge_volume (wulff_convex s) (wulff_nhds s hs)
  intro u
  rw [gauge_wulff_eq_max s hs]
  exact wulffMax_pos s hs (by intro h; simpa [h] using norm_coe u)

end PettyProjection
end

noncomputable section
open Set MeasureTheory Metric Filter Topology Function
open scoped ENNReal NNReal RealInnerProductSpace
namespace PettyProjection
open Spherical (Sphere norm_coe)

lemma wulff_sphere_gauge_bounds {n : ℕ} [NeZero n] (s : C(Sphere n,ℝ))
    {m M : ℝ} (hm : 0 < m) (hs : ∀ u, m ≤ s u ∧ s u ≤ M)
    (u : Sphere n) : M⁻¹ ≤ gauge (wulff s) (u : Space n) ∧
      gauge (wulff s) (u : Space n) ≤ m⁻¹ := by
  have hp : ∀ v, 0 < s v := fun v => hm.trans_le (hs v).1
  rw [gauge_wulff_eq_max s hp]
  constructor
  · have h := le_wulffMax s hp (u : Space n) u
    rw [real_inner_self_eq_norm_sq,norm_coe,one_pow,one_div] at h
    exact (inv_anti₀ (hp u) (hs u).2).trans h
  · obtain ⟨v,hv⟩ := wulffMax_attained s hp (u : Space n)
    rw [hv]
    have hi : ⟪(u : Space n),(v : Space n)⟫ ≤ 1 := by
      simpa only [norm_coe,one_mul] using real_inner_le_norm (u : Space n) (v : Space n)
    calc
      _ ≤ 1 / s v := div_le_div_of_nonneg_right hi (hp v).le
      _ ≤ m⁻¹ := by simpa only [one_div] using inv_anti₀ hm (hs v).1

lemma quotient_perturb_bound {a b c t r m B : ℝ} (hm : 0 < m)
    (ht : m ≤ b+t*c) (hr : m ≤ b+r*c) (ha : |a| ≤ 1) (hc : |c| ≤ B) :
    |a/(b+t*c)-a/(b+r*c)| ≤ (B/m^2)*|t-r| := by
  have ht0 := hm.trans_le ht
  have hr0 := hm.trans_le hr
  have hB : 0 ≤ B := (abs_nonneg c).trans hc
  have he : a/(b+t*c)-a/(b+r*c) = a*c*(r-t)/((b+t*c)*(b+r*c)) := by
    rw [div_sub_div _ _ ht0.ne' hr0.ne']
    congr 1
    ring
  rw [he,abs_div,abs_mul,abs_mul,abs_mul,abs_of_pos ht0,abs_of_pos hr0,abs_sub_comm r t]
  calc
    _ ≤ (1*B)*|t-r|/(m*m) := by gcongr
    _ = _ := by ring

lemma wulff_gauge_param_sub_le {n : ℕ} [NeZero n] (s φ : C(Sphere n,ℝ))
    {m t r : ℝ} (hm : 0 < m) (ht : ∀ u, m ≤ (s+t • φ) u)
    (hr : ∀ u, m ≤ (s+r • φ) u) (u : Sphere n) :
    gauge (wulff ⇑(s+t • φ)) (u : Space n)-gauge (wulff ⇑(s+r • φ)) (u : Space n) ≤
      (‖φ‖/m^2)*|t-r| := by
  have htp : ∀ v, 0 < (s+t • φ) v := fun v => hm.trans_le (ht v)
  have hrp : ∀ v, 0 < (s+r • φ) v := fun v => hm.trans_le (hr v)
  rw [gauge_wulff_eq_max (s+t • φ) htp,gauge_wulff_eq_max (s+r • φ) hrp]
  obtain ⟨v,hv⟩ := wulffMax_attained (s+t • φ) htp (u : Space n)
  rw [hv]
  have hi : |⟪(u : Space n),(v : Space n)⟫| ≤ 1 := by
    simpa only [norm_coe,one_mul] using abs_real_inner_le_norm (u : Space n) (v : Space n)
  calc
    _ ≤ ⟪(u : Space n),(v : Space n)⟫/(s+t • φ) v - ⟪(u : Space n),(v : Space n)⟫/(s+r • φ) v :=
      sub_le_sub_left (le_wulffMax (s+r • φ) hrp _ v) _
    _ ≤ |⟪(u : Space n),(v : Space n)⟫/(s+t • φ) v - ⟪(u : Space n),(v : Space n)⟫/(s+r • φ) v| := le_abs_self _
    _ ≤ _ := quotient_perturb_bound hm (ht v) (hr v) hi (φ.norm_coe_le_norm v)

lemma wulff_gauge_param_lipschitz {n : ℕ} [NeZero n] (s φ : C(Sphere n,ℝ))
    {m : ℝ} (hm : 0 < m) {T : Set ℝ} (hT : ∀ t ∈ T, ∀ u, m ≤ (s+t • φ) u)
    (u : Sphere n) : LipschitzOnWith ⟨‖φ‖/m^2,by positivity⟩
      (fun t : ℝ => gauge (wulff ⇑(s+t • φ)) (u : Space n)) T := by
  apply LipschitzOnWith.of_dist_le_mul
  intro t ht r hr
  change |gauge (wulff ⇑(s+t • φ)) (u : Space n)-gauge (wulff ⇑(s+r • φ)) (u : Space n)| ≤ (‖φ‖/m^2)*|t-r|
  apply abs_le.mpr
  constructor
  · have h := wulff_gauge_param_sub_le s φ hm (hT r hr) (hT t ht) u
    rw [abs_sub_comm r t] at h
    linarith
  · exact wulff_gauge_param_sub_le s φ hm (hT t ht) (hT r hr) u

end PettyProjection
end

noncomputable section
open Set MeasureTheory Metric Filter Topology Function
open scoped ENNReal NNReal RealInnerProductSpace Gradient
namespace PettyProjection
open Spherical (Sphere norm_coe sigma mean)

lemma measurable_gradient {n : ℕ} (f : Space n → ℝ) : Measurable (gradient f) := by
  exact (InnerProductSpace.toDual ℝ (Space n)).symm.continuous.measurable.comp (measurable_fderiv ℝ f)

lemma wulff_invpow_param_lipschitz {n : ℕ} [NeZero n]
    (s φ : C(Sphere n,ℝ)) (hs : ∀ u,0 < s u) :
    ∃ T ∈ 𝓝 (0 : ℝ), ∃ C : ℝ≥0, ∀ u : Sphere n,
      LipschitzOnWith C (fun t : ℝ => (gauge (wulff ⇑(s+t • φ)) (u : Space n))⁻¹ ^ n) T := by
  obtain ⟨m,M,hm,hM,he⟩ := positive_constraints_eventually s φ hs
  let T : Set ℝ := {t | ∀ u, m ≤ (s+t • φ) u ∧ (s+t • φ) u ≤ M}
  have hT : T ∈ 𝓝 (0 : ℝ) := he
  have hc : ContDiffOn ℝ 1 (fun a : ℝ => a⁻¹^n) (Icc M⁻¹ m⁻¹) := by
    intro a ha
    exact ((contDiffAt_id.inv ((inv_pos.mpr hM).trans_le ha.1).ne').pow n).contDiffWithinAt
  obtain ⟨D,hD⟩ := hc.exists_lipschitzOnWith (by norm_num) (convex_Icc _ _) isCompact_Icc
  let C : ℝ≥0 := ⟨‖φ‖/m^2,by positivity⟩
  refine ⟨T,hT,D*C,?_⟩
  intro u
  apply hD.comp (wulff_gauge_param_lipschitz s φ hm (fun t ht v => (ht v).1) u)
  intro t ht
  exact wulff_sphere_gauge_bounds (s+t • φ) hm ht u

lemma wulff_invpow_derivative {n : ℕ} [NeZero n] (s : C(Sphere n,ℝ))
    (hs : ∀ u,0 < s u) (φ : Space n → ℝ) (hφ : Continuous φ)
    (hh : ∀ (a : ℝ),0 < a → ∀ x,φ (a • x)=a*φ x)
    {u : Sphere n} (hd : DifferentiableAt ℝ (gauge (wulff s)) (u : Space n)) :
    HasDerivAt (fun t : ℝ => (gauge (wulff ⇑(s+t • (⟨fun v : Sphere n => φ v,
      hφ.comp continuous_subtype_val⟩ : C(Sphere n,ℝ)))) (u : Space n))⁻¹^n)
      (n*(gauge (wulff s) (u : Space n))⁻¹^n*φ (∇ (gauge (wulff s)) (u : Space n))) 0 := by
  have hp : 0 < gauge (wulff s) (u : Space n) := by
    rw [gauge_wulff_eq_max s hs]
    exact wulffMax_pos s hs (by intro h; simpa [h] using norm_coe u)
  have h := ((wulff_derivative s hs φ hφ hh hd).inv
    (by simpa only [zero_smul,add_zero] using hp.ne')).pow n
  simp only [zero_smul,add_zero] at h
  apply h.congr_deriv
  simp only [Pi.inv_apply,zero_smul,add_zero]
  let q := gauge (wulff s) (u : Space n)
  have hn : n-1+1 = n := Nat.sub_add_cancel (NeZero.one_le : 1 ≤ n)
  have he : (q⁻¹)^(n-1)*q⁻¹ = (q⁻¹)^n := by rw [← pow_succ,hn]
  change (n:ℝ)*q⁻¹^(n-1)*(-(-q*_)/q^2) = (n:ℝ)*q⁻¹^n*_
  rw [← he]
  field_simp [show q ≠ 0 from hp.ne']

/-- Actual two-sided first variation in positive Wulff constraints. This is
valid for arbitrary continuous degree-one tests, not only support functions. -/
theorem wulff_volume_derivative {n : ℕ} [NeZero n] (s : C(Sphere n,ℝ))
    (hs : ∀ u,0 < s u) (φ : Space n → ℝ) (hφ : Continuous φ)
    (hh : ∀ (a : ℝ),0 < a → ∀ x,φ (a • x)=a*φ x) :
    HasDerivAt (fun t : ℝ => volume.real (wulff ⇑(s+t • (⟨fun u : Sphere n => φ u,
      hφ.comp continuous_subtype_val⟩ : C(Sphere n,ℝ)))))
      (n*kappa n*mean (fun u : Sphere n => (gauge (wulff s) (u : Space n))⁻¹^n*
        φ (∇ (gauge (wulff s)) (u : Space n)))) 0 := by
  let φs : C(Sphere n,ℝ) := ⟨fun u => φ u,hφ.comp continuous_subtype_val⟩
  let F : ℝ → Sphere n → ℝ := fun t u => (gauge (wulff ⇑(s+t • φs)) (u : Space n))⁻¹^n
  let F' : Sphere n → ℝ := fun u => (n:ℝ)*(gauge (wulff s) (u : Space n))⁻¹^n*
    φ (∇ (gauge (wulff s)) (u : Space n))
  have hg : Continuous (gauge (wulff s)) := continuous_gauge (wulff_convex s) (wulff_nhds s hs)
  have hgp : ∀ u : Sphere n,0 < gauge (wulff s) (u : Space n) := by
    intro u
    rw [gauge_wulff_eq_max s hs]
    exact wulffMax_pos s hs (by intro h; simpa [h] using norm_coe u)
  have hc : Continuous (F 0) := by
    change Continuous (fun u : Sphere n => (gauge (wulff ⇑(s+0 • φs)) (u : Space n))⁻¹^n)
    simp only [zero_smul,add_zero]
    exact ((hg.comp continuous_subtype_val).inv₀ (fun u => (hgp u).ne')).pow n
  obtain ⟨T,hT,C,hC⟩ := wulff_invpow_param_lipschitz s φs hs
  have hFm : ∀ᶠ t in 𝓝 (0:ℝ), AEStronglyMeasurable (F t) (sigma n) := by
    filter_upwards [positive_constraints_nhds s φs hs] with t ht
    exact (((continuous_gauge (wulff_convex _) (wulff_nhds (s+t • φs) ht)).comp
      continuous_subtype_val).measurable.inv.pow_const n).aestronglyMeasurable
  have hF'm : AEStronglyMeasurable F' (sigma n) := by
    apply Measurable.aestronglyMeasurable
    exact (measurable_const.mul ((hg.measurable.comp measurable_subtype_coe).inv.pow_const n)).mul
      (hφ.measurable.comp ((measurable_gradient _).comp measurable_subtype_coe))
  have hder : ∀ᵐ u ∂sigma n, HasDerivAt (fun t => F t u) (F' u) 0 := by
    filter_upwards [gauge_ae_differentiable_sphere (wulff_convex s) (wulff_nhds s hs)] with u hu
    exact wulff_invpow_derivative s hs φ hφ hh hu
  have hI := (hasDerivAt_integral_of_dominated_loc_of_lip hT hFm
    (hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)) hF'm
    (Eventually.of_forall (fun u => by simpa only [Real.nnabs_coe] using hC u))
    (integrable_const (C:ℝ)) hder).2
  have he : (fun t => volume.real (wulff ⇑(s+t • φs))) =ᶠ[𝓝 (0:ℝ)]
      (fun t => kappa n * ∫ u,F t u ∂sigma n) := by
    filter_upwards [positive_constraints_nhds s φs hs] with t ht
    exact wulff_volume (s+t • φs) ht
  have h := (hI.const_mul (kappa n)).congr_of_eventuallyEq he
  apply h.congr_deriv
  dsimp only [F']
  simp_rw [mul_assoc (n:ℝ)]
  rw [integral_const_mul]
  dsimp only [mean]
  ring

end PettyProjection
end

noncomputable section
open Set MeasureTheory Metric Filter Topology Function
open scoped ENNReal NNReal RealInnerProductSpace Pointwise Gradient
namespace PettyProjection
open Spherical (Sphere norm_coe sigma mean)

lemma support_smul_set {n : ℕ} {K : Set (Space n)} (hK : IsCompact K) (hKn : K.Nonempty)
    {t : ℝ} (ht : 0 ≤ t) (u : Space n) : support (t • K) u = t*support K u := by
  have hn : (t • K).Nonempty := by obtain ⟨x,hx⟩ := hKn; exact ⟨t • x,smul_mem_smul_set hx⟩
  apply le_antisymm
  · apply (support_le_iff (hK.smul t) hn).mpr
    rintro _ ⟨x,hx,rfl⟩
    rw [real_inner_smul_right]
    exact mul_le_mul_of_nonneg_left (inner_le_support hK hx u) ht
  · obtain ⟨x,hx,he⟩ := support_attained hK hKn u
    rw [he]
    simpa only [real_inner_smul_right] using
      inner_le_support (hK.smul t) (smul_mem_smul_set hx) u

lemma support_pos_of_nhds {n : ℕ} {K : Set (Space n)} (hK : IsCompact K)
    (h0 : K ∈ 𝓝 (0 : Space n)) (u : Sphere n) : 0 < support K u := by
  obtain ⟨r,hr,hrK⟩ := Metric.mem_nhds_iff.mp h0
  have hx : (r/2) • (u : Space n) ∈ K := by
    apply hrK
    rw [mem_ball,dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_pos (by positivity),norm_coe,mul_one]
    linarith
  have h := inner_le_support hK hx (u : Space n)
  rw [real_inner_smul_right,real_inner_self_eq_norm_sq,norm_coe,one_pow,mul_one] at h
  linarith

/-- First-variation identity for actual Minkowski addition; the added
set is allowed to have any dimension. -/
theorem minkowski_volume_derivative {n : ℕ} [NeZero n] {K M : Set (Space n)}
    (hK : IsCompact K) (hcK : Convex ℝ K) (h0 : K ∈ 𝓝 (0 : Space n))
    (hM : IsCompact M) (hcM : Convex ℝ M) (hMn : M.Nonempty) :
    HasDerivWithinAt (fun t : ℝ => volume.real (K+t • M))
      (n*kappa n*mean (fun u : Sphere n => (gauge K (u : Space n))⁻¹^n*
        support M (∇ (gauge K) (u : Space n)))) (Ici 0) 0 := by
  have hKn : K.Nonempty := ⟨0,mem_of_mem_nhds h0⟩
  let s : C(Sphere n,ℝ) := ⟨fun u => support K u,(support_continuous hK).comp continuous_subtype_val⟩
  have hs : ∀ u,0 < s u := support_pos_of_nhds hK h0
  let φ : C(Sphere n,ℝ) := ⟨fun u => support M u,(support_continuous hM).comp continuous_subtype_val⟩
  have he : ∀ t : ℝ, 0 ≤ t → wulff ⇑(s+t • φ) = K+t • M := by
    intro t ht
    have hf : ⇑(s+t • φ) = fun u : Sphere n => support (K+t • M) u := by
      funext u
      simp only [ContinuousMap.coe_add,ContinuousMap.coe_smul,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
      change support K u+t*support M u = support (K+t • M) u
      rw [support_minkowski hK hKn (hM.smul t)
        (by obtain ⟨x,hx⟩ := hMn; exact ⟨t • x,smul_mem_smul_set hx⟩),
        support_smul_set hM hMn ht]
    rw [hf]
    exact wulff_support (hK.add (hM.smul t)) (hcK.add (hcM.smul t)) (hKn.add (by obtain ⟨x,hx⟩ := hMn; exact ⟨t • x,smul_mem_smul_set hx⟩))
  have h := (wulff_volume_derivative s hs (support M) (support_continuous hM)
    (fun a ha x => support_smul hM hMn ha.le x)).hasDerivWithinAt (s := Ici (0:ℝ))
  have hw : wulff s = K := wulff_support hK hcK hKn
  rw [hw] at h
  exact h.congr (fun t ht => congrArg volume.real (he t ht).symm)
    (congrArg volume.real (he 0 le_rfl).symm)

end PettyProjection
end

end OAI
