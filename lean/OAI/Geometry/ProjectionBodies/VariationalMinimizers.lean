import OAI.Geometry.ProjectionBodies.RelativeGauges

namespace OAI

noncomputable section
open Set MeasureTheory Metric Filter Topology
open scoped NNReal RealInnerProductSpace
namespace PettyProjection
namespace RelativeGauge
variable {n : ℕ} [NeZero n] {V : Submodule ℝ (Space n)}

omit [NeZero n] in
lemma exists_normalized {μ : Measure (Space n)}
    (hμ : Integrable (fun x : Space n => ‖x‖) μ) (hV : V≠⊥)
    (hq : ∀ x∈V,x≠0 → 0<cosineSeminorm μ hμ x) :
    ∃ g : RelativeGauge V,supportFunctional μ g.body=1 := by
  let g := ball V
  have hp := g.functional_pos hV hμ hq
  refine ⟨g.scale _ hp,?_⟩
  rw [functional_scale g _ hp μ,inv_mul_cancel₀ hp.ne']

/-- The actual fixed-subspace variational minimizer, including singular V. -/
theorem exists_minimizer {μ : Measure (Space n)}
    (hμ : Integrable (fun x : Space n => ‖x‖) μ) (hV : V≠⊥)
    (hq : ∀ x∈V,x≠0 → 0<cosineSeminorm μ hμ x) (b : Bool) :
    ∃ g : RelativeGauge V,supportFunctional μ g.body=1 ∧
      ∀ f : RelativeGauge V,supportFunctional μ f.body=1 →
        Spherical.objective b g.toSeminorm≤Spherical.objective b f.toSeminorm := by
  let S : Set ℝ := {r | ∃ g : RelativeGauge V,supportFunctional μ g.body=1 ∧ Spherical.objective b g.toSeminorm=r}
  obtain ⟨g₀,hg₀⟩ := exists_normalized hμ hV hq
  have hS : S.Nonempty := ⟨_,g₀,hg₀,rfl⟩
  let q := (cosineSeminorm μ hμ).comp V.starProjection.toLinearMap
  have hq0 : q≠0 := by
    obtain ⟨x,hx,hx0⟩ := (Submodule.ne_bot_iff V).mp hV
    intro he
    have hp := hq x hx hx0
    have hz : q x=0 := by rw [he]; rfl
    change cosineSeminorm μ hμ (V.starProjection x)=0 at hz
    rw [V.starProjection_eq_self_iff.mpr hx] at hz
    linarith
  have hSb : BddBelow S := by
    refine ⟨Spherical.objective b q,?_⟩
    rintro _ ⟨g,hg,rfl⟩
    exact Spherical.objective_mono b hq0 (g.ne_zero hV) (g.normalized_lower hμ hg)
  obtain ⟨r,hr,ht,hm⟩ := exists_seq_tendsto_sInf hS hSb
  choose g hgn hgr using hm
  obtain ⟨f,φ,hφ,hfn,hu,hfo⟩ := normalized_subsequence hμ hV hq b g hgn
    (M := r 0) (fun i => by rw [hgr i]; exact hr (Nat.zero_le i))
  have he : Spherical.objective b f.toSeminorm=sInf S := by
    apply tendsto_nhds_unique hfo
    have hh := ht.comp hφ.tendsto_atTop
    simpa only [Function.comp_def,← hgr] using hh
  refine ⟨f,hfn,fun g hg => ?_⟩
  rw [he]
  exact csInf_le hSb ⟨g,hg,rfl⟩

end RelativeGauge
end PettyProjection
end

noncomputable section
open Set MeasureTheory Metric Filter Topology
open scoped NNReal RealInnerProductSpace Pointwise
namespace PettyProjection
namespace RelativeGauge
variable {n : ℕ} {V : Submodule ℝ (Space n)}

def midBody (g f : RelativeGauge V) : Set (Space n) := (1/2:ℝ) • (g.body+f.body)
lemma midBody_compact (g f : RelativeGauge V) : IsCompact (midBody g f) :=
  (g.compact.add f.compact).smul _
lemma midBody_convex (g f : RelativeGauge V) : Convex ℝ (midBody g f) :=
  (g.convex.add f.convex).smul _
lemma midBody_balanced (g f : RelativeGauge V) : Balanced ℝ (midBody g f) :=
  (g.balanced.add f.balanced).smul _
lemma midBody_sub (g f : RelativeGauge V) : midBody g f⊆V := by
  rintro x ⟨y,⟨a,ha,b,hb,rfl⟩,rfl⟩
  exact V.smul_mem _ (V.add_mem ha.1 hb.1)
lemma midBody_inner (g f : RelativeGauge V) :
    ∃ r : ℝ,0<r ∧ ∀ x∈V,‖x‖≤r → x∈midBody g f := by
  obtain ⟨r,hr,hin⟩ := g.inner_ball
  refine ⟨r/2,by positivity,fun x hx hh => ?_⟩
  refine ⟨(2:ℝ) • x,⟨(2:ℝ) • x,hin _ (V.smul_mem _ hx) ?_,0,f.zero_mem,by simp⟩,by simp [smul_smul]⟩
  rw [norm_smul,Real.norm_of_nonneg (by norm_num : (0:ℝ)≤2)]
  linarith

def midpoint (g f : RelativeGauge V) : RelativeGauge V :=
  ofBody (midBody_compact g f) (midBody_convex g f) (midBody_balanced g f) (midBody_inner g f)
lemma body_midpoint (g f : RelativeGauge V) : (midpoint g f).body=midBody g f :=
  body_ofBody _ _ _ (midBody_sub g f) _
lemma functional_midpoint (g f : RelativeGauge V) {μ : Measure (Space n)}
    (hμ : Integrable (fun x : Space n => ‖x‖) μ) :
    supportFunctional μ (midpoint g f).body=(supportFunctional μ g.body+supportFunctional μ f.body)/2 := by
  rw [body_midpoint,midBody,functional_smul (g.compact.add f.compact) (g.nonempty.add f.nonempty) (by norm_num : (0:ℝ)≤1/2),
    functional_add hμ g.compact g.nonempty f.compact f.nonempty]
  ring

lemma midpoint_harmonic (g f : RelativeGauge V) {x : Space n} (hx : V.starProjection x≠0) :
    midpoint g f x≤((g x)⁻¹+(f x)⁻¹)⁻¹*2 := by
  let y := V.starProjection x
  have hy : y∈V := V.starProjection_apply_mem x
  have hg : 0<g x := by simpa only [y,g.projection] using g.pos hy hx
  have hf : 0<f x := by simpa only [y,f.projection] using f.pos hy hx
  have hmem : ((g x)⁻¹/2+(f x)⁻¹/2) • y∈(midpoint g f).body := by
    rw [body_midpoint]
    refine ⟨(g x)⁻¹ • y+(f x)⁻¹ • y,⟨_,?_,_,?_,rfl⟩,?_⟩
    · simpa only [y,g.projection] using g.radial_mem hy hx
    · simpa only [y,f.projection] using f.radial_mem hy hx
    · simp only [smul_smul,← add_smul]; congr 1; ring
  have hpos : 0<(g x)⁻¹/2+(f x)⁻¹/2 := by positivity
  have hh : (midpoint g f).toSeminorm (((g x)⁻¹/2+(f x)⁻¹/2) • y)≤1 := hmem.2
  rw [map_smul_eq_mul,Real.norm_of_nonneg hpos.le,(midpoint g f).projection] at hh
  have hb := (le_div_iff₀ hpos).mpr (by simpa only [mul_comm] using hh)
  have he : 1/((g x)⁻¹/2+(f x)⁻¹/2)=((g x)⁻¹+(f x)⁻¹)⁻¹*2 := by
    rw [show (g x)⁻¹/2+(f x)⁻¹/2=((g x)⁻¹+(f x)⁻¹)/2 by ring,one_div,inv_div]
    ring
  exact hb.trans_eq he

end RelativeGauge
end PettyProjection
end

noncomputable section
open Set
namespace PettyProjection.Spherical

lemma harmonic_objective {a d c : ℝ} (ha : 0<a) (hd : 0<d) (hc : 0<c)
    (hle : c≤(a⁻¹+d⁻¹)⁻¹*2) (b : Bool) :
    objectiveIntegrand b c≤(objectiveIntegrand b a+objectiveIntegrand b d)/2 ∧
      (objectiveIntegrand b c=(objectiveIntegrand b a+objectiveIntegrand b d)/2 → a=d) := by
  have hsum : 0<a+d := add_pos ha hd
  have he : (a⁻¹+d⁻¹)⁻¹*2=2*a*d/(a+d) := by field_simp; ring
  have hmul : c*(a+d)≤2*a*d := (le_div_iff₀ hsum).mp (by rwa [← he])
  have havg : c≤(a+d)/2 := by nlinarith [sq_nonneg (a-d)]
  cases b
  · change c≤(a+d)/2 ∧ (c=(a+d)/2 → a=d)
    refine ⟨havg,fun hh => ?_⟩
    nlinarith [sq_nonneg (a-d)]
  · change Real.log c≤(Real.log a+Real.log d)/2 ∧
      (Real.log c=(Real.log a+Real.log d)/2 → a=d)
    have hmean : 0<(a⁻¹+d⁻¹)/2 := by positivity
    have he' : (a⁻¹+d⁻¹)⁻¹*2=((a⁻¹+d⁻¹)/2)⁻¹ := by field_simp
    have hlog : Real.log c≤ -Real.log ((a⁻¹+d⁻¹)/2) := by
      have hh := Real.strictMonoOn_log.monotoneOn hc (inv_pos.mpr hmean) (by rwa [← he'])
      simpa only [Real.log_inv] using hh
    have hj : (1/2:ℝ)*Real.log a⁻¹+(1/2:ℝ)*Real.log d⁻¹≤Real.log ((1/2:ℝ)*a⁻¹+(1/2:ℝ)*d⁻¹) :=
      (strictConcaveOn_log_Ioi).concaveOn.2 (inv_pos.mpr ha) (inv_pos.mpr hd) (by norm_num) (by norm_num) (by norm_num)
    simp only [Real.log_inv] at hj
    have hemean : (1/2:ℝ)*a⁻¹+(1/2:ℝ)*d⁻¹=(a⁻¹+d⁻¹)/2 := by ring
    rw [hemean] at hj
    refine ⟨by linarith,fun hh => ?_⟩
    by_contra hne
    have hi : a⁻¹≠d⁻¹ := by intro he; exact hne (inv_injective he)
    have hs : (1/2:ℝ)*Real.log a⁻¹+(1/2:ℝ)*Real.log d⁻¹<Real.log ((1/2:ℝ)*a⁻¹+(1/2:ℝ)*d⁻¹) :=
      strictConcaveOn_log_Ioi.2 (inv_pos.mpr ha) (inv_pos.mpr hd) hi (by norm_num) (by norm_num) (by norm_num)
    simp only [Real.log_inv,hemean] at hs
    linarith

end PettyProjection.Spherical
end

noncomputable section
open Set MeasureTheory Metric Filter Topology
open scoped NNReal RealInnerProductSpace
namespace PettyProjection
open Spherical (Sphere sigma objective objectiveIntegrand objective_integrable)
namespace RelativeGauge
variable {n : ℕ} [NeZero n] {V : Submodule ℝ (Space n)}

omit [NeZero n] in
@[ext] lemma ext {g f : RelativeGauge V} (h : g.toSeminorm=f.toSeminorm) : g=f := by
  cases g; cases f; cases h; rfl

lemma midpoint_objective {g f : RelativeGauge V} (hV : V≠⊥) (b : Bool) :
    objective b (midpoint g f).toSeminorm≤(objective b g.toSeminorm+objective b f.toSeminorm)/2 ∧
      (objective b (midpoint g f).toSeminorm=(objective b g.toSeminorm+objective b f.toSeminorm)/2 → g=f) := by
  let h := midpoint g f
  have hpos := Spherical.seminorm_pos_ae_sphere (g.ne_zero hV)
  have hposf := Spherical.seminorm_pos_ae_sphere (f.ne_zero hV)
  have hposh := Spherical.seminorm_pos_ae_sphere (h.ne_zero hV)
  have hmul : ∀ᵐ u : Sphere n ∂sigma n,
      objectiveIntegrand b (h u)≤(objectiveIntegrand b (g u)+objectiveIntegrand b (f u))/2 ∧
        (objectiveIntegrand b (h u)=(objectiveIntegrand b (g u)+objectiveIntegrand b (f u))/2 → g u=f u) := by
    filter_upwards [hpos,hposf,hposh] with u hu hv hw
    have hx : V.starProjection (u:Space n)≠0 := by
      intro he
      have hz := g.projection u
      rw [he,map_zero] at hz
      linarith
    exact Spherical.harmonic_objective hu hv hw (g.midpoint_harmonic f hx) b
  have hi : Integrable (fun u : Sphere n => (objectiveIntegrand b (g u)+objectiveIntegrand b (f u))/2) (sigma n) :=
    ((objective_integrable b (g.ne_zero hV)).add (objective_integrable b (f.ne_zero hV))).div_const 2
  have hh := objective_integrable b (h.ne_zero hV)
  have havg : (∫ u : Sphere n,(objectiveIntegrand b (g u)+objectiveIntegrand b (f u))/2 ∂sigma n)=
      (objective b g.toSeminorm+objective b f.toSeminorm)/2 := by
    rw [integral_div,integral_add (objective_integrable b (g.ne_zero hV)) (objective_integrable b (f.ne_zero hV))]
    rfl
  have hle := integral_mono_ae hh hi (hmul.mono (fun _ h => h.1))
  refine ⟨by simpa only [havg,objective,Spherical.mean,h] using hle,fun he => ?_⟩
  have hae := (integral_eq_iff_of_ae_le hh hi (hmul.mono (fun _ h => h.1))).mp (by
    rw [havg]; exact he)
  have hae' : (fun u : Sphere n => g u)=ᵐ[sigma n] (fun u : Sphere n => f u) := by
    filter_upwards [hae,hmul] with u hu hv
    exact hv.2 hu
  have hp := Measure.eq_of_ae_eq hae' ((Spherical.seminorm_continuous n g.toSeminorm).comp continuous_subtype_val)
    ((Spherical.seminorm_continuous n f.toSeminorm).comp continuous_subtype_val)
  apply ext
  ext x
  rw [← Spherical.radialExtension_seminorm g.toSeminorm x,← Spherical.radialExtension_seminorm f.toSeminorm x,hp]

lemma minimizer_unique {μ : Measure (Space n)}
    (hμ : Integrable (fun x : Space n => ‖x‖) μ) (hV : V≠⊥) (b : Bool)
    {g f : RelativeGauge V} (hgn : supportFunctional μ g.body=1) (hfn : supportFunctional μ f.body=1)
    (hmin : ∀ q : RelativeGauge V,supportFunctional μ q.body=1 → objective b g.toSeminorm≤objective b q.toSeminorm)
    (heq : objective b g.toSeminorm=objective b f.toSeminorm) : g=f := by
  have hn : supportFunctional μ (midpoint g f).body=1 := by
    rw [functional_midpoint g f hμ,hgn,hfn]; norm_num
  have hm := hmin (midpoint g f) hn
  obtain ⟨hle,he⟩ := midpoint_objective (g := g) (f := f) hV b
  apply he
  rw [← heq] at hle ⊢
  linarith

end RelativeGauge
end PettyProjection
end

noncomputable section
open Set MeasureTheory Metric Filter Topology Function
open scoped ENNReal NNReal RealInnerProductSpace Gradient
namespace PettyProjection
open Spherical (Sphere norm_coe sigma mean objectiveIntegrand)

lemma objective_param_lipschitz {n : ℕ} [NeZero n] (b : Bool)
    (s φ : C(Sphere n,ℝ)) (hs : ∀ u,0 < s u) :
    ∃ T ∈ 𝓝 (0 : ℝ), ∃ C : ℝ≥0, ∀ u : Sphere n,
      LipschitzOnWith C (fun t : ℝ => objectiveIntegrand b (gauge (wulff ⇑(s+t • φ)) (u : Space n))) T := by
  obtain ⟨m,M,hm,hM,he⟩ := positive_constraints_eventually s φ hs
  let T : Set ℝ := {t | ∀ u, m ≤ (s+t • φ) u ∧ (s+t • φ) u ≤ M}
  have hT : T ∈ 𝓝 (0 : ℝ) := he
  have hc : ContDiffOn ℝ 1 (objectiveIntegrand b) (Icc M⁻¹ m⁻¹) := by
    cases b
    · exact contDiff_id.contDiffOn
    · intro a ha
      exact (Real.contDiffAt_log.mpr ((inv_pos.mpr hM).trans_le ha.1).ne').contDiffWithinAt
  obtain ⟨D,hD⟩ := hc.exists_lipschitzOnWith (by norm_num) (convex_Icc _ _) isCompact_Icc
  let C : ℝ≥0 := ⟨‖φ‖/m^2,by positivity⟩
  refine ⟨T,hT,D*C,fun u => ?_⟩
  apply hD.comp (wulff_gauge_param_lipschitz s φ hm (fun t ht v => (ht v).1) u)
  exact fun t ht => wulff_sphere_gauge_bounds (s+t • φ) hm ht u

lemma objectiveIntegrand_continuousOn (b : Bool) : ContinuousOn (objectiveIntegrand b) (Ioi 0) := by
  cases b
  · exact continuous_id.continuousOn
  · exact Real.continuousOn_log.mono (fun _ h => ne_of_gt h)

lemma objective_gauge_derivative {n : ℕ} [NeZero n] (b : Bool) (s : C(Sphere n,ℝ))
    (hs : ∀ u,0 < s u) (φ : Space n → ℝ) (hφ : Continuous φ)
    (hh : ∀ (a : ℝ),0 < a → ∀ x,φ (a • x)=a*φ x)
    {u : Sphere n} (hd : DifferentiableAt ℝ (gauge (wulff s)) (u : Space n)) :
    HasDerivAt (fun t : ℝ => objectiveIntegrand b (gauge (wulff ⇑(s+t • (⟨fun v : Sphere n => φ v,
      hφ.comp continuous_subtype_val⟩ : C(Sphere n,ℝ)))) (u : Space n)))
      (- (if b then 1 else gauge (wulff s) (u:Space n))*φ (∇ (gauge (wulff s)) (u : Space n))) 0 := by
  have hp := gauge_pos_sphere (wulff_compact s hs) (wulff_convex _) (wulff_nhds s hs) u
  have hder := wulff_derivative s hs φ hφ hh hd
  cases b
  · exact hder
  · have hdlog := hder.log (by simpa only [zero_smul,add_zero] using hp.ne')
    apply hdlog.congr_deriv
    simp only [zero_smul,add_zero]
    change -gauge (wulff s) (u:Space n)*φ _/gauge (wulff s) (u:Space n)= -1*φ _
    field_simp

/-- Two-sided first variation of both variational objectives, with no smoothness
assumption on the optimizer. -/
theorem wulff_objective_derivative {n : ℕ} [NeZero n] (b : Bool) (s : C(Sphere n,ℝ))
    (hs : ∀ u,0 < s u) (φ : Space n → ℝ) (hφ : Continuous φ)
    (hh : ∀ (a : ℝ),0 < a → ∀ x,φ (a • x)=a*φ x) :
    HasDerivAt (fun t : ℝ => mean (fun u : Sphere n => objectiveIntegrand b
      (gauge (wulff ⇑(s+t • (⟨fun v : Sphere n => φ v,
        hφ.comp continuous_subtype_val⟩ : C(Sphere n,ℝ)))) (u:Space n))))
      (-mean (fun u : Sphere n => (if b then 1 else gauge (wulff s) (u:Space n))*
        φ (∇ (gauge (wulff s)) (u:Space n)))) 0 := by
  let φs : C(Sphere n,ℝ) := ⟨fun u => φ u,hφ.comp continuous_subtype_val⟩
  let F : ℝ → Sphere n → ℝ := fun t u => objectiveIntegrand b (gauge (wulff ⇑(s+t • φs)) (u:Space n))
  let F' : Sphere n → ℝ := fun u => -(if b then 1 else gauge (wulff s) (u:Space n))*φ (∇ (gauge (wulff s)) (u:Space n))
  have hg := continuous_gauge (wulff_convex s) (wulff_nhds s hs)
  have hp := gauge_pos_sphere (wulff_compact s hs) (wulff_convex _) (wulff_nhds s hs)
  have hc : Continuous (F 0) := by
    simp only [F,zero_smul,add_zero]
    exact (objectiveIntegrand_continuousOn b).comp_continuous (hg.comp continuous_subtype_val) hp
  obtain ⟨T,hT,C,hC⟩ := objective_param_lipschitz b s φs hs
  have hFm : ∀ᶠ t in 𝓝 (0:ℝ), AEStronglyMeasurable (F t) (sigma n) := by
    filter_upwards [positive_constraints_nhds s φs hs] with t ht
    have hgt := continuous_gauge (wulff_convex (s+t • φs)) (wulff_nhds (s+t • φs) ht)
    have hpt := gauge_pos_sphere (wulff_compact (s+t • φs) ht) (wulff_convex _) (wulff_nhds (s+t • φs) ht)
    exact ((objectiveIntegrand_continuousOn b).comp_continuous (hgt.comp continuous_subtype_val) hpt).aestronglyMeasurable
  have hF'm : AEStronglyMeasurable F' (sigma n) := by
    apply Measurable.aestronglyMeasurable
    apply Measurable.mul
    · cases b <;> simp only [Bool.false_eq_true,ite_false,ite_true]
      · exact (hg.measurable.comp measurable_subtype_coe).neg
      · exact measurable_const
    · exact hφ.measurable.comp ((measurable_gradient _).comp measurable_subtype_coe)
  have hder : ∀ᵐ u ∂sigma n, HasDerivAt (fun t => F t u) (F' u) 0 := by
    filter_upwards [gauge_ae_differentiable_sphere (wulff_convex s) (wulff_nhds s hs)] with u hu
    exact objective_gauge_derivative b s hs φ hφ hh hu
  have hI := (hasDerivAt_integral_of_dominated_loc_of_lip hT hFm
    (Spherical.continuous_integrable hc) hF'm
    (Eventually.of_forall (fun u => by simpa only [Real.nnabs_coe] using hC u))
    (integrable_const (C:ℝ)) hder).2
  apply hI.congr_deriv
  dsimp only [F',mean]
  simp only [neg_mul,integral_neg]

end PettyProjection
end

noncomputable section
open Set MeasureTheory Metric Filter Topology
open scoped NNReal RealInnerProductSpace Pointwise
namespace PettyProjection
open Spherical (Sphere)

lemma support_even {n : ℕ} {K : Set (Space n)} (hK : IsCompact K)
    (hne : K.Nonempty) (hsym : ∀ x∈K,-x∈K) (u : Space n) : support K (-u)=support K u := by
  apply le_antisymm
  · apply (support_le_iff hK hne).mpr
    intro x hx
    have hh := inner_le_support hK (hsym x hx) u
    simpa only [inner_neg_left,inner_neg_right] using hh
  · apply (support_le_iff hK hne).mpr
    intro x hx
    have hh := inner_le_support hK (hsym x hx) (-u)
    simpa only [inner_neg_left,inner_neg_right,neg_neg] using hh

lemma wulff_balanced {n : ℕ} (s : Sphere n → ℝ)
    (hs : ∀ u : Sphere n,s ⟨-(u:Space n),by simp⟩=s u) : Balanced ℝ (wulff s) := by
  apply (balanced_iff_neg_mem (wulff_convex s)).mpr
  intro x hx u
  have hh := hx ⟨-(u:Space n),by simp⟩
  change ⟪(u:Space n),-x⟫≤ s u
  simpa only [inner_neg_left,inner_neg_right,hs] using hh

namespace RelativeGauge
variable {n : ℕ}

lemma top_body (g : RelativeGauge (⊤ : Submodule ℝ (Space n))) : g.body=seminormUnit g.toSeminorm := by
  ext x; simp [body]
lemma top_nhds (g : RelativeGauge (⊤ : Submodule ℝ (Space n))) : g.body∈𝓝 (0:Space n) := by
  rw [g.top_body]; exact seminormUnit_nhds _
lemma top_gauge (g : RelativeGauge (⊤ : Submodule ℝ (Space n))) (x : Space n) : gauge g.body x=g x := by
  rw [g.top_body]; exact gauge_seminormUnit _ _
lemma full_inner {K : Set (Space n)} (h0 : K∈𝓝 (0:Space n)) :
    ∃ r : ℝ,0<r ∧ ∀ x∈(⊤ : Submodule ℝ (Space n)),‖x‖≤r → x∈K := by
  obtain ⟨r,hr,hin⟩ := Metric.mem_nhds_iff.mp h0
  refine ⟨r/2,by positivity,fun x _ hx => hin ?_⟩
  rw [mem_ball,dist_zero_right]; linarith

def ofFullBody {K : Set (Space n)} (hK : IsCompact K) (hc : Convex ℝ K)
    (hb : Balanced ℝ K) (h0 : K∈𝓝 (0:Space n)) : RelativeGauge (⊤ : Submodule ℝ (Space n)) :=
  ofBody hK hc hb (full_inner h0)
lemma body_ofFullBody {K : Set (Space n)} (hK : IsCompact K) (hc : Convex ℝ K)
    (hb : Balanced ℝ K) (h0 : K∈𝓝 (0:Space n)) : (ofFullBody hK hc hb h0).body=K :=
  body_ofBody _ _ _ (fun _ _ => Submodule.mem_top) _
lemma ofFullBody_apply {K : Set (Space n)} (hK : IsCompact K) (hc : Convex ℝ K)
    (hb : Balanced ℝ K) (h0 : K∈𝓝 (0:Space n)) (x : Space n) : ofFullBody hK hc hb h0 x=gauge K x := by
  rw [← top_gauge,body_ofFullBody]

end RelativeGauge

lemma homogeneous_integrable {n : ℕ} [NeZero n] {μ : Measure (Space n)}
    (hμ : Integrable (fun x : Space n => ‖x‖) μ) {φ : Space n → ℝ} (hφ : Continuous φ)
    (hh : ∀ a : ℝ,0<a → ∀ x,φ (a • x)=a*φ x) : Integrable φ μ := by
  let φs : C(Sphere n,ℝ) := ⟨fun u => φ u,hφ.comp continuous_subtype_val⟩
  have hzero : φ 0=0 := by
    have hz := hh 2 (by norm_num) 0
    simp only [smul_zero] at hz
    linarith
  apply (hμ.const_mul ‖φs‖).mono' hφ.aestronglyMeasurable
  apply Eventually.of_forall
  intro x
  by_cases hx : x=0
  · simp [hx,hzero]
  have hp := norm_pos_iff.mpr hx
  let u : Sphere n := ⟨‖x‖⁻¹ • x,by simp [norm_smul,hx]⟩
  have he : x=‖x‖ • (u:Space n) := by simp [u,smul_smul,hx]
  rw [he,hh _ hp,norm_mul,Real.norm_of_nonneg hp.le]
  have hbound := φs.norm_coe_le_norm u
  change |φ (u:Space n)|≤‖φs‖ at hbound
  have heq : ‖‖x‖ • (u:Space n)‖=‖x‖ := by simp [norm_smul]
  rw [heq]
  simpa only [Real.norm_eq_abs,mul_comm] using mul_le_mul_of_nonneg_left hbound hp.le

end PettyProjection
end

noncomputable section
open Set MeasureTheory Metric Filter Topology
open scoped NNReal RealInnerProductSpace Pointwise
namespace PettyProjection
open Spherical (Sphere norm_coe seminorm_continuous)

/-- Hahn--Banach attainment for the actual Wulff body of a seminorm. -/
lemma seminorm_supporting_vector {n : ℕ} (q : Seminorm ℝ (Space n)) (u : Sphere n) :
    ∃ z : Space n,(∀ x : Space n,|⟪x,z⟫|≤q x) ∧ ⟪(u:Space n),z⟫=q u := by
  let V := Submodule.span ℝ {(u:Space n)}
  let f : Module.Dual ℝ V := q u • ((innerSL ℝ (u:Space n)).toLinearMap.comp V.subtype)
  have hf (x : V) : |f x|≤q (x:Space n) := by
    obtain ⟨a,ha⟩ := Submodule.mem_span_singleton.mp x.property
    change |q u*⟪(u:Space n),(x:Space n)⟫|≤q (x:Space n)
    rw [← ha,inner_smul_right,real_inner_self_eq_norm_sq,norm_coe,map_smul_eq_mul]
    simp only [one_pow,mul_one,Real.norm_eq_abs,abs_mul,abs_of_nonneg (apply_nonneg q _)]
    rw [mul_comm]
  obtain ⟨φ,hφ,hb⟩ := Module.Dual.exists_continuous_extension_of_le_seminorm_real
    V f (seminorm_continuous n q) (fun x => (le_abs_self _).trans (hf x))
  let z := (InnerProductSpace.toDual ℝ (Space n)).symm φ
  have hz (x : Space n) : ⟪x,z⟫=φ x := by
    rw [real_inner_comm]
    exact InnerProductSpace.toDual_symm_apply
  refine ⟨z,fun x => by rw [hz];exact hb x,?_⟩
  rw [hz]
  have h := hφ ⟨(u:Space n),Submodule.mem_span_singleton_self (u:Space n)⟩
  simpa [f,real_inner_self_eq_norm_sq,norm_coe] using h

lemma support_wulff_seminorm_unit {n : ℕ} [NeZero n] (q : Seminorm ℝ (Space n))
    (hq : ∀ u : Sphere n,0<q u) (u : Sphere n) :
    support (wulff (fun v : Sphere n => q v)) u=q u := by
  let s : C(Sphere n,ℝ) := ⟨fun u => q u,(seminorm_continuous n q).comp continuous_subtype_val⟩
  have hc := wulff_compact s hq
  have hn : (wulff s).Nonempty := ⟨0,mem_of_mem_nhds (wulff_nhds s hq)⟩
  apply le_antisymm
  · exact (support_le_iff hc hn).mpr (fun x hx => hx u)
  · obtain ⟨z,hz,he⟩ := seminorm_supporting_vector q u
    have hmem : z∈wulff s := fun v => (le_abs_self _).trans (hz v)
    rw [← he]
    exact inner_le_support hc hmem u

lemma support_wulff_seminorm {n : ℕ} [NeZero n] (q : Seminorm ℝ (Space n))
    (hq : ∀ u : Sphere n,0<q u) (x : Space n) :
    support (wulff (fun v : Sphere n => q v)) x=q x := by
  let s : C(Sphere n,ℝ) := ⟨fun u => q u,(seminorm_continuous n q).comp continuous_subtype_val⟩
  have hc := wulff_compact s hq
  have hn : (wulff s).Nonempty := ⟨0,mem_of_mem_nhds (wulff_nhds s hq)⟩
  change IsCompact (wulff (fun v : Sphere n => q v)) at hc
  change (wulff (fun v : Sphere n => q v)).Nonempty at hn
  by_cases hx : x=0
  · subst x
    obtain ⟨z,_,he⟩ := support_attained hc hn 0
    simpa only [inner_zero_left,map_zero] using he
  · let u : Sphere n := ⟨‖x‖⁻¹ • x,by simp [norm_smul,hx]⟩
    have hxu : x=‖x‖ • (u:Space n) := by simp [u,smul_smul,norm_ne_zero_iff.mpr hx]
    rw [hxu,support_smul hc hn (norm_nonneg _),support_wulff_seminorm_unit q hq]
    simpa only [Real.norm_of_nonneg (norm_nonneg x)] using (map_smul_eq_mul q ‖x‖ (u:Space n)).symm

end PettyProjection
end

noncomputable section
open Set MeasureTheory Metric Filter Topology
open scoped NNReal RealInnerProductSpace
namespace PettyProjection
open Spherical (Sphere)

lemma homogeneous_zero {n : ℕ} {φ : Space n → ℝ}
    (hh : ∀ a : ℝ,0<a → ∀ x,φ (a • x)=a*φ x) : φ 0=0 := by
  have hh := hh 2 (by norm_num) 0
  simp only [smul_zero] at hh
  linarith

lemma support_wulff_bound {n : ℕ} [NeZero n] {K : Set (Space n)}
    (hK : IsCompact K) (hne : K.Nonempty) (φ : Space n → ℝ) (hφ : Continuous φ)
    (hh : ∀ a : ℝ,0<a → ∀ x,φ (a • x)=a*φ x) (t : ℝ)
    (hp : ∀ u : Sphere n,0 < support K u+t*φ u) (x : Space n) :
    support (wulff (fun u : Sphere n => support K u+t*φ u)) x≤ support K x+t*φ x := by
  let s : C(Sphere n,ℝ) := ⟨fun u => support K u+t*φ u,((support_continuous hK).comp continuous_subtype_val).add (continuous_const.mul (hφ.comp continuous_subtype_val))⟩
  have hW := wulff_compact s hp
  have hWn : (wulff s).Nonempty := ⟨0,mem_of_mem_nhds (wulff_nhds s hp)⟩
  apply (support_le_iff hW hWn).mpr
  intro y hy
  by_cases hx : x=0
  · subst x
    rw [homogeneous_zero hh,inner_zero_left]
    have hz : support K 0=0 := by
      obtain ⟨z,hz,he⟩ := support_attained hK hne 0
      simpa only [inner_zero_left] using he
    simp only [hz,mul_zero,add_zero,le_refl]
  have hxpos := norm_pos_iff.mpr hx
  let u : Sphere n := ⟨‖x‖⁻¹ • x,by simp [norm_smul,hx]⟩
  have hu := hy u
  have he : x=‖x‖ • (u:Space n) := by simp [u,smul_smul,hx]
  calc
    ⟪x,y⟫ = ‖x‖*⟪(u:Space n),y⟫ := by
      conv_lhs => rw [he,inner_smul_left]
      rfl
    _ ≤ ‖x‖*(support K u+t*φ u) := mul_le_mul_of_nonneg_left hu hxpos.le
    _ = support K x+t*φ x := by
      conv_rhs => rw [he,support_smul hK hne hxpos.le,hh _ hxpos]
      ring

lemma functional_wulff_bound {n : ℕ} [NeZero n] {μ : Measure (Space n)}
    (hμ : Integrable (fun x : Space n => ‖x‖) μ) {K : Set (Space n)}
    (hK : IsCompact K) (hne : K.Nonempty) (φ : Space n → ℝ) (hφ : Continuous φ)
    (hh : ∀ a : ℝ,0<a → ∀ x,φ (a • x)=a*φ x) (t : ℝ)
    (hp : ∀ u : Sphere n,0 < support K u+t*φ u) :
    supportFunctional μ (wulff (fun u : Sphere n => support K u+t*φ u))≤
      supportFunctional μ K+t*(∫ x,φ x ∂μ) := by
  let s : C(Sphere n,ℝ) := ⟨fun u => support K u+t*φ u,((support_continuous hK).comp continuous_subtype_val).add (continuous_const.mul (hφ.comp continuous_subtype_val))⟩
  have hi := support_integrable hμ (wulff_compact s hp) ⟨0,mem_of_mem_nhds (wulff_nhds s hp)⟩
  have hφi := homogeneous_integrable hμ hφ hh
  have hh := integral_mono hi ((support_integrable hμ hK hne).add (hφi.const_mul t))
    (support_wulff_bound hK hne φ hφ hh t hp)
  simp only [Pi.add_apply] at hh
  rwa [integral_add (support_integrable hμ hK hne) (hφi.const_mul t),integral_const_mul] at hh

namespace RelativeGauge
variable {n : ℕ} [NeZero n] {V : Submodule ℝ (Space n)}
lemma minimizer_scaled_lower {μ : Measure (Space n)}
    (hμ : Integrable (fun x : Space n => ‖x‖) μ) (hV : V≠⊥)
    (hq : ∀ x∈V,x≠0 → 0<cosineSeminorm μ hμ x) (b : Bool)
    {g : RelativeGauge V}
    (hmin : ∀ q : RelativeGauge V,supportFunctional μ q.body=1 →
      Spherical.objective b g.toSeminorm≤Spherical.objective b q.toSeminorm)
    (f : RelativeGauge V) {a : ℝ} (ha : 0<a) (hle : supportFunctional μ f.body≤a) :
    Spherical.objective b g.toSeminorm≤Spherical.objective b (f.scale a ha).toSeminorm := by
  have hp := f.functional_pos hV hμ hq
  have hn : supportFunctional μ (f.scale _ hp).body=1 := by
    rw [f.functional_scale _ hp μ,inv_mul_cancel₀ hp.ne']
  apply (hmin _ hn).trans
  apply Spherical.objective_mono b ((f.scale _ hp).ne_zero hV) ((f.scale _ ha).ne_zero hV)
  intro x
  exact mul_le_mul_of_nonneg_right hle (apply_nonneg f.toSeminorm x)

end RelativeGauge
end PettyProjection
end

end OAI
