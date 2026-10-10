import OAI.Geometry.ProjectionBodies.SeminormBounds

namespace OAI

noncomputable section
open Set Metric Filter Topology
open scoped NNReal RealInnerProductSpace Pointwise
namespace PettyProjection
open Spherical (Sphere seminorm_continuous)

/-- A genuine extended gauge of a relative symmetric convex body. The lower
bound is only on its supporting subspace, so cylinders are retained. -/
structure RelativeGauge {n : ℕ} (V : Submodule ℝ (Space n)) where
  toSeminorm : Seminorm ℝ (Space n)
  projection : ∀ x,toSeminorm (V.starProjection x)=toSeminorm x
  lower : ∃ c : ℝ,0<c ∧ ∀ x,c*‖V.starProjection x‖≤toSeminorm x

instance {n : ℕ} {V : Submodule ℝ (Space n)} : CoeFun (RelativeGauge V) (fun _ => Space n → ℝ) :=
  ⟨fun g => g.toSeminorm⟩

namespace RelativeGauge
variable {n : ℕ} {V : Submodule ℝ (Space n)}

def body (g : RelativeGauge V) : Set (Space n) := (V : Set (Space n)) ∩ seminormUnit g.toSeminorm

lemma zero_mem (g : RelativeGauge V) : 0∈g.body := ⟨V.zero_mem,seminormUnit_zero _⟩
lemma nonempty (g : RelativeGauge V) : g.body.Nonempty := ⟨0,g.zero_mem⟩
lemma convex (g : RelativeGauge V) : Convex ℝ g.body := V.convex.inter (seminormUnit_convex _)
lemma closed (g : RelativeGauge V) : IsClosed g.body := V.closed_of_finiteDimensional.inter (seminormUnit_closed _)
lemma neg_mem (g : RelativeGauge V) {x : Space n} (hx : x∈g.body) : -x∈g.body := by
  exact ⟨V.neg_mem hx.1,by
    change g.toSeminorm (-x)≤1
    rw [map_neg_eq_map]
    exact hx.2⟩

lemma compact (g : RelativeGauge V) : IsCompact g.body := by
  obtain ⟨c,hc,hbound⟩ := g.lower
  apply (isCompact_closedBall (0:Space n) c⁻¹).of_isClosed_subset g.closed
  intro x hx
  rw [mem_closedBall,dist_zero_right,inv_eq_one_div,le_div_iff₀ hc]
  have hb := hbound x
  rw [V.starProjection_eq_self_iff.mpr hx.1] at hb
  have hh : g x≤1 := hx.2
  nlinarith

lemma ne_zero (g : RelativeGauge V) (hV : V≠⊥) : g.toSeminorm≠0 := by
  obtain ⟨x,hx,hx0⟩ := (Submodule.ne_bot_iff V).mp hV
  obtain ⟨c,hc,hb⟩ := g.lower
  intro h
  have hh := hb x
  rw [V.starProjection_eq_self_iff.mpr hx,h] at hh
  have : 0<c*‖x‖ := mul_pos hc (norm_pos_iff.mpr hx0)
  exact this.not_ge hh

lemma pos (g : RelativeGauge V) {x : Space n} (hx : x∈V) (hx0 : x≠0) : 0<g x := by
  obtain ⟨c,hc,hb⟩ := g.lower
  have hh := hb x
  rw [V.starProjection_eq_self_iff.mpr hx] at hh
  exact (mul_pos hc (norm_pos_iff.mpr hx0)).trans_le hh

lemma radial_mem (g : RelativeGauge V) {x : Space n} (hx : x∈V) (hx0 : x≠0) :
    (g x)⁻¹ • x∈g.body := by
  refine ⟨V.smul_mem _ hx,?_⟩
  change g.toSeminorm ((g x)⁻¹ • x)≤1
  rw [map_smul_eq_mul,Real.norm_of_nonneg (inv_nonneg.mpr (apply_nonneg _ _)),
    inv_mul_cancel₀ (g.pos hx hx0).ne']

lemma inner_le_gauge_support (g : RelativeGauge V) (u x : Space n) :
    ⟪u,V.starProjection x⟫≤g x*support g.body u := by
  by_cases hx : V.starProjection x=0
  · rw [hx,inner_zero_right]
    exact mul_nonneg (apply_nonneg _ _) (support_nonneg g.compact g.zero_mem u)
  have hp := g.pos (V.starProjection_apply_mem x) hx
  have hh := inner_le_support g.compact (g.radial_mem (V.starProjection_apply_mem x) hx) u
  rw [inner_smul_right,inv_mul_le_iff₀ hp,g.projection] at hh
  simpa only [mul_comm] using hh

lemma cosine_le_gauge_functional (g : RelativeGauge V) {μ : MeasureTheory.Measure (Space n)}
    (hμ : MeasureTheory.Integrable (fun x : Space n => ‖x‖) μ) (x : Space n) :
    cosineSeminorm μ hμ (V.starProjection x)≤g x*supportFunctional μ g.body := by
  by_cases hx : V.starProjection x=0
  · rw [hx,map_zero]
    exact mul_nonneg (apply_nonneg _ _) (functional_nonneg g.compact g.zero_mem)
  have hp := g.pos (V.starProjection_apply_mem x) hx
  have hh := cosine_le_functional hμ g.compact (fun y hy => g.neg_mem hy)
    (g.radial_mem (V.starProjection_apply_mem x) hx)
  rw [map_smul_eq_mul,Real.norm_of_nonneg (inv_nonneg.mpr hp.le),inv_mul_le_iff₀ hp,
    g.projection] at hh
  simpa only [mul_comm] using hh

/-- Every positive dilation is again the exact relative gauge. -/
def scale (g : RelativeGauge V) (a : ℝ) (ha : 0<a) : RelativeGauge V where
  toSeminorm := Seminorm.of (fun x => a*g x)
    (fun x y => by simpa only [mul_add] using mul_le_mul_of_nonneg_left (map_add_le_add g.toSeminorm x y) ha.le)
    (fun r x => by rw [map_smul_eq_mul]; ring)
  projection x := by change a*g (V.starProjection x)=a*g x; rw [g.projection]
  lower := by
    obtain ⟨c,hc,hb⟩ := g.lower
    refine ⟨a*c,mul_pos ha hc,fun x => ?_⟩
    change a*c*‖V.starProjection x‖≤a*g x
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hb x) ha.le

lemma scale_apply (g : RelativeGauge V) (a : ℝ) (ha : 0<a) (x : Space n) :
    g.scale a ha x=a*g x := rfl

lemma body_scale (g : RelativeGauge V) (a : ℝ) (ha : 0<a) :
    (g.scale a ha).body=a⁻¹ • g.body := by
  ext x
  constructor
  · rintro ⟨hx,hg⟩
    refine ⟨a • x,⟨V.smul_mem a hx,?_⟩,inv_smul_smul₀ ha.ne' x⟩
    change g.toSeminorm (a • x)≤1
    rw [map_smul_eq_mul,Real.norm_of_nonneg ha.le]
    exact hg
  · rintro ⟨y,hy,rfl⟩
    refine ⟨V.smul_mem _ hy.1,?_⟩
    change a*g.toSeminorm (a⁻¹ • y)≤1
    rw [map_smul_eq_mul,Real.norm_of_nonneg (inv_nonneg.mpr ha.le),← mul_assoc,
      mul_inv_cancel₀ ha.ne',one_mul]
    exact hy.2

lemma functional_scale (g : RelativeGauge V) (a : ℝ) (ha : 0<a)
    (μ : MeasureTheory.Measure (Space n)) :
    supportFunctional μ (g.scale a ha).body=a⁻¹*supportFunctional μ g.body := by
  rw [g.body_scale a ha,functional_smul g.compact g.nonempty (inv_nonneg.mpr ha.le)]

end RelativeGauge
end PettyProjection
end

noncomputable section
open Set MeasureTheory Metric Filter Topology
open scoped NNReal RealInnerProductSpace
namespace PettyProjection.Spherical

/-- Variational objective: the logarithmic endpoint (k=1), or the linear (k=2). -/
def objectiveIntegrand (logarithmic : Bool) (t : ℝ) : ℝ :=
  if logarithmic then Real.log t else t

def objective {n : ℕ} (logarithmic : Bool) (g : Seminorm ℝ (Space n)) : ℝ :=
  mean (fun u : Sphere n => objectiveIntegrand logarithmic (g u))

lemma seminorm_integrable {n : ℕ} [NeZero n] (g : Seminorm ℝ (Space n)) :
    Integrable (fun u : Sphere n => g u) (sigma n) :=
  continuous_integrable ((seminorm_continuous n g).comp continuous_subtype_val)

lemma objective_integrable {n : ℕ} [NeZero n] (b : Bool) {g : Seminorm ℝ (Space n)} (hg : g≠0) :
    Integrable (fun u : Sphere n => objectiveIntegrand b (g u)) (sigma n) := by
  cases b
  · exact seminorm_integrable g
  · exact seminorm_log_integrable hg

lemma objectiveIntegrand_strictMono (b : Bool) : StrictMonoOn (objectiveIntegrand b) (Ioi 0) := by
  cases b
  · exact fun _ _ _ _ h => h
  · exact Real.strictMonoOn_log

lemma objective_mono {n : ℕ} [NeZero n] (b : Bool) {g f : Seminorm ℝ (Space n)}
    (hg : g≠0) (hf : f≠0) (hle : ∀ x,g x≤f x) : objective b g≤objective b f := by
  apply integral_mono_ae (objective_integrable b hg) (objective_integrable b hf)
  filter_upwards [seminorm_pos_ae_sphere hg,seminorm_pos_ae_sphere hf] with u hu hv
  exact (objectiveIntegrand_strictMono b).monotoneOn hu hv (hle u)

lemma objective_mono_eq {n : ℕ} [NeZero n] (b : Bool) {g f : Seminorm ℝ (Space n)}
    (hg : g≠0) (hf : f≠0) (hle : ∀ x,g x≤f x) (heq : objective b g=objective b f) : g=f := by
  have hnn : 0≤ᵐ[sigma n] (fun u : Sphere n => objectiveIntegrand b (f u)-objectiveIntegrand b (g u)) := by
    filter_upwards [seminorm_pos_ae_sphere hg,seminorm_pos_ae_sphere hf] with u hu hv
    exact sub_nonneg.mpr ((objectiveIntegrand_strictMono b).monotoneOn hu hv (hle u))
  have hi := (objective_integrable b hf).sub (objective_integrable b hg)
  have hz : (∫ u : Sphere n,objectiveIntegrand b (f u)-objectiveIntegrand b (g u) ∂sigma n)=0 := by
    rw [integral_sub (objective_integrable b hf) (objective_integrable b hg)]
    exact sub_eq_zero.mpr heq.symm
  have hae := (integral_eq_zero_iff_of_nonneg_ae hnn hi).mp hz
  have he : (fun u : Sphere n => f u)=ᵐ[sigma n] (fun u : Sphere n => g u) := by
    filter_upwards [hae,seminorm_pos_ae_sphere hg,seminorm_pos_ae_sphere hf] with u hu hgu hfu
    exact (objectiveIntegrand_strictMono b).injOn hfu hgu (sub_eq_zero.mp hu)
  have hpoint := Measure.eq_of_ae_eq he ((seminorm_continuous n f).comp continuous_subtype_val)
    ((seminorm_continuous n g).comp continuous_subtype_val)
  ext x
  rw [← radialExtension_seminorm g x,← radialExtension_seminorm f x,hpoint]

lemma objective_scale {n : ℕ} [NeZero n] (b : Bool) {g f : Seminorm ℝ (Space n)}
    (hg : g≠0) {a : ℝ} (ha : 0<a) (he : ∀ x,f x=a*g x) :
    objective b f=if b then Real.log a+objective b g else a*objective b g := by
  cases b
  · change (∫ u : Sphere n,f u ∂sigma n)=a*∫ u : Sphere n,g u ∂sigma n
    simp_rw [he]; exact integral_const_mul _ _
  · have hae : (fun u : Sphere n => Real.log (f u))=ᵐ[sigma n]
        (fun u : Sphere n => Real.log a+Real.log (g u)) := by
      filter_upwards [seminorm_pos_ae_sphere hg] with u hu
      rw [he,Real.log_mul ha.ne' hu.ne']
    change (∫ u : Sphere n,Real.log (f u) ∂sigma n)=Real.log a+∫ u : Sphere n,Real.log (g u) ∂sigma n
    rw [integral_congr_ae hae,integral_add (integrable_const _) (seminorm_log_integrable hg),integral_const]
    simp only [probReal_univ,one_smul]

lemma coordinate_mean_pos (n : ℕ) [NeZero n] :
    0 < mean (fun u : Sphere n => |⟪(pole n:Space n),(u:Space n)⟫|) := by
  let f := fun u : Sphere n => |⟪(pole n:Space n),(u:Space n)⟫|
  have hc : Continuous f := by fun_prop
  apply integral_pos_of_integrable_nonneg_nonzero (x := pole n) hc (continuous_integrable hc) (fun _ => abs_nonneg _)
  dsimp [f]
  simp only [real_inner_self_eq_norm_sq,norm_coe,one_pow,abs_one,one_ne_zero,not_false_eq_true]

/-- Objective sublevels impose a common Lipschitz bound, including cylinders. -/
lemma objective_coercive {n : ℕ} [NeZero n] (b : Bool) (M : ℝ) :
    ∃ R : ℝ,0<R ∧ ∀ g : Seminorm ℝ (Space n),g≠0 → objective b g≤M → ∀ u : Sphere n,g u≤R := by
  let c := mean (fun u : Sphere n => Real.log |⟪(pole n:Space n),(u:Space n)⟫|)
  let d := mean (fun u : Sphere n => |⟪(pole n:Space n),(u:Space n)⟫|)
  have hd : 0<d := coordinate_mean_pos n
  cases b
  · refine ⟨max 1 (M/d),lt_of_lt_of_le zero_lt_one (le_max_left _ _),fun g hg hM u => ?_⟩
    obtain ⟨R,e,hR,hm,hb⟩ := seminorm_coordinate_minorant g hg
    have hlow : R*d≤objective false g := by
      have hi : Integrable (fun u : Sphere n => |⟪(e:Space n),(u:Space n)⟫|) (sigma n) :=
        continuous_integrable (by fun_prop : Continuous (fun u : Sphere n => |⟪(e:Space n),(u:Space n)⟫|))
      have h := integral_mono (hi.const_mul R) (seminorm_integrable g) (fun u => by
        simpa only [real_inner_comm] using hb u)
      rw [integral_const_mul] at h
      change R*mean _≤_ at h
      rw [mean_inner_independent (fun t => |t|) e (pole n)] at h
      exact h
    exact (hm u).trans (((le_div_iff₀ hd).mpr (hlow.trans hM)).trans (le_max_right _ _))
  · refine ⟨Real.exp (M-c),Real.exp_pos _,fun g hg hM u => ?_⟩
    obtain ⟨R,e,hR,hm,hb⟩ := seminorm_coordinate_minorant g hg
    have hlow := seminorm_log_coercivity hR hg hb
    change mean (fun u : Sphere n => Real.log (g u))≤M at hM
    have hh : Real.log R≤M-c := by change Real.log R+c≤_ at hlow; linarith
    exact (hm u).trans ((Real.log_le_iff_le_exp hR).mp hh)

lemma objective_tendsto {n : ℕ} [NeZero n] (b : Bool)
    {g : ℕ → Seminorm ℝ (Space n)} {f : Seminorm ℝ (Space n)} {r R : ℝ}
    (hr : 0<r) (hlo : ∀ i,∃ u : Sphere n,r≤g i u) (hhi : ∀ i (u : Sphere n),g i u≤R)
    (hf : f≠0) (hc : ∀ u : Sphere n,Tendsto (fun i => g i u) atTop (𝓝 (f u))) :
    Tendsto (fun i => objective b (g i)) atTop (𝓝 (objective b f)) := by
  cases b
  · apply tendsto_integral_of_dominated_convergence (fun _ => |R|)
    · exact fun i => (seminorm_integrable (g i)).aestronglyMeasurable
    · exact integrable_const _
    · intro i
      exact Eventually.of_forall (fun u => by
        change ‖g i u‖≤|R|
        rw [Real.norm_of_nonneg (apply_nonneg (g i) _)]
        exact (hhi i u).trans (le_abs_self _))
    · exact Eventually.of_forall hc
  · exact seminorm_log_integral_tendsto hr hlo hhi hf hc

end PettyProjection.Spherical
end

noncomputable section
open Set MeasureTheory Metric Filter Topology
open scoped NNReal RealInnerProductSpace Pointwise
namespace PettyProjection
open Spherical (Sphere seminorm_continuous)

lemma seminorm_positive_subspace_bound {n : ℕ} (V : Submodule ℝ (Space n)) (hV : V≠⊥)
    (g : Seminorm ℝ (Space n)) (hg : ∀ x∈V,x≠0 → 0<g x) :
    ∃ c : ℝ,0<c ∧ ∀ x,c*‖V.starProjection x‖≤g (V.starProjection x) := by
  let S : Set (Space n) := (V : Set (Space n)) ∩ sphere 0 1
  obtain ⟨v,hv,hv0⟩ := (Submodule.ne_bot_iff V).mp hV
  have hne : S.Nonempty := ⟨‖v‖⁻¹ • v,V.smul_mem _ hv,by simp [norm_smul,hv0]⟩
  have hc : IsCompact S := (isCompact_sphere (0:Space n) 1).inter_left V.closed_of_finiteDimensional
  obtain ⟨u,hu,hmin⟩ := hc.exists_isMinOn hne (seminorm_continuous n g).continuousOn
  have hu1 : ‖u‖=1 := by simpa only [mem_sphere,dist_zero_right] using hu.2
  have hu0 : u≠0 := by intro h; simp [h] at hu1
  refine ⟨g u,hg u hu.1 hu0,fun x => ?_⟩
  by_cases hx : V.starProjection x=0
  · simp [hx]
  have hn : 0<‖V.starProjection x‖ := norm_pos_iff.mpr hx
  have hunit : ‖V.starProjection x‖⁻¹ • V.starProjection x∈S :=
    ⟨V.smul_mem _ (V.starProjection_apply_mem x),by simp [norm_smul,hn.ne']⟩
  have hh : g u≤g (‖V.starProjection x‖⁻¹ • V.starProjection x) := hmin hunit
  rw [map_smul_eq_mul,Real.norm_of_nonneg (inv_nonneg.mpr hn.le)] at hh
  have h := mul_le_mul_of_nonneg_left hh hn.le
  rw [← mul_assoc,mul_inv_cancel₀ hn.ne',one_mul] at h
  simpa only [mul_comm] using h

namespace RelativeGauge
variable {n : ℕ} {V : Submodule ℝ (Space n)}

/-- Extended gauge of the unit ball in V. -/
def ball (V : Submodule ℝ (Space n)) : RelativeGauge V where
  toSeminorm := (normSeminorm ℝ (Space n)).comp V.starProjection.toLinearMap
  projection x := by
    change ‖V.starProjection (V.starProjection x)‖=‖V.starProjection x‖
    rw [V.starProjection_eq_self_iff.mpr (V.starProjection_apply_mem x)]
  lower := ⟨1,zero_lt_one,fun _ => by simp⟩

lemma ball_apply (V : Submodule ℝ (Space n)) (x : Space n) : ball V x=‖V.starProjection x‖ := rfl

lemma support_ball (V : Submodule ℝ (Space n)) (u : Space n) :
    support (ball V).body u=‖V.starProjection u‖ := by
  apply le_antisymm
  · apply (support_le_iff (ball V).compact (ball V).nonempty).mpr
    intro x hx
    have hx1 : ‖x‖≤1 := by
      have h : ‖V.starProjection x‖≤1 := hx.2
      rwa [V.starProjection_eq_self_iff.mpr hx.1] at h
    calc
      ⟪u,x⟫ = ⟪V.starProjection u,x⟫ := by
        rw [Submodule.inner_starProjection_left_eq_right,V.starProjection_eq_self_iff.mpr hx.1]
      _ ≤ ‖V.starProjection u‖*‖x‖ := real_inner_le_norm _ _
      _ ≤ ‖V.starProjection u‖ := mul_le_of_le_one_right (norm_nonneg _) hx1
  · by_cases hu : V.starProjection u=0
    · rw [hu,norm_zero]; exact support_nonneg (ball V).compact (ball V).zero_mem u
    have hp : 0<‖V.starProjection u‖ := norm_pos_iff.mpr hu
    have hz := (ball V).radial_mem (V.starProjection_apply_mem u) hu
    have he : ball V (V.starProjection u)=‖V.starProjection u‖ := by
      rw [ball_apply,V.starProjection_eq_self_iff.mpr (V.starProjection_apply_mem u)]
    have hh := inner_le_support (ball V).compact hz u
    have hi : ⟪u,V.starProjection u⟫=‖V.starProjection u‖^2 := by
      have h := Submodule.inner_starProjection_left_eq_right V u (V.starProjection u)
      rw [V.starProjection_eq_self_iff.mpr (V.starProjection_apply_mem u),real_inner_self_eq_norm_sq] at h
      exact h.symm
    rw [he,inner_smul_right,hi] at hh
    have hmul : ‖V.starProjection u‖⁻¹*‖V.starProjection u‖^2=‖V.starProjection u‖ := by
      field_simp
    rwa [hmul] at hh

lemma cylinder_nhds {K : Set (Space n)}
    (hinner : ∃ r : ℝ,0<r ∧ ∀ x∈V,‖x‖≤r → x∈K) :
    V.starProjection ⁻¹' K∈𝓝 (0:Space n) := by
  obtain ⟨r,hr,hin⟩ := hinner
  apply Filter.mem_of_superset (Metric.ball_mem_nhds (0:Space n) hr)
  intro x hx
  apply hin _ (V.starProjection_apply_mem x)
  exact (V.norm_starProjection_apply_le x).trans (by
    have hh : ‖x‖<r := by simpa only [mem_ball,dist_zero_right] using hx
    exact hh.le)

/-- Recover the relative extended gauge from an actual relative convex body. -/
def ofBody {K : Set (Space n)} (hK : IsCompact K) (hc : Convex ℝ K) (hb : Balanced ℝ K)
    (hinner : ∃ r : ℝ,0<r ∧ ∀ x∈V,‖x‖≤r → x∈K) : RelativeGauge V := by
  let Z := V.starProjection ⁻¹' K
  have hZc : Convex ℝ Z := hc.linear_preimage V.starProjection.toLinearMap
  have hZb : Balanced ℝ Z := by
    intro a ha y hy
    obtain ⟨z,hz,rfl⟩ := hy
    change V.starProjection (a • z)∈K
    rw [map_smul]
    exact hb a ha ⟨V.starProjection z,hz,rfl⟩
  have hZn : Z∈𝓝 (0:Space n) := cylinder_nhds hinner
  let g := gaugeSeminorm hZb hZc (absorbent_nhds_zero hZn)
  refine ⟨g,?_,?_⟩
  · intro x
    change gauge Z (V.starProjection x)=gauge Z x
    simp only [gauge_def',Z,mem_preimage,map_smul,
      V.starProjection_eq_self_iff.mpr (V.starProjection_apply_mem x)]
  · obtain ⟨R,hR,hbound⟩ := hK.isBounded.exists_pos_norm_le
    refine ⟨R⁻¹,inv_pos.mpr hR,fun x => ?_⟩
    change R⁻¹*‖V.starProjection x‖≤gauge Z x
    unfold gauge
    apply le_csInf (absorbent_nhds_zero hZn).gauge_set_nonempty
    rintro r ⟨hr,y,hy,rfl⟩
    rw [map_smul,norm_smul,Real.norm_of_nonneg hr.le]
    have hh : ‖V.starProjection y‖≤R := hbound _ hy
    calc
      R⁻¹*(r*‖V.starProjection y‖)≤R⁻¹*(r*R) := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hh hr.le) (inv_nonneg.mpr hR.le)
      _ = r := by field_simp

lemma ofBody_apply {K : Set (Space n)} (hK : IsCompact K) (hc : Convex ℝ K) (hb : Balanced ℝ K)
    (hinner : ∃ r : ℝ,0<r ∧ ∀ x∈V,‖x‖≤r → x∈K) (x : Space n) :
    ofBody hK hc hb hinner x=gauge (V.starProjection ⁻¹' K) x := rfl

lemma body_ofBody {K : Set (Space n)} (hK : IsCompact K) (hc : Convex ℝ K) (hb : Balanced ℝ K)
    (hsub : K⊆V) (hinner : ∃ r : ℝ,0<r ∧ ∀ x∈V,‖x‖≤r → x∈K) :
    (ofBody hK hc hb hinner).body=K := by
  ext x
  change (x∈V ∧ gauge (V.starProjection ⁻¹' K) x≤1) ↔ x∈K
  rw [gauge_le_one_iff_mem_closure (s := V.starProjection ⁻¹' K) (hc.linear_preimage V.starProjection.toLinearMap)
    (cylinder_nhds hinner),(hK.isClosed.preimage V.starProjection.continuous).closure_eq]
  constructor
  · rintro ⟨hx,hy⟩
    change V.starProjection x∈K at hy
    rwa [V.starProjection_eq_self_iff.mpr hx] at hy
  · intro hx
    refine ⟨hsub hx,?_⟩
    change V.starProjection x∈K
    rwa [V.starProjection_eq_self_iff.mpr (hsub hx)]

end RelativeGauge
end PettyProjection
end

noncomputable section
open Set MeasureTheory Metric Filter Topology
open scoped NNReal RealInnerProductSpace Pointwise
namespace PettyProjection
open Spherical (Sphere seminorm_continuous)

lemma support_mono_compact {n : ℕ} {K L : Set (Space n)} (hK : IsCompact K)
    (hKn : K.Nonempty) (hL : IsCompact L) (hsub : K⊆L) (u : Space n) :
    support K u≤ support L u := by
  obtain ⟨x,hx,he⟩ := support_attained hK hKn u
  rw [he]
  exact inner_le_support hL (hsub hx) u

lemma functional_mono_compact {n : ℕ} {μ : Measure (Space n)}
    (hμ : Integrable (fun x : Space n => ‖x‖) μ)
    {K L : Set (Space n)} (hK : IsCompact K) (hKn : K.Nonempty) (hL : IsCompact L) (hsub : K⊆L) :
    supportFunctional μ K≤ supportFunctional μ L :=
  integral_mono (support_integrable hμ hK hKn) (support_integrable hμ hL (hKn.mono hsub))
    (support_mono_compact hK hKn hL hsub)

namespace RelativeGauge
variable {n : ℕ} {V : Submodule ℝ (Space n)}

lemma balanced (g : RelativeGauge V) : Balanced ℝ g.body := by
  intro a ha y hy
  obtain ⟨z,hz,rfl⟩ := hy
  refine ⟨V.smul_mem _ hz.1,?_⟩
  exact (seminormUnit_balanced g.toSeminorm) a ha ⟨z,hz.2,rfl⟩

lemma inner_ball (g : RelativeGauge V) : ∃ r : ℝ,0<r ∧ ∀ x∈V,‖x‖≤r → x∈g.body := by
  obtain ⟨ε,hε,hεg⟩ := Metric.mem_nhds_iff.mp (seminormUnit_nhds g.toSeminorm)
  refine ⟨ε/2,by positivity,fun x hx hnorm => ⟨hx,hεg ?_⟩⟩
  rw [mem_ball,dist_zero_right]
  linarith

lemma body_subset_smul (g f : RelativeGauge V) {a : ℝ} (ha : 0<a)
    (hle : ∀ x,f x≤a*g x) : g.body⊆a • f.body := by
  intro x hx
  refine ⟨a⁻¹ • x,⟨V.smul_mem _ hx.1,?_⟩,smul_inv_smul₀ ha.ne' x⟩
  change f.toSeminorm (a⁻¹ • x)≤1
  rw [map_smul_eq_mul,Real.norm_of_nonneg (inv_nonneg.mpr ha.le),inv_mul_le_iff₀ ha,mul_one]
  exact (hle x).trans (mul_le_of_le_one_right ha.le hx.2)

lemma functional_le_scale (g f : RelativeGauge V) {μ : Measure (Space n)}
    (hμ : Integrable (fun x : Space n => ‖x‖) μ) {a : ℝ} (ha : 0<a)
    (hle : ∀ x,f x≤a*g x) : supportFunctional μ g.body≤a*supportFunctional μ f.body := by
  have hh := functional_mono_compact hμ g.compact g.nonempty (f.compact.smul a)
    (g.body_subset_smul f ha hle)
  rwa [functional_smul f.compact f.nonempty ha.le] at hh

lemma functional_pos (g : RelativeGauge V) (hV : V≠⊥) {μ : Measure (Space n)}
    (hμ : Integrable (fun x : Space n => ‖x‖) μ)
    (hq : ∀ x∈V,x≠0 → 0<cosineSeminorm μ hμ x) : 0 < supportFunctional μ g.body := by
  obtain ⟨x,hx,hx0⟩ := (Submodule.ne_bot_iff V).mp hV
  have hy := g.radial_mem hx hx0
  have hqy := hq _ hy.1 (smul_ne_zero (inv_ne_zero (g.pos hx hx0).ne') hx0)
  exact hqy.trans_le (cosine_le_functional hμ g.compact (fun _ h => g.neg_mem h) hy)

lemma normalized_lower (g : RelativeGauge V) {μ : Measure (Space n)}
    (hμ : Integrable (fun x : Space n => ‖x‖) μ) (hn : supportFunctional μ g.body=1) (x : Space n) :
    cosineSeminorm μ hμ (V.starProjection x)≤g x := by
  have hh := g.cosine_le_gauge_functional hμ x
  rwa [hn,mul_one] at hh

lemma support_bound (g : RelativeGauge V) {c : ℝ} (hc : 0<c)
    (hl : ∀ x,c*‖V.starProjection x‖≤g x) (u : Space n) : support g.body u≤c⁻¹*‖u‖ := by
  apply (support_le_iff g.compact g.nonempty).mpr
  intro x hx
  have hh := hl x
  rw [V.starProjection_eq_self_iff.mpr hx.1] at hh
  have hb : ‖x‖≤c⁻¹ := by
    rw [inv_eq_one_div,le_div_iff₀ hc]
    have hx1 : g x≤1 := hx.2
    nlinarith
  exact (real_inner_le_norm _ _).trans (by nlinarith [norm_nonneg u])

lemma functional_bound (g : RelativeGauge V) {μ : Measure (Space n)}
    (hμ : Integrable (fun x : Space n => ‖x‖) μ) {c : ℝ} (hc : 0<c)
    (hl : ∀ x,c*‖V.starProjection x‖≤g x) : supportFunctional μ g.body≤c⁻¹*(∫ x,‖x‖ ∂μ) := by
  have hh := integral_mono (support_integrable hμ g.compact g.nonempty) (hμ.const_mul c⁻¹)
    (g.support_bound hc hl)
  rwa [integral_const_mul] at hh

lemma seminorm_close_ambient [NeZero n] (g f : Seminorm ℝ (Space n)) {ε : ℝ}
    (hclose : ∀ u : Sphere n,|g u-f u|≤ε) (x : Space n) : |g x-f x|≤ε*‖x‖ := by
  by_cases hx : x=0
  · simp [hx]
  have hp : 0<‖x‖ := norm_pos_iff.mpr hx
  let u : Sphere n := ⟨‖x‖⁻¹ • x,by simp [norm_smul,hp.ne']⟩
  have hh := hclose u
  change |g (‖x‖⁻¹ • x)-f (‖x‖⁻¹ • x)|≤ε at hh
  rw [map_smul_eq_mul,map_smul_eq_mul,Real.norm_of_nonneg (inv_nonneg.mpr hp.le),← mul_sub,
    abs_mul,abs_of_pos (inv_pos.mpr hp),inv_mul_le_iff₀ hp] at hh
  simpa only [mul_comm] using hh

lemma close_le_scale [NeZero n] (g f : RelativeGauge V) {c ε : ℝ} (hc : 0<c) (hε : 0≤ε)
    (hl : ∀ x,c*‖V.starProjection x‖≤g x)
    (hclose : ∀ u : Sphere n,|g u-f u|≤ε) (x : Space n) : f x≤(1+ε/c)*g x := by
  have hh := seminorm_close_ambient g.toSeminorm f.toSeminorm hclose (V.starProjection x)
  rw [g.projection,f.projection] at hh
  have hdiff := (abs_le.mp hh).1
  have hprod := mul_le_mul_of_nonneg_left (hl x) (div_nonneg hε hc.le)
  have he : (ε/c)*(c*‖V.starProjection x‖)=ε*‖V.starProjection x‖ := by field_simp
  rw [he] at hprod
  nlinarith

lemma functional_close [NeZero n] (g f : RelativeGauge V) {μ : Measure (Space n)}
    (hμ : Integrable (fun x : Space n => ‖x‖) μ) {c ε : ℝ} (hc : 0<c) (hε : 0≤ε)
    (hg : ∀ x,c*‖V.starProjection x‖≤g x) (hf : ∀ x,c*‖V.starProjection x‖≤f x)
    (hclose : ∀ u : Sphere n,|g u-f u|≤ε) :
    |supportFunctional μ g.body-supportFunctional μ f.body|≤(ε/c)*(c⁻¹*(∫ x,‖x‖ ∂μ)) := by
  have ha : 0<1+ε/c := by positivity
  have h1 := g.functional_le_scale f hμ ha (g.close_le_scale f hc hε hg hclose)
  have hclose' : ∀ u : Sphere n,|f u-g u|≤ε := fun u => by rw [abs_sub_comm]; exact hclose u
  have h2 := f.functional_le_scale g hμ ha (f.close_le_scale g hc hε hf hclose')
  have hb1 := mul_le_mul_of_nonneg_left (g.functional_bound hμ hc hg) (div_nonneg hε hc.le)
  have hb2 := mul_le_mul_of_nonneg_left (f.functional_bound hμ hc hf) (div_nonneg hε hc.le)
  rw [abs_le]
  constructor <;> nlinarith

end RelativeGauge
end PettyProjection
end

noncomputable section
open Set MeasureTheory Metric Filter Topology
open scoped NNReal RealInnerProductSpace
namespace PettyProjection
open Spherical (Sphere)
namespace RelativeGauge
variable {n : ℕ} [NeZero n] {V : Submodule ℝ (Space n)}

lemma functional_tendsto {g : ℕ → RelativeGauge V} {f : RelativeGauge V}
    {μ : Measure (Space n)} (hμ : Integrable (fun x : Space n => ‖x‖) μ)
    {c : ℝ} (hc : 0<c) (hg : ∀ i x,c*‖V.starProjection x‖≤g i x)
    (hf : ∀ x,c*‖V.starProjection x‖≤f x)
    (hunif : TendstoUniformly (fun i (u : Sphere n) => g i u) (fun u => f u) atTop) :
    Tendsto (fun i => supportFunctional μ (g i).body) atTop (𝓝 (supportFunctional μ f.body)) := by
  let C := c⁻¹*(c⁻¹*(∫ x,‖x‖ ∂μ))
  have hC : 0≤C := mul_nonneg (inv_nonneg.mpr hc.le)
    (mul_nonneg (inv_nonneg.mpr hc.le) (integral_nonneg (fun _ => norm_nonneg _)))
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have hδ : 0<ε/(C+1) := div_pos hε (by linarith)
  have hu := (Metric.tendstoUniformly_iff.mp hunif) (ε/(C+1)) hδ
  obtain ⟨N,hN⟩ := eventually_atTop.mp hu
  refine ⟨N,fun i hi => ?_⟩
  have hh := (g i).functional_close f hμ hc hδ.le (hg i) hf (fun u => by
    have h := hN i hi u
    rw [Real.dist_eq] at h
    simpa only [abs_sub_comm] using h.le)
  rw [Real.dist_eq]
  have he : (ε/(C+1)/c)*(c⁻¹*(∫ x,‖x‖ ∂μ))=(ε/(C+1))*C := by dsimp [C]; ring
  rw [he] at hh
  apply hh.trans_lt
  have ht : C/(C+1)<1 := (div_lt_one (by linarith : 0<C+1)).mpr (by linarith)
  have hm := mul_lt_mul_of_pos_left ht hε
  simpa only [div_eq_mul_inv,mul_assoc,mul_comm,mul_left_comm,mul_one] using hm

/-- Compactness of fixed-subspace normalized gauges. All constants arise
from the actual cosine norm and objective, not regularity assumptions. -/
theorem normalized_subsequence {μ : Measure (Space n)}
    (hμ : Integrable (fun x : Space n => ‖x‖) μ) (hV : V≠⊥)
    (hq : ∀ x∈V,x≠0 → 0<cosineSeminorm μ hμ x)
    (b : Bool) (g : ℕ → RelativeGauge V) (hn : ∀ i,supportFunctional μ (g i).body=1)
    {M : ℝ} (hM : ∀ i,Spherical.objective b (g i).toSeminorm≤M) :
    ∃ f : RelativeGauge V, ∃ φ : ℕ → ℕ, StrictMono φ ∧ supportFunctional μ f.body=1 ∧
      TendstoUniformly (fun i (u : Sphere n) => g (φ i) u) (fun u => f u) atTop ∧
      Tendsto (fun i => Spherical.objective b (g (φ i)).toSeminorm) atTop
        (𝓝 (Spherical.objective b f.toSeminorm)) := by
  obtain ⟨c,hc,hcb⟩ := seminorm_positive_subspace_bound V hV (cosineSeminorm μ hμ) hq
  have hlo (i : ℕ) (x : Space n) : c*‖V.starProjection x‖≤g i x :=
    (hcb x).trans ((g i).normalized_lower hμ (hn i) x)
  obtain ⟨R,hR,hRb⟩ := Spherical.objective_coercive (n := n) b M
  have hhi (i : ℕ) (u : Sphere n) : g i u≤R := hRb _ ((g i).ne_zero hV) (hM i) u
  obtain ⟨q,φ,hφ,hu,hpoint⟩ := Spherical.bounded_seminorm_subsequence
    (R := ⟨R,hR.le⟩) (fun i => (g i).toSeminorm) hhi
  have hqp : ∀ x,q (V.starProjection x)=q x := by
    intro x
    apply tendsto_nhds_unique (hpoint (V.starProjection x))
    simpa only [(g _).projection] using hpoint x
  have hql (x : Space n) : c*‖V.starProjection x‖≤q x :=
    ge_of_tendsto (hpoint x) (Eventually.of_forall (fun i => hlo (φ i) x))
  let f : RelativeGauge V := ⟨q,hqp,⟨c,hc,hql⟩⟩
  have hf : supportFunctional μ f.body=1 := by
    have ht := functional_tendsto (f := f) hμ hc (fun i => hlo (φ i)) hql hu
    have hc1 : Tendsto (fun i => supportFunctional μ (g (φ i)).body) atTop (𝓝 (1:ℝ)) := by
      simp_rw [hn]
      exact tendsto_const_nhds
    exact tendsto_nhds_unique ht hc1
  obtain ⟨x,hx,hx0⟩ := (Submodule.ne_bot_iff V).mp hV
  let u : Sphere n := ⟨‖x‖⁻¹ • x,by simp [norm_smul,hx0]⟩
  have huV : (u:Space n)∈V := V.smul_mem _ hx
  have hlow (i : ℕ) : ∃ v : Sphere n,c≤g i v := by
    refine ⟨u,?_⟩
    have h := hlo i u
    rwa [V.starProjection_eq_self_iff.mpr huV,Spherical.norm_coe,mul_one] at h
  refine ⟨f,φ,hφ,hf,hu,?_⟩
  exact Spherical.objective_tendsto b hc (fun i => hlow (φ i)) (fun i => hhi (φ i))
    (f.ne_zero hV) (fun u => hpoint u)

end RelativeGauge
end PettyProjection
end

end OAI
