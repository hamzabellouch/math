import OAI.Geometry.ProjectionBodies.GaussianMeasures

namespace OAI

noncomputable section
open Set MeasureTheory Metric Filter Topology
open scoped NNReal RealInnerProductSpace
namespace PettyProjection
open Spherical (Sphere)
variable {n : ℕ}

/-- Actual lower-semicontinuity at a singular change of range, formulated
with a bounded projected cylinder instead of extended real support functions. -/
lemma support_min_tendsto {V : Submodule ℝ (Space n)}
    {Vj : ℕ → Submodule ℝ (Space n)} (gj : ∀ i,RelativeGauge (Vj i))
    (g : Seminorm ℝ (Space n)) {c : ℝ} (hc : 0<c)
    (hl : ∀ x,c*‖V.starProjection x‖≤g x)
    (hg : ∀ x,Tendsto (fun i => gj i x) atTop (𝓝 (g x)))
    {uj : ℕ → Space n} {u : Space n} (hu : u∈V) (huj : ∀ i,uj i∈Vj i)
    (ht : Tendsto uj atTop (𝓝 u)) :
    Tendsto (fun i => min (support (gj i).body (uj i))
      (support (RelativeGauge.project V g hc hl).body u)) atTop
      (𝓝 (support (RelativeGauge.project V g hc hl).body u)) := by
  let f := RelativeGauge.project V g hc hl
  apply tendsto_order.mpr
  constructor
  · intro r hr
    have hex : ∃ z∈seminormUnit g,r<⟪u,z⟫ := by
      by_contra! hn
      have hb : support f.body u≤r := by
        apply (support_le_iff f.compact f.nonempty).mpr
        intro y hy
        rw [RelativeGauge.project_body] at hy
        have hs : projectedUnit V g⊆{y | ⟪u,y⟫≤r} := by
          apply closure_minimal _ (isClosed_le (by fun_prop) continuous_const)
          rintro _ ⟨z,hz,rfl⟩
          change ⟪u,V.starProjection z⟫≤r
          rw [← Submodule.inner_starProjection_left_eq_right,V.starProjection_eq_self_iff.mpr hu]
          exact hn z hz
        exact hs hy
      exact (not_le_of_gt hr) hb
    obtain ⟨z,hz,hzr⟩ := hex
    have hm : max 1 (g z)=1 := max_eq_left hz
    have hd : Tendsto (fun i => ⟪uj i,z⟫ / max 1 (gj i z)) atTop (𝓝 ⟪u,z⟫) := by
      have hh := (ht.inner (tendsto_const_nhds (x := z))).div (tendsto_const_nhds.max (hg z)) (by rw [hm]; norm_num)
      change Tendsto (fun i => ⟪uj i,z⟫ / max 1 (gj i z)) atTop (𝓝 (⟪u,z⟫ / max 1 (g z))) at hh
      simpa only [hm,div_one] using hh
    filter_upwards [hd.eventually (lt_mem_nhds hzr)] with i hi
    exact lt_min (hi.trans_le ((gj i).support_cylinder_bound (uj i) (huj i) z)) hr
  · intro r hr
    exact Eventually.of_forall (fun i => (min_le_right _ _).trans_lt hr)

lemma projected_limit_normalization {μ : Measure (Space n)}
    (hμ : Integrable (fun x : Space n => ‖x‖) μ)
    {A : Space n →L[ℝ] Space n} {Aj : ℕ → Space n →L[ℝ] Space n}
    (hA : ∀ x,Tendsto (fun i => Aj i x) atTop (𝓝 (A x)))
    (gj : ∀ i,RelativeGauge (LinearMap.range (Aj i).toLinearMap))
    (hjn : ∀ i,supportFunctional (μ.map (Aj i)) (gj i).body=1)
    (g : Seminorm ℝ (Space n))
    (hg : ∀ x,Tendsto (fun i => gj i x) atTop (𝓝 (g x)))
    {c : ℝ} (hc : 0<c)
    (hl : ∀ x,c*‖(LinearMap.range A.toLinearMap).starProjection x‖≤g x) :
    supportFunctional (μ.map A) (RelativeGauge.project (LinearMap.range A.toLinearMap) g hc hl).body≤1 := by
  let V := LinearMap.range A.toLinearMap
  let f := RelativeGauge.project V g hc hl
  let H : Space n → ℝ := fun x => support f.body (A x)
  let Hj : ℕ → Space n → ℝ := fun i x => support (gj i).body (Aj i x)
  have hi : Integrable H μ := by
    exact (integrable_map_measure (support_continuous f.compact).aestronglyMeasurable
      A.continuous.measurable.aemeasurable).mp
        (support_integrable (norm_integrable_map hμ A) f.compact f.nonempty)
  have hij (i : ℕ) : Integrable (Hj i) μ := by
    exact (integrable_map_measure (support_continuous (gj i).compact).aestronglyMeasurable
      (Aj i).continuous.measurable.aemeasurable).mp
        (support_integrable (norm_integrable_map hμ (Aj i)) (gj i).compact (gj i).nonempty)
  have hpos (x : Space n) : 0≤H x := support_nonneg f.compact f.zero_mem _
  have hjpos (i : ℕ) (x : Space n) : 0≤Hj i x := support_nonneg (gj i).compact (gj i).zero_mem _
  have ht : Tendsto (fun i => ∫ x,min (Hj i x) (H x) ∂μ) atTop (𝓝 (∫ x,H x ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence H
    · intro i
      exact ((hij i).inf hi).aestronglyMeasurable
    · exact hi
    · intro i
      filter_upwards [] with x
      rw [Real.norm_eq_abs,abs_of_nonneg (le_min (hjpos i x) (hpos x))]
      exact min_le_right _ _
    · filter_upwards [] with x
      exact support_min_tendsto gj g hc hl hg (show A x∈V from ⟨x,rfl⟩)
        (fun i => show Aj i x∈LinearMap.range (Aj i).toLinearMap from ⟨x,rfl⟩) (hA x)
  have hb (i : ℕ) : (∫ x,min (Hj i x) (H x) ∂μ)≤1 := by
    have hh := integral_mono ((hij i).inf hi) (hij i) (fun _ => min_le_left _ _)
    have he : (∫ x,Hj i x ∂μ)=1 := by rw [← functional_map _ (gj i).compact,hjn]
    exact hh.trans he.le
  rw [functional_map _ f.compact]
  exact le_of_tendsto ht (Eventually.of_forall hb)

end PettyProjection
end

noncomputable section
open Set MeasureTheory Metric Filter Topology
open scoped NNReal RealInnerProductSpace Pointwise
namespace PettyProjection
open Spherical (Sphere objective)
namespace RelativeGauge
variable {n : ℕ}

lemma full_lower (f : RelativeGauge (⊤ : Submodule ℝ (Space n))) :
    ∃ c : ℝ,0< c ∧ ∀ x,c*‖x‖≤ f x := by
  obtain ⟨c,hc,hb⟩ := f.lower
  exact ⟨c,hc,fun x => by simpa only [Submodule.starProjection_top,ContinuousLinearMap.id_apply] using hb x⟩

def projectFull (V : Submodule ℝ (Space n))
    (f : RelativeGauge (⊤ : Submodule ℝ (Space n))) : RelativeGauge V :=
  project V f.toSeminorm f.full_lower.choose_spec.1 (fun x =>
    (mul_le_mul_of_nonneg_left (V.norm_starProjection_apply_le x) f.full_lower.choose_spec.1.le).trans
      (f.full_lower.choose_spec.2 x))

lemma projectFull_le (V : Submodule ℝ (Space n))
    (f : RelativeGauge (⊤ : Submodule ℝ (Space n))) (x : Space n) : projectFull V f x≤ f x :=
  project_le _ _ _ _ _

lemma projectFull_body (V : Submodule ℝ (Space n))
    (f : RelativeGauge (⊤ : Submodule ℝ (Space n))) :
    (projectFull V f).body=V.starProjection '' f.body := by
  rw [projectFull,project_body,projectedUnit,← f.top_body]
  exact (f.compact.image V.starProjection.continuous).isClosed.closure_eq

lemma support_projectFull (V : Submodule ℝ (Space n))
    (f : RelativeGauge (⊤ : Submodule ℝ (Space n))) {u : Space n} (hu : u∈V) :
    support (projectFull V f).body u=support f.body u := by
  have he (x : Space n) : ⟪u,V.starProjection x⟫=⟪u,x⟫ := by
    rw [← Submodule.inner_starProjection_left_eq_right,V.starProjection_eq_self_iff.mpr hu]
  apply le_antisymm
  · apply (support_le_iff (projectFull V f).compact (projectFull V f).nonempty).mpr
    intro x hx
    rw [projectFull_body] at hx
    obtain ⟨y,hy,rfl⟩ := hx
    rw [he]
    exact inner_le_support f.compact hy u
  · obtain ⟨x,hx,hxe⟩ := support_attained f.compact f.nonempty u
    rw [hxe,← he]
    apply inner_le_support (projectFull V f).compact
    rw [projectFull_body]
    exact mem_image_of_mem _ hx

lemma functional_projectFull {μ : Measure (Space n)} (A : Space n →L[ℝ] Space n)
    (f : RelativeGauge (⊤ : Submodule ℝ (Space n))) :
    supportFunctional (μ.map A) (projectFull (LinearMap.range A.toLinearMap) f).body=
      supportFunctional (μ.map A) f.body := by
  rw [functional_map _ (projectFull _ f).compact,functional_map _ f.compact]
  congr 1
  funext x
  exact support_projectFull _ f (show A x∈LinearMap.range A.toLinearMap from ⟨x,rfl⟩)

lemma minimizer_full_comparison [NeZero n] {μ : Measure (Space n)}
    (hμ : Integrable (fun x : Space n => ‖x‖) μ)
    (hq : ∀ x : Space n,x≠0 → 0< cosineSeminorm μ hμ x)
    (A : Space n →L[ℝ] Space n) (hA : LinearMap.range A.toLinearMap≠⊥) (b : Bool)
    (g : RelativeGauge (LinearMap.range A.toLinearMap))
    (hmin : ∀ q : RelativeGauge (LinearMap.range A.toLinearMap),supportFunctional (μ.map A) q.body=1 →
      objective b g.toSeminorm≤ objective b q.toSeminorm)
    (f : RelativeGauge (⊤ : Submodule ℝ (Space n))) :
    ∃ ha : 0< supportFunctional (μ.map A) f.body,
      objective b g.toSeminorm≤ objective b (f.scale _ ha).toSeminorm := by
  let p := projectFull (LinearMap.range A.toLinearMap) f
  have hp := p.functional_pos hA (norm_integrable_map hμ A) (cosine_map_pos hμ hq A)
  have he : supportFunctional (μ.map A) p.body=supportFunctional (μ.map A) f.body := functional_projectFull A f
  have ha : 0< supportFunctional (μ.map A) f.body := he ▸ hp
  refine ⟨ha,?_⟩
  have hpn : supportFunctional (μ.map A) (p.scale _ ha).body=1 := by
    rw [p.functional_scale _ ha (μ.map A),he,inv_mul_cancel₀ ha.ne']
  apply (hmin _ hpn).trans
  apply Spherical.objective_mono b ((p.scale _ ha).ne_zero hA) ((f.scale _ ha).ne_zero top_ne_bot)
  intro x
  exact mul_le_mul_of_nonneg_left (projectFull_le _ f x) ha.le

end RelativeGauge
end PettyProjection
end

noncomputable section
open Set MeasureTheory Metric Filter Topology
open scoped NNReal RealInnerProductSpace
namespace PettyProjection
open Spherical (Sphere objective)
namespace RelativeGauge
variable {n : ℕ} {V : Submodule ℝ (Space n)}

/-- A genuine full-dimensional approximation of an arbitrary relative gauge.
The sum regularization avoids any constant-rank assumption. -/
def thicken (g : RelativeGauge V) (ε : ℝ) (hε : 0<ε) :
    RelativeGauge (⊤ : Submodule ℝ (Space n)) where
  toSeminorm := Seminorm.of (fun x => g x+ε*‖x‖)
    (fun x y => by
      have hg := map_add_le_add g.toSeminorm x y
      have hn := mul_le_mul_of_nonneg_left (norm_add_le x y) hε.le
      linarith)
    (fun r x => by rw [map_smul_eq_mul,norm_smul]; ring)
  projection x := by simp only [Submodule.starProjection_top,ContinuousLinearMap.id_apply]
  lower := ⟨ε,hε,fun x => by
    change ε*‖(⊤ : Submodule ℝ (Space n)).starProjection x‖≤ g x+ε*‖x‖
    simp only [Submodule.starProjection_top,ContinuousLinearMap.id_apply]
    linarith [apply_nonneg g.toSeminorm x]⟩

lemma thicken_apply (g : RelativeGauge V) {ε : ℝ} (hε : 0<ε) (x : Space n) :
    thicken g ε hε x=g x+ε*‖x‖ := rfl

lemma thicken_ge (g : RelativeGauge V) {ε : ℝ} (hε : 0<ε) (x : Space n) :
    g x≤ thicken g ε hε x := le_add_of_nonneg_right (mul_nonneg hε.le (norm_nonneg x))

lemma support_thicken_le (g : RelativeGauge V) {ε : ℝ} (hε : 0<ε)
    {u : Space n} (hu : u∈V) : support (thicken g ε hε).body u≤ support g.body u := by
  apply (support_le_iff (thicken g ε hε).compact (thicken g ε hε).nonempty).mpr
  intro x hx
  have hpx : V.starProjection x∈g.body := by
    refine ⟨V.starProjection_apply_mem x,?_⟩
    change g (V.starProjection x)≤1
    rw [g.projection]
    exact (g.thicken_ge hε x).trans hx.2
  have hh := inner_le_support g.compact hpx u
  rwa [← Submodule.inner_starProjection_left_eq_right,V.starProjection_eq_self_iff.mpr hu] at hh

lemma functional_thicken_le {μ : Measure (Space n)}
    (hμ : Integrable (fun x : Space n => ‖x‖) μ)
    (A : Space n →L[ℝ] Space n) (g : RelativeGauge (LinearMap.range A.toLinearMap))
    {ε : ℝ} (hε : 0<ε) :
    supportFunctional (μ.map A) (g.thicken ε hε).body≤ supportFunctional (μ.map A) g.body := by
  rw [functional_map _ (g.thicken ε hε).compact,functional_map _ g.compact]
  have hi (f : Set (Space n)) (hf : IsCompact f) (hfn : f.Nonempty) :=
    (integrable_map_measure (support_continuous hf).aestronglyMeasurable A.continuous.measurable.aemeasurable).mp
      (support_integrable (norm_integrable_map hμ A) hf hfn)
  exact integral_mono (hi _ (g.thicken ε hε).compact (g.thicken ε hε).nonempty) (hi _ g.compact g.nonempty)
    (fun x => support_thicken_le g hε (show A x∈LinearMap.range A.toLinearMap from ⟨x,rfl⟩))

lemma objective_thicken_tendsto [NeZero n] (g : RelativeGauge V) (hV : V≠⊥) (b : Bool) :
    Tendsto (fun i : ℕ => objective b (g.thicken (1/((i:ℝ)+1)) (by positivity)).toSeminorm)
      atTop (𝓝 (objective b g.toSeminorm)) := by
  obtain ⟨x,hx,hx0⟩ := (Submodule.ne_bot_iff V).mp hV
  let u : Sphere n := ⟨‖x‖⁻¹ • x,by simp [norm_smul,hx0]⟩
  have huV : (u:Space n)∈V := V.smul_mem _ hx
  have hun : (u:Space n)≠0 := by intro he; have hh := Spherical.norm_coe u; simp [he] at hh
  have hp := g.pos huV hun
  let F : C(Sphere n,ℝ) := ⟨fun u => g u,(Spherical.seminorm_continuous n g.toSeminorm).comp continuous_subtype_val⟩
  refine Spherical.objective_tendsto b hp (fun i => ⟨u,g.thicken_ge (by positivity) u⟩)
    (R := ‖F‖+1) ?_ (g.ne_zero hV) ?_
  · intro i v
    rw [thicken_apply,Spherical.norm_coe,mul_one]
    have hf : g v≤‖F‖ := (le_abs_self _).trans (F.norm_coe_le_norm v)
    have hi : (1:ℝ)/((i:ℝ)+1)≤1 := (div_le_one (by positivity)).mpr (by linarith [Nat.cast_nonneg (α := ℝ) i])
    linarith
  · intro v
    have ht := (tendsto_const_nhds (x := g v)).add ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).mul_const ‖(v:Space n)‖)
    simpa only [thicken_apply,zero_mul,add_zero] using ht

end RelativeGauge
end PettyProjection
end

noncomputable section
open Set MeasureTheory Metric Filter Topology
open scoped NNReal RealInnerProductSpace
namespace PettyProjection
open Spherical (Sphere objective)
namespace RelativeGauge
variable {n : ℕ} [NeZero n] {μ : Measure (Space n)}

omit [NeZero n] in
lemma cosine_map_tendsto (hμ : Integrable (fun x : Space n => ‖x‖) μ)
    {Aj : ℕ → Space n →L[ℝ] Space n} {A : Space n →L[ℝ] Space n}
    (hA : Tendsto Aj atTop (𝓝 A)) (x : Space n) :
    Tendsto (fun i => cosineSeminorm (μ.map (Aj i)) (norm_integrable_map hμ (Aj i)) x)
      atTop (𝓝 (cosineSeminorm (μ.map A) (norm_integrable_map hμ A) x)) := by
  simp_rw [cosine_map μ hμ]
  have hc : Continuous (fun B : Space n →L[ℝ] Space n => cosineSeminorm μ hμ (B.adjoint x)) :=
    (Spherical.seminorm_continuous n _).comp (by fun_prop)
  exact (hc.tendsto A).comp hA

omit [NeZero n] in
lemma normalized_limit_lower (hμ : Integrable (fun x : Space n => ‖x‖) μ)
    {Aj : ℕ → Space n →L[ℝ] Space n} {A : Space n →L[ℝ] Space n}
    (hA : Tendsto Aj atTop (𝓝 A))
    (gj : ∀ i,RelativeGauge (LinearMap.range (Aj i).toLinearMap))
    (hn : ∀ i,supportFunctional (μ.map (Aj i)) (gj i).body=1)
    {g : Seminorm ℝ (Space n)} (hg : ∀ x,Tendsto (fun i => gj i x) atTop (𝓝 (g x))) (x : Space n) :
    cosineSeminorm (μ.map A) (norm_integrable_map hμ A) x≤ g x := by
  apply le_of_tendsto_of_tendsto (cosine_map_tendsto hμ hA x) (hg x)
  apply Eventually.of_forall
  intro i
  have hh := (gj i).normalized_lower (norm_integrable_map hμ (Aj i)) (hn i) x
  rwa [cosine_map_projection hμ] at hh

lemma full_comparison_limit (hμ : Integrable (fun x : Space n => ‖x‖) μ)
    (hq : ∀ x : Space n,x≠0 → 0< cosineSeminorm μ hμ x)
    {Aj : ℕ → Space n →L[ℝ] Space n} {A : Space n →L[ℝ] Space n}
    (hA : Tendsto Aj atTop (𝓝 A)) (hAn : LinearMap.range A.toLinearMap≠⊥)
    (hAj : ∀ i,LinearMap.range (Aj i).toLinearMap≠⊥) (b : Bool)
    (gj : ∀ i,RelativeGauge (LinearMap.range (Aj i).toLinearMap))
    (hm : ∀ i (q : RelativeGauge (LinearMap.range (Aj i).toLinearMap)),supportFunctional (μ.map (Aj i)) q.body=1 → objective b (gj i).toSeminorm≤ objective b q.toSeminorm)
    {g : Seminorm ℝ (Space n)}
    (hobj : Tendsto (fun i => objective b (gj i).toSeminorm) atTop (𝓝 (objective b g)))
    (f : RelativeGauge (⊤ : Submodule ℝ (Space n))) :
    ∃ ha : 0< supportFunctional (μ.map A) f.body,
      objective b g≤ objective b (f.scale _ ha).toSeminorm := by
  obtain ⟨gA,hgn,hgm⟩ := exists_minimizer (norm_integrable_map hμ A) hAn (cosine_map_pos hμ hq A) b
  obtain ⟨ha,_⟩ := minimizer_full_comparison hμ hq A hAn b gA hgm f
  refine ⟨ha,?_⟩
  have hscale : ∀ {a : ℝ} (ha : 0< a),objective b (f.scale a ha).toSeminorm=
      if b then Real.log a+objective b f.toSeminorm else a*objective b f.toSeminorm := by
    intro a ha
    exact Spherical.objective_scale b (f.ne_zero top_ne_bot) ha (fun _ => rfl)
  rw [hscale]
  have ht := ((functional_map_continuous hμ f.compact f.nonempty).tendsto A).comp hA
  have htr : Tendsto (fun i => if b then Real.log (supportFunctional (μ.map (Aj i)) f.body)+objective b f.toSeminorm
      else supportFunctional (μ.map (Aj i)) f.body*objective b f.toSeminorm)
      atTop (𝓝 (if b then Real.log (supportFunctional (μ.map A) f.body)+objective b f.toSeminorm
        else supportFunctional (μ.map A) f.body*objective b f.toSeminorm)) := by
    cases b
    · exact ht.mul_const _
    · exact (ht.log ha.ne').add_const _
  apply le_of_tendsto_of_tendsto hobj htr
  apply Eventually.of_forall
  intro i
  obtain ⟨hai,hi⟩ := minimizer_full_comparison hμ hq (Aj i) (hAj i) b (gj i) (hm i) f
  rwa [hscale] at hi

/-- Every seminorm limit of actual minimizers is the actual minimizer in the
limiting range, including arbitrary drops of rank. -/
theorem minimizer_limit_identify (hμ : Integrable (fun x : Space n => ‖x‖) μ)
    (hq : ∀ x : Space n,x≠0 → 0< cosineSeminorm μ hμ x)
    {Aj : ℕ → Space n →L[ℝ] Space n} {A : Space n →L[ℝ] Space n}
    (hA : Tendsto Aj atTop (𝓝 A)) (hAn : LinearMap.range A.toLinearMap≠⊥)
    (hAj : ∀ i,LinearMap.range (Aj i).toLinearMap≠⊥) (b : Bool)
    (gj : ∀ i,RelativeGauge (LinearMap.range (Aj i).toLinearMap))
    (hn : ∀ i,supportFunctional (μ.map (Aj i)) (gj i).body=1)
    (hm : ∀ i (q : RelativeGauge (LinearMap.range (Aj i).toLinearMap)),supportFunctional (μ.map (Aj i)) q.body=1 → objective b (gj i).toSeminorm≤ objective b q.toSeminorm)
    (gA : RelativeGauge (LinearMap.range A.toLinearMap)) (hgn : supportFunctional (μ.map A) gA.body=1)
    (hgm : ∀ q : RelativeGauge (LinearMap.range A.toLinearMap),supportFunctional (μ.map A) q.body=1 → objective b gA.toSeminorm≤ objective b q.toSeminorm)
    {g : Seminorm ℝ (Space n)} (hg : ∀ x,Tendsto (fun i => gj i x) atTop (𝓝 (g x)))
    (hobj : Tendsto (fun i => objective b (gj i).toSeminorm) atTop (𝓝 (objective b g))) :
    g=gA.toSeminorm := by
  let V := LinearMap.range A.toLinearMap
  have hμA := norm_integrable_map hμ A
  have hqA := cosine_map_pos hμ hq A
  have hqle := normalized_limit_lower hμ hA gj hn hg
  obtain ⟨c,hc,hcb⟩ := seminorm_positive_subspace_bound V hAn (cosineSeminorm (μ.map A) hμA) hqA
  have hl (x : Space n) : c*‖V.starProjection x‖≤ g x := by
    have hh := hcb x
    rw [cosine_map_projection hμ] at hh
    exact hh.trans (hqle x)
  let p := project V g hc hl
  have hpnle : supportFunctional (μ.map A) p.body≤1 := by
    apply projected_limit_normalization hμ _ gj hn g hg hc hl
    intro x
    exact ((show Continuous (fun B : Space n →L[ℝ] Space n => B x) by fun_prop).tendsto A).comp hA
  have hp := p.functional_pos hAn hμA hqA
  let q := p.scale _ hp
  have hqn : supportFunctional (μ.map A) q.body=1 := by
    rw [functional_scale p _ hp (μ.map A),inv_mul_cancel₀ hp.ne']
  have hqg (x : Space n) : q x≤ g x := by
    exact (mul_le_of_le_one_left (apply_nonneg p.toSeminorm x) hpnle).trans (project_le V g hc hl x)
  have hg0 : g≠0 := by
    intro he
    have hzero : q.toSeminorm=0 := by ext x; exact le_antisymm (by simpa only [he,zero_apply] using hqg x) (apply_nonneg q.toSeminorm x)
    exact q.ne_zero hAn hzero
  have hupper : objective b g≤ objective b gA.toSeminorm := by
    apply ge_of_tendsto (gA.objective_thicken_tendsto hAn b)
    apply Eventually.of_forall
    intro i
    let ε : ℝ := 1/((i:ℝ)+1)
    have hε : 0<ε := by dsimp [ε]; positivity
    let f := gA.thicken ε hε
    obtain ⟨ha,hh⟩ := full_comparison_limit hμ hq hA hAn hAj b gj hm hobj f
    have hle : supportFunctional (μ.map A) f.body≤1 := by
      exact (functional_thicken_le hμ A gA hε).trans hgn.le
    apply hh.trans
    apply Spherical.objective_mono b ((f.scale _ ha).ne_zero top_ne_bot) (f.ne_zero top_ne_bot)
    intro x
    exact mul_le_of_le_one_left (apply_nonneg f.toSeminorm x) hle
  have hlower := hgm q hqn
  have hmid := Spherical.objective_mono b (q.ne_zero hAn) hg0 hqg
  have heq : objective b q.toSeminorm=objective b g := le_antisymm hmid (hupper.trans hlower)
  have hqeq := Spherical.objective_mono_eq b (q.ne_zero hAn) hg0 hqg heq
  have huniq := minimizer_unique hμA hAn b hgn hqn hgm (le_antisymm hlower (hmid.trans hupper))
  rw [← hqeq,← huniq]

end RelativeGauge
end PettyProjection
end

noncomputable section
open Set MeasureTheory Metric Filter Topology
open scoped NNReal RealInnerProductSpace
namespace PettyProjection
open Spherical (Sphere objective)
namespace RelativeGauge
variable {n : ℕ} [NeZero n] {μ : Measure (Space n)}

omit [NeZero n] in
lemma full_functional_pos (hμ : Integrable (fun x : Space n => ‖x‖) μ)
    (hq : ∀ x : Space n,x≠0 → 0< cosineSeminorm μ hμ x)
    (A : Space n →L[ℝ] Space n) (hA : LinearMap.range A.toLinearMap≠⊥)
    (f : RelativeGauge (⊤ : Submodule ℝ (Space n))) : 0< supportFunctional (μ.map A) f.body := by
  have hp := (projectFull (LinearMap.range A.toLinearMap) f).functional_pos hA
    (norm_integrable_map hμ A) (cosine_map_pos hμ hq A)
  rwa [functional_projectFull] at hp

lemma minimizers_uniform_bound (hμ : Integrable (fun x : Space n => ‖x‖) μ)
    (hq : ∀ x : Space n,x≠0 → 0< cosineSeminorm μ hμ x)
    {Aj : ℕ → Space n →L[ℝ] Space n} {A : Space n →L[ℝ] Space n}
    (hA : Tendsto Aj atTop (𝓝 A)) (hAn : LinearMap.range A.toLinearMap≠⊥)
    (hAj : ∀ i,LinearMap.range (Aj i).toLinearMap≠⊥) (b : Bool)
    (gj : ∀ i,RelativeGauge (LinearMap.range (Aj i).toLinearMap))
    (hm : ∀ i (q : RelativeGauge (LinearMap.range (Aj i).toLinearMap)),supportFunctional (μ.map (Aj i)) q.body=1 →
      objective b (gj i).toSeminorm≤ objective b q.toSeminorm) :
    ∃ R : ℝ,0< R ∧ ∀ i (u : Sphere n),gj i u≤ R := by
  let f := ball (⊤ : Submodule ℝ (Space n))
  let a : (Space n →L[ℝ] Space n) → ℝ := fun B => supportFunctional (μ.map B) f.body
  have ha := full_functional_pos hμ hq A hAn f
  have ht : Tendsto (fun i => a (Aj i)) atTop (𝓝 (a A)) :=
    ((functional_map_continuous hμ f.compact f.nonempty).tendsto A).comp hA
  let v : ℕ → ℝ := fun i => if b then Real.log (a (Aj i))+objective b f.toSeminorm
    else a (Aj i)*objective b f.toSeminorm
  have hvt : Tendsto v atTop (𝓝 (if b then Real.log (a A)+objective b f.toSeminorm else a A*objective b f.toSeminorm)) := by
    cases b
    · exact ht.mul_const _
    · exact (ht.log ha.ne').add_const _
  obtain ⟨M,hM⟩ := (Metric.isBounded_range_of_tendsto v hvt).bddAbove
  obtain ⟨R,hR,hRb⟩ := Spherical.objective_coercive (n := n) b M
  refine ⟨R,hR,fun i u => hRb _ ((gj i).ne_zero (hAj i)) ?_ u⟩
  obtain ⟨hai,hh⟩ := minimizer_full_comparison hμ hq (Aj i) (hAj i) b (gj i) (hm i) f
  have he := Spherical.objective_scale b (g := f.toSeminorm) (f := (f.scale _ hai).toSeminorm)
    (f.ne_zero top_ne_bot) hai (fun _ => rfl)
  rw [he] at hh
  exact hh.trans (hM (mem_range_self i))

lemma objective_tendsto_of_pointwise {gj : ℕ → Seminorm ℝ (Space n)} {g : Seminorm ℝ (Space n)}
    (hg : g≠0) {R : ℝ} (hR : ∀ i (u : Sphere n),gj i u≤ R)
    (ht : ∀ x,Tendsto (fun i => gj i x) atTop (𝓝 (g x))) (b : Bool) :
    Tendsto (fun i => objective b (gj i)) atTop (𝓝 (objective b g)) := by
  have hex : ∃ u : Sphere n,0< g u := by
    by_contra! hn
    have he : g=0 := by
      ext x
      rw [← Spherical.radialExtension_seminorm g x]
      have hz : (fun u : Sphere n => g u)=(fun _ => 0) := by
        funext u; exact le_antisymm (hn u) (apply_nonneg g _)
      rw [hz]
      unfold Spherical.radialExtension
      split_ifs <;> simp
    exact hg he
  obtain ⟨u,hu⟩ := hex
  have hh := (ht u).eventually (lt_mem_nhds (show g u/2< g u by linarith))
  obtain ⟨N,hN⟩ := eventually_atTop.mp hh
  apply (tendsto_add_atTop_iff_nat N).mp
  apply Spherical.objective_tendsto b (show 0< g u/2 by linarith)
    (fun i => ⟨u,(hN (i+N) (Nat.le_add_left N i)).le⟩) (fun i => hR (i+N)) hg
  intro v
  exact (ht v).comp (tendsto_add_atTop_nat N)

omit [NeZero n] in
lemma limit_ne_zero (hμ : Integrable (fun x : Space n => ‖x‖) μ)
    (hq : ∀ x : Space n,x≠0 → 0< cosineSeminorm μ hμ x)
    {Aj : ℕ → Space n →L[ℝ] Space n} {A : Space n →L[ℝ] Space n}
    (hA : Tendsto Aj atTop (𝓝 A)) (hAn : LinearMap.range A.toLinearMap≠⊥)
    (gj : ∀ i,RelativeGauge (LinearMap.range (Aj i).toLinearMap))
    (hn : ∀ i,supportFunctional (μ.map (Aj i)) (gj i).body=1)
    {g : Seminorm ℝ (Space n)} (ht : ∀ x,Tendsto (fun i => gj i x) atTop (𝓝 (g x))) : g≠0 := by
  obtain ⟨x,hx,hx0⟩ := (Submodule.ne_bot_iff _).mp hAn
  have hp := cosine_map_pos hμ hq A x hx hx0
  have hh := normalized_limit_lower hμ hA gj hn ht x
  intro he
  rw [he,zero_apply] at hh
  linarith

/-- Sequential uniform compactness, and identification, for the actual
optimizer family across all nonzero linear maps, without a rank restriction. -/
theorem minimizers_subsequence (hμ : Integrable (fun x : Space n => ‖x‖) μ)
    (hq : ∀ x : Space n,x≠0 → 0< cosineSeminorm μ hμ x)
    {Aj : ℕ → Space n →L[ℝ] Space n} {A : Space n →L[ℝ] Space n}
    (hA : Tendsto Aj atTop (𝓝 A)) (hAn : LinearMap.range A.toLinearMap≠⊥)
    (hAj : ∀ i,LinearMap.range (Aj i).toLinearMap≠⊥) (b : Bool)
    (gj : ∀ i,RelativeGauge (LinearMap.range (Aj i).toLinearMap))
    (hn : ∀ i,supportFunctional (μ.map (Aj i)) (gj i).body=1)
    (hm : ∀ i (q : RelativeGauge (LinearMap.range (Aj i).toLinearMap)),supportFunctional (μ.map (Aj i)) q.body=1 →
      objective b (gj i).toSeminorm≤ objective b q.toSeminorm)
    (gA : RelativeGauge (LinearMap.range A.toLinearMap)) (hgn : supportFunctional (μ.map A) gA.body=1)
    (hgm : ∀ q : RelativeGauge (LinearMap.range A.toLinearMap),supportFunctional (μ.map A) q.body=1 →
      objective b gA.toSeminorm≤ objective b q.toSeminorm) :
    ∃ φ : ℕ → ℕ,StrictMono φ ∧
      TendstoUniformly (fun i (u : Sphere n) => gj (φ i) u) (fun u => gA u) atTop := by
  obtain ⟨R,hR,hRb⟩ := minimizers_uniform_bound hμ hq hA hAn hAj b gj hm
  obtain ⟨g,φ,hφ,hu,ht⟩ := Spherical.bounded_seminorm_subsequence (R := ⟨R,hR.le⟩)
    (fun i => (gj i).toSeminorm) hRb
  have hA' := hA.comp hφ.tendsto_atTop
  have hg := limit_ne_zero hμ hq hA' hAn (fun i => gj (φ i)) (fun i => hn (φ i)) ht
  have ho := objective_tendsto_of_pointwise hg (fun i => hRb (φ i)) ht b
  have he := minimizer_limit_identify hμ hq hA' hAn (fun i => hAj (φ i)) b
    (fun i => gj (φ i)) (fun i => hn (φ i)) (fun i => hm (φ i)) gA hgn hgm ht ho
  refine ⟨φ,hφ,?_⟩
  rwa [he] at hu

end RelativeGauge
end PettyProjection
end

end OAI
