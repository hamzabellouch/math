import OAI.Dynamics.ThreeTorus.Stages

namespace OAI

/-! All-order local smooth jet limits, positive and negative iterate diagonal, cover descent, and volume preservation. -/

section

noncomputable section
open Set Function Filter
open scoped Topology ContDiff
namespace ThreeTorus

/-- Locally uniform limits of EVERY actual spatial jet are a smooth map.
The limiting derivative data are not an assumed smooth diagonal. -/
theorem smooth_of_jet_limits {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : ℕ → E → F) (hf : ∀ n, ContDiff ℝ ∞ (f n))
    (q : (d : ℕ) → E → E [×d]→L[ℝ] F)
    (hq : ∀ d, TendstoLocallyUniformly (fun n => iteratedFDeriv ℝ d (f n)) (q d) atTop) :
    ContDiff ℝ ∞ (fun x => (q 0 x).curry0) := by
  refine ⟨fun x d => q d x, ?_⟩
  refine ⟨fun _ => rfl,?_,?_⟩
  · intro d hd x
    let e := continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (d+1) => E) F
    have hconv := e.isometry.uniformContinuous.comp_tendstoLocallyUniformly (hq (d+1))
    apply hasFDerivAt_of_tendstoLocallyUniformlyOn isOpen_univ
      hconv.tendstoLocallyUniformlyOn
    · intro n y _
      exact (hf n).ftaylorSeries.fderiv d hd y
    · intro y _
      exact (hq d).tendstoLocallyUniformlyOn.tendsto_at (mem_univ y)
    · trivial
  · intro d hd
    exact (hq d).continuous (.of_forall fun n => (hf n).continuous_iteratedFDeriv hd)

end ThreeTorus
end
end

section

noncomputable section
open Set Function Filter
open scoped Topology BigOperators ContDiff
namespace ThreeTorus

/-- A canonical local limit; no pointwise convergence or smooth limit is assumed. -/
def incrementLimit {X F : Type*} [NormedAddCommGroup F] (f : ℕ → X → F) (x : X) : F :=
  f 0 x + ∑' n, (f (n+1) x-f n x)

lemma uniform_incrementLimit {X F : Type*} [NormedAddCommGroup F] [CompleteSpace F]
    (f : ℕ → X → F) {s : Set X} {b : ℕ → ℝ} (hb : Summable b)
    (h : ∀ᶠ n in atTop, ∀ x ∈ s, dist (f (n+1) x) (f n x) ≤ b n) :
    TendstoUniformlyOn f (incrementLimit f) atTop s := by
  have ht := tendstoUniformlyOn_tsum_nat_eventually hb (h.mono fun n hn x hx =>
    show ‖f (n+1) x-f n x‖ ≤ b n by simpa only [dist_eq_norm] using hn x hx)
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp ht ε hε] with n hn
  intro x hx
  specialize hn x hx
  rw [Finset.sum_range_sub (fun k => f k x)] at hn
  convert hn using 1
  rw [dist_eq_norm,dist_eq_norm,incrementLimit]
  congr 1
  abel

/-- Summable changes on increasing balls and increasing derivative orders
produce a genuine smooth diagonal with locally uniform convergence of ALL
jets. This is the completeness step used after the finite-stage producer. -/
theorem smooth_diagonal_of_summable_jets {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [LocallyCompactSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (f : ℕ → E → F) (hf : ∀ n, ContDiff ℝ ∞ (f n))
    {b : ℕ → ℝ} (hb : Summable b)
    (hstep : ∀ (n d : ℕ), d ≤ n → ∀ x : E, ‖x‖ ≤ (n:ℝ) →
      dist (iteratedFDeriv ℝ d (f (n+1)) x) (iteratedFDeriv ℝ d (f n) x) ≤ b n) :
    ∃ g : E → F, ContDiff ℝ ∞ g ∧ TendstoLocallyUniformly f g atTop ∧
      ∀ d : ℕ, TendstoLocallyUniformly (fun n => iteratedFDeriv ℝ d (f n))
        (incrementLimit (fun n => iteratedFDeriv ℝ d (f n))) atTop := by
  let q (d : ℕ) := incrementLimit (fun n => iteratedFDeriv ℝ d (f n))
  have hq (d : ℕ) : TendstoLocallyUniformly (fun n => iteratedFDeriv ℝ d (f n)) (q d) atTop := by
    apply tendstoLocallyUniformly_iff_forall_isCompact.mpr
    intro K hK
    obtain ⟨r,hr⟩ := hK.isBounded.subset_closedBall (0:E)
    apply uniform_incrementLimit _ hb
    have hn : ∀ᶠ n : ℕ in atTop, r ≤ (n:ℝ) :=
      tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop _)
    filter_upwards [hn,eventually_ge_atTop d] with n hn hnd
    intro x hx
    apply hstep n d hnd x
    have hxnorm : ‖x‖ ≤ r := by simpa only [Metric.mem_closedBall,dist_zero_right] using hr hx
    exact hxnorm.trans hn
  refine ⟨fun x => (q 0 x).curry0,smooth_of_jet_limits f hf q hq,?_,hq⟩
  have hh := (continuousMultilinearCurryFin0 ℝ E F).isometry.uniformContinuous.comp_tendstoLocallyUniformly (hq 0)
  simpa only [Function.comp_def,continuousMultilinearCurryFin0_apply,ContinuousMultilinearMap.curry0_apply,iteratedFDeriv_zero_apply] using hh

end ThreeTorus
end
end

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology
namespace ThreeTorus

lemma continuous_tripleProject : Continuous tripleProject := by
  change Continuous (fun x : Cover => ((x 0:UnitAddCircle),(x 1:UnitAddCircle),(x 2:UnitAddCircle)))
  exact ((AddCircle.continuous_mk' 1).comp (continuous_apply 0)).prodMk
    (((AddCircle.continuous_mk' 1).comp (continuous_apply 1)).prodMk
      ((AddCircle.continuous_mk' 1).comp (continuous_apply 2)))

lemma circle_dist_coe_le (x y : ℝ) : dist (x:UnitAddCircle) (y:UnitAddCircle) ≤ dist x y := by
  rw [dist_eq_norm,dist_eq_norm,← AddCircle.coe_sub]
  exact QuotientAddGroup.norm_mk_le_norm

lemma tripleProject_dist_le (x y : Cover) : dist (tripleProject x) (tripleProject y) ≤ dist x y := by
  change max (dist (x 0:UnitAddCircle) (y 0:UnitAddCircle))
    (max (dist (x 1:UnitAddCircle) (y 1:UnitAddCircle)) (dist (x 2:UnitAddCircle) (y 2:UnitAddCircle))) ≤ _
  exact max_le ((circle_dist_coe_le _ _).trans (dist_le_pi_dist x y 0))
    (max_le ((circle_dist_coe_le _ _).trans (dist_le_pi_dist x y 1))
      ((circle_dist_coe_le _ _).trans (dist_le_pi_dist x y 2)))

def tripleSection (z : TripleTorus) : Cover :=
  ![circleRep 0 z.1,circleRep 0 z.2.1,circleRep 0 z.2.2]
lemma tripleProject_section (z : TripleTorus) : tripleProject (tripleSection z)=z := by
  change ((circleRep 0 z.1:UnitAddCircle),(circleRep 0 z.2.1:UnitAddCircle),(circleRep 0 z.2.2:UnitAddCircle))=z
  simp only [coe_circleRep]
lemma tripleSection_norm (z : TripleTorus) : ‖tripleSection z‖ ≤ 1 := by
  apply pi_norm_le_iff_of_nonneg zero_le_one |>.2
  intro i
  have h (w : UnitAddCircle) : ‖circleRep 0 w‖ ≤ 1 := by
    have hw := ((AddCircle.measurableEquivIoc 1 0) w).2
    change 0 < circleRep 0 w ∧ circleRep 0 w ≤ 0+1 at hw
    simpa only [Real.norm_eq_abs,abs_of_pos hw.1,zero_add] using hw.2
  fin_cases i <;> exact h _

/-- Local uniform cover convergence, plus the exact graph equations, descends
uniformly on the compact torus. The section is only a proof device; no
continuity of the measurable representatives is asserted. -/
lemma descend_uniform_limit (f : ℕ → Cover → Cover) (g : Cover → Cover)
    (F : ℕ → TripleTorus → TripleTorus)
    (hg : TendstoLocallyUniformly f g atTop)
    (hgraph : ∀ n x, tripleProject (f n x) = F n (tripleProject x)) :
    TendstoUniformly F (fun z => tripleProject (g (tripleSection z))) atTop := by
  have hc : IsCompact (Metric.closedBall (0:Cover) 1) := isCompact_closedBall _ _
  have hu := (tendstoLocallyUniformly_iff_forall_isCompact.mp hg) _ hc
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hu ε hε] with n hn
  intro z
  have hz : tripleSection z ∈ Metric.closedBall (0:Cover) 1 := by
    simpa only [Metric.mem_closedBall,dist_zero_right] using tripleSection_norm z
  have hh := (tripleProject_dist_le (g (tripleSection z)) (f n (tripleSection z))).trans_lt (hn _ hz)
  simpa only [hgraph,tripleProject_section] using hh

lemma descend_limit_graph (f : ℕ → Cover → Cover) (g : Cover → Cover)
    (F : ℕ → TripleTorus → TripleTorus)
    (hg : TendstoLocallyUniformly f g atTop)
    (hgraph : ∀ n x, tripleProject (f n x) = F n (tripleProject x)) (x : Cover) :
    tripleProject (g (tripleSection (tripleProject x))) = tripleProject (g x) := by
  have h₁ := (descend_uniform_limit f g F hg hgraph).tendsto_at (tripleProject x)
  have h₂ := continuous_tripleProject.continuousAt.tendsto.comp (((tendstoLocallyUniformly_iff_forall_isCompact.mp hg) {x} (isCompact_singleton)).tendsto_at (mem_singleton x))
  have he : (fun n => tripleProject (f n x)) = (fun n => F n (tripleProject x)) := by
    funext n; exact hgraph n x
  change Tendsto (fun n => tripleProject (f n x)) atTop (𝓝 (tripleProject (g x))) at h₂
  rw [he] at h₂
  exact tendsto_nhds_unique h₁ h₂

end ThreeTorus
end
end

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators
namespace ThreeTorus

def jetIndices (N : ℕ) : Finset (ℤ × ℕ) :=
  (Finset.Icc (-(N:ℤ)) N).product (Finset.range (N+1))

def jetExhaustion (N : ℕ) : PhysicalJetData where
  size := Fintype.card ↥(jetIndices N)
  sign i := ((Fintype.equivFin ↥(jetIndices N)).symm i).val.1
  order i := ((Fintype.equivFin ↥(jetIndices N)).symm i).val.2
  domain _ := Metric.closedBall (0:Cover) (N+1)
  compact _ := isCompact_closedBall _ _

lemma mem_jetIndices {N : ℕ} {k : ℤ} {d : ℕ} :
    (k,d) ∈ jetIndices N ↔ k.natAbs ≤ N ∧ d ≤ N := by
  simp only [jetIndices,Finset.product_eq_sprod,Finset.mem_product,Finset.mem_Icc,Finset.mem_range]
  omega

lemma jetExhaustion_close_iff {N : ℕ} {ε : ℝ} {F G : PhysicalFrame} {V W : ℝ → ℝ} :
    (jetExhaustion N).Close ε F V G W ↔
      ∀ k : ℤ, k.natAbs ≤ N → ∀ d : ℕ, d ≤ N → ∀ x : Cover, ‖x‖ ≤ (N:ℝ)+1 →
        dist (iteratedFDeriv ℝ d (G.mapLift W k) x)
          (iteratedFDeriv ℝ d (F.mapLift V k) x) ≤ ε := by
  constructor
  · intro h k hk d hd x hx
    let j : ↥(jetIndices N) := ⟨(k,d),mem_jetIndices.mpr ⟨hk,hd⟩⟩
    let P (q : ℤ × ℕ) : Prop := ∀ y : Cover, ‖y‖ ≤ (N:ℝ)+1 →
      dist (iteratedFDeriv ℝ q.2 (G.mapLift W q.1) y)
        (iteratedFDeriv ℝ q.2 (F.mapLift V q.1) y) ≤ ε
    have hh : P (((Fintype.equivFin ↥(jetIndices N)).symm
        ((Fintype.equivFin ↥(jetIndices N)) j)).val) := by
      intro y hy
      exact h _ y (by simpa only [jetExhaustion,Metric.mem_closedBall,dist_zero_right] using hy)
    have he : ((Fintype.equivFin ↥(jetIndices N)).symm
        ((Fintype.equivFin ↥(jetIndices N)) j)).val = (k,d) :=
      congrArg Subtype.val ((Fintype.equivFin ↥(jetIndices N)).symm_apply_apply j)
    exact (Eq.mp (congrArg P he) hh) x hx
  · intro h i x hx
    let j := (Fintype.equivFin ↥(jetIndices N)).symm i
    have hj := mem_jetIndices.mp j.property
    exact h j.val.1 hj.1 j.val.2 hj.2 x
      (by simpa only [jetExhaustion,Metric.mem_closedBall,dist_zero_right] using hx)

lemma jetExhaustion_mono {M N : ℕ} (hMN : M ≤ N) {ε : ℝ}
    {F G : PhysicalFrame} {V W : ℝ → ℝ}
    (h : (jetExhaustion N).Close ε F V G W) :
    (jetExhaustion M).Close ε F V G W := by
  rw [jetExhaustion_close_iff] at h ⊢
  intro k hk d hd x hx
  exact h k (hk.trans hMN) d (hd.trans hMN) x
    (hx.trans (by exact_mod_cast Nat.add_le_add_right hMN 1))

namespace StageState

def mapCont (s : StageState) (k : ℤ) : C(TripleTorus,TripleTorus) :=
  ⟨s.mapPow k,s.mapPow_cont k⟩

lemma mapCont_dist_of_jets {s t : StageState} {N : ℕ} {ε : ℝ} (hε : 0 ≤ ε)
    (hj : (jetExhaustion N).Close ε s.frame s.V t.frame t.V)
    {k : ℤ} (hk : k.natAbs ≤ N) : dist (mapCont s k) (mapCont t k) ≤ ε := by
  apply (ContinuousMap.dist_le hε).mpr
  intro z
  have hx : ‖tripleSection z‖ ≤ (N:ℝ)+1 :=
    (tripleSection_norm z).trans (le_add_of_nonneg_left (Nat.cast_nonneg N))
  have hh := jetExhaustion_close_iff.mp hj k hk 0 (Nat.zero_le _) (tripleSection z) hx
  have h0 (F : Cover → Cover) :
      (continuousMultilinearCurryFin0 ℝ Cover Cover) (iteratedFDeriv ℝ 0 F (tripleSection z)) =
        F (tripleSection z) := by simp
  have hd := (continuousMultilinearCurryFin0 ℝ Cover Cover).dist_map
    (iteratedFDeriv ℝ 0 (t.frame.mapLift t.V k) (tripleSection z))
    (iteratedFDeriv ℝ 0 (s.frame.mapLift s.V k) (tripleSection z))
  rw [h0,h0] at hd
  rw [← hd] at hh
  have he := (tripleProject_dist_le _ _).trans hh
  change dist (s.mapPow k z) (t.mapPow k z) ≤ ε
  simpa only [t.mapPow_graph,s.mapPow_graph,tripleProject_section,dist_comm] using he

end StageState
end ThreeTorus
end
end

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology
namespace ThreeTorus

instance tripleVolume_regular : tripleVolume.Regular :=
  Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure tripleVolume

/-- Volume invariance is closed under uniform convergence of continuous maps
on the actual compact torus. No invertibility of the limit is assumed here. -/
lemma measurePreserving_uniform_limit {F : ℕ → C(TripleTorus,TripleTorus)}
    {G : C(TripleTorus,TripleTorus)} (hG : Tendsto F atTop (𝓝 G))
    (hF : ∀ n, MeasurePreserving (F n) tripleVolume tripleVolume) :
    MeasurePreserving G tripleVolume tripleVolume := by
  let : (Measure.map G tripleVolume).Regular :=
    Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure _
  refine ⟨G.continuous.measurable,?_⟩
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  have ht : Tendsto (fun n => ∫ x, f (F n x) ∂tripleVolume) atTop
      (𝓝 (∫ x, f (G x) ∂tripleVolume)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => ‖f.toContinuousMap‖)
    · intro n
      exact (f.continuous.comp (F n).continuous).aestronglyMeasurable
    · exact integrable_const _
    · intro n
      exact ae_of_all _ (fun x => f.toContinuousMap.norm_coe_le_norm (F n x))
    · exact ae_of_all _ (fun x => f.continuous.continuousAt.tendsto.comp (hG.eval_const x))
  have hconst (n : ℕ) : (∫ x, f (F n x) ∂tripleVolume)=∫ x, f x ∂tripleVolume := by
    change (∫ x, f.toContinuousMap (F n x) ∂tripleVolume)=∫ x, f.toContinuousMap x ∂tripleVolume
    rw [← integral_map (hF n).measurable.aemeasurable f.continuous.aestronglyMeasurable,(hF n).map_eq]
  simp only [hconst] at ht
  change (∫ x, f.toContinuousMap x ∂Measure.map G tripleVolume)=∫ x, f.toContinuousMap x ∂tripleVolume
  rw [integral_map G.continuous.measurable.aemeasurable f.continuous.aestronglyMeasurable]
  exact tendsto_nhds_unique ht tendsto_const_nhds

end ThreeTorus
end
end

end OAI
