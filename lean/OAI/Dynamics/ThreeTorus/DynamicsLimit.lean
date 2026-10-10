import OAI.Dynamics.ThreeTorus.SmoothLimits

namespace OAI

/-! Stage topology, genuine smooth limiting dynamics, initial stage, unconditional diagonal, and limiting moments. -/

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators
namespace ThreeTorus
namespace StageState

def coordinate (s : StageState) : L2 × (ℤ → C(TripleTorus,TripleTorus)) :=
  (s.vec,s.mapCont)
instance : TopologicalSpace StageState := TopologicalSpace.induced coordinate inferInstance

lemma continuous_coordinate : Continuous coordinate := continuous_induced_dom
lemma continuous_vec : Continuous (fun s : StageState => s.vec) := continuous_coordinate.fst
lemma continuous_mapCont (k : ℤ) : Continuous (fun s : StageState => s.mapCont k) :=
  (continuous_apply k).comp continuous_coordinate.snd
lemma continuous_orbit (k : ℤ) : Continuous (fun s : StageState => s.orbit k) :=
  continuous_vec.compMeasurePreservingLp (continuous_mapCont k) (fun s => s.mapPow_mp k) (by norm_num)
lemma continuous_laurent (c : ℤ →₀ ℂ) : Continuous (fun s : StageState => s.laurent c) := by
  classical
  exact continuous_finsetSum _ (fun k _ => (continuous_orbit k).const_smul (c k))

/-- Finite jets and a physical vector tolerance reach every neighborhood needed
for retaining previously chosen Laurent polynomials. -/
lemma finite_neighborhood_control (s : StageState) {U : Set StageState} (hU : U ∈ 𝓝 s) :
    ∃ N : ℕ, ∃ ε > 0, ∀ t : StageState,
      dist s.vec t.vec < ε → (jetExhaustion N).Close ε s.frame s.V t.frame t.V → t ∈ U := by
  classical
  by_contra hh
  push Not at hh
  have hp (n : ℕ) : 0 < (1/2:ℝ)^n := pow_pos (by norm_num) _
  choose t hvt hjt hut using fun n => hh n ((1/2:ℝ)^n) (hp n)
  have hz : Tendsto (fun n : ℕ => (1/2:ℝ)^n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hv : Tendsto (fun n => (t n).vec) atTop (𝓝 s.vec) := by
    apply Metric.tendsto_atTop.mpr
    intro ε hε
    obtain ⟨N,hN⟩ := eventually_atTop.mp (hz.eventually (gt_mem_nhds hε))
    exact ⟨N,fun n hn => by simpa only [dist_comm] using (hvt n).trans (hN n hn)⟩
  have hm (k : ℤ) : Tendsto (fun n => (t n).mapCont k) atTop (𝓝 (s.mapCont k)) := by
    apply Metric.tendsto_atTop.mpr
    intro ε hε
    obtain ⟨N,hN⟩ := eventually_atTop.mp (hz.eventually (gt_mem_nhds hε))
    refine ⟨max N k.natAbs,fun n hn => ?_⟩
    have hh' := mapCont_dist_of_jets (hp n).le (hjt n) (le_trans (le_max_right _ _) hn)
    have hh'' : dist ((t n).mapCont k) (s.mapCont k) ≤ (1/2:ℝ)^n := by
      simpa only [dist_comm] using hh'
    exact hh''.trans_lt (hN n (le_trans (le_max_left _ _) hn))
  have ht : Tendsto t atTop (𝓝 s) := by
    apply (Topology.IsInducing.induced coordinate).tendsto_nhds_iff.mpr
    exact hv.prodMk_nhds (tendsto_pi_nhds.mpr hm)
  obtain ⟨n,hn⟩ := (ht.eventually hU).exists
  exact hut n hn

end StageState
end ThreeTorus
end
end

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ContDiff
namespace ThreeTorus

lemma smooth_diagonal_eventual_jets (f : ℕ → Cover → Cover)
    (hf : ∀ n, ContDiff ℝ ∞ (f n)) {b : ℕ → ℝ} (hb : Summable b)
    (hstep : ∀ (d : ℕ) (R : ℝ), ∀ᶠ n in atTop, ∀ x : Cover, ‖x‖ ≤ R →
      dist (iteratedFDeriv ℝ d (f (n+1)) x) (iteratedFDeriv ℝ d (f n) x) ≤ b n) :
    ∃ g : Cover → Cover, ContDiff ℝ ∞ g ∧ TendstoLocallyUniformly f g atTop := by
  let q (d : ℕ) := incrementLimit (fun n => iteratedFDeriv ℝ d (f n))
  have hq (d : ℕ) : TendstoLocallyUniformly (fun n => iteratedFDeriv ℝ d (f n)) (q d) atTop := by
    apply tendstoLocallyUniformly_iff_forall_isCompact.mpr
    intro K hK
    obtain ⟨R,hR⟩ := hK.isBounded.subset_closedBall (0:Cover)
    apply uniform_incrementLimit _ hb
    filter_upwards [hstep d R] with n hn
    intro x hx
    exact hn x (by simpa only [Metric.mem_closedBall,dist_zero_right] using hR hx)
  refine ⟨fun x => (q 0 x).curry0,smooth_of_jet_limits f hf q hq,?_⟩
  have hh := (continuousMultilinearCurryFin0 ℝ Cover Cover).isometry.uniformContinuous.comp_tendstoLocallyUniformly (hq 0)
  simpa only [Function.comp_def,continuousMultilinearCurryFin0_apply,ContinuousMultilinearMap.curry0_apply,iteratedFDeriv_zero_apply] using hh

/-- An actual smooth, volume preserving integer action on the physical torus.
This is limit DATA constructed below, not an assumption on a stage. -/
structure SmoothDynamics where
  map : ℤ → C(TripleTorus,TripleTorus)
  zero : ∀ x, map 0 x=x
  add : ∀ k j x, map (k+j) x=map k (map j x)
  mp : ∀ k, MeasurePreserving (map k) tripleVolume tripleVolume
  lift : ℤ → Cover → Cover
  smooth : ∀ k, ContDiff ℝ ∞ (lift k)
  graph : ∀ k x, tripleProject (lift k x)=map k (tripleProject x)

/-- Mere summable finite jet changes suffice for the genuine smooth action,
including the inverse and standard volume; every fixed integer power is kept. -/
theorem smooth_dynamics_of_jets (s : ℕ → StageState) {b : ℕ → ℝ} (hb : Summable b)
    (hj : ∀ n, (jetExhaustion n).Close (b n) (s n).frame (s n).V (s (n+1)).frame (s (n+1)).V) :
    ∃ D : SmoothDynamics, ∀ k : ℤ, Tendsto (fun n => (s n).mapCont k) atTop (𝓝 (D.map k)) := by
  have hh (k : ℤ) : ∃ g : Cover → Cover, ContDiff ℝ ∞ g ∧
      TendstoLocallyUniformly (fun n => (s n).frame.mapLift (s n).V k) g atTop := by
    apply smooth_diagonal_eventual_jets _ (fun n => (s n).frame.mapLift_smooth (s n).smooth k) hb
    intro d R
    obtain ⟨N,hN⟩ := exists_nat_ge R
    filter_upwards [eventually_ge_atTop (max N (max k.natAbs d))] with n hn
    intro x hx
    apply jetExhaustion_close_iff.mp (hj n) k (by omega) d (by omega) x
    have hNn : (N:ℝ) ≤ n := by exact_mod_cast (show N ≤ n by omega)
    linarith
  choose G hGs hGc using hh
  have hu (k : ℤ) := descend_uniform_limit _ (G k) (fun n => (s n).mapPow k) (hGc k)
    (fun n => (s n).mapPow_graph k)
  let T (k : ℤ) : C(TripleTorus,TripleTorus) :=
    ⟨fun z => tripleProject (G k (tripleSection z)),
      (hu k).continuous ((Eventually.of_forall (fun n => (s n).mapPow_cont k)).frequently)⟩
  have hT (k : ℤ) : Tendsto (fun n => (s n).mapCont k) atTop (𝓝 (T k)) :=
    ContinuousMap.tendsto_iff_tendstoUniformly.mpr (hu k)
  have h0 (x : TripleTorus) : T 0 x=x := by
    have hh := (hT 0).eval_const x
    have he (n : ℕ) : (s n).mapCont 0 x=x := (s n).mapPow_zero x
    simp only [he] at hh
    exact tendsto_nhds_unique hh tendsto_const_nhds
  have hadd (k j : ℤ) (x : TripleTorus) : T (k+j) x=T k (T j x) := by
    have h₁ := (hT (k+j)).eval_const x
    have h₂ := (hT k).eval ((hT j).eval_const x)
    have he : (fun n => (s n).mapCont (k+j) x)=
        (fun n => (s n).mapCont k ((s n).mapCont j x)) := by
      funext n; exact (s n).mapPow_add k j x
    rw [he] at h₁
    exact tendsto_nhds_unique h₁ h₂
  refine ⟨{
    map := T, zero := h0, add := hadd,
    mp := fun k => measurePreserving_uniform_limit (hT k) (fun n => (s n).mapPow_mp k),
    lift := G, smooth := hGs,
    graph := fun k x => (descend_limit_graph _ _ _ (hGc k) (fun n => (s n).mapPow_graph k) x).symm },hT⟩

end ThreeTorus
end
end

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ComplexConjugate ENNReal
namespace ThreeTorus

/-- Starting the actual construction needs no dynamical oracle: two reflected
angular packets on a single affine good arc have exactly Haar spectrum. -/
theorem exists_initial_stage {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < 1/8) :
    ∃ s : StageState, s.δ = δ := by
  let cut := lawCutoffs δ hδ hδ'
  let V := neutralJitterReal cut 1 0
  let p := neutralJitterReal_periodic cut 1 0
  let φ := p.lift
  have hs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V := neutralJitterReal_smooth cut 1 0
  have hc : Continuous φ := continuous_neutralJitter cut 1 0
  have hv (x : ℝ) (hx : x ∈ Icc (1/4:ℝ) (3/4)) : φ (x:UnitAddCircle)=x := by
    change V x=x
    simpa only [one_mul,add_zero] using neutralJitterReal_affine cut hδ 1 0
      (a := x) (show x ∈ Icc δ (1-δ) by constructor <;> linarith [hx.1,hx.2])
  have hd (x : ℝ) (hx : x ∈ Icc (1/4:ℝ) (3/4)) :
      HasDerivWithinAt (fun y : ℝ => φ (y:UnitAddCircle)) 1 (Icc (1/4:ℝ) (3/4)) x := by
    have he : deriv V x=1 := neutralJitterReal_deriv cut hδ 1 0
      (show x ∈ Ioo δ (1-δ) by constructor <;> linarith [hx.1,hx.2])
    change HasDerivWithinAt V 1 _ x
    rw [← he]
    exact ((hs.differentiable (by simp)).differentiableAt.hasDerivAt).hasDerivWithinAt
  obtain ⟨m,_,hm,t,ht,hlt,hA,hAL,hAr,hp,hn,hAs⟩ := exists_flat_packet_spectra_above
    hc.measurable (measurable_const : Measurable (fun _ : ℝ => (1:ℝ)))
    (show (1/4:ℝ)<3/4 by norm_num) hd
    (by intro x hx y hy hxy; simpa only [hv x hx,hv y hy] using hxy)
    (show Icc (1/4:ℝ) (3/4) ⊆ Ioc (0:ℝ) (0+1) by intro x hx; constructor <;> linarith [hx.1,hx.2]) 0
  let A := fun ua : UnitAddCircle × UnitAddCircle =>
    flatAmplitude 0 (1/4) t (fun _ => (m:ℝ)*1) ua.1
  have hmz : (m:ℤ) ≠ 0 := by exact_mod_cast (ne_of_gt hm)
  let F : MeasurablePackets := {
    Index := Bool, finite := inferInstance,
    m := fun b => if b then (m:ℤ) else -(m:ℤ),
    injective := by intro b c h; cases b <;> cases c <;> simp_all,
    nonzero := by intro b; cases b <;> simpa using hmz,
    A := fun _ => A, measurable := fun _ => hA, memLp := fun _ => hAL }
  have hr : F.Reflection Bool.not := by
    refine ⟨(by intro b; cases b <;> rfl),?_,?_⟩
    · intro b; cases b <;> simp [F]
    · intro b ua; exact (hAr ua).symm
  have hflat : F.spectrum (fun z => (φ z:UnitAddCircle))=phaseHaar := by
    change (∑ b : Bool, packetSpectralMeasure (fun z => (φ z:UnitAddCircle))
      (if b then (m:ℤ) else -(m:ℤ)) A)=phaseHaar
    simp only [A,Fintype.sum_bool,Bool.false_eq_true,ite_false,ite_true,hp,hn,← add_smul]
    rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
    norm_num
  have hsupport : F.Supported (1/4) (3/4) := by
    intro b ua hua
    obtain ⟨x,hx,hxe⟩ := (hAs hua).1
    exact ⟨⟨x,⟨hx.1,hx.2.trans ht.2⟩,hxe⟩,mem_univ _⟩
  refine ⟨{
    frame := PhysicalFrame.ident,
    chart_cont := continuous_id,
    chart_mp := MeasurePreserving.id _,
    packets := F, reflected := ⟨Bool.not,hr⟩,
    V := V, periodic := p, smooth := hs,
    δ := δ, l := 1/4, u := 3/4, δ_pos := hδ, δ_half := by linarith,
    δ_l := by linarith, l_u := by norm_num, u_δ := by linarith,
    increasing := by intro x hx; rw [neutralJitterReal_deriv cut hδ 1 0 hx]; norm_num,
    supported := hsupport, flat := hflat },rfl⟩

end ThreeTorus
end
end

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators
namespace ThreeTorus

/-- The finite history is kept at every successor; no density or limit is
part of this bookkeeping data. -/
structure StageHistory (test : ℕ → PhysicalTest) (e : ℕ → ℝ) (n : ℕ) where
  stage : StageState
  coeff : ℕ → (ℤ →₀ ℂ)
  small : stage.δ < (e n)^2/8
  retained : ∀ i < n, dist (test i).vec (stage.laurent (coeff i)) < e i

namespace StageHistory
variable {test : ℕ → PhysicalTest} {e : ℕ → ℝ} (he : ∀ n, 0 < e n)
include he

lemma exists_start : Nonempty (StageHistory test e 0) := by
  let δ := min ((e 0)^2/16) (1/16:ℝ)
  have hδ : 0 < δ := lt_min (div_pos (sq_pos_of_pos (he 0)) (by norm_num)) (by norm_num)
  obtain ⟨s,hs⟩ := exists_initial_stage hδ (lt_of_le_of_lt (min_le_right _ _) (by norm_num))
  refine ⟨⟨s,fun _ => 0,?_,by omega⟩⟩
  rw [hs]
  have hh := min_le_left ((e 0)^2/16) (1/16:ℝ)
  have hp := sq_pos_of_pos (he 0)
  dsimp [δ] at *
  linarith

lemma exists_next {n : ℕ} (a : StageHistory test e n) {b : ℝ} (hb : 0 < b) :
    ∃ t : StageHistory test e (n+1),
      (∀ i < n, t.coeff i=a.coeff i) ∧
      dist a.stage.vec t.stage.vec < b ∧
      (jetExhaustion n).Close b a.stage.frame a.stage.V t.stage.frame t.stage.V := by
  classical
  let U : Set StageState := {s | ∀ i : Fin n,
    dist (test i).vec (s.laurent (a.coeff i)) < e i}
  have hUo : IsOpen U := by
    have hUeq : U = ⋂ i : Fin n, {s : StageState | dist (test i).vec (s.laurent (a.coeff i)) < e i} := by
      ext s; simp only [U,mem_ofPred_eq,mem_iInter]
    rw [hUeq]
    exact isOpen_iInter_of_finite (fun i => isOpen_lt
      (continuous_const.dist (StageState.continuous_laurent (a.coeff i))) continuous_const)
  have hUa : a.stage ∈ U := fun i => a.retained i i.isLt
  obtain ⟨N,ε,hε,hcontrol⟩ := a.stage.finite_neighborhood_control (hUo.mem_nhds hUa)
  let z := min b (ε/2)
  have hz : 0 < z := lt_min hb (half_pos hε)
  obtain ⟨s,c,hsδ,hjs,hvs,hcs⟩ := a.stage.exists_step (test n)
    (jetExhaustion (max n N)) (ε := z) (η := e n/2) (κ := (e (n+1))^2/8) (ζ := z) hz (half_pos (he n))
    (div_pos (sq_pos_of_pos (he (n+1))) (by norm_num)) hz
  have hsU : s ∈ U := hcontrol s
    (hvs.trans_le ((min_le_right _ _).trans (by linarith)))
    ((jetExhaustion_mono (le_max_right n N) hjs).mono
      ((min_le_right _ _).trans (by linarith)))
  have hsq : Real.sqrt (2*a.stage.δ) < e n/2 := by
    apply (Real.sqrt_lt' (half_pos (he n))).mpr
    nlinarith [a.small]
  let t : StageHistory test e (n+1) := {
    stage := s,
    coeff := Function.update a.coeff n c,
    small := hsδ,
    retained := by
      intro i hi
      by_cases hin : i=n
      · subst i
        simp only [Function.update_self]
        exact hcs.trans (by linarith)
      · rw [Function.update_of_ne hin]
        exact hsU ⟨i,by omega⟩ }
  refine ⟨t,?_,hvs.trans_le (min_le_left _ _),
    (jetExhaustion_mono (le_max_left n N) hjs).mono (min_le_left _ _)⟩
  intro i hi
  exact Function.update_of_ne (by omega : i ≠ n) c a.coeff

end StageHistory

/-- A literal diagonal of actual stage states with simultaneously retained
finite polynomials. Only the externally selected real tests occur in the input;
all dynamics, packets and coefficient choices are produced by the stage. -/
theorem exists_stage_diagonal (test : ℕ → PhysicalTest) (e b : ℕ → ℝ)
    (he : ∀ n, 0 < e n) (hb : ∀ n, 0 < b n) :
    ∃ s : ℕ → StageState, ∃ c : ℕ → (ℤ →₀ ℂ),
      (∀ n, dist (s n).vec (s (n+1)).vec < b n) ∧
      (∀ n, (jetExhaustion n).Close (b n) (s n).frame (s n).V
        (s (n+1)).frame (s (n+1)).V) ∧
      (∀ i n, i < n → dist (test i).vec ((s n).laurent (c i)) < e i) := by
  classical
  let next {n : ℕ} (a : StageHistory test e n) : StageHistory test e (n+1) :=
    Classical.choose (a.exists_next he (hb n))
  have hn {n : ℕ} (a : StageHistory test e n) :=
    Classical.choose_spec (a.exists_next he (hb n))
  let a : (n : ℕ) → StageHistory test e n :=
    fun n => Nat.rec (Classical.choice (StageHistory.exists_start (test := test) he))
      (fun _ an => next an) n
  have has (n : ℕ) : a (n+1)=next (a n) := rfl
  have hc (i n : ℕ) (hin : i<n) : (a n).coeff i=(a (i+1)).coeff i := by
    induction n with
    | zero => omega
    | succ n ih =>
      by_cases h : i=n
      · subst i; rfl
      · rw [has,(hn (a n)).1 i (by omega)]
        exact ih (by omega)
  refine ⟨fun n => (a n).stage,fun i => (a (i+1)).coeff i,?_,?_,?_⟩
  · intro n; exact (hn (a n)).2.1
  · intro n; exact (hn (a n)).2.2
  · intro i n hin
    change dist (test i).vec ((a n).stage.laurent ((a (i+1)).coeff i)) < e i
    rw [← hc i n hin]
    exact (a n).retained i hin

end ThreeTorus
end
end

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ComplexConjugate
namespace ThreeTorus
namespace StageState
variable (s : StageState)

lemma orbit_zero : s.orbit 0=s.vec := by
  apply Lp.ext
  filter_upwards [s.orbit_ae 0,s.vec_ae] with x hx hy
  simpa only [s.mapPow_zero,hy] using hx

lemma orbit_comp (k j : ℤ) :
    Lp.compMeasurePreserving (s.mapPow j) (s.mapPow_mp j) (s.orbit k)=s.orbit (k+j) := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_compMeasurePreserving (s.orbit k) (s.mapPow_mp j),
    (s.mapPow_mp j).quasiMeasurePreserving.ae (s.orbit_ae k),s.orbit_ae (k+j)] with x hx hy hz
  simpa only [Function.comp_apply,hy,hz,s.mapPow_add] using hx

lemma inner_vec_orbit (k : ℤ) : inner ℂ s.vec (s.orbit k)=if k=0 then 1 else 0 := by
  rw [L2.inner_def]
  have he : (fun x => inner ℂ (s.vec x) (s.orbit k x)) =ᵐ[tripleVolume]
      fun x => conj (s.packets.vector (s.frame.chart x))*
        s.packets.vector (twistIter s.speed k (s.frame.chart x)) := by
    filter_upwards [s.vec_ae,s.orbit_ae k] with x hx hy
    rw [hx,hy]
    simp only [vector,mapPow_apply,Function.comp_apply,s.frame.chart.apply_symm_apply,
      RCLike.inner_apply,mul_comm]
  rw [integral_congr_ae he,
    s.chart_mp.integral_comp s.chartHomeo.toMeasurableEquiv.measurableEmbedding
      (g := fun x => conj (s.packets.vector x)*s.packets.vector (twistIter s.speed k x))]
  exact s.packets.flat_moment s.speed_cont.measurable s.flat k

lemma orbit_orthonormal : Orthonormal ℂ s.orbit := by
  rw [orthonormal_iff_ite]
  intro k j
  have hh := (Lp.compMeasurePreservingₗᵢ ℂ (s.mapPow k) (s.mapPow_mp k)).inner_map_map
    s.vec (s.orbit (j-k))
  change inner ℂ (s.orbit k)
    (Lp.compMeasurePreserving (s.mapPow k) (s.mapPow_mp k) (s.orbit (j-k))) = _ at hh
  rw [s.orbit_comp,sub_add_cancel,s.inner_vec_orbit] at hh
  simpa only [sub_eq_zero,eq_comm] using hh

lemma vec_norm : ‖s.vec‖=1 := by
  have hh := s.orbit_orthonormal.norm_eq_one 0
  rwa [s.orbit_zero] at hh

end StageState
end ThreeTorus
end
end

end OAI
