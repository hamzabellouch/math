import OAI.MathematicalPhysics.Boltzmann.Branching.FiveGainRank
import OAI.MathematicalPhysics.Boltzmann.Branching.PublishedInputs
import OAI.MathematicalPhysics.Boltzmann.Branching.PullbackCoordinates
import OAI.MathematicalPhysics.Boltzmann.Branching.RescaledParameterSlab
import OAI.MathematicalPhysics.Boltzmann.Branching.UpperTimeDeletion
import OAI.MathematicalPhysics.Boltzmann.Collision.AnalyticRankAlmostEverywhere
import OAI.MathematicalPhysics.Boltzmann.Jets.CoreJointParameterDensity
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Prod

namespace OAI

section

/-! # Rank seven of the actual map at the explicit collision witness -/

noncomputable section

open Matrix Function
open scoped Matrix
open BoltzmannNonuniqueness.FiveGainWitness

namespace BoltzmannNonuniqueness.FiveGainMap

theorem rank_at_witness {R : ℝ} (hR : 0 < R) {α γ τ : ℝ}
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hτ : 0 < τ)
    (σ s : Fin 5 → ℝ) (hs : ∀ i, 0 < s i) (t₀ z : ℝ) (x₀ : V) :
    let endpoint : State := (t₀,x₀,![R,0,z])
    let a := equalTimeSpeeds σ s α γ τ endpoint
    let q : Parameters := ((fun _ => τ),witnessAngles R z a)
    Surjective (fderiv ℝ (map σ s α γ endpoint) q) := by
  dsimp only
  let endpoint : State := (t₀,x₀,![R,0,z])
  let a := equalTimeSpeeds σ s α γ τ endpoint
  let L := witnessAngles R z a
  let q : Parameters := ((fun _ => τ),L)
  let T := fderiv ℝ (map σ s α γ endpoint) q
  change Surjective T
  have heq : ∀ i, q.1 i = τ := fun _ => rfl
  have hpos (c : V) : (T (firstTimeDirection c)).2.1 = witnessPosition R (z-a 2) c := by
    change (fderiv ℝ (map σ s α γ endpoint) q (firstTimeDirection c)).2.1 = _
    rw [map_derivative_position hα hγ hs hτ endpoint q _ heq]
    have hp (i : Fin 4) : (path σ s α γ endpoint q (i.val+1)).2.2 =
        witnessVelocities R z (z-a 2) ⟨i.val+1,by omega⟩ := by
      have h := congrArg (fun u : State => u.2.2)
        (path_equal_time σ s α γ τ endpoint L (k := i.val+1) (by omega) (by omega))
      exact h.trans (witness_velocityPath hR z a (i.val+1) (by omega))
    simp_rw [hp]
    exact positionDirection_at_witness R z a c
  have hw₃ : velocityPath a L endpoint.2.2 3 = witnessVelocities R z (z-a 2) 3 :=
    witness_velocityPath hR z a 3 (by decide)
  have hw₄ : velocityStep (a 3) (L 3) (velocityPath a L endpoint.2.2 3) =
      witnessVelocities R z (z-a 2) 4 := by
    exact witness_velocityPath hR z a 4 (by decide)
  have hang (A B : V) : (T (lastAngularDirection A B)).2.2 =
      (witnessVelocities R z (z-a 2) 3-axis (a 3)) ⨯₃ A+
      (witnessVelocities R z (z-a 2) 4-axis (a 4)) ⨯₃ B := by
    have h := map_derivative_last_angular (σ := σ) hα hγ hs hτ endpoint L
      (witnessAngles_last R z a) A B
    change (T (lastAngularDirection A B)).2.2 =
      (velocityPath a L endpoint.2.2 3-axis (a 3)) ⨯₃ A+
      (velocityStep (a 3) (L 3) (velocityPath a L endpoint.2.2 3)-axis (a 4)) ⨯₃ B at h
    rwa [hw₄,hw₃] at h
  apply surjective_of_blocks T
  · intro d
    exact map_derivative_time hα hγ hs endpoint q d (fun _ => hτ)
  · intro x
    obtain ⟨c,hc⟩ := witnessPosition_surjective R (z-a 2) x
    exact ⟨c,(hpos c).trans hc⟩
  · intro A B
    change (fderiv ℝ (map σ s α γ endpoint) q (lastAngularDirection A B)).2.1 = 0
    rw [map_derivative_position hα hγ hs hτ endpoint q _ heq]
    simp [positionDirection,lastAngularDirection]
  · intro v
    have hsur := final_angular_surjective R (z-a 2)
      (z+smallFactor R (z-a 2)*transverseSquare R-a 3)
      (z+smallFactor R (z-a 2)*transverseSquare R-a 4)
    obtain ⟨p,hp⟩ := hsur v
    refine ⟨p,(hang p.1 p.2).trans ?_⟩
    simpa [witnessVelocities,axis,Pi.sub_apply] using hp

end BoltzmannNonuniqueness.FiveGainMap

end

end

section

/-! # Transporting the rank witness to every nonaxial endpoint -/

noncomputable section

open Matrix Function
open scoped Matrix

namespace BoltzmannNonuniqueness.FiveGainMap

theorem rank_rotation {c s : ℝ} (hcs : c^2+s^2 = 1)
    {σ μ : Fin 5 → ℝ} {α γ : ℝ} (hα : 0 ≤ α) (hγ : 0 ≤ γ)
    (hμ : ∀ i, 0 < μ i) (z : State) (q : Parameters) (ht : q ∈ positiveDomain)
    (hrank : Surjective (fderiv ℝ (map σ μ α γ z) q)) :
    Surjective (fderiv ℝ (map σ μ α γ (rotateState c s z)) (rotateParameters c s q)) := by
  let P := rotateParameters c s
  let S := rotateState c s
  let D := fderiv ℝ (map σ μ α γ z) q
  let D' := fderiv ℝ (map σ μ α γ (S z)) (P q)
  have h₁ := ((map_analytic (σ := σ) hα hγ hμ (S z) (P q) ht).hasStrictFDerivAt.hasFDerivAt).comp q P.hasFDerivAt
  have h₂ := S.hasFDerivAt.comp q
    (map_analytic (σ := σ) hα hγ hμ z q ht).hasStrictFDerivAt.hasFDerivAt
  have he : (fun r => map σ μ α γ (S z) (P r)) =
      (fun r => S (map σ μ α γ z r)) := funext (map_rotation hcs σ μ α γ z)
  change HasFDerivAt (fun r => map σ μ α γ (S z) (P r)) (D'.comp P) q at h₁
  change HasFDerivAt (fun r => S (map σ μ α γ z r)) (S.comp D) q at h₂
  rw [he] at h₁
  have hD := h₁.unique h₂
  intro w
  obtain ⟨v,hv⟩ := rotateState_surjective hcs w
  obtain ⟨u,hu⟩ := hrank v
  refine ⟨P u,?_⟩
  have h := congrArg (fun L : Parameters →L[ℝ] State => L u) hD
  change D' (P u) = S (D u) at h
  exact h.trans (by rw [show D u = v from hu]; exact hv)

theorem exists_nonaxial_rank_point {σ μ : Fin 5 → ℝ} {α γ τ : ℝ}
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hμ : ∀ i, 0 < μ i) (hτ : 0 < τ)
    (t₀ : ℝ) (x v : V) (hv : 0 < v 0^2+v 1^2) :
    ∃ q : Parameters, (∀ i, q.1 i = τ) ∧ Surjective (fderiv ℝ (map σ μ α γ (t₀,x,v)) q) := by
  let R := Real.sqrt (v 0^2+v 1^2)
  have hR : 0 < R := Real.sqrt_pos.mpr hv
  have hR2 : R^2 = v 0^2+v 1^2 := Real.sq_sqrt hv.le
  let c := v 0/R
  let s := v 1/R
  have hcs : c^2+s^2 = 1 := by
    dsimp [c,s]
    field_simp
    nlinarith
  let z : State := (t₀,rotation c (-s) x,![R,0,v 2])
  have hz : rotateState c s z = (t₀,x,v) := by
    have hn : c^2+(-s)^2 = 1 := by simpa using hcs
    refine Prod.ext rfl (Prod.ext ?_ ?_)
    · simpa only [z,rotateState_apply,neg_neg] using rotation_inverse hn x
    · ext i
      fin_cases i <;> simp [z,rotateState_apply,rotation_apply,c,s,ne_of_gt hR]
  let a := equalTimeSpeeds σ μ α γ τ z
  let q : Parameters := ((fun _ => τ),witnessAngles R (v 2) a)
  have hrank : Surjective (fderiv ℝ (map σ μ α γ z) q) :=
    rank_at_witness hR hα hγ hτ σ μ hμ t₀ (v 2) (rotation c (-s) x)
  refine ⟨rotateParameters c s q,(fun _ => rfl),?_⟩
  rw [← hz]
  exact rank_rotation hcs hα hγ hμ z q (fun _ => hτ) hrank

end BoltzmannNonuniqueness.FiveGainMap

end

end

section

/-! # Removing the terminal-time cutoff from five positive gains -/

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology
open BoltzmannNonuniqueness.Published

namespace BoltzmannNonuniqueness.PositiveIteration

theorem five_tendsto_of_time_cutoffs {a T : ℝ} (hT : 0 < T)
    (K : ℕ → Kernel KineticPhase Velocity) [∀ n, IsSFiniteKernel (K n)]
    {C B : ℝ≥0∞} (hC : C ≠ ∞) (hB : B ≠ ∞)
    (hK : ∀ n z, z.1.1 ∈ Icc a T → K n z univ ≤ C)
    {f : ℕ → KineticPhase → ℝ≥0∞} (hf : ∀ n, Measurable (f n))
    (hfB : ∀ n z, z.1.1 ∈ Icc a T → f n z ≤ B)
    (z : ℕ → KineticPhase) (hz : ∀ n, (z n).1.1 ∈ Icc a T)
    (hcut : ∀ δ : ℝ, 0 < δ → δ < T → Tendsto (fun n =>
      iterate a (K n) ({y : KineticPhase | y.1.1 ≤ T-δ}.indicator (f n)) 5 (z n))
      atTop (𝓝 0)) :
    Tendsto (fun n => iterate a (K n) (f n) 5 (z n)) atTop (𝓝 0) := by
  apply ENNReal.tendsto_nhds_zero.mpr
  intro ε hε
  obtain ⟨e,he,heε⟩ := ENNReal.exists_nnreal_pos_mul_lt (by norm_num : (2:ℝ≥0∞) ≠ ∞) hε.ne'
  have he' : (0:ℝ≥0∞) < e := ENNReal.coe_pos.mpr he
  let d : ℕ → ℝ := fun j => 1/((j:ℝ)+1)
  have hd : Tendsto d atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hecost : Tendsto (fun j => B*(C*ENNReal.ofReal (d j))^5) atTop (𝓝 0) := by
    have h₁ := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hd
    simp only [ENNReal.ofReal_zero,Function.comp_def] at h₁
    have h₂ := ENNReal.Tendsto.const_mul h₁ (Or.inr hC)
    simp only [mul_zero] at h₂
    have h₃ := ENNReal.Tendsto.const_mul (ENNReal.Tendsto.pow (n := 5) h₂) (Or.inr hB)
    simpa only [zero_pow (by decide : (5:ℕ) ≠ 0),mul_zero] using h₃
  obtain ⟨j,hj,hcost⟩ := ((hd.eventually (gt_mem_nhds hT)).and
    (ENNReal.tendsto_nhds_zero.mp hecost e he')).exists
  have hdpos : 0 < d j := by dsimp [d]; positivity
  filter_upwards [ENNReal.tendsto_nhds_zero.mp (hcut (d j) hdpos hj) e he'] with n hn
  let g := {y : KineticPhase | y.1.1 ≤ T-d j}.indicator (f n)
  let h := {y : KineticPhase | T-d j < y.1.1}.indicator (f n)
  have hg : Measurable g := (hf n).indicator (measurableSet_le measurable_fst.fst measurable_const)
  have hsum : f n ≤ g+h := by
    intro y
    by_cases hy : y.1.1 ≤ T-d j
    · simp [g,h,hy,not_lt_of_ge hy]
    · simp [g,h,hy,lt_of_not_ge hy]
  have hbound := late_terminal_five_bound (K n) (hK n) (hfB n) (δ := d j) (hz n)
  calc
    _ ≤ iterate a (K n) (g+h) 5 (z n) := iterate_slab_mono (K n) (fun y _ => hsum y) 5 _ (hz n)
    _ = iterate a (K n) g 5 (z n)+iterate a (K n) h 5 (z n) :=
      congrFun (iterate_add a (K n) hg 5) (z n)
    _ ≤ e+e := add_le_add hn (hbound.trans hcost)
    _ = (e:ℝ≥0∞)*2 := by ring
    _ ≤ ε := heε.le

end BoltzmannNonuniqueness.PositiveIteration

end

end

section

/-! # Almost-everywhere rank of the actual five-gain map -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.FiveGainMap

theorem map_rank_ae (hM : Published.Mityagin2020FiveGainParameters)
    {σ μ : Fin 5 → ℝ} {α γ : ℝ} (hα : 0 ≤ α) (hγ : 0 ≤ γ)
    (hμ : ∀ i, 0 < μ i) (t₀ : ℝ) (x v : V) (hv : 0 < v 0^2+v 1^2) :
    volume {q ∈ positiveDomain | ¬Function.Surjective
      (fderiv ℝ (map σ μ α γ (t₀,x,v)) q)} = 0 := by
  obtain ⟨q,hq,hrank⟩ := exists_nonaxial_rank_point hα hγ hμ (by norm_num : (0 : ℝ) < 1)
    t₀ x v hv
  apply analytic_rank_ae hM positiveDomain_open positiveDomain_preconnected
    (map_analyticOnNhd hα hγ hμ (t₀,x,v)) (q₀ := q) _ hrank
  intro i
  rw [hq]
  norm_num

end BoltzmannNonuniqueness.FiveGainMap

end

end

section

/-! # Exact derivative of the zero-width map, including spectator variables -/

noncomputable section

namespace BoltzmannNonuniqueness.FiveGainMap

theorem controlDerivative_zero_apply {σ s : Fin 5 → ℝ} {α γ : ℝ}
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hs : ∀ i, 0 < s i)
    (z : State) (q : Parameters) (w : Fin 5 → V) (ht : ∀ i, 0 < q.1 i)
    (d : ThermalControls) :
    controlDerivative σ α γ ((s,0,z),(q,w)) d =
      fderiv ℝ (map σ s α γ z) q d.1 := by
  have hf := thermalControl_hasFDerivAt (σ := σ) hα hγ
    (⟨(s,0,z),hs⟩ : PositiveEnvironment) (q,w) ht
  have hg := ((map_analytic (σ := σ) hα hγ hs z q ht).hasStrictFDerivAt.hasFDerivAt).comp
    (q,w) (hasFDerivAt_fst (𝕜 := ℝ))
  have he : (fun u : ThermalControls => thermalMap σ α γ ((s,0,z),u)) =
      (fun u : ThermalControls => map σ s α γ z u.1) :=
    funext (fun u => thermalMap_zero σ s α γ z u.1 u.2)
  change HasFDerivAt (fun u : ThermalControls => thermalMap σ α γ ((s,0,z),u))
    (controlDerivative σ α γ ((s,0,z),(q,w))) (q,w) at hf
  change HasFDerivAt (fun u : ThermalControls => map σ s α γ z u.1)
    ((fderiv ℝ (map σ s α γ z) q).comp (ContinuousLinearMap.fst ℝ _ _)) (q,w) at hg
  rw [he] at hf
  exact congrArg (fun L : ThermalControls →L[ℝ] State => L d) (hf.unique hg)

theorem controlDerivative_zero_surjective {σ s : Fin 5 → ℝ} {α γ : ℝ}
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hs : ∀ i, 0 < s i)
    (z : State) (q : Parameters) (w : Fin 5 → V) (ht : ∀ i, 0 < q.1 i)
    (hrank : Function.Surjective (fderiv ℝ (map σ s α γ z) q)) :
    Function.Surjective (controlDerivative σ α γ ((s,0,z),(q,w))) := by
  intro v
  obtain ⟨d,hd⟩ := hrank v
  refine ⟨(d,0),?_⟩
  rw [controlDerivative_zero_apply hα hγ hs z q w ht]
  exact hd

end BoltzmannNonuniqueness.FiveGainMap

end

end

section

/-! # The zero-width rank statement with all fifteen thermal spectator variables -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.FiveGainMap

theorem zeroWidth_rank_ae (hM : Published.Mityagin2020FiveGainParameters)
    {σ μ : Fin 5 → ℝ} {α γ : ℝ} (hα : 0 ≤ α) (hγ : 0 ≤ γ)
    (hμ : ∀ i, 0 < μ i) (t₀ : ℝ) (x v : V) (hv : 0 < v 0^2+v 1^2) :
    ((volume : Measure Parameters).prod (volume : Measure (Fin 5 → V)))
      {p : ThermalControls | p.1 ∈ positiveDomain ∧ ¬Function.Surjective
        (controlDerivative σ α γ ((μ,0,(t₀,x,v)),p))} = 0 := by
  let Z := {q ∈ positiveDomain | ¬Function.Surjective
    (fderiv ℝ (map σ μ α γ (t₀,x,v)) q)}
  have hZ : (volume : Measure Parameters) Z = 0 :=
    map_rank_ae hM hα hγ hμ t₀ x v hv
  have hsub : {p : ThermalControls | p.1 ∈ positiveDomain ∧ ¬Function.Surjective
      (controlDerivative σ α γ ((μ,0,(t₀,x,v)),p))} ⊆ Z ×ˢ Set.univ := by
    intro p hp
    refine ⟨⟨hp.1,?_⟩,Set.mem_univ _⟩
    intro hq
    exact hp.2 (controlDerivative_zero_surjective hα hγ hμ (t₀,x,v) p.1 p.2 hp.1 hq)
  apply measure_mono_null hsub
  rw [Measure.prod_prod,hZ,zero_mul]

end BoltzmannNonuniqueness.FiveGainMap

end

end

section

/-! # Compact pullback convergence for the actual five thermal gains -/

noncomputable section

open MeasureTheory MeasureTheory.Measure Filter Set Function
open scoped ENNReal Topology

namespace BoltzmannNonuniqueness.FiveGainMap

def controlDomain : Set ThermalControls := {q | q.1 ∈ positiveDomain}

theorem controlDomain_open : IsOpen controlDomain :=
  positiveDomain_open.preimage continuous_fst

/-- Seven output coordinates and twenty-eight complementary parameters. -/
def controlCoordinates : ThermalControls ≃L[ℝ] State × (Fin 28 → ℝ) :=
  (LinearEquiv.ofFinrankEq _ _ (by
    simp [ThermalControls,Parameters,State,V,Module.finrank_prod,
      Module.finrank_pi_fintype])).toContinuousLinearEquiv

theorem controlDerivative_continuousAt {σ : Fin 5 → ℝ} {α γ : ℝ}
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (env : PositiveEnvironment)
    {q : ThermalControls} (hq : q ∈ controlDomain) :
    ContinuousAt (fun u => controlDerivative σ α γ (env.val,u)) q := by
  let precomp := (ContinuousLinearMap.compL ℝ ThermalControls ThermalInput State).flip
    (ContinuousLinearMap.inr ℝ ThermalEnvironment ThermalControls)
  have hd := (thermalMap_analytic (σ := σ) hα hγ (env.val,q) env.property hq).fderiv.continuousAt
  exact precomp.continuous.continuousAt.comp
    (hd.comp (f := fun u => (env.val,u)) (continuousAt_const.prodMk continuousAt_id))

/-- Uniformly bounded parameter densities pull local L1 errors back to zero
through the five thermal gains, at any nonaxial limiting endpoint. -/
theorem thermal_compact_pullback_zero (hMityagin : Published.Mityagin2020FiveGainParameters)
    {σ μ : Fin 5 → ℝ} {α γ : ℝ} (hα : 0 ≤ α) (hγ : 0 ≤ γ)
    (hμ : ∀ i, 0 < μ i) (t₀ : ℝ) (x v : V) (hv : 0 < v 0^2+v 1^2)
    {env : ℕ → PositiveEnvironment}
    (henv : Tendsto env atTop (𝓝 (⟨(μ,0,(t₀,x,v)),hμ⟩ : PositiveEnvironment)))
    {K : Set ThermalControls} (hK : IsCompact K) (hKT : K ⊆ controlDomain)
    {g : ℕ → State → ℝ≥0∞} {ρ : ℕ → ThermalControls → ℝ≥0∞} {B M : ℝ≥0∞}
    (hB : B ≠ ∞) (hM : M ≠ ∞) (hg : ∀ n, Measurable (g n))
    (hρ : ∀ n q, q ∈ controlDomain → ρ n q ≤ B) (hgM : ∀ n z, g n z ≤ M)
    (hL : Tendsto (fun n => ∫⁻ z, g n z) atTop (𝓝 0)) :
    Tendsto (fun n => ∫⁻ q in K, ρ n q*g n (thermalMap σ α γ ((env n).val,q)))
      atTop (𝓝 0) := by
  have : IsAddHaarMeasure (volume : Measure (V × V)) :=
    Measure.prod.instIsAddHaarMeasure _ _
  have : IsAddHaarMeasure (volume : Measure State) :=
    Measure.prod.instIsAddHaarMeasure _ _
  have : IsAddHaarMeasure (volume : Measure (Fin 5 → V)) :=
    Measure.pi.isAddHaarMeasure _
  have : IsAddHaarMeasure (volume : Measure Parameters) :=
    Measure.prod.instIsAddHaarMeasure _ _
  have : IsAddHaarMeasure (volume : Measure ThermalControls) :=
    Measure.prod.instIsAddHaarMeasure _ _
  let env₀ : PositiveEnvironment := ⟨(μ,0,(t₀,x,v)),hμ⟩
  let Z := {q : ThermalControls | q ∈ controlDomain ∧
    ¬Surjective (controlDerivative σ α γ (env₀.val,q))}
  have hZ : (volume : Measure ThermalControls) Z = 0 :=
    zeroWidth_rank_ae hMityagin hα hγ hμ t₀ x v hv
  apply GainPullback.compact_pullback_zero_coordinates controlCoordinates
    controlDomain_open hK hKT hZ
    (fun n q hq => thermalControl_hasFDerivAt hα hγ (env n) q hq)
    (fun q hq => controlDerivative_continuousAt hα hγ env₀ hq)
    (φ' := fun q => controlDerivative σ α γ (env₀.val,q))
    (fun q hq => by
      by_contra hn
      exact hq.2 ⟨hKT hq.1,hn⟩)
    (fun C hC hCT => thermalDerivative_compact_tendsto hα hγ henv hC
      (fun q hq => hCT hq)) hB hM hg hρ hgM hL

end BoltzmannNonuniqueness.FiveGainMap

end

end

section

/-! # Local L1 smallness suffices for the five-gain pullback -/

noncomputable section

open MeasureTheory Filter Set Function Metric
open scoped ENNReal Topology

namespace BoltzmannNonuniqueness.FiveGainMap

attribute [local irreducible] thermalMap

/-- Only the values on one fixed output ball enter a compact parameter integral. -/
theorem thermal_compact_pullback_zero_local
    (hMityagin : Published.Mityagin2020FiveGainParameters)
    {σ μ : Fin 5 → ℝ} {α γ : ℝ} (hα : 0 ≤ α) (hγ : 0 ≤ γ)
    (hμ : ∀ i, 0 < μ i) (t₀ : ℝ) (x v : V) (hv : 0 < v 0^2+v 1^2)
    {env : ℕ → PositiveEnvironment}
    (henv : Tendsto env atTop (𝓝 (⟨(μ,0,(t₀,x,v)),hμ⟩ : PositiveEnvironment)))
    {K : Set ThermalControls} (hK : IsCompact K) (hKT : K ⊆ controlDomain)
    {g : ℕ → State → ℝ≥0∞} {ρ : ℕ → ThermalControls → ℝ≥0∞} {B M : ℝ≥0∞}
    (hB : B ≠ ∞) (hM : M ≠ ∞) (hg : ∀ n, Measurable (g n))
    (hρ : ∀ n q, q ∈ controlDomain → ρ n q ≤ B) (hgM : ∀ n z, g n z ≤ M)
    (hL : ∀ R : ℝ, 0 < R → Tendsto
      (fun n => ∫⁻ z in closedBall (0 : State) R, g n z) atTop (𝓝 0)) :
    Tendsto (fun n => ∫⁻ q in K, ρ n q*g n (thermalMap σ α γ ((env n).val,q)))
      atTop (𝓝 0) := by
  let env₀ : PositiveEnvironment := ⟨(μ,0,(t₀,x,v)),hμ⟩
  let φ₀ := fun q => thermalMap σ α γ (env₀.val,q)
  have hc : ContinuousOn φ₀ K := by
    intro q hq
    exact (thermalControl_hasFDerivAt (σ := σ) hα hγ env₀ q (hKT hq)).continuousAt.continuousWithinAt
  obtain ⟨R,hR⟩ := hK.exists_bound_of_continuousOn hc
  let R' := max R 0+1
  have hR' : 0 < R' := by dsimp [R']; positivity
  have hu := thermalMap_compact_tendsto (σ := σ) hα hγ henv hK
    (fun q hq => hKT hq)
  have himage : ∀ᶠ n in atTop, ∀ q ∈ K,
      thermalMap σ α γ ((env n).val,q) ∈ closedBall (0 : State) R' := by
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp hu 1 (by norm_num)] with n hn
    intro q hq
    rw [mem_closedBall,dist_zero_right]
    have hd : ‖thermalMap σ α γ ((env n).val,q)-φ₀ q‖ < 1 := by
      have hd := hn q hq
      change dist (φ₀ q) (thermalMap σ α γ ((env n).val,q)) < 1 at hd
      rwa [dist_eq_norm,norm_sub_rev] at hd
    have hr := hR q hq
    have ht := norm_add_le (thermalMap σ α γ ((env n).val,q)-φ₀ q) (φ₀ q)
    rw [sub_add_cancel] at ht
    exact ht.trans (by dsimp [R']; linarith [le_max_left R 0])
  let g' := fun n => (closedBall (0 : State) R').indicator (g n)
  have hg' : ∀ n, Measurable (g' n) := fun n => (hg n).indicator isClosed_closedBall.measurableSet
  have hb' : ∀ n z, g' n z ≤ M := by
    intro n z
    exact (indicator_le_self _ _ z).trans (hgM n z)
  have hlim : Tendsto (fun n => ∫⁻ z, g' n z) atTop (𝓝 0) := by
    simpa only [g',lintegral_indicator isClosed_closedBall.measurableSet] using hL R' hR'
  have ht := thermal_compact_pullback_zero (σ := σ) hMityagin hα hγ hμ t₀ x v hv
    henv hK hKT hB hM hg' hρ hb' hlim
  apply ht.congr'
  filter_upwards [himage] with n hn
  apply setLIntegral_congr_fun hK.measurableSet
  intro q hq
  change ρ n q*g' n (thermalMap σ α γ ((env n).val,q)) =
    ρ n q*g n (thermalMap σ α γ ((env n).val,q))
  rw [show g' n (thermalMap σ α γ ((env n).val,q)) =
    g n (thermalMap σ α γ ((env n).val,q)) from indicator_of_mem (hn q hq) _]

end BoltzmannNonuniqueness.FiveGainMap

end

end

section

/-! # The five-gain output coordinates preserve physical kinetic volume -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.FiveGainMap

def toKinetic : State ≃ᵐ Published.KineticPhase :=
  (MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ)
    (MeasurableEquiv.prodCongr (MeasurableEquiv.toLp 2 V) (MeasurableEquiv.toLp 2 V))).trans
      MeasurableEquiv.prodAssoc.symm

theorem toKinetic_apply (z : State) :
    toKinetic z = ((z.1,WithLp.toLp 2 z.2.1),WithLp.toLp 2 z.2.2) := rfl

theorem toKinetic_measurePreserving : MeasurePreserving toKinetic := by
  have hV := PiLp.volume_preserving_toLp (Fin 3)
  have h := (MeasurePreserving.id (volume : Measure ℝ)).prod (hV.prod hV)
  have hA := (measurePreserving_prodAssoc (volume : Measure ℝ)
    (volume : Measure Published.Velocity) (volume : Measure Published.Velocity)).symm
  exact h.trans hA

end BoltzmannNonuniqueness.FiveGainMap

end

end

section

/-! # The five-gain pullback applied to physical kinetic densities -/

noncomputable section

open MeasureTheory Filter Set Metric
open scoped ENNReal Topology

namespace BoltzmannNonuniqueness.FiveGainMap

theorem toKinetic_continuous : Continuous toKinetic := by
  change Continuous (fun z : State =>
    ((z.1,WithLp.toLp 2 z.2.1),WithLp.toLp 2 z.2.2))
  exact (continuous_fst.prodMk ((PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).comp
    continuous_snd.fst)).prodMk ((PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).comp
      continuous_snd.snd)

theorem thermal_compact_pullback_zero_physical
    (hMityagin : Published.Mityagin2020FiveGainParameters)
    {σ μ : Fin 5 → ℝ} {α γ : ℝ} (hα : 0 ≤ α) (hγ : 0 ≤ γ)
    (hμ : ∀ i, 0 < μ i) (t₀ : ℝ) (x v : V) (hv : 0 < v 0^2+v 1^2)
    {env : ℕ → PositiveEnvironment}
    (henv : Tendsto env atTop (𝓝 (⟨(μ,0,(t₀,x,v)),hμ⟩ : PositiveEnvironment)))
    {K : Set ThermalControls} (hK : IsCompact K) (hKT : K ⊆ controlDomain)
    {g : ℕ → Published.KineticPhase → ℝ≥0∞}
    {ρ : ℕ → ThermalControls → ℝ≥0∞} {B M : ℝ≥0∞}
    (hB : B ≠ ∞) (hM : M ≠ ∞) (hg : ∀ n, Measurable (g n))
    (hρ : ∀ n q, q ∈ controlDomain → ρ n q ≤ B) (hgM : ∀ n z, g n z ≤ M)
    (hL : ∀ C : Set Published.KineticPhase, IsCompact C →
      Tendsto (fun n => ∫⁻ z in C, g n z) atTop (𝓝 0)) :
    Tendsto (fun n => ∫⁻ q in K,
      ρ n q*g n (toKinetic (thermalMap σ α γ ((env n).val,q)))) atTop (𝓝 0) := by
  apply thermal_compact_pullback_zero_local hMityagin hα hγ hμ t₀ x v hv henv hK hKT
    hB hM (fun n => (hg n).comp toKinetic.measurable) hρ (fun n z => hgM n (toKinetic z))
  intro R hR
  let C := toKinetic '' closedBall (0 : State) R
  have hC : IsCompact C := (isCompact_closedBall (0 : State) R).image toKinetic_continuous
  have hi (n : ℕ) : (∫⁻ z in closedBall (0 : State) R, g n (toKinetic z)) =
      ∫⁻ z in C, g n z := by
    have h := toKinetic_measurePreserving.setLIntegral_comp_preimage hC.measurableSet (hg n)
    simpa only [C,toKinetic.injective.preimage_image] using h
  simpa only [Function.comp_apply,hi] using hL C hC

end BoltzmannNonuniqueness.FiveGainMap

end

end

section

/-! # Bounded actual five-gain parameter densities

Each factor is the six-parameter density of the physical rescaled core.
Arbitrary retained-path masks are allowed, with their velocity and time
restrictions stated explicitly. The final lemma applies the proved thermal
map pullback theorem to these actual factors.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.JetCoreSheet

namespace BoltzmannNonuniqueness.FiveGainMap

def stagePrevious (colors : Fin 5 → Bool) (α γ : ℝ) (env : ThermalEnvironment)
    (q : ThermalControls) (i : Fin 5) : State :=
  thermalPath (fun i => JetPrototype.sign (colors i)) α γ env q i.val

def stagePosition (colors : Fin 5 → Bool) (α γ : ℝ) (env : ThermalEnvironment)
    (q : ThermalControls) (i : Fin 5) : V :=
  let z := stagePrevious colors α γ env q i
  z.2.1-(z.1-q.1.1 i) • z.2.2

def stagePoint (colors : Fin 5 → Bool) (α γ : ℝ) (env : ThermalEnvironment)
    (q : ThermalControls) (i : Fin 5) : Velocity :=
  parameterPoint α γ (env.1 i) (env.2.1 i) (q.1.1 i) (colors i)
    (jetPosition (stagePosition colors α γ env q i))
    (WithLp.toLp 2 (stagePrevious colors α γ env q i).2.2) (q.2 i) (q.1.2 i)

def stageDensity (colors : Fin 5 → Bool) (r η K α γ qexp : ℝ)
    (env : ThermalEnvironment) (q : ThermalControls) (i : Fin 5) : ℝ≥0∞ :=
  rescaledParameterDensity r η K α γ (env.1 i) (env.2.1 i) (q.1.1 i) qexp (colors i)
    (jetPosition (stagePosition colors α γ env q i))
    (WithLp.toLp 2 (stagePrevious colors α γ env q i).2.2) (q.2 i) (q.1.2 i)

def pathDensity (colors : Fin 5 → Bool) (r η K α γ qexp : ℝ)
    (env : ThermalEnvironment) (q : ThermalControls) : ℝ≥0∞ :=
  ∏ i : Fin 5, stageDensity colors r η K α γ qexp env q i

def stageGood (colors : Fin 5 → Bool) (α γ a b Vmax : ℝ)
    (env : ThermalEnvironment) (q : ThermalControls) (i : Fin 5) : Prop :=
  a ≤ q.1.1 i ∧ ‖WithLp.toLp 2 (stagePrevious colors α γ env q i).2.2‖ ≤ Vmax ∧
    b ≤ ‖transverse (stagePoint colors α γ env q i)‖

theorem stageDensity_bound {r K α γ qexp a b Vmax : ℝ}
    (hr : 0 < r) (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ)
    (hq : 0 ≤ qexp) (ha : 0 < a) (hb : 0 < b) (hV : 0 ≤ Vmax)
    (colors : Fin 5 → Bool) (η : ℝ) (env : PositiveEnvironment) (q : ThermalControls)
    (i : Fin 5) (hi : stageGood colors α γ a b Vmax env.val q i) :
    stageDensity colors r η K α γ qexp env.val q i ≤
      parameterSlabBound K α γ qexp a b Vmax :=
  rescaledParameterDensity_slab_bound hr hK hα hγ (env.property i) ha hi.1 hq hb hV
    η _ _ _ _ _ _ hi.2.1 hi.2.2

theorem masked_pathDensity_bound {r K α γ qexp a b Vmax : ℝ}
    (hr : 0 < r) (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ)
    (hq : 0 ≤ qexp) (ha : 0 < a) (hb : 0 < b) (hV : 0 ≤ Vmax)
    (colors : Fin 5 → Bool) (η : ℝ) (env : PositiveEnvironment)
    (q : ThermalControls) (m : ℝ≥0∞) (hm : m ≤ 1)
    (hgood : m ≠ 0 → ∀ i, stageGood colors α γ a b Vmax env.val q i) :
    m*pathDensity colors r η K α γ qexp env.val q ≤
      (parameterSlabBound K α γ qexp a b Vmax)^5 := by
  by_cases hz : m = 0
  · simp only [hz,zero_mul]
    exact zero_le
  have hp : pathDensity colors r η K α γ qexp env.val q ≤
      (parameterSlabBound K α γ qexp a b Vmax)^5 := by
    unfold pathDensity
    calc
      _ ≤ ∏ _i : Fin 5, parameterSlabBound K α γ qexp a b Vmax :=
        Finset.prod_le_prod (fun i _ => stageDensity_bound hr hK hα hγ hq ha hb hV
          colors η env q i (hgood hz i))
      _ = _ := by simp
  simpa only [one_mul] using mul_le_mul' hm hp

theorem five_gain_parameter_tendsto
    (hMityagin : Published.Mityagin2020FiveGainParameters)
    {K α γ qexp a b Vmax : ℝ} (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ)
    (hq : 0 ≤ qexp) (ha : 0 < a) (hb : 0 < b) (hV : 0 ≤ Vmax)
    (colors : Fin 5 → Bool) (η : ℝ) {μ : Fin 5 → ℝ} (hμ : ∀ i, 0 < μ i)
    (t₀ : ℝ) (x v : V) (hv : 0 < v 0^2+v 1^2)
    {env : ℕ → PositiveEnvironment}
    (henv : Tendsto env atTop (𝓝 (⟨(μ,0,(t₀,x,v)),hμ⟩ : PositiveEnvironment)))
    (r : ℕ → ℝ) (hr : ∀ n, 0 < r n)
    {D : Set ThermalControls} (hD : IsCompact D) (hDT : D ⊆ controlDomain)
    (mask : ℕ → ThermalControls → ℝ≥0∞)
    (hm : ∀ n q, q ∈ controlDomain → mask n q ≤ 1)
    (hgood : ∀ n q, q ∈ controlDomain → mask n q ≠ 0 →
      ∀ i, stageGood colors α γ a b Vmax (env n).val q i)
    {g : ℕ → Published.KineticPhase → ℝ≥0∞} {M : ℝ≥0∞}
    (hM : M ≠ ∞) (hg : ∀ n, Measurable (g n)) (hgM : ∀ n z, g n z ≤ M)
    (hL : ∀ C : Set Published.KineticPhase, IsCompact C →
      Tendsto (fun n => ∫⁻ z in C, g n z) atTop (𝓝 0)) :
    Tendsto (fun n => ∫⁻ q in D,
      (mask n q*pathDensity colors (r n) η K α γ qexp (env n).val q)*
        g n (toKinetic (thermalMap (fun i => JetPrototype.sign (colors i)) α γ ((env n).val,q))))
      atTop (𝓝 0) := by
  apply thermal_compact_pullback_zero_physical hMityagin hα.le hγ.le hμ t₀ x v hv henv hD hDT
    (B := (parameterSlabBound K α γ qexp a b Vmax)^5)
    (ENNReal.pow_ne_top (parameterSlabBound_ne_top K α γ qexp a b Vmax)) hM hg ?_ hgM hL
  intro n q hqD
  exact masked_pathDensity_bound (hr n) hK hα hγ hq ha hb hV colors η (env n) q
    (mask n q) (hm n q hqD) (hgood n q hqD)

end BoltzmannNonuniqueness.FiveGainMap

end

end

section

/-! # Measurability of the actual five-gain path density on positive times -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.JetCoreSheet

namespace BoltzmannNonuniqueness.FiveGainMap

attribute [local irreducible] thermalPath stagePrevious stagePosition stageDensity pathDensity
  rescaledParameterDensity

theorem thermalPath_continuous_positive {σ : Fin 5 → ℝ} {α γ : ℝ}
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (env : PositiveEnvironment) (k : ℕ) :
    Continuous (fun q : controlDomain => thermalPath σ α γ env.val q.val k) := by
  apply continuous_iff_continuousAt.mpr
  intro q
  have ha : ContinuousAt (fun y : ThermalInput => thermalPath σ α γ y.1 y.2 k)
      (env.val,q.val) :=
    (thermalPath_analytic hα hγ (env.val,q.val) env.property q.property k).continuousAt
  have hb : ContinuousAt (fun u : controlDomain => (env.val,u.val)) q :=
    (continuous_const.prodMk continuous_subtype_val).continuousAt
  exact ha.comp (f := fun u : controlDomain => (env.val,u.val)) (x := q) hb

theorem stageDensity_measurable_positive {r α γ : ℝ} (hr : 0 < r)
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (colors : Fin 5 → Bool) (η K qexp : ℝ)
    (env : PositiveEnvironment) (i : Fin 5) :
    Measurable (fun q : controlDomain => stageDensity colors r η K α γ qexp env.val q.val i) := by
  have hp : Continuous (fun q : controlDomain => stagePrevious colors α γ env.val q.val i) := by
    unfold stagePrevious
    exact thermalPath_continuous_positive hα hγ env i.val
  have ht : Continuous (fun q : controlDomain => q.val.1.1 i) := by fun_prop
  have hx : Continuous (fun q : controlDomain => stagePosition colors α γ env.val q.val i) := by
    unfold stagePosition
    exact hp.snd.fst.sub ((hp.fst.sub ht).smul hp.snd.snd)
  have hj : Continuous (jetPosition : V → JetPrototype.Space) := by
    unfold jetPosition VelocityWeight.transverse
    fun_prop
  have harg : Measurable (fun q : controlDomain =>
      (((q.val.1.1 i,jetPosition (stagePosition colors α γ env.val q.val i)),
        (WithLp.toLp 2 (stagePrevious colors α γ env.val q.val i).2.2,
          (q.val.2 i,q.val.1.2 i))) : ParameterArguments)) :=
    ((ht.prodMk (hj.comp hx)).prodMk
      (((PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).comp hp.snd.snd).prodMk
        (show Continuous (fun q : controlDomain => (q.val.2 i,q.val.1.2 i)) by fun_prop))).measurable
  have hm := (clamped_rescaledParameterDensity_measurable hr hα hγ (env.property i)
    η K (env.val.2.1 i) qexp (colors i)).comp harg
  unfold stageDensity
  convert hm using 1
  funext q
  dsimp only [Function.comp_apply]
  rw [max_eq_right (show 0 ≤ q.val.1.1 i from (q.property i).le)]

theorem pathDensity_measurable_positive {r α γ : ℝ} (hr : 0 < r)
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (colors : Fin 5 → Bool) (η K qexp : ℝ)
    (env : PositiveEnvironment) :
    Measurable (fun q : controlDomain => pathDensity colors r η K α γ qexp env.val q.val) := by
  unfold pathDensity
  exact Finset.measurable_prod _ (fun i _ =>
    stageDensity_measurable_positive hr hα hγ colors η K qexp env i)

theorem masked_path_integrand_measurable {r α γ : ℝ} (hr : 0 < r)
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (colors : Fin 5 → Bool) (η K qexp : ℝ)
    (env : PositiveEnvironment) {mask : ThermalControls → ℝ≥0∞} (hm : Measurable mask)
    {g : Published.KineticPhase → ℝ≥0∞} (hg : Measurable g) :
    Measurable (controlDomain.indicator (fun q =>
      (mask q*pathDensity colors r η K α γ qexp env.val q)*
        g (toKinetic (thermalMap (fun i => JetPrototype.sign (colors i)) α γ (env.val,q))))) := by
  classical
  apply measurable_of_restrict_of_restrict_compl controlDomain_open.measurableSet
  · have hmap : Continuous (fun q : controlDomain =>
        toKinetic (thermalMap (fun i => JetPrototype.sign (colors i)) α γ (env.val,q.val))) :=
      toKinetic_continuous.comp (thermalPath_continuous_positive hα hγ env 5)
    have h := ((hm.comp measurable_subtype_coe).mul
      (pathDensity_measurable_positive hr hα hγ colors η K qexp env)).mul (hg.comp hmap.measurable)
    convert h using 1
    funext q
    exact indicator_of_mem q.property _
  · have he : controlDomainᶜ.domRestrict (controlDomain.indicator (fun q =>
        (mask q*pathDensity colors r η K α γ qexp env.val q)*
          g (toKinetic (thermalMap (fun i => JetPrototype.sign (colors i)) α γ (env.val,q))))) =
        (fun _ => 0) := by
      funext q
      exact indicator_of_notMem q.property _
    rw [he]
    exact measurable_const

end BoltzmannNonuniqueness.FiveGainMap

end

end

section

/-! # Product volume for the five physical collision parameter blocks -/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace BoltzmannNonuniqueness.FiveGainMap

abbrev StageControls := (ℝ × V) × V

def packControls : (Fin 5 → StageControls) ≃ᵐ ThermalControls :=
  (MeasurableEquiv.arrowProdEquivProdArrow (ℝ × V) V (Fin 5)).trans
    (MeasurableEquiv.prodCongr (MeasurableEquiv.arrowProdEquivProdArrow ℝ V (Fin 5))
      (MeasurableEquiv.refl (Fin 5 → V)))

theorem packControls_apply (q : Fin 5 → StageControls) :
    packControls q = ((fun i => (q i).1.1,fun i => (q i).1.2),fun i => (q i).2) := rfl

theorem packControls_measurePreserving : MeasurePreserving packControls :=
  (volume_measurePreserving_arrowProdEquivProdArrow (ℝ × V) V (Fin 5)).trans
    ((volume_measurePreserving_arrowProdEquivProdArrow ℝ V (Fin 5)).prod
      (MeasurePreserving.id volume))

def integrateControls : (n : ℕ) → ((Fin n → StageControls) → ℝ≥0∞) → ℝ≥0∞
  | 0, F => F Fin.elim0
  | n+1, F => ∫⁻ p : StageControls, integrateControls n (fun q => F (Fin.cons p q))

theorem integrateControls_eq (n : ℕ) {F : (Fin n → StageControls) → ℝ≥0∞}
    (hF : Measurable F) : integrateControls n F = ∫⁻ q, F q := by
  induction n with
  | zero =>
    rw [Measure.volume_pi_eq_dirac (Fin.elim0 : Fin 0 → StageControls)]
    simp only [integrateControls,lintegral_dirac' _ hF]
  | succ n ih =>
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => StageControls) 0
    have he : MeasurePreserving e :=
      volume_preserving_piFinSuccAbove (fun _ : Fin (n+1) => StageControls) 0
    have heq (p : StageControls × (Fin n → StageControls)) :
        e.symm p = Fin.cons p.1 p.2 := by
      exact Fin.insertNth_zero' p.1 p.2
    have hcons : Measurable (fun p : StageControls × (Fin n → StageControls) =>
        F (Fin.cons p.1 p.2)) := by
      simpa only [Function.comp_def,heq] using hF.comp e.symm.measurable
    have hinner (p : StageControls) : Measurable (fun q => F (Fin.cons p q)) :=
      hcons.comp measurable_prodMk_left
    simp only [integrateControls,ih (hinner _)]
    have hprod := lintegral_prod (μ := (volume : Measure StageControls))
      (ν := (volume : Measure (Fin n → StageControls))) _ hcons.aemeasurable
    change (∫⁻ p, ∫⁻ q, F (Fin.cons p q)) = _
    rw [← hprod]
    simpa only [heq,Measure.volume_eq_prod] using he.symm.lintegral_comp hF

theorem five_gain_product_integral {F : ThermalControls → ℝ≥0∞} (hF : Measurable F) :
    integrateControls 5 (fun q => F (packControls q)) = ∫⁻ q, F q := by
  exact (integrateControls_eq 5 (F := fun q => F (packControls q))
    (hF.comp packControls.measurable)).trans
      (packControls_measurePreserving.lintegral_comp hF)

end BoltzmannNonuniqueness.FiveGainMap

end

end

section

/-! # A compact parameter box for all five retained collisions -/

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace BoltzmannNonuniqueness.FiveGainMap

def velocityParameterBall (R : ℝ) : Set V :=
  (WithLp.ofLp : Velocity → V) '' closedBall 0 R

theorem mem_velocityParameterBall (R : ℝ) (v : V) :
    v ∈ velocityParameterBall R ↔ ‖WithLp.toLp 2 v‖ ≤ R := by
  constructor
  · rintro ⟨w,hw,rfl⟩
    simpa only [mem_closedBall,dist_zero_right,WithLp.toLp_ofLp] using hw
  · intro hv
    refine ⟨WithLp.toLp 2 v,?_,rfl⟩
    simpa only [mem_closedBall,dist_zero_right] using hv

theorem velocityParameterBall_compact (R : ℝ) : IsCompact (velocityParameterBall R) :=
  (isCompact_closedBall (0 : Velocity) R).image (PiLp.continuous_ofLp 2 (fun _ : Fin 3 => ℝ))

def parameterBox (a T R : ℝ) : Set ThermalControls :=
  ((pi univ (fun _ : Fin 5 => Icc a T)) ×ˢ
    (pi univ (fun _ : Fin 5 => velocityParameterBall R))) ×ˢ
      (pi univ (fun _ : Fin 5 => velocityParameterBall 1))

theorem parameterBox_compact (a T R : ℝ) : IsCompact (parameterBox a T R) :=
  ((isCompact_univ_pi (fun _ : Fin 5 => isCompact_Icc)).prod
    (isCompact_univ_pi (fun _ : Fin 5 => velocityParameterBall_compact R))).prod
      (isCompact_univ_pi (fun _ : Fin 5 => velocityParameterBall_compact 1))

theorem mem_parameterBox (a T R : ℝ) (q : ThermalControls) :
    q ∈ parameterBox a T R ↔ ∀ i : Fin 5,
      q.1.1 i ∈ Icc a T ∧ ‖WithLp.toLp 2 (q.1.2 i)‖ ≤ R ∧
        ‖WithLp.toLp 2 (q.2 i)‖ ≤ 1 := by
  constructor
  · rintro ⟨⟨ht,hL⟩,hw⟩ i
    exact ⟨ht i (mem_univ i),(mem_velocityParameterBall R _).mp (hL i (mem_univ i)),
      (mem_velocityParameterBall 1 _).mp (hw i (mem_univ i))⟩
  · intro h
    exact ⟨⟨fun i _ => (h i).1,fun i _ => (mem_velocityParameterBall R _).mpr (h i).2.1⟩,
      fun i _ => (mem_velocityParameterBall 1 _).mpr (h i).2.2⟩

theorem parameterBox_subset_domain {a : ℝ} (ha : 0 < a) (T R : ℝ) :
    parameterBox a T R ⊆ controlDomain := by
  intro q hq i
  exact ha.trans_le ((mem_parameterBox a T R q).mp hq i).1.1

end BoltzmannNonuniqueness.FiveGainMap

end

end

end OAI
