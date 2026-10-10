import OAI.MathematicalPhysics.RapidForcing.ClassicalSolution
import OAI.MathematicalPhysics.RapidForcing.Energy
import OAI.MathematicalPhysics.RapidForcing.Uniqueness

namespace OAI

section
open scoped BigOperators ENNReal Topology NNReal InnerProductSpace
open Set MeasureTheory
namespace RapidForcing

lemma L2ContinuousOn.memLp {E : Type} [NormedAddCommGroup E]
    {f : Field E} {T t : ℝ} (hf : L2ContinuousOn f T) (ht : t ∈ Icc 0 T) :
    MemLp (f t) 2 volume := by
  obtain ⟨v, _, hv⟩ := hf
  exact (Lp.memLp (v t)).ae_eq (hv t ht)

@[simp] lemma spatialMulti_zero {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : Field E) : spatialMulti 0 f = f := by simp [spatialMulti]

lemma spatialMulti_single {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : Field E) (i : Fin 3) (n : ℕ) :
    spatialMulti (Pi.single i n) f = (spatialD i)^[n] f := by
  fin_cases i <;> simp [spatialMulti]

lemma order_single (i : Fin 3) (n : ℕ) : order (Pi.single i n) = n := by
  simp [order]

lemma EnergyRegularity.memLp_velocity {u : Field Space} {p : Field ℝ}
    (h : EnergyRegularity u p) {t : ℝ} (ht : 0 ≤ t) : MemLp (u t) 2 volume := by
  have he := (h t ht).1 0 (by simp [order])
  simpa using he.memLp (right_mem_Icc.mpr ht)

lemma EnergyRegularity.memLp_pressure {u : Field Space} {p : Field ℝ}
    (h : EnergyRegularity u p) {t : ℝ} (ht : 0 ≤ t) : MemLp (p t) 2 volume := by
  have he := (h t ht).2.2 0 (by simp [order])
  simpa using he.memLp (right_mem_Icc.mpr ht)

lemma EnergyRegularity.memLp_velocityD {u : Field Space} {p : Field ℝ}
    (h : EnergyRegularity u p) {t : ℝ} (ht : 0 ≤ t) (i : Fin 3) :
    MemLp (spaceD i (u t)) 2 volume := by
  have he := (h t ht).1 (Pi.single i 1) (by rw [order_single]; norm_num)
  have this := he.memLp (right_mem_Icc.mpr ht)
  rw [spatialMulti_single] at this
  exact this

lemma EnergyRegularity.memLp_velocityDD {u : Field Space} {p : Field ℝ}
    (h : EnergyRegularity u p) {t : ℝ} (ht : 0 ≤ t) (i : Fin 3) :
    MemLp (spaceD i (spaceD i (u t))) 2 volume := by
  have he := (h t ht).1 (Pi.single i 2) (by rw [order_single])
  have this := he.memLp (right_mem_Icc.mpr ht)
  rw [spatialMulti_single] at this
  exact this

lemma EnergyRegularity.memLp_pressureD {u : Field Space} {p : Field ℝ}
    (h : EnergyRegularity u p) {t : ℝ} (ht : 0 ≤ t) (i : Fin 3) :
    MemLp (spaceD i (p t)) 2 volume := by
  have he := (h t ht).2.2 (Pi.single i 1) (by rw [order_single])
  have this := he.memLp (right_mem_Icc.mpr ht)
  rw [spatialMulti_single] at this
  exact this

lemma timeD_sub {u v : Field Space} (hu : ∀ x, DifferentiableOn ℝ (fun t => u t x) (Ici 0))
    (hv : ∀ x, DifferentiableOn ℝ (fun t => v t x) (Ici 0)) {t : ℝ} (ht : 0 ≤ t) (x : Space) :
    timeD (fun t x => u t x - v t x) t x = timeD u t x - timeD v t x :=
  derivWithin_sub (hu x t ht) (hv x t ht)

lemma spaceD_sub_twice {u v : Space → Space}
    (hu : ContDiff ℝ 2 u) (hv : ContDiff ℝ 2 v) (i : Fin 3) :
    spaceD i (spaceD i (fun x => u x - v x)) =
      fun x => spaceD i (spaceD i u) x - spaceD i (spaceD i v) x := by
  rw [spaceD_sub (hu.differentiable (by norm_num)) (hv.differentiable (by norm_num))]
  exact spaceD_sub ((spaceD_contDiff hu i).differentiable (by norm_num))
    ((spaceD_contDiff hv i).differentiable (by norm_num)) i

lemma advection_difference {u v : Space → Space}
    (hu : Differentiable ℝ u) (hv : Differentiable ℝ v) (x : Space) :
    (∑ i, v x i • spaceD i v x) - (∑ i, u x i • spaceD i u x) =
      (∑ i, v x i • spaceD i (fun z => v z - u z) x) +
        fderiv ℝ u x (v x - u x) := by
  simp only [spaceD_sub hv hu, smul_sub, Finset.sum_sub_distrib,
    spaceD_sum, map_sub]
  abel

lemma navierStokes_difference_energy {ν : ℝ} (hν : 0 ≤ ν)
    {f u v : Field Space} {p q : Field ℝ}
    (hu : Classical u p) (hv : Classical v q)
    (heu : EnergyRegularity u p) (hev : EnergyRegularity v q)
    (hnsu : NavierStokes ν f u p) (hnsv : NavierStokes ν f v q)
    {t C B A : ℝ} (ht : 0 ≤ t)
    (huC : ∀ x, ‖fderiv ℝ (u t) x‖ ≤ C)
    (hvB : ∀ x, ‖v t x‖ ≤ B) (huA : ∀ x, ‖u t x‖ ≤ A) :
    (∫ x, ⟪v t x - u t x, timeD v t x - timeD u t x⟫_ℝ) ≤
      C * ∫ x, ‖v t x - u t x‖ ^ 2 := by
  let w : Space → Space := fun x => v t x - u t x
  let r : Space → ℝ := fun x => q t x - p t x
  have hu₂ := (hu.1 t ht).1
  have hv₂ := (hv.1 t ht).1
  have hp₁ := (hu.1 t ht).2
  have hq₁ := (hv.1 t ht).2
  have hu' := hu₂.differentiable (by norm_num)
  have hv' := hv₂.differentiable (by norm_num)
  have hp' := hp₁.differentiable (by norm_num)
  have hq' := hq₁.differentiable (by norm_num)
  have hw1 (i : Fin 3) : MemLp (spaceD i w) 2 volume := by
    dsimp [w]; rw [spaceD_sub hv' hu']
    exact (hev.memLp_velocityD ht i).sub (heu.memLp_velocityD ht i)
  have hw2 (i : Fin 3) : MemLp (spaceD i (spaceD i w)) 2 volume := by
    dsimp [w]; rw [spaceD_sub_twice hv₂ hu₂]
    exact (hev.memLp_velocityDD ht i).sub (heu.memLp_velocityDD ht i)
  have hr1 (i : Fin 3) : MemLp (spaceD i r) 2 volume := by
    dsimp [r]; rw [spaceD_sub hq' hp']
    exact (hev.memLp_pressureD ht i).sub (heu.memLp_pressureD ht i)
  have hdv (x : Space) : ∑ i, spaceD i (v t) x i = 0 := hnsv.2.1 t ht x
  have hdw (x : Space) : ∑ i, spaceD i w x i = 0 := by
    dsimp [w]
    simp_rw [spaceD_sub hv' hu', PiLp.sub_apply, Finset.sum_sub_distrib]
    change divergence v t x - divergence u t x = 0
    rw [hnsv.2.1 t ht x, hnsu.2.1 t ht x, sub_self]
  have hbound := spatial_energy_bound hu₂ hv' (hv₂.sub hu₂) (hq'.sub hp')
    ((hev.memLp_velocity ht).sub (heu.memLp_velocity ht))
    ((hev.memLp_pressure ht).sub (heu.memLp_pressure ht))
    (hev.memLp_velocityD ht) hw1 hw2 hr1 hν huC hvB
    (fun x => (norm_sub_le (v t x) (u t x)).trans (add_le_add (hvB x) (huA x))) hdv hdw
  have heq (x : Space) : timeD v t x - timeD u t x =
      -(∑ i, spaceD i r x • basis i) + ν • (∑ i, spaceD i (spaceD i w) x) -
        (∑ i, v t x i • spaceD i w x) - fderiv ℝ (u t) x (w x) := by
    have ha := advection_difference hu' hv' x
    change advection v t x - advection u t x =
      (∑ i, v t x i • spaceD i w x) + fderiv ℝ (u t) x (w x) at ha
    have hl : (∑ i, spaceD i (spaceD i w) x) = laplace v t x - laplace u t x := by
      simp only [w, spaceD_sub_twice hv₂ hu₂, Finset.sum_sub_distrib]
      rfl
    have hg : (∑ i, spaceD i r x • basis i) = gradient q t x - gradient p t x := by
      simp only [r, spaceD_sub hq' hp', sub_smul, Finset.sum_sub_distrib]
      rfl
    rw [hl, hg, smul_sub]
    have hvns := hnsv.1 t ht x
    have huns := hnsu.1 t ht x
    linear_combination (norm := module) hvns - huns - ha
  change (∫ x, ⟪w x, -(∑ i, spaceD i r x • basis i) +
    ν • (∑ i, spaceD i (spaceD i w) x) - (∑ i, v t x i • spaceD i w x) -
    fderiv ℝ (u t) x (w x)⟫_ℝ) ≤ C * ∫ x, ‖w x‖ ^ 2 at hbound
  simpa only [← heq] using hbound

lemma energy_zero {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {v v' : ℝ → E} {T C : ℝ} (hT : 0 ≤ T)
    (hv : ContinuousOn v (Icc 0 T))
    (hd : ∀ t ∈ Icc 0 T, HasDerivWithinAt v (v' t) (Icc 0 T) t)
    (h0 : v 0 = 0)
    (hb : ∀ t ∈ Icc 0 T, ⟪v t, v' t⟫_ℝ ≤ C * ‖v t‖ ^ 2) :
    ∀ t ∈ Icc 0 T, v t = 0 := by
  let e : ℝ → ℝ := fun s => Real.exp (-2 * C * s) * ‖v s‖ ^ 2
  let e' : ℝ → ℝ := fun s => Real.exp (-2 * C * s) *
    (2 * ⟪v s, v' s⟫_ℝ - 2 * C * ‖v s‖ ^ 2)
  have he : ContinuousOn e (Icc 0 T) :=
    ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn).mul (hv.norm.pow 2)
  have he' (s : ℝ) (hs : s ∈ Icc 0 T) : HasDerivWithinAt e (e' s) (Icc 0 T) s := by
    have h := (((hasDerivAt_id s).const_mul (-2 * C)).exp.hasDerivWithinAt).mul (hd s hs).norm_sq
    convert h using 1 <;> first | rfl | (dsimp only [e, e', id_eq]; ring)
  have hn (s : ℝ) (hs : s ∈ Icc 0 T) : e' s ≤ 0 := by
    apply mul_nonpos_of_nonneg_of_nonpos (Real.exp_nonneg _)
    have := hb s hs
    linarith
  have hanti : AntitoneOn e (Icc 0 T) :=
    antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 T) he
      (fun s hs => (he' s (interior_subset hs)).mono interior_subset)
      (fun s hs => hn s (interior_subset hs))
  intro t ht
  have h := hanti (left_mem_Icc.mpr hT) ht ht.1
  have hle : Real.exp (-2 * C * t) * ‖v t‖ ^ 2 ≤ 0 := by simpa [e, h0] using h
  have hz : ‖v t‖ ^ 2 = 0 := le_antisymm (nonpos_of_mul_nonpos_right hle (Real.exp_pos _))
    (sq_nonneg _)
  exact norm_eq_zero.mp (eq_zero_of_pow_eq_zero hz)

theorem energy_velocity_unique {ν : ℝ} (hν : 0 ≤ ν)
    {f u v : Field Space} {p q : Field ℝ}
    (hu : Classical u p) (hv : Classical v q)
    (heu : EnergyClass u p) (hev : EnergyCompetitor v q)
    (hnsu : NavierStokes ν f u p) (hnsv : NavierStokes ν f v q) :
    ∀ t : ℝ, 0 ≤ t → v t = u t := by
  intro t ht
  obtain ⟨U, U', hU, hU', huCoe, hu'Coe, hdU⟩ := (heu.1 t ht).2.1
  obtain ⟨V, V', hV, hV', hvCoe, hv'Coe, hdV⟩ := (hev.1 t ht).2.1
  obtain ⟨C, hC⟩ := heu.2 t ht
  obtain ⟨B, hB⟩ := hev.2 t ht
  let W := fun s => V s - U s
  let W' := fun s => V' s - U' s
  have hCoe (s : ℝ) (hs : s ∈ Icc 0 t) :
      ((W s) : Space → Space) =ᵐ[volume] (fun x => v s x - u s x) := by
    filter_upwards [Lp.coeFn_sub (V s) (U s), hvCoe s hs, huCoe s hs] with x hw hv hu
    change (V s - U s) x = _
    rw [hw, Pi.sub_apply, hv, hu]
  have h'Coe (s : ℝ) (hs : s ∈ Icc 0 t) :
      ((W' s) : Space → Space) =ᵐ[volume] (fun x => timeD v s x - timeD u s x) := by
    filter_upwards [Lp.coeFn_sub (V' s) (U' s), hv'Coe s hs, hu'Coe s hs] with x hw hv hu
    change (V' s - U' s) x = _
    rw [hw, Pi.sub_apply, hv, hu]
  have h0 : W 0 = 0 := by
    apply Lp.ext
    filter_upwards [hCoe 0 (left_mem_Icc.mpr ht), Lp.coeFn_zero (E := Space) (p := 2)
      (μ := (volume : Measure Space))] with x hw hz
    rw [hw, hnsv.2.2 x, hnsu.2.2 x, sub_self, hz]
    rfl
  have henergy (s : ℝ) (hs : s ∈ Icc 0 t) : ⟪W s, W' s⟫_ℝ ≤ C * ‖W s‖ ^ 2 := by
    have hi : ⟪W s, W' s⟫_ℝ = ∫ x, ⟪v s x - u s x, timeD v s x - timeD u s x⟫_ℝ := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hCoe s hs, h'Coe s hs] with x hw hw'
      rw [hw, hw']
    have hn : ‖W s‖ ^ 2 = ∫ x, ‖v s x - u s x‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hCoe s hs] with x hx
      rw [hx, real_inner_self_eq_norm_sq]
    rw [hi, hn]
    apply navierStokes_difference_energy hν hu hv heu.1 hev.1 hnsu hnsv hs.1
    · intro x
      exact (le_add_of_nonneg_left (norm_nonneg (u s x))).trans (hC s hs x)
    · exact hB s hs
    · intro x
      exact (le_add_of_nonneg_right (norm_nonneg (fderiv ℝ (u s) x))).trans (hC s hs x)
  have heq : W t = 0 := energy_zero ht (hV.sub hU)
    (fun s hs => (hdV s hs).sub (hdU s hs)) h0 henergy t (right_mem_Icc.mpr ht)
  apply ((hv.1 t ht).1.continuous.ae_eq_iff_eq volume (hu.1 t ht).1.continuous).mp
  have h := hCoe t (right_mem_Icc.mpr ht)
  rw [heq] at h
  filter_upwards [h, Lp.coeFn_zero (E := Space) (p := 2) (μ := (volume : Measure Space))]
    with x hx hz
  rw [hz] at hx
  exact sub_eq_zero.mp hx.symm

lemma volume_space_univ : volume (univ : Set Space) = ∞ := by
  have h := (PiLp.volume_preserving_ofLp (Fin 3)).measure_preimage MeasurableSet.univ
  change volume (univ : Set Space) = volume (univ : Set (Fin 3 → ℝ)) at h
  rw [h, ← pi_univ (univ : Set (Fin 3)), volume_pi_pi]
  simp

lemma gradient_apply (p : Field ℝ) (t : ℝ) (x : Space) (i : Fin 3) :
    gradient p t x i = spatialD i p t x := by
  simp [gradient, basis, Pi.single_apply, apply_ite]

theorem energy_pressure_unique {ν : ℝ} {f u v : Field Space} {p q : Field ℝ}
    (hu : Classical u p) (hv : Classical v q)
    (heu : EnergyRegularity u p) (hev : EnergyRegularity v q)
    (hnsu : NavierStokes ν f u p) (hnsv : NavierStokes ν f v q)
    (heq : ∀ t : ℝ, 0 ≤ t → v t = u t) :
    ∀ t : ℝ, 0 ≤ t → ∀ x : Space, q t x = p t x := by
  intro t ht
  have htime (x : Space) : timeD v t x = timeD u t x := by
    apply derivWithin_congr (fun s hs => congrFun (heq s hs) x) (congrFun (heq t ht) x)
  have hgrad (x : Space) : gradient q t x = gradient p t x := by
    have h := hnsv.1 t ht x
    have h' := hnsu.1 t ht x
    have ha : advection v t x = advection u t x := by
      simp only [advection, spatialD, heq t ht]
    have hl : laplace v t x = laplace u t x := by
      unfold laplace spatialD
      rw [heq t ht]
    rw [htime, ha, hl] at h
    linear_combination (norm := module) h - h'
  let r : Space → ℝ := fun x => q t x - p t x
  have hp := (hu.1 t ht).2.differentiable (by norm_num)
  have hq := (hv.1 t ht).2.differentiable (by norm_num)
  have hdr (x : Space) : fderiv ℝ r x = 0 := by
    ext z
    have hd (i : Fin 3) : fderiv ℝ r x (basis i) = 0 := by
      have h := congrArg (fun z : Space => z i) (hgrad x)
      rw [gradient_apply, gradient_apply] at h
      simpa [r, fderiv_fun_sub (hq x) (hp x), spatialD] using sub_eq_zero.mpr h
    calc
      (fderiv ℝ r x) z = (fderiv ℝ r x) (∑ i, z i • basis i) := by rw [sum_basis]
      _ = 0 := by simp [map_sum, hd]
  have hconst : r = fun _ => r 0 := funext fun x =>
    is_const_of_fderiv_eq_zero (hq.sub hp) hdr x 0
  have hr : MemLp r 2 volume := (hev.memLp_pressure ht).sub (heu.memLp_pressure ht)
  rw [hconst] at hr
  have hz := (memLp_const_iff (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by simp)).mp hr
  have hz : r 0 = 0 := hz.resolve_right (by simp)
  intro x
  exact sub_eq_zero.mp ((congrFun hconst x).trans hz)

theorem energy_solution_unique {ν : ℝ} (hν : 0 ≤ ν)
    {f u : Field Space} {p : Field ℝ} (hu : Classical u p)
    (heu : EnergyClass u p) (hnsu : NavierStokes ν f u p) :
    UniqueEnergySolution ν f u p := by
  refine ⟨hu, heu, hnsu, ?_⟩
  intro v q hv hev hnsv
  have heq := energy_velocity_unique hν hu hv heu hev hnsu hnsv
  have hp := energy_pressure_unique hu hv heu.1 hev.1 hnsu hnsv heq
  exact fun t ht x => ⟨congrFun (heq t ht) x, hp t ht x⟩

theorem addressed_uniqueEnergySolution {ν : ℝ} (hν : 0 ≤ ν) (M : Machine) (w : M.Input) :
    UniqueEnergySolution ν (addressedForce ν M w) (addressedVelocity M w) (fun _ _ => 0) := by
  exact energy_solution_unique hν (addressed_classical_solution ν M w).2.2.2.2.1
    (addressed_energyClass M w) (addressed_pointwise_equations ν M w)

end RapidForcing

end

end OAI
