import OAI.Probability.LatticePassage.LocalPassage

namespace OAI

namespace CompanionFPP
open MeasureTheory Real

lemma integrable_trail_exp {x y : Vertex} (p : lattice.Walk x y) (hp : p.IsTrail) :
    Integrable (fun ω : Environment => exp (pathCost ω p / 2)) environmentLaw := by
  apply (lintegral_ofReal_ne_top_iff_integrable (by fun_prop)
    (by filter_upwards [] with ω; positivity)).mp
  rw [trail_positive_moment p hp]
  finiteness

lemma integral_trail_exp {x y : Vertex} (p : lattice.Walk x y) (hp : p.IsTrail) :
    (∫ ω : Environment, exp (pathCost ω p / 2) ∂environmentLaw) = (2 : ℝ)^p.length := by
  rw [integral_eq_lintegral_of_nonneg_ae (by filter_upwards [] with ω; positivity)
    (by fun_prop), trail_positive_moment p hp]
  simp

lemma integrable_trail_cost {x y : Vertex} (p : lattice.Walk x y) (hp : p.IsTrail) :
    Integrable (fun ω : Environment => pathCost ω p) environmentLaw := by
  apply ((integrable_trail_exp p hp).const_mul 2).mono' (by fun_prop)
  filter_upwards [all_edge_weights_positive] with ω hω
  rw [Real.norm_eq_abs, abs_of_nonneg (pathCost_nonneg ω (fun e => (hω e).le) p)]
  have he := add_one_le_exp (pathCost ω p / 2)
  linarith

lemma localPassageTime_le_pathCost (ω : Environment) {x y : Vertex} {R : ℕ}
    (p : lattice.Walk x y) (hp : p.IsPath) (hl : p.length < R) :
    localPassageTime ω x y R ≤ pathCost ω p :=
  csInf_le (local_costs_finite ω x y R).bddBelow ⟨p,hp,hl,rfl⟩

lemma passageTime_le_localPassageTime (ω : Environment) (hω : ∀ e, 0 ≤ ω e)
    (x y : Vertex) (R : ℕ) (hR : latticeDistance x y < R) :
    passageTime ω x y ≤ localPassageTime ω x y R := by
  obtain ⟨p,_,_,hp⟩ := local_geodesic_exists ω x y R hR
  rw [← hp]
  exact passageTime_le_pathCost ω hω p

theorem integrable_localPassageTime (x y : Vertex) (R : ℕ)
    (hR : latticeDistance x y < R) :
    Integrable (fun ω : Environment => localPassageTime ω x y R) environmentLaw := by
  obtain ⟨p,hp,hl⟩ := coordinate_path x y
  apply (integrable_trail_cost p hp.isTrail).mono' (by fun_prop)
  filter_upwards [all_edge_weights_positive] with ω hω
  have ht := passageTime_nonneg ω (fun e => (hω e).le) (lattice_walk x y)
  have hn := passageTime_le_localPassageTime ω (fun e => (hω e).le) x y R hR
  rw [Real.norm_eq_abs, abs_of_nonneg (ht.trans hn)]
  exact localPassageTime_le_pathCost ω p hp (hl.trans_lt hR)

private lemma rare_cost_pointwise (S u : ℝ) (hu : 0 ≤ u) (P : Prop) [Decidable P] :
    (if P then S else 0) ≤ (if P then u else 0) + 4*exp (-u/4)*exp (S/2) := by
  by_cases hP : P
  · simp only [ite_eq_left hP]
    by_cases hs : S ≤ u
    · have : 0 ≤ 4*exp (-u/4)*exp (S/2) := by positivity
      linarith
    · have he := add_one_le_exp (S/4)
      have he' : exp (S/4) ≤ exp (-u/4 + S/2) := by
        rw [exp_le_exp]
        linarith
      rw [mul_assoc, ← exp_add]
      linarith
  · simp only [ite_eq_right hP, zero_add]
    positivity

theorem rare_cost_integral {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ] (S : Ω → ℝ) (hS : Integrable S μ)
    (he : Integrable (fun ω => exp (S ω / 2)) μ) (F : Set Ω) (hF : MeasurableSet F)
    (u : ℝ) (hu : 0 ≤ u) :
    (∫ ω, F.indicator S ω ∂μ) ≤
      u * μ.real F + 4*exp (-u/4) * (∫ ω, exp (S ω/2) ∂μ) := by
  classical
  have hbound := integral_mono_ae (hS.indicator hF)
    (((integrable_const u).indicator hF).add (he.const_mul (4*exp (-u/4))))
    (Filter.Eventually.of_forall (fun ω => rare_cost_pointwise (S ω) u hu (ω ∈ F)))
  simp only [Pi.add_apply] at hbound
  rw [integral_add ((integrable_const u).indicator hF) (he.const_mul (4*exp (-u/4))),
    integral_const_mul, integral_indicator_const u hF] at hbound
  simpa [smul_eq_mul, mul_comm] using hbound

theorem localPassageTime_mean_error (x y : Vertex) (R : ℕ) (hR : 1 ≤ R)
    (hscale : 40*latticeDistance x y ≤ R) :
    (∫ ω : Environment, localPassageTime ω x y R - passageTime ω x y ∂environmentLaw) ≤
      (R : ℝ) * ((11/3 : ℝ)*exp (-(log 2/40)*R)) +
        4*exp (-(R : ℝ)/4)*(2 : ℝ)^latticeDistance x y := by
  classical
  have hd : latticeDistance x y < R := by omega
  obtain ⟨p,hp,hl⟩ := coordinate_path x y
  let F := {ω : Environment | localPassageTime ω x y R ≠ passageTime ω x y}
  have hF : MeasurableSet F := (measurableSet_eq_fun (measurable_localPassageTime x y R)
    (measurable_passageTime x y)).compl
  have hcost := integrable_trail_cost p hp.isTrail
  have hb : (∫ ω : Environment, localPassageTime ω x y R - passageTime ω x y ∂environmentLaw) ≤
      ∫ ω, F.indicator (fun ω => pathCost ω p) ω ∂environmentLaw := by
    apply integral_mono_ae ((integrable_localPassageTime x y R hd).sub (integrable_passageTime x y))
      (hcost.indicator hF)
    filter_upwards [all_edge_weights_positive] with ω hω
    simp only [Pi.sub_apply]
    by_cases hf : ω ∈ F
    · rw [Set.indicator_of_mem hf]
      have h₁ := localPassageTime_le_pathCost ω p hp (hl.trans_lt hd)
      have h₂ := passageTime_nonneg ω (fun e => (hω e).le) (lattice_walk x y)
      linarith
    · rw [Set.indicator_of_notMem hf]
      have heq : localPassageTime ω x y R = passageTime ω x y := not_not.mp hf
      rw [heq, sub_self]
  apply hb.trans
  have hm := rare_cost_integral environmentLaw (fun ω => pathCost ω p) hcost
    (integrable_trail_exp p hp.isTrail) F hF (R : ℝ) (by positivity)
  rw [integral_trail_exp p hp.isTrail] at hm
  apply hm.trans
  apply add_le_add
  · exact mul_le_mul_of_nonneg_left (localPassageTime_failure_probability x y R hR hscale)
      (Nat.cast_nonneg _)
  · gcongr
    norm_num

theorem localPassageTime_mean_error_exponential (x y : Vertex) (R : ℕ) (hR : 1 ≤ R)
    (hscale : 40*latticeDistance x y ≤ R) :
    (∫ ω : Environment, localPassageTime ω x y R - passageTime ω x y ∂environmentLaw) ≤
      ((11/3 : ℝ)*R + 4) * exp (-(log 2/40)*R) := by
  apply (localPassageTime_mean_error x y R hR hscale).trans
  have hn : 0 ≤ (R : ℝ) := Nat.cast_nonneg _
  have hl : 40*(latticeDistance x y : ℝ) ≤ R := by exact_mod_cast hscale
  have hlog : log (2 : ℝ) ≤ 1 := by
    have := log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hpow : (2 : ℝ)^latticeDistance x y =
      exp ((latticeDistance x y : ℝ)*log 2) := by
    rw [exp_nat_mul, exp_log (by norm_num : (0 : ℝ) < 2)]
  have hb : exp (-(R : ℝ)/4) * (2 : ℝ)^latticeDistance x y ≤
      exp (-(log 2/40)*R) := by
    rw [hpow, ← exp_add, exp_le_exp]
    have hd : 0 ≤ (latticeDistance x y : ℝ) := Nat.cast_nonneg _
    nlinarith
  nlinarith

end CompanionFPP

end OAI
