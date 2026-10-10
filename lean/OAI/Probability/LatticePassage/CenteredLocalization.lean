import OAI.Probability.LatticePassage.NaturalMoment

namespace OAI

namespace CompanionFPP
open MeasureTheory Real

lemma mean_passageTime_nonneg (x y : Vertex) :
    0 ≤ ∫ ω : Environment, passageTime ω x y ∂environmentLaw := by
  apply integral_nonneg_of_ae
  filter_upwards [passageTime_properties] with ω hω
  exact hω.1 x y

theorem passageTime_centered_large (x y : Vertex) (hd : 1 ≤ latticeDistance x y)
    (u : ℝ) (hu : 4*(latticeDistance x y : ℝ) ≤ u) :
    environmentLaw.real {ω : Environment |
      u ≤ |passageTime ω x y - ∫ η : Environment, passageTime η x y ∂environmentLaw|} ≤
      exp (-u/4) := by
  have hm := mean_passageTime_le_distance x y
  have hm0 := mean_passageTime_nonneg x y
  have hd' : (1 : ℝ) ≤ latticeDistance x y := by exact_mod_cast hd
  have hsub : environmentLaw {ω : Environment |
      u ≤ |passageTime ω x y - ∫ η : Environment, passageTime η x y ∂environmentLaw|} ≤
      environmentLaw {ω : Environment | u ≤ passageTime ω x y} := by
    apply measure_mono_ae
    filter_upwards [passageTime_properties] with ω hω
    intro he
    have hn := hω.1 x y
    rcases le_abs.mp he with he | he <;> linarith
  apply (ENNReal.toReal_mono (measure_ne_top _ _) hsub).trans
  apply (passageTime_upper_tail x y u).trans
  rw [show (2 : ℝ)^latticeDistance x y = exp ((latticeDistance x y : ℝ)*log 2) by
    rw [exp_nat_mul, exp_log (by norm_num : (0 : ℝ) < 2)], ← exp_add, exp_le_exp]
  have hlog := log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  nlinarith

theorem passageTime_centered_large_sqrt (x y : Vertex) (hd : 1 ≤ latticeDistance x y)
    (t : ℝ) (ht : 4*sqrt (latticeDistance x y) ≤ t) :
    environmentLaw.real {ω : Environment |
      t*sqrt (latticeDistance x y) ≤
        |passageTime ω x y - ∫ η : Environment, passageTime η x y ∂environmentLaw|} ≤
      exp (-t/4) := by
  have hd' : (1 : ℝ) ≤ latticeDistance x y := by exact_mod_cast hd
  have hs := sqrt_nonneg (latticeDistance x y : ℝ)
  have hsq := sq_sqrt (show 0 ≤ (latticeDistance x y : ℝ) by positivity)
  have hs1 : 1 ≤ sqrt (latticeDistance x y : ℝ) := by nlinarith
  have ht0 : 0 ≤ t := by linarith
  apply (passageTime_centered_large x y hd (t*sqrt (latticeDistance x y))
    (by nlinarith)).trans
  rw [exp_le_exp]
  nlinarith

theorem localPassageTime_center_shift (x y : Vertex) (R : ℕ) (hR : 1 ≤ R)
    (hscale : 40*latticeDistance x y ≤ R) :
    |(∫ ω : Environment, localPassageTime ω x y R ∂environmentLaw) -
      (∫ ω : Environment, passageTime ω x y ∂environmentLaw)| ≤
        ((11/3 : ℝ)*R+4)*exp (-(log 2/40)*R) := by
  have hd : latticeDistance x y < R := by omega
  have hn : 0 ≤ (∫ ω : Environment, localPassageTime ω x y R ∂environmentLaw) -
      (∫ ω : Environment, passageTime ω x y ∂environmentLaw) := by
    apply sub_nonneg.mpr
    apply integral_mono_ae (integrable_passageTime x y) (integrable_localPassageTime x y R hd)
    filter_upwards [all_edge_weights_positive] with ω hω
    exact passageTime_le_localPassageTime ω (fun e => (hω e).le) x y R hd
  rw [abs_of_nonneg hn, ← integral_sub (integrable_localPassageTime x y R hd)
    (integrable_passageTime x y)]
  exact localPassageTime_mean_error_exponential x y R hR hscale

theorem passageTime_centered_localization (x y : Vertex) (R : ℕ) (hR : 1 ≤ R)
    (hscale : 40*latticeDistance x y ≤ R) (u : ℝ) :
    environmentLaw.real {ω : Environment |
      u ≤ |passageTime ω x y - ∫ η : Environment, passageTime η x y ∂environmentLaw|} ≤
      (11/3 : ℝ)*exp (-(log 2/40)*R) +
      environmentLaw.real {ω : Environment |
        u - ((11/3 : ℝ)*R+4)*exp (-(log 2/40)*R) ≤
          |localPassageTime ω x y R -
            ∫ η : Environment, localPassageTime η x y R ∂environmentLaw|} := by
  let F := {ω : Environment | localPassageTime ω x y R ≠ passageTime ω x y}
  let G := {ω : Environment |
    u - ((11/3 : ℝ)*R+4)*exp (-(log 2/40)*R) ≤
      |localPassageTime ω x y R -
        ∫ η : Environment, localPassageTime η x y R ∂environmentLaw|}
  have hs : {ω : Environment |
      u ≤ |passageTime ω x y - ∫ η : Environment, passageTime η x y ∂environmentLaw|} ⊆
      F ∪ G := by
    intro ω hω
    by_cases hf : ω ∈ F
    · exact Or.inl hf
    · right
      have he : localPassageTime ω x y R = passageTime ω x y := not_not.mp hf
      have hb := abs_add_le (localPassageTime ω x y R -
        ∫ η : Environment, localPassageTime η x y R ∂environmentLaw)
        ((∫ η : Environment, localPassageTime η x y R ∂environmentLaw) -
        ∫ η : Environment, passageTime η x y ∂environmentLaw)
      rw [sub_add_sub_cancel, he] at hb
      have hc := localPassageTime_center_shift x y R hR hscale
      change u ≤ |passageTime ω x y - ∫ η : Environment, passageTime η x y ∂environmentLaw| at hω
      change u - ((11/3 : ℝ)*R+4)*exp (-(log 2/40)*R) ≤
        |localPassageTime ω x y R - ∫ η : Environment, localPassageTime η x y R ∂environmentLaw|
      rw [he]
      linarith
  apply (measureReal_mono hs).trans
  apply (measureReal_union_le F G).trans
  exact add_le_add (localPassageTime_failure_probability x y R hR hscale) le_rfl

end CompanionFPP

end OAI
