import OAI.Geometry.Convex.GeneralMahler.BoundField
import OAI.Geometry.Convex.GeneralMahler.GaussianTail

namespace OAI
/-! §02 growth estimates for negative and positive bias layers. -/
noncomputable section
open MeasureTheory MeasureTheory.Measure Filter Set Real Metric
open scoped Topology ENNReal NNReal RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator
namespace GeneralMahler
open Layers
variable {m : ℕ} [NeZero m]
namespace ProjField
variable (m) {K : ℝ}
theorem uniform_X_neg (hk : 1 ≤ K) :
    ∃ C ≥ (0:ℝ), ∀ q : ProjField m, q.Bound K → ∀ s ≥ (0:ℝ), ∀ x : Rn m,
      ‖q.XT (-s) x‖ ≤ C*(1+‖x‖) := by
  have hp : 0 < K := lt_of_lt_of_le zero_lt_one hk
  let d : ℝ := (√(2*π))⁻¹
  have hd : 0 ≤ d := by dsimp [d]; positivity
  let C := K*(m*d+1+J m)
  have H := j_nonneg m
  have hm : 0 < (m:ℝ) := m_pos
  refine ⟨C,by dsimp [C]; positivity,?_⟩
  intro q hq s hs x
  have he := norm_le_mean_error (q.X_int (-s))
    (fun x y => XT_lip' hq x y (-s)) hp.le x
  have hh := hq.X_mean (-s)
  have hw : a (-s) ≤ d := (a_high s hs).trans (phi_bdd s)
  have hb := mul_le_mul_of_nonneg_left hw (show 0 ≤ K*m by positivity)
  apply he.trans
  have hx := norm_nonneg x
  have hv : K*m*d + K*J m+K ≤ C := by dsimp [C]; linarith
  have hc : K ≤ C := by
    dsimp only [C]; nlinarith [mul_nonneg hd hm.le]
  nlinarith

omit [NeZero m] in
theorem norm_IP_integrable (q : ProjField m) (s:ℝ) :
    Integrable (fun g => ⟪q.XT s g,q.Z g⟫) (normal m) := by
  let f := q.XT s
  let b := q.Z
  have hh : PolyBound (fun g => ⟪f g,b g⟫) :=
    PolyBound.of_prod_le (poly_sample q.C q.root (q.shift s)) (PolyBound.clm q.root.toContinuousLinearMap)
      fun g => abs_real_inner_le_norm _ _
  exact hh.gaussian_integrable ((continuous_sample ..).inner q.root.continuous).aestronglyMeasurable

-- split the mixed moment at 4(1+s), exterior small even compared to a (-s)
theorem negative_mean (hk : 1 ≤ K) :
    ∃ C ≥ (0:ℝ), ∀ q : ProjField m, q.Bound K → ∀ s ≥ (0:ℝ),
      q.avH (-s) ≤ C*(1+s)*a (-s) ∧ q.Bt (-s) ≤ C*(1+s) := by
  have hp : 0 < K := lt_of_lt_of_le zero_lt_one hk
  obtain ⟨d,hd,hx⟩ := uniform_X_neg m hk
  obtain ⟨c,hc,hc'⟩ := normal_tail m 2
  have hm : 0 < (m:ℝ) := m_pos
  let a0 := √(2*π)*Real.exp 4
  have ha0 : 0 ≤ a0 := by dsimp [a0]; positivity
  let C := 4*K*K+d*K*c*a0/m
  refine ⟨C,by dsimp [C]; positivity,?_⟩
  intro q hq s hs
  let w := q.XT (-s)
  let t := 4*(1+s)
  let S : Set (Rn m) := {x | t ≤ ‖x‖}
  have hS : MeasurableSet S := (isClosed_le continuous_const continuous_norm).measurableSet
  have ht : 0 ≤ t := by dsimp [t]; positivity
  let f := fun x : Rn m => (d*K)*(1+‖x‖)^2
  have hif : Integrable f (normal m) :=
    (integrable_envelope _).const_mul _
  have hI := (q.X_int (-s)).norm
  have hu : (∫ x in S, f x ∂normal m) ≤ d*K*c*a0*a (-s) := by
    have ha : Real.exp (-(t^2)/4) ≤ a0*a (-s) := tail_exp_le_a s hs
    unfold f; rw [integral_const_mul]
    calc
      _ ≤ d*K*(c*Real.exp (-(t^2)/4)) :=
        mul_le_mul_of_nonneg_left (hc' t ht) (by positivity)
      _ ≤ d*K*(c*(a0*a (-s))) := by gcongr
      _ = _ := by ring
  classical
  have he (x:Rn m) : ⟪w x,q.Z x⟫ ≤ K*t * ‖w x‖ + S.indicator f x := by
    have hn := hq.normZ x
    apply (real_inner_le_norm ..).trans
    by_cases h : x ∈ S
    · rw [indicator_of_mem h]
      have hb := hx q hq s hs x
      apply le_trans _ (le_add_of_nonneg_left (by positivity))
      unfold f
      change ‖w x‖ ≤ _ at hb
      have hi := mul_le_mul hb hn (norm_nonneg _) (show 0 ≤ d * (1+‖x‖) by positivity)
      nlinarith [show 0 ≤ d*K*(1+‖x‖) by positivity]
    rw [indicator_of_notMem h,add_zero,mul_comm (K*t)]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    exact hn.trans (mul_le_mul_of_nonneg_left (le_of_not_ge h) hp.le)
  have h₁ : q.avH (-s) ≤ C*(1+s)*a (-s) := by
    rw [q.avH_as_mean_ip,div_le_iff₀ hm]
    have hi : Integrable (fun x => K*t * ‖w x‖) (normal m) := hI.const_mul _
    apply (integral_mono (norm_IP_integrable m q _) (hi.add (hif.indicator hS)) he).trans
    change ∫ x, (K*t * ‖w x‖ + S.indicator f x) ∂normal m ≤ _
    rw [integral_add hi (hif.indicator hS),integral_const_mul,integral_indicator hS]
    have hh := mul_le_mul_of_nonneg_left (hq.X_mean (-s))
      (show 0 ≤ K*t by positivity)
    have hh₂ : 0 ≤ s*(d*K*c*a0*a (-s)) := by
      have ha : 0 < a (-s) := a_pos _
      positivity
    apply (add_le_add hh hu).trans
    dsimp only [C,t]
    field_simp
    nlinarith
  refine ⟨h₁,?_⟩
  have ha := a_pos (-s)
  have h := (mul_Bt_avH q (-s)).trans h₁
  exact le_of_mul_le_mul_left (by simpa only [mul_comm _ (a (-s))] using h) ha

theorem positive_mean (q : ProjField m) (hq : q.Bound K) (s : ℝ) :
    (∫ x, ‖q.YT s x‖ ∂normal m) ≤ K*m*K^2/a s := by
  apply (hq.Y_mean _).trans
  rw [le_div_iff₀ (a_pos s)]
  have h := ((mul_Bt_avH q s).trans (q.avH_le_s s)).trans hq.s0_le
  have he := mul_le_mul_of_nonneg_left h (show 0 ≤ K*m from mul_nonneg hq.positive.le (Nat.cast_nonneg _))
  linarith

-- both bias and samples pointwise at most linear growth
lemma layers_growth (hk : 1 ≤ K) :
    ∃ C ≥ (0:ℝ), ∀ q : ProjField m, q.Bound K → ∀ s,
      ‖q.shift s‖ ≤ C*(1+|s|) := by
  obtain ⟨c,hc,he⟩ := negative_mean m hk
  have hp : 0 < K := lt_of_lt_of_le zero_lt_one hk
  have hm : 0 < (m:ℝ) := m_pos
  let b := (√(2*π))⁻¹
  have hb : 0 < b := by dsimp [b]; positivity
  let Z := K*m*K^2/a 0
  have ha : 0 < a 0 := a_pos _
  have hZ : 0 ≤ Z := by dsimp [Z]; positivity
  let C := (b+1)*K+(K*m*c+Z)
  refine ⟨C,by dsimp [C]; positivity,?_⟩
  intro q hq s
  let y := ∫ x, q.YT s x ∂normal m
  have hy : ‖y‖ ≤ (K*m*c+Z)*(1+|s|) := by
    apply (norm_integral_le_integral_norm _).trans
    by_cases h : 0 ≤ s
    · apply (positive_mean m q hq _).trans
      have hh : K*m*K^2/a s ≤ Z := by
        unfold Z; gcongr; exact a_mono.monotone h
      have h' : 0 ≤ K*m*c := by positivity
      nlinarith [abs_nonneg s]
    · have hh := (he q hq (-s) (by linarith)).2
      rw [neg_neg] at hh
      apply (hq.Y_mean s).trans
      rw [abs_of_neg (by linarith)]
      have h' := mul_le_mul_of_nonneg_left hh (show 0 ≤ K*m by positivity)
      nlinarith
  have hah : a s ≤ (b+1)*(1+|s|) := by
    have h₁ := p_lt_one s
    have h₂ := p_pos s
    have h₃ : phi s ≤ b := phi_bdd s
    rw [a]
    nlinarith [le_abs_self s, abs_nonneg s]
  have heq : q.shift s = (a s) • q.U - y := by rw [show y = _ from q.Y_mean s]; abel
  rw [heq]; apply (norm_sub_le ..).trans
  rw [norm_smul,Real.norm_eq_abs, abs_of_pos (a_pos _)]
  have h' := mul_le_mul hah hq.Ub (norm_nonneg _) (show 0 ≤ (b+1)*(1+|s|) by positivity)
  dsimp only [C]
  linarith
end ProjField
end GeneralMahler

end

end OAI
