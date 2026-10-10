import Mathlib
import OAI.Probability.SKSupport.Regularity.ParameterChords

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace ZeroTemperatureSK
open WeakIto Heat Nonuniform

def positiveValue (γ : OrderParameter) (n : ℕ) : ℝ → ℝ → ℝ :=
  finiteValue (positiveCoeff γ n) (approxMesh n) (softAbs (positiveTerminal γ n)) (n+1) 0

def positiveError (γ : OrderParameter) (n : ℕ) : ℝ :=
  Real.log 2 / positiveTerminal γ n+(3/2:ℝ)*∫ s in (0:ℝ)..1, |positiveGamma γ n s-extend γ.val s|

lemma positiveError_limit (γ : OrderParameter) : Tendsto (positiveError γ) atTop (𝓝 0) := by
  have hh : Tendsto (fun n => Real.log 2 / positiveTerminal γ n) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv,mul_zero] using
      tendsto_const_nhds.mul (positiveTerminal_inv_tendsto γ) (a := Real.log 2)
  have hi := tendsto_const_nhds.mul (positiveGamma_L1 γ) (a := (3/2:ℝ))
  have h := hh.add hi
  unfold positiveError
  convert h using 1
  simp only [mul_zero,add_zero]

variable {Ω : Type*} [MeasurableSpace Ω]

lemma positiveValue_error (W : BrownianSystem Ω) (γ : OrderParameter) (n : ℕ)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (x : ℝ) :
    |positiveValue γ n t x-value W γ t x| ≤ positiveError γ n := by
  apply finiteValue_control_error W γ _ _ _ (approxMesh_horizon n)
    (regularDatum_softAbs (ne_of_gt (positiveTerminal_pos γ n))) (softAbs_lipschitz (ne_of_gt (positiveTerminal_pos γ n))) _ ht0 ht1 x
  intro z
  have hh := softAbs_bounds (positiveTerminal_pos γ n) z
  rw [abs_of_nonneg hh.1]
  exact hh.2

lemma positiveValue_uniform (W : BrownianSystem Ω) (γ : OrderParameter) :
    TendstoUniformlyOn (fun n (p : ℝ × ℝ) => positiveValue γ n p.1 p.2)
      (fun p => value W γ p.1 p.2) atTop (Icc (0:ℝ) 1 ×ˢ Set.univ) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [(positiveError_limit γ).eventually (gt_mem_nhds hε)] with n hn p hp
  rw [Real.dist_eq,abs_sub_comm]
  exact (positiveValue_error W γ n hp.1.1 hp.1.2 p.2).trans_lt hn

lemma positiveValue_uniform_spatial (W : BrownianSystem Ω) (γ : OrderParameter)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    TendstoUniformly (fun n => positiveValue γ n t) (value W γ t) atTop := by
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  filter_upwards [(positiveError_limit γ).eventually (gt_mem_nhds hε)] with n hn x
  rw [Real.dist_eq,abs_sub_comm]
  exact (positiveValue_error W γ n ht0 ht1 x).trans_lt hn

lemma positiveValue_regular (γ : OrderParameter) (n : ℕ) (t : ℝ) :
    RegularDatum (positiveValue γ n t) :=
  finiteValue_regular (regularDatum_softAbs (ne_of_gt (positiveTerminal_pos γ n)))
    (softAbs_lipschitz (ne_of_gt (positiveTerminal_pos γ n))) _ _ _ _ _

lemma positiveValue_uniform_derivative_bounds (γ : OrderParameter) {T : ℝ}
    (hT0 : 0 ≤ T) (hT1 : T < 1) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n, ∀ t ∈ Icc (0:ℝ) T, ∀ x,
      |iteratedDeriv (m+1) (positiveValue γ n t) x| ≤ C := by
  let δ := (1-T)/2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hB : T+δ ∈ Ico (0:ℝ) 1 := by dsimp [δ]; constructor <;> linarith
  let D := γ.val ⟨T+δ,hB⟩+1
  obtain ⟨C,hC,hbound⟩ := finiteGradient_uniform_smoothing m D (by dsimp [D]; linarith [γ.nonneg ⟨T+δ,hB⟩]) δ hδ
  refine ⟨C,hC,fun n t ht x => ?_⟩
  have hc : ∀ s ∈ Icc (0:ℝ) (T+δ),
      finiteCoeff (positiveCoeff γ n) (approxMesh n) (n+1) 0 s ≤ D := by
    intro s hs
    have hmem : s ∈ Ico (0:ℝ) 1 := ⟨hs.1,hs.2.trans_lt hB.2⟩
    have hh := γ.monotone (show (⟨s,hmem⟩ : Time) ≤ ⟨T+δ,hB⟩ from hs.2)
    exact (positiveGamma_bound γ n ⟨s,hmem⟩).trans (add_le_add hh le_rfl)
  have hh := hbound _ (regularDatum_softAbs (ne_of_gt (positiveTerminal_pos γ n)))
    (softAbs_lipschitz (ne_of_gt (positiveTerminal_pos γ n))) (positiveCoeff γ n) (approxMesh n) (n+1) 0 T hT0
    (by rw [approxMesh_horizon]; exact hB.2.le) hc m le_rfl t ht x
  simpa only [positiveValue,iteratedDeriv_succ'] using hh

theorem positive_limit_contDiff (W : BrownianSystem Ω) (γ : OrderParameter)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) : ContDiff ℝ ∞ (value W γ t) := by
  apply (smooth_limit_of_uniform_derivative_bounds
    (fun n => (positiveValue_regular γ n t).smooth) _
    (positiveValue_uniform_spatial W γ ht0 ht1.le)).1
  intro m
  obtain ⟨C,hC,hb⟩ := positiveValue_uniform_derivative_bounds γ ht0 ht1 (m+1)
  exact ⟨C,hC,fun n x => hb n t ⟨ht0,le_rfl⟩ x⟩

lemma positiveValue_derivative_uniform_spatial (W : BrownianSystem Ω) (γ : OrderParameter)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) (m : ℕ) :
    TendstoUniformly (fun n => iteratedDeriv m (positiveValue γ n t))
      (iteratedDeriv m (value W γ t)) atTop := by
  apply (smooth_limit_of_uniform_derivative_bounds
    (fun n => (positiveValue_regular γ n t).smooth) _
    (positiveValue_uniform_spatial W γ ht0 ht1.le)).2 m
  intro j
  obtain ⟨C,hC,hb⟩ := positiveValue_uniform_derivative_bounds γ ht0 ht1 (j+1)
  exact ⟨C,hC,fun n x => hb n t ⟨ht0,le_rfl⟩ x⟩

theorem positive_limit_derivative_bounds (W : BrownianSystem Ω) (γ : OrderParameter)
    {T : ℝ} (hT0 : 0 ≤ T) (hT1 : T < 1) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc (0:ℝ) T, ∀ x,
      |iteratedDeriv (m+1) (value W γ t) x| ≤ C := by
  obtain ⟨C,hC,hb⟩ := positiveValue_uniform_derivative_bounds γ hT0 hT1 m
  refine ⟨C,hC,fun t ht x => ?_⟩
  exact iteratedDeriv_limit_bound (m+1)
    (positiveValue_derivative_uniform_spatial W γ ht.1 (ht.2.trans_lt hT1) (m+1))
    (fun n x => hb n t ht x) x

lemma positiveValue_derivative_uniform (W : BrownianSystem Ω) (γ : OrderParameter)
    {T : ℝ} (hT0 : 0 ≤ T) (hT1 : T < 1) (m : ℕ) :
    TendstoUniformlyOn (fun n (p : ℝ × ℝ) => iteratedDeriv m (positiveValue γ n p.1) p.2)
      (fun p => iteratedDeriv m (value W γ p.1) p.2) atTop (Icc (0:ℝ) T ×ˢ Set.univ) := by
  induction m with
  | zero =>
    simp only [iteratedDeriv_zero]
    exact (positiveValue_uniform W γ).mono (Set.prod_mono (Icc_subset_Icc le_rfl hT1.le) (Subset.refl _))
  | succ m ih =>
    obtain ⟨C,hC,hb⟩ := positiveValue_uniform_derivative_bounds γ hT0 hT1 (m+1)
    have hbg : ∀ t ∈ Icc (0:ℝ) T, ∀ x, |iteratedDeriv (m+2) (value W γ t) x| ≤ C := by
      intro t ht x
      exact iteratedDeriv_limit_bound (m+2)
        (positiveValue_derivative_uniform_spatial W γ ht.1 (ht.2.trans_lt hT1) (m+2))
        (fun n y => by simpa only [Nat.add_assoc] using hb n t ht y) x
    have hh := tendstoUniformlyOn_deriv_family (S := Icc (0:ℝ) T)
      (f := fun n t => iteratedDeriv m (positiveValue γ n t))
      (g := fun t => iteratedDeriv m (value W γ t))
      (fun n t _ => (contDiff_iteratedDeriv_infty (positiveValue_regular γ n t).smooth m).of_le
        (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
      (fun t ht => (contDiff_iteratedDeriv_infty (value_contDiff W γ ht.1 (ht.2.trans_lt hT1)) m).of_le
        (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)) hC
      (by simpa only [show m+2=(m+1)+1 by omega,iteratedDeriv_succ] using hb)
      (by simpa only [show m+2=(m+1)+1 by omega,iteratedDeriv_succ] using hbg) ih
    simpa only [iteratedDeriv_succ] using hh

end ZeroTemperatureSK

end
end

end OAI
