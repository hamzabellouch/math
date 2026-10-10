import OAI.Analysis.FourierLLogL.Weak.Modular

noncomputable section
open MeasureTheory Filter Set Function
open scoped ENNReal BigOperators Topology

namespace OAI

namespace FourierLLogL.Weak
open Real
open scoped Classical
variable {f : Torus → ℂ}

/-- allocate an integral for the good-part majorant, uniformly on modular ball -/
lemma feeSummed (h : inside f) :
    (∑' j : ℕ,(2:ℝ)^(j+1)*heightLayerMass f j) ≤ 1 := by
  let g := Young f
  let A := heightLayerSet f
  have hF : Integrable g circleMeasure := h.1.2
  have HD := hasSum_integral_iUnion_ae (heightLayerSet_nullMeasurable h.1)
      ((heightLayerSet_pairwise_disjoint f).mono (fun _ _ h ↦ h.aedisjoint))
      (show IntegrableOn g _ _ from hF.integrableOn)
  have hi (j : ℕ) : (2:ℝ)^(j+1)*heightLayerMass f j ≤ ∫ x in A j,g x ∂circleMeasure := by
    rw [heightLayerMass, ← integral_const_mul]
    apply integral_mono_ae (h.1.integrable.norm.integrableOn.const_mul _) hF.integrableOn
    filter_upwards [ae_restrict_mem₀ (heightLayerSet_nullMeasurable h.1 j)] with x hx
    have hlog : (2:ℝ)^(j+1) ≤ Real.log (2+‖f x‖) := le_trans
      (Real.log_exp ((2:ℝ)^(j+1))).symm.le
      (Real.log_le_log (Real.exp_pos _) (hx.1.trans (by linarith)))
    unfold g Young priceΦ; nlinarith [norm_nonneg (f x)]
  calc
    _ ≤ ∑' j,∫ x in A j,g x ∂circleMeasure := h.1.summable_weighted_heightLayerMass.tsum_le_tsum hi HD.summable
    _ = ∫ x in ⋃ i, A i,g x ∂circleMeasure := HD.tsum_eq
    _ ≤ ∫ x,g x ∂circleMeasure := by
      conv_rhs => rw [← setIntegral_univ]
      apply setIntegral_mono_set hF.integrableOn (ae_of_all _ fun x => p_nonneg _ (norm_nonneg _))
        (subset_univ _).eventuallyLE
    _ ≤ 1 := mod_unit f ▸ h.2

def piece (f : Torus→ℂ) : ℕ → Torus → ℂ
| 0 => boundedPart f
| j+1 => heightLayer f j
def grit (j : ℕ) : ℝ := (1/4:ℝ)^j
lemma grit_pos (j : ℕ) : 0 < grit j := by unfold grit; positivity
lemma grits : Summable (fun j => (2:ℝ)^(j+1) * grit j) := by
  simp only [grit,pow_succ]
  apply Summable.congr ( (summable_geometric_of_norm_lt_one (by norm_num : ‖(2:ℝ)*(1/4)‖ < 1)).mul_right 2)
  intro n; rw [mul_pow]; ring


private lemma grit_height (j : ℕ) :
    Real.exp ((2:ℝ)^(j+2)) ≤ grit j * Real.exp ((2:ℝ)^(j+4)) := by
  have hj : (j:ℝ) ≤ (2:ℝ)^j := by exact_mod_cast (Nat.lt_two_pow_self (n:=j)).le
  have hex : (4:ℝ)^j ≤ Real.exp ((3:ℝ) * j) := by
    have h3 := Real.add_one_le_exp 3
    rw [mul_comm 3, Real.exp_nat_mul]
    exact pow_le_pow_left₀ (by norm_num) (by norm_num at h3; linarith) _
  have Hmul : (4:ℝ)^j * Real.exp ((2:ℝ)^(j+2)) ≤ Real.exp ((2:ℝ)^(j+4)) := by
    refine (mul_le_mul_of_nonneg_right hex (Real.exp_nonneg _)).trans ?_
    rw [← Real.exp_add]
    apply Real.exp_monotone
    simp only [pow_add]
    linarith
  simp only [grit, one_div, inv_pow, ← div_eq_inv_mul]
  apply (le_div_iff₀ (by positivity : (0:ℝ)<4^j)).mpr
  rw [mul_comm]
  exact Hmul

def allowance (f : Torus → ℂ) : ℕ → ℝ
| 0 => exp 2
| j+1 => heightLayerMass f j + grit j
lemma taxpayer (h : inside f) (j : ℕ) :
    let w := allowance f j; let F := piece f j
    0<w ∧ Integrable F circleMeasure ∧ (∫ x,‖F x‖ ∂circleMeasure) ≤ w ∧
      ∀ x, ‖F x‖ ≤ w*exp ((2:ℝ)^(j+4)) := by
  intro w F
  cases j with
  | zero =>
    have hi := h.1.boundedPart_integrable
    refine ⟨exp_pos _,hi,?_,fun x => (norm_boundedPart_le _ _).trans ?_⟩
    · apply le_trans (integral_mono hi.norm (integrable_const (μ:=circleMeasure) w)
        (norm_boundedPart_le _)) (by simp)
    · exact le_mul_of_one_le_right (exp_pos 2).le (one_le_exp (by positivity))
  | succ j =>
    have Hi := heightLayerMass_nonneg f j
    have he : grit j ≤ w := le_add_of_nonneg_left Hi
    refine ⟨lt_of_lt_of_le (grit_pos j) he,h.1.heightLayer_integrable _,?_,?_⟩
    · rw [show F=heightLayer f j from rfl]
      rw [← heightLayerMass_eq_integral_norm h.1]
      exact le_add_of_nonneg_right (grit_pos j).le
    intro x
    apply le_trans (le_trans (norm_heightLayer_le f j x) (grit_height j))
    apply mul_le_mul he (exp_monotone ?_) (exp_pos _).le (le_trans (grit_pos j).le he)
    exact pow_le_pow_right₀ (by norm_num) (by omega)

def tollMax : ℝ := exp 2 + 1 + ∑' j, (2:ℝ)^(j+1)*grit j
lemma toll_bound (h : inside f) :
    let a (j : ℕ) := (2:ℝ)^j*allowance f j
    Summable a ∧ ∑' j,a j ≤ tollMax := by
  intro a
  let F (j : ℕ) := (2:ℝ)^(j+1)*heightLayerMass f j; let w (j : ℕ) := (2:ℝ)^(j+1)*grit j
  have hF : Summable F := h.1.summable_weighted_heightLayerMass
  have HX : (fun j => a (j+1))=fun j => F j+w j := by funext j; unfold a w F; rw [allowance,mul_add]
  have HT : Summable a := (summable_nat_add_iff 1).mp (HX ▸ (hF.add grits))
  refine ⟨HT,?_⟩
  rw [← HT.sum_add_tsum_nat_add 1,HX]
  rw [hF.tsum_add grits]
  have HE : ∑' i,F i ≤ 1 := feeSummed h
  simp only [Finset.sum_range_one]
  have hi : a 0=exp 2 := by simp [a,allowance]
  rw [hi]
  unfold tollMax; linarith

lemma paid_transform (h : inside f) (x : Torus) (n : ℕ) :
    ENNReal.ofReal ‖symmetricPartialSum f n x‖ ≤ ∑' i, symmetricMaximal (piece f i) x := by
  let F (i : ℕ) := symmetricPartialSum (piece f i) n x
  let t (i : ℕ) := ‖F i‖
  have HE (i) : t (i+1) ≤ (2*n+1:ℕ)*(∫ x, ‖heightLayer f i x‖ ∂circleMeasure) :=
    norm_symmetricPartialSum_le _ n x
  have Hs : Summable t := (summable_nat_add_iff 1).mp
    ((h.1.summable_heightLayer_norm.mul_left ((2*n+1:ℕ):ℝ)).of_nonneg_of_le
      (fun n => norm_nonneg _) HE)
  have HH := h.1.symmetricPartialSum_heightDecomposition n x
  have H : symmetricPartialSum f n x=∑' j,F j := by
    rw [← (Hs.of_norm).sum_add_tsum_nat_add 1,Finset.sum_range_one]; exact HH
  rw [H]
  calc
    _ ≤ ENNReal.ofReal (∑' i,t i) := ENNReal.ofReal_le_ofReal (norm_tsum_le_tsum_norm Hs)
    _ = _ := ENNReal.ofReal_tsum_of_nonneg (fun i => norm_nonneg (F i)) Hs
    _ ≤ ∑' i,symmetricMaximal (piece f i) x :=
      ENNReal.tsum_le_tsum fun i => le_iSup (fun n=> ENNReal.ofReal ‖symmetricPartialSum (piece f i) n x‖) n

end FourierLLogL.Weak

end OAI
