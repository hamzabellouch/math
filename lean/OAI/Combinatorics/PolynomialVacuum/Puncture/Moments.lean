import OAI.Combinatorics.PolynomialVacuum.Puncture.Calibration

namespace OAI

namespace PolynomialVacuumCylinder
open Real MeasureTheory Set

private theorem sinh_lower_exponential {u : ℝ} (hu : 0<u) :
    u*Real.exp u ≤ (1+2*u)*Real.sinh u := by
  have he := (Real.add_one_lt_exp (mul_pos (by norm_num : (0 : ℝ)<2) hu).ne').le
  have hp := Real.exp_pos u
  have hn := Real.exp_pos (-u)
  have heq : Real.exp (2*u)=Real.exp u*Real.exp u := by
    rw [show 2*u=u+u by ring,Real.exp_add]
  have hinv : Real.exp u*Real.exp (-u)=1 := by rw [←Real.exp_add]; simp
  rw [heq] at he
  rw [Real.sinh_eq]
  nlinarith [mul_nonneg (sub_nonneg.mpr he) hn.le]

theorem denominatorReferenceWeight_bound {p : ℝ} (hp : 0<p) :
    denominatorReferenceWeight p ≤
      (2/(3*Real.pi)+p/2)*Real.exp (-(3*Real.pi/8)*p) := by
  let a : ℝ := 3*Real.pi/8
  have ha : 0<a := by dsimp [a]; positivity
  have hs : 0<Real.sinh (a*p) := Real.sinh_pos_iff.mpr (mul_pos ha hp)
  have he : 0<Real.exp (a*p) := Real.exp_pos _
  have h := sinh_lower_exponential (mul_pos ha hp)
  have hi : Real.exp (-(a*p))*Real.exp (a*p)=1 := by rw [←Real.exp_add]; simp
  rw [denominatorReferenceWeight,ite_eq_right hp.ne']
  rw [show 3*Real.pi*p/8=a*p by dsimp [a]; ring]
  change p/(4*Real.sinh (a*p)) ≤ (2/(3*Real.pi)+p/2)*Real.exp (-a*p)
  rw [div_le_iff₀ (by positivity : 0<4*Real.sinh (a*p))]
  apply (mul_le_mul_iff_left₀ ha).mp
  apply (mul_le_mul_iff_right₀ he).mp
  have hc : a*(2/(3*Real.pi)+p/2)*4=1+2*(a*p) := by
    dsimp [a]
    field_simp
    ring
  calc
    Real.exp (a*p)*(p*a) = a*p*Real.exp (a*p) := by ring
    _ ≤ (1+2*(a*p))*Real.sinh (a*p) := h
    _ = Real.exp (a*p)*(((2/(3*Real.pi)+p/2)*Real.exp (-a*p)*(4*Real.sinh (a*p)))*a) := by
      rw [show -a*p=-(a*p) by ring]
      calc
        _ = (a*(2/(3*Real.pi)+p/2)*4)*Real.sinh (a*p) := by rw [hc]
        _ = (a*(2/(3*Real.pi)+p/2)*4)*Real.sinh (a*p) *
            (Real.exp (-(a*p))*Real.exp (a*p)) := by rw [hi,mul_one]
        _ = _ := by ring

theorem denominatorMomentWeight_le_reference (p : ℝ) :
    denominatorMomentWeight p ≤ (3/2)*denominatorReferenceWeight p := by
  rw [denominatorMomentWeight_factor,denominatorCorrection,
    Real.exp_log (by positivity : 0<1+1/(2*Real.cosh (Real.pi*p/4)))]
  have h := Real.one_le_cosh (Real.pi*p/4)
  have hi : 1/(2*Real.cosh (Real.pi*p/4)) ≤ (1/2 : ℝ) := by
    apply (div_le_iff₀ (by positivity : 0<2*Real.cosh (Real.pi*p/4))).mpr
    linarith
  nlinarith [mul_nonneg (denominatorReferenceWeight_pos p).le (show 0≤(1/2 : ℝ)-1/(2*Real.cosh (Real.pi*p/4)) by linarith)]

theorem denominatorMomentWeight_measurable : Measurable denominatorMomentWeight := by
  unfold denominatorMomentWeight
  exact Measurable.ite (measurableSet_singleton 0)
    measurable_const (by fun_prop)

private theorem power_laplace_integrable (m : ℕ) {a : ℝ} (ha : 0<a) :
    IntegrableOn (fun p : ℝ=>p^m*Real.exp (-a*p)) (Ioi 0) := by
  simpa only [Real.rpow_natCast,Real.rpow_one] using
    (integrableOn_rpow_mul_exp_neg_mul_rpow (s:=(m : ℝ)) (p:=1)
      (by have := Nat.cast_nonneg (α:=ℝ) m; linarith) (by norm_num) ha)

 

theorem denominator_moment_integrable_positive (m : ℕ) :
    IntegrableOn (fun p : ℝ=>p^m*denominatorMomentWeight p) (Ioi 0) := by
  let a : ℝ := 3*Real.pi/8
  have ha : 0<a := by dsimp [a]; positivity
  have h0 := (power_laplace_integrable m ha).const_mul ((3/2)*(2/(3*Real.pi)))
  have h1 := (power_laplace_integrable (m+1) ha).const_mul ((3/2)*(1/2))
  apply (h0.add h1).mono'
  · exact ((measurable_id.pow_const m).mul denominatorMomentWeight_measurable).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with p hp
    have hp0 : 0<p := hp
    rw [Real.norm_of_nonneg (mul_nonneg (pow_nonneg hp0.le m) (denominatorMomentWeight_pos p).le)]
    have hb := mul_le_mul_of_nonneg_left (denominatorReferenceWeight_bound hp0) (by norm_num : (0 : ℝ)≤3/2)
    have hc := (denominatorMomentWeight_le_reference p).trans hb
    have hd := mul_le_mul_of_nonneg_left hc (pow_nonneg hp0.le m)
    apply hd.trans_eq
    simp only [Pi.add_apply,a,pow_succ]
    ring

theorem denominatorMomentWeight_even (p : ℝ) :
    denominatorMomentWeight (-p)=denominatorMomentWeight p := by
  by_cases hp : p=0
  · subst p; simp
  · simp [denominatorMomentWeight,hp,neg_div,div_neg]

theorem denominator_even_moment_integrable (m : ℕ) :
    Integrable (fun p : ℝ=>p^(2*m)*denominatorMomentWeight p) := by
  rw [←integrableOn_univ,←@Iio_union_Ici _ _ (0 : ℝ),integrableOn_union,
    integrableOn_Ici_iff_integrableOn_Ioi]
  refine ⟨?_,denominator_moment_integrable_positive (2*m)⟩
  rw [←(Measure.measurePreserving_neg (volume : Measure ℝ)).integrableOn_comp_preimage
    (Homeomorph.neg ℝ).measurableEmbedding]
  simpa only [Function.comp_def,neg_preimage,neg_Iio,neg_zero,pow_mul,neg_sq,
    denominatorMomentWeight_even] using denominator_moment_integrable_positive (2*m)

theorem denominator_matrix_entry_integrable (n : ℕ) (j k : Fin n) :
    Integrable (fun p : ℝ=>p^(2*j.val+2*k.val)*denominatorMomentWeight p) := by
  rw [show 2*j.val+2*k.val=2*(j.val+k.val) by omega]
  exact denominator_even_moment_integrable _

end PolynomialVacuumCylinder

end OAI
