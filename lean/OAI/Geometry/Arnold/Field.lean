import OAI.Geometry.Arnold.Factors

namespace OAI

universe uι

noncomputable section
open scoped BigOperators ContDiff

namespace ArnoldCounterexample.Field
open ArnoldCounterexample.Quadric ArnoldCounterexample.ThreePoints ArnoldCounterexample.Factors
open scoped ContDiff Topology
open Set Filter

/-- The ambient symplectic bilinear form, with the factor 2 normalization. -/
def symplectic : CV →L[ℝ] CV →L[ℝ] ℝ :=
  (2 : ℝ) • (∑ i : Fin 5, ((realCoord i).smulRight (imagCoord i) - (imagCoord i).smulRight (realCoord i)))

lemma symplectic_apply (v w : CV) : symplectic v w = omega v w := by
  simp only [symplectic, smul_apply, sum_apply, sub_apply, ContinuousLinearMap.smulRight_apply,
    realCoord_apply, imagCoord_apply, smul_eq_mul, omega, Complex.im_sum, Complex.mul_im,
    Complex.star_def, Complex.conj_re, Complex.conj_im]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma symplectic_skew (v w : CV) : symplectic v w = -symplectic w v := by
  simp only [symplectic, smul_apply, sum_apply, sub_apply, ContinuousLinearMap.smulRight_apply,
    realCoord_apply, imagCoord_apply, smul_eq_mul]
  rw [show -(2 * ∑ i, ((w i).re * (v i).im - (w i).im * (v i).re)) =
    2 * ∑ i, -((w i).re * (v i).im - (w i).im * (v i).re) by rw [Finset.sum_neg_distrib]; ring]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

def rotor (a b : Fin 5) : CV →L[ℝ] CV :=
  (ContinuousLinearMap.single ℝ (fun _ : Fin 5 ↦ ℂ) b).comp (ContinuousLinearMap.proj a) -
    (ContinuousLinearMap.single ℝ (fun _ : Fin 5 ↦ ℂ) a).comp (ContinuousLinearMap.proj b)

lemma rotor_apply (a b : Fin 5) (z : CV) : rotor a b z = Pi.single b (z a) - Pi.single a (z b) := rfl

lemma rotor_phase (a b : Fin 5) (z : CV) (c : ℂ) : rotor a b (c • z) = c • rotor a b z := by
  ext i
  simp [rotor_apply, Pi.single_apply, mul_sub]

lemma bilinear_rotor (a b : Fin 5) (w z : CV) :
    bilinear w (rotor a b z) = w b * z a - w a * z b := by
  simp [bilinear, rotor_apply, Pi.single_apply, mul_sub, mul_ite, Finset.sum_sub_distrib]

lemma moment_hasFDerivAt (a b : Fin 5) (z : CV) :
    HasFDerivAt (moment a b) (symplectic (rotor a b z)) z := by
  have hd := ((((realCoord a).hasFDerivAt (x := z)).mul (imagCoord b).hasFDerivAt).sub
    ((imagCoord a).hasFDerivAt.mul (realCoord b).hasFDerivAt)).const_mul 2
  convert! hd using 1
  · funext w
    exact moment_real a b w
  · ext v
    rw [symplectic_skew, symplectic_apply]
    change -(2 * (bilinear (star v) (rotor a b z)).im) = _
    rw [bilinear_rotor]
    simp [Complex.mul_im]
    ring

def leftOperator (i : Fin 3) : CV →L[ℝ] CV :=
  ![rotor 1 2 + rotor 3 4, rotor 1 3 - rotor 2 4, rotor 1 4 + rotor 2 3] i

def rightOperator (i : Fin 3) : CV →L[ℝ] CV :=
  ![rotor 1 2 - rotor 3 4, rotor 1 3 + rotor 2 4, rotor 1 4 - rotor 2 3] i

lemma left_hasFDerivAt (i : Fin 3) (z : CV) :
    HasFDerivAt (fun w ↦ leftSphere w i) (symplectic (leftOperator i z)) z := by
  fin_cases i <;> simp [leftSphere, leftOperator]
  · exact (moment_hasFDerivAt 1 2 z).add (moment_hasFDerivAt 3 4 z)
  · exact (moment_hasFDerivAt 1 3 z).sub (moment_hasFDerivAt 2 4 z)
  · exact (moment_hasFDerivAt 1 4 z).add (moment_hasFDerivAt 2 3 z)

lemma right_hasFDerivAt (i : Fin 3) (z : CV) :
    HasFDerivAt (fun w ↦ rightSphere w i) (symplectic (rightOperator i z)) z := by
  fin_cases i <;> simp [rightSphere, rightOperator]
  · exact (moment_hasFDerivAt 1 2 z).sub (moment_hasFDerivAt 3 4 z)
  · exact (moment_hasFDerivAt 1 3 z).add (moment_hasFDerivAt 2 4 z)
  · exact (moment_hasFDerivAt 1 4 z).sub (moment_hasFDerivAt 2 3 z)

lemma left_phase (i : Fin 3) (z : CV) (c : ℂ) :
    leftOperator i (c • z) = c • leftOperator i z := by
  fin_cases i <;> simp [leftOperator, rotor_phase, smul_add, smul_sub]

lemma right_phase (i : Fin 3) (z : CV) (c : ℂ) :
    rightOperator i (c • z) = c • rightOperator i z := by
  fin_cases i <;> simp [rightOperator, rotor_phase, smul_add, smul_sub]

/-- A real-skew field is simultaneously tangent to every sphere and complex quadric. -/
def SkewAt (z v : CV) : Prop := (bilinear (star z) v).re = 0 ∧ bilinear z v = 0

lemma skewAt_zero (z : CV) : SkewAt z 0 := by simp [SkewAt, bilinear]
lemma skewAt_add {z v w : CV} (hv : SkewAt z v) (hw : SkewAt z w) : SkewAt z (v+w) := by
  simp only [SkewAt, bilinear_add_right, Complex.add_re, hv.1, hw.1, hv.2, hw.2, add_zero, and_self]
lemma skewAt_sub {z v w : CV} (hv : SkewAt z v) (hw : SkewAt z w) : SkewAt z (v-w) := by
  simp only [SkewAt, bilinear, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib, Complex.sub_re] at *
  exact ⟨by rw [hv.1, hw.1]; ring, by rw [hv.2, hw.2]; ring⟩
lemma skewAt_smul {z v : CV} (hv : SkewAt z v) (a : ℝ) : SkewAt z (a • v) := by
  have he : a • v = (a : ℂ) • v := by ext i; simp
  change (bilinear (star z) (a • v)).re = 0 ∧ bilinear z (a • v) = 0
  rw [he, bilinear_smul_right, bilinear_smul_right]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero, hv.1, hv.2, mul_zero, and_self]
lemma skewAt_sum {ι : Type uι} (T : Finset ι) {z : CV} (v : ι → CV)
    (hv : ∀ i ∈ T, SkewAt z (v i)) : SkewAt z (∑ i ∈ T, v i) := by
  classical
  induction T using Finset.induction_on with
  | empty => simpa using skewAt_zero z
  | @insert a T ha ih =>
    rw [Finset.sum_insert ha]
    exact skewAt_add (hv a (by simp)) (ih (fun i hi ↦ hv i (by simp [hi])))

lemma rotor_skew (a b : Fin 5) (z : CV) : SkewAt z (rotor a b z) := by
  simp only [SkewAt, bilinear_rotor, Complex.sub_re, Complex.mul_re, Pi.star_apply,
    Complex.star_def, Complex.conj_re, Complex.conj_im]
  constructor <;> ring

lemma left_skew (i : Fin 3) (z : CV) : SkewAt z (leftOperator i z) := by
  fin_cases i <;> simp [leftOperator]
  · exact skewAt_add (rotor_skew _ _ z) (rotor_skew _ _ z)
  · exact skewAt_sub (rotor_skew _ _ z) (rotor_skew _ _ z)
  · exact skewAt_add (rotor_skew _ _ z) (rotor_skew _ _ z)

lemma right_skew (i : Fin 3) (z : CV) : SkewAt z (rightOperator i z) := by
  fin_cases i <;> simp [rightOperator]
  · exact skewAt_sub (rotor_skew _ _ z) (rotor_skew _ _ z)
  · exact skewAt_add (rotor_skew _ _ z) (rotor_skew _ _ z)
  · exact skewAt_sub (rotor_skew _ _ z) (rotor_skew _ _ z)

end ArnoldCounterexample.Field

namespace ArnoldCounterexample.Field
open ArnoldCounterexample.Quadric ArnoldCounterexample.ThreePoints ArnoldCounterexample.Factors
open scoped ContDiff Topology
open Set Filter

lemma exists_radial : ∃ b : ℝ → ℝ, ContDiff ℝ ∞ b ∧
    ∀ s ∈ Icc (1/32 : ℝ) 32, b s = (Real.sqrt s)⁻¹ := by
  obtain ⟨b, hb, he⟩ := Extension.global_extension (isCompact_Icc (a := (1/32 : ℝ)) (b := 32))
    (fun s ↦ (Real.sqrt (s : ℝ))⁻¹) (by
      intro s
      refine ⟨Ioi 0, fun x ↦ (Real.sqrt x)⁻¹, isOpen_Ioi, ?_, ?_, ?_⟩
      · exact lt_of_lt_of_le (by norm_num) s.property.1
      · exact (contDiffOn_id.sqrt (fun x hx ↦ ne_of_gt hx)).inv (fun x hx ↦ (Real.sqrt_pos.2 hx).ne')
      · intro y _; rfl)
  exact ⟨b, hb, fun s hs ↦ he ⟨s,hs⟩⟩

def radial : ℝ → ℝ := exists_radial.choose
lemma radial_smooth : ContDiff ℝ ∞ radial := exists_radial.choose_spec.1
lemma radial_eq (s : ℝ) (hs : s ∈ Icc (1/32 : ℝ) 32) : radial s = (Real.sqrt s)⁻¹ :=
  exists_radial.choose_spec.2 s hs

lemma radial_eventually {s : ℝ} (hs : s ∈ Ioo (1/32 : ℝ) 32) :
    radial =ᶠ[𝓝 s] fun x ↦ (Real.sqrt x)⁻¹ := by
  filter_upwards [isOpen_Ioo.mem_nhds hs] with x hx
  exact radial_eq x ⟨le_of_lt hx.1, le_of_lt hx.2⟩

lemma radial_squared (r : ℝ) (hr : r ∈ Ioo (1/2 : ℝ) 2) :
    radial (r^2) = r⁻¹ ∧ deriv radial (r^2) = -(2*r^3)⁻¹ := by
  have hr0 : 0 < r := lt_trans (by norm_num) hr.1
  have hs : r^2 ∈ Ioo (1/32 : ℝ) 32 := by constructor <;> nlinarith [hr.1, hr.2, sq_nonneg (r-2), sq_nonneg (r-1/2)]
  have hsqrt : Real.sqrt (r^2) = r := Real.sqrt_sq hr0.le
  have he : radial (r^2) = r⁻¹ := by rw [radial_eq _ ⟨hs.1.le,hs.2.le⟩, hsqrt]
  refine ⟨he, ?_⟩
  have hd := (((hasDerivAt_id (r^2)).sqrt (sq_pos_of_pos hr0).ne').inv ((Real.sqrt_pos.2 (sq_pos_of_pos hr0)).ne'))
  have hb := hd.congr_of_eventuallyEq (radial_eventually hs)
  rw [hb.deriv]
  simp only [id_eq, hsqrt]
  field_simp

lemma radial_at_one : radial 1 = 1 ∧ deriv radial 1 = -(1/2 : ℝ) := by
  simpa using radial_squared 1 (by norm_num)

def casimir (z : CV) : ℝ := ∑ i : Fin 3, leftSphere z i ^ 2

def pairing (z : CV) : ℝ := ∑ i : Fin 3, leftSphere z i * rightSphere z i

def mixedField (z : CV) : CV := ∑ i : Fin 3,
  ((rightSphere z i) • leftOperator i z + (leftSphere z i) • rightOperator i z)

def selfField (z : CV) : CV := ∑ i : Fin 3, (leftSphere z i) • leftOperator i z

/-- A degree-two Hamiltonian near the unit fixed quadric, with restriction f. -/
def potential (z : CV) : ℝ := leftSphere z 0 - rightSphere z 2 + radial (casimir z) * pairing z

def core (z : CV) : CV := leftOperator 0 z - rightOperator 2 z +
  radial (casimir z) • mixedField z + (2 * deriv radial (casimir z) * pairing z) • selfField z

lemma casimir_smooth : ContDiff ℝ ∞ casimir := by
  have h (i : Fin 3) : ContDiff ℝ ∞ (fun z : CV ↦ leftSphere z i) :=
    (contDiff_apply ℝ ℝ i).comp (sphereFactors_smooth.fst)
  exact ContDiff.sum (fun i _ ↦ (h i).pow 2)

lemma pairing_smooth : ContDiff ℝ ∞ pairing := by
  have hL (i : Fin 3) : ContDiff ℝ ∞ (fun z : CV ↦ leftSphere z i) :=
    (contDiff_apply ℝ ℝ i).comp (sphereFactors_smooth.fst)
  have hR (i : Fin 3) : ContDiff ℝ ∞ (fun z : CV ↦ rightSphere z i) :=
    (contDiff_apply ℝ ℝ i).comp (sphereFactors_smooth.snd)
  exact ContDiff.sum (fun i _ ↦ (hL i).mul (hR i))

lemma potential_smooth : ContDiff ℝ ∞ potential := by
  have hL : ContDiff ℝ ∞ (fun z : CV ↦ leftSphere z 0) :=
    (contDiff_apply ℝ ℝ 0).comp (sphereFactors_smooth.fst)
  have hR : ContDiff ℝ ∞ (fun z : CV ↦ rightSphere z 2) :=
    (contDiff_apply ℝ ℝ 2).comp (sphereFactors_smooth.snd)
  exact (hL.sub hR).add ((radial_smooth.comp casimir_smooth).mul pairing_smooth)

lemma mixed_smooth : ContDiff ℝ ∞ mixedField := by
  apply ContDiff.sum
  intro i _
  exact (((contDiff_apply ℝ ℝ i).comp sphereFactors_smooth.snd).smul (leftOperator i).contDiff).add
    (((contDiff_apply ℝ ℝ i).comp sphereFactors_smooth.fst).smul (rightOperator i).contDiff)

lemma self_smooth : ContDiff ℝ ∞ selfField := by
  apply ContDiff.sum
  intro i _
  exact ((contDiff_apply ℝ ℝ i).comp sphereFactors_smooth.fst).smul (leftOperator i).contDiff

lemma core_smooth : ContDiff ℝ ∞ core := by
  have hd : ContDiff ℝ ∞ (deriv radial) := (contDiff_infty_iff_deriv.mp radial_smooth).2
  exact (((leftOperator 0).contDiff.sub (rightOperator 2).contDiff).add
    ((radial_smooth.comp casimir_smooth).smul mixed_smooth)).add
      ((contDiff_const.mul (hd.comp casimir_smooth) |>.mul pairing_smooth).smul self_smooth)

lemma casimir_hasFDerivAt (z : CV) :
    HasFDerivAt casimir ((2 : ℝ) • symplectic (selfField z)) z := by
  have hd := HasFDerivAt.fun_sum (u := Finset.univ)
    (fun i : Fin 3 ↦ fun _ ↦ (left_hasFDerivAt i z).pow 2)
  convert! hd using 1
  ext v
  simp only [selfField, map_sum, map_smul, sum_apply, smul_apply, smul_eq_mul,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma pairing_hasFDerivAt (z : CV) :
    HasFDerivAt pairing (symplectic (mixedField z)) z := by
  have hd := HasFDerivAt.fun_sum (u := Finset.univ)
    (fun i : Fin 3 ↦ fun _ ↦ (left_hasFDerivAt i z).mul (right_hasFDerivAt i z))
  convert! hd using 1
  ext v
  simp only [mixedField, map_sum, map_add, map_smul, sum_apply, add_apply, smul_apply]
  apply Finset.sum_congr rfl
  intro i _
  abel

lemma core_hamiltonian (z : CV) : symplectic (core z) = fderiv ℝ potential z := by
  have hb := (radial_smooth.differentiable (by simp) (casimir z)).hasDerivAt.comp_hasFDerivAt z
    (casimir_hasFDerivAt z)
  have hd := ((left_hasFDerivAt 0 z).sub (right_hasFDerivAt 2 z)).add
    (hb.mul (pairing_hasFDerivAt z))
  change HasFDerivAt potential _ z at hd
  rw [hd.fderiv]
  ext v
  simp only [core, map_add, map_sub, map_smul, add_apply, sub_apply, smul_apply, smul_eq_mul, Function.comp_apply]
  ring

lemma core_skew (z : CV) : SkewAt z (core z) := by
  unfold core
  apply skewAt_add
  · apply skewAt_add (skewAt_sub (left_skew 0 z) (right_skew 2 z))
    apply skewAt_smul
    unfold mixedField
    exact skewAt_sum Finset.univ _ (fun i _ ↦
      skewAt_add (skewAt_smul (left_skew i z) _) (skewAt_smul (right_skew i z) _))
  · apply skewAt_smul
    unfold selfField
    exact skewAt_sum Finset.univ _ (fun i _ ↦ skewAt_smul (left_skew i z) _)

end ArnoldCounterexample.Field

end

end OAI
