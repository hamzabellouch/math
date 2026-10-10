import OAI.Geometry.Arnold.Hamiltonian

namespace OAI

noncomputable section
open scoped BigOperators ContDiff
open scoped Topology NNReal
open Set Filter

namespace ArnoldCounterexample.Construction
open ArnoldCounterexample.Quadric ArnoldCounterexample.Field ArnoldCounterexample.Factors
open ArnoldCounterexample.ThreePoints
open scoped ContDiff Topology Matrix
open Set Filter

lemma fixed_lift (z : UnitQuadric) (hz : mainEquiv (project z) = project z) :
    ∃ c : ℂ, Complex.normSq c = 1 ∧ c • (z:CV) = forward (1,z) := by
  rw [mainEquiv_project] at hz
  exact (project_eq_iff_phase _ _).mp hz

lemma fixed_zero_coordinate (z : UnitQuadric) (hz : mainEquiv (project z) = project z) :
    (z:CV) 0 = 0 := by
  by_contra hzero
  obtain ⟨c,hc,he⟩ := fixed_lift z hz
  have he0 := congrFun he 0
  simp only [Pi.smul_apply, smul_eq_mul, forward, rotationPath_finish,
    involutionLinear_apply, forwardMid_zero_coordinate] at he0
  have hc1 : c = 1 := (mul_right_cancel₀ hzero (he0.trans (one_mul _).symm))
  rw [hc1, one_smul] at he
  have hrest (i : Fin 5) (hi : i ≠ 0) : center (1,z) i = 0 := by
    have hei := congrFun he i
    simp only [forward, rotationPath_finish, involutionLinear_apply, ite_eq_right hi] at hei
    have hav := congrFun (center_average (1,z)) i
    simp only [Pi.smul_apply, Pi.add_apply, Complex.real_smul] at hav
    rw [hei, neg_add_cancel] at hav
    exact (mul_eq_zero.mp hav).resolve_left (by norm_num)
  have hX : vectorField (center (1,z)) = 0 := vectorField_zero_rest _ hrest
  have hcenter : center (1,z) = (z:CV) := by simpa only [hX, smul_zero, add_zero] using center_identity (1,z)
  have hzrest (i : Fin 5) (hi : i ≠ 0) : (z:CV) i = 0 := by rw [← hcenter]; exact hrest i hi
  have hp := z.property.2
  simp only [quadricPolynomial, Fin.sum_univ_succ] at hp
  simp [hzrest] at hp
  exact hzero hp

lemma fixed_mid_phase (z : UnitQuadric) (hz : mainEquiv (project z) = project z) :
    ∃ d : ℂ, Complex.normSq d = 1 ∧ forwardMid (1,z) = d • (z:CV) := by
  obtain ⟨c,hc,he⟩ := fixed_lift z hz
  refine ⟨-c, by simpa using hc, ?_⟩
  ext i
  have hei := congrFun he i
  by_cases hi : i = 0
  · subst i
    simp [forwardMid_zero_coordinate, fixed_zero_coordinate z hz]
  · simp only [Pi.smul_apply, smul_eq_mul, forward, rotationPath_finish,
      involutionLinear_apply, ite_eq_right hi] at hei ⊢
    linear_combination hei

lemma fixed_factor_critical (z : UnitQuadric) (hz : mainEquiv (project z) = project z) :
    MultiplierCritical (sphereFactors z) := by
  have hz0 := fixed_zero_coordinate z hz
  obtain ⟨d,hd,hM⟩ := fixed_mid_phase z hz
  let a : ℂ := (1+d)/2
  have hcenter : center (1,z) = a • (z:CV) := by
    have hav := center_average (1,z)
    rw [hM] at hav
    ext i
    have hi := congrFun hav i
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, Complex.real_smul] at hi ⊢
    norm_num at hi
    dsimp [a]
    linear_combination hi/2
  have ha : Complex.normSq a ∈ Ioo (1/2:ℝ) 2 := by
    have h := center_bound 1 z
    simpa only [hcenter, normSquared_smul, z.property.1, mul_one] using h
  have hX : vectorField (center (1,z)) = a • core z := by
    rw [vectorField, cutoff_eq_one (le_of_lt (lt_trans (center_bound 1 z).2 (by norm_num))),
      one_smul, hcenter, core_homogeneous z hz0 a ha]
  have hId := center_identity (1,z)
  rw [hX, hcenter, parameter_one] at hId
  have ha0 : a ≠ 0 := by intro h; simp [h] at ha; linarith
  apply core_complex_vertical_critical z hz0 ((a-1)/((epsilon:ℂ)*a))
  ext i
  have hi := congrFun hId i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Complex.real_smul] at hi ⊢
  have he0 : (epsilon:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt epsilon_pos)
  field_simp
  linear_combination -hi

end ArnoldCounterexample.Construction

namespace ArnoldCounterexample.Construction
open ArnoldCounterexample.Quadric ArnoldCounterexample.Field ArnoldCounterexample.Factors
open ArnoldCounterexample.ThreePoints
open scoped ContDiff Topology Matrix
open Set Filter

lemma epsilon_le : epsilon ≤ 1/100 := by
  have hc := constant.coe_nonneg
  unfold epsilon
  rw [div_le_div_iff₀ (by positivity : 0 < 100*((constant:ℝ)+1)) (by norm_num : (0:ℝ)<100)]
  nlinarith

lemma vertical_core_fixed (z : UnitQuadric) (hz0 : (z:CV) 0 = 0) (b : ℝ)
    (hb : |b| ≤ 3) (hcore : core z = b • (Complex.I • (z:CV))) :
    mainEquiv (project z) = project z := by
  let s : ℝ := epsilon*b
  have hs : |s| ≤ 3/100 := by
    dsimp [s]
    rw [abs_mul, abs_of_pos epsilon_pos]
    nlinarith [mul_le_mul epsilon_le hb (abs_nonneg b) (by norm_num : (0:ℝ)≤1/100)]
  have hsq : s^2 < 1 := by
    have := abs_le.mp hs
    nlinarith [this.1,this.2]
  let a : ℂ := (1-(s:ℂ)*Complex.I)⁻¹
  have hden : (1-(s:ℂ)*Complex.I) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
  have hna : Complex.normSq a = (1+s^2)⁻¹ := by
    simp [a, Complex.normSq_apply, pow_two]
  have ha : Complex.normSq a ∈ Ioo (1/2:ℝ) 2 := by
    rw [hna]
    constructor
    · have h := (inv_lt_inv₀ (by norm_num : (0:ℝ)<2) (by positivity : (0:ℝ)<1+s^2)).mpr (by linarith : 1+s^2 < 2)
      norm_num at h ⊢
      exact h
    · have := inv_le_one_of_one_le₀ (by nlinarith [sq_nonneg s] : (1:ℝ)≤1+s^2)
      linarith
  have hn : normSquared (a • (z:CV)) < 4 := by
    rw [normSquared_smul, z.property.1, mul_one]
    linarith [ha.2]
  have hX : vectorField (a • (z:CV)) = a • core z := by
    rw [vectorField, cutoff_eq_one hn.le, one_smul, core_homogeneous z hz0 a ha]
  have haeq : a = 1 + (s:ℂ)*Complex.I*a := by
    dsimp [a]
    field_simp
    ring
  have hcenter : center (1,z) = a • (z:CV) := by
    symm
    apply Midpoint.resolvent_unique _ lipschitz _ parameter_contract
    rw [hX, hcore, parameter_one]
    ext i
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, Complex.real_smul]
    have hi := congrArg (fun c : ℂ ↦ c * (z:CV) i) haeq
    dsimp [s] at hi
    rw [Complex.ofReal_mul] at hi
    linear_combination hi
  have hM : forwardMid (1,z) = (2*a-1) • (z:CV) := by
    change (2:ℝ) • center (1,z) - (z:CV) = _
    rw [hcenter]
    ext i
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Complex.real_smul]
    norm_num
    ring
  have hF : forward (1,z) = (-(2*a-1)) • (z:CV) := by
    rw [forward, rotationPath_finish, hM]
    ext i
    by_cases hi : i = 0
    · subst i; simp [hz0]
    · simp [involutionLinear_apply, hi]
      ring
  have hphase : Complex.normSq (-(2*a-1)) = 1 := by
    have hn := (forward_preserves 1 z).1
    rwa [hF, normSquared_smul, z.property.1, mul_one] at hn
  rw [mainEquiv_project]
  exact (project_eq_iff_phase _ _).mpr ⟨_,hphase,hF.symm⟩

end ArnoldCounterexample.Construction

end

end OAI
