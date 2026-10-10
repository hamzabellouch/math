import Mathlib
import OAI.Analysis.HardSphere.Geometry.TorusLiftBox
import OAI.Analysis.HardSphere.Geometry.HeadLift
import OAI.Analysis.HardSphere.Cutoffs.Near
import OAI.Analysis.HardSphere.Operators.Regularize

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
namespace HardSphere.CellOrbital
open MeasureTheory Set Filter PeriodicCutoff TightCutoff
open scoped ComplexConjugate

def bump (L : Length) (δ : ℝ) (x y : Torus L) : ℝ :=
  Real.cos (TightCutoff.angle L.val δ y x)

def centerLift (L : Length) (x : Torus L) : Fin 3 → ℝ :=
  fun j ↦ (AddCircle.equivIco L.val 0 (x j)).val

lemma centerLift_coe (L : Length) (x : Torus L) :
    (fun j ↦ (centerLift L x j : AddCircle L.val))=x := by
  ext j
  exact AddCircle.coe_equivIco

lemma bump_project (L : Length) (δ : ℝ) (x : Torus L) (R : LiftedConfiguration 1) :
    bump L δ x (project 1 L R 0)=
      Real.cos (TightCutoff.angleLift L.val δ (R 0-centerLift L x)) := by
  unfold bump TightCutoff.angle TightCutoff.angleLift
  change Real.cos (Real.pi / 2 * Real.smoothTransition
    ((pairQ L.val (fun j ↦ (R 0 j : AddCircle L.val)) x-(5/4)*δ^2)/((1/4)*δ^2))) = _
  conv_lhs => rw [← centerLift_coe L x, pairQ_coe]

lemma bump_smooth (L : Length) (δ : ℝ) (x : Torus L) :
    ContDiff ℝ ((⊤:ℕ∞):WithTop ℕ∞)
      (fun R : LiftedConfiguration 1 ↦ (bump L δ x (project 1 L R 0) : ℂ)) := by
  simp_rw [bump_project]
  exact Complex.ofRealCLM.contDiff.comp ((Real.contDiff_cos.comp
    (TightCutoff.angleLift_smooth L.val δ)).comp ((contDiff_apply ℝ (Fin 3 → ℝ) 0).sub contDiff_const))

def raw (L : Length) (δ : ℝ) (x : Torus L) : SmoothMultiplier 1 L :=
  .ofSmooth (fun X ↦ (bump L δ x (X 0) : ℂ)) (bump_smooth L δ x)

lemma bump_continuous (L : Length) (δ : ℝ) (x : Torus L) : Continuous (bump L δ x) := by
  unfold bump TightCutoff.angle
  exact Real.continuous_cos.comp (continuous_const.mul (Real.smoothTransition.continuous.comp
    (((pairQ_continuous L.val).comp (continuous_id.prodMk continuous_const)).sub
      continuous_const |>.div_const _)))

lemma bump_bounds (L : Length) (δ : ℝ) (x y : Torus L) : 0 ≤ bump L δ x y ∧ bump L δ x y ≤ 1 := by
  refine ⟨?_,Real.cos_le_one _⟩
  apply Real.cos_nonneg_of_mem_Icc
  exact ⟨by linarith [(TightCutoff.angle_bounds L.val δ y x).1,Real.pi_pos],
    (TightCutoff.angle_bounds L.val δ y x).2⟩

lemma bump_eq_one {L : Length} {δ : ℝ} (hδ : 0<δ) (x : Torus L) {y : Torus L}
    (hy : y∈box L.val (δ/2) x) : bump L δ x y=1 := by
  have hd j : dist (y j) (x j) ≤ δ/2 := (Set.mem_univ_pi.mp hy) j
  have hq := pairQ_le L.val y x
  have hs : (∑ j : Fin 3, dist (y j) (x j)^2) ≤ 3*(δ/2)^2 := by
    calc
      _ ≤ ∑ _j : Fin 3, (δ/2)^2 := Finset.sum_le_sum fun j _ ↦
        (sq_le_sq₀ dist_nonneg (by positivity)).mpr (hd j)
      _ = _ := by simp
  unfold bump
  rw [TightCutoff.angle_zero L.val hδ (by nlinarith), Real.cos_zero]

lemma bump_eq_zero {L : Length} {δ : ℝ} (hδ : 0<δ) (x : Torus L) {y : Torus L}
    (hy : y∉TightCutoff.near L.val δ x) : bump L δ x y=0 := by
  rw [bump,TightCutoff.angle_one_outside L.val hδ hy,Real.cos_pi_div_two]

lemma bump_support {L : Length} {δ : ℝ} (hδ : 0<δ) (x : Torus L) :
    tsupport (bump L δ x) ⊆ TightCutoff.near L.val δ x := by
  apply closure_minimal
  · intro y hy
    by_contra hn
    exact hy (bump_eq_zero hδ x hn)
  · exact isClosed_le ((pairQ_continuous L.val).comp
      (continuous_id.prodMk continuous_const)) continuous_const

lemma box_volume_eq {L : Length} {b : ℝ} (hb : 0 ≤ b) (hbL : 2*b ≤ L.val) (x : Torus L) :
    volume.real (box L.val b x)=(2*b)^3 := by
  have he : volume (box L.val b x)=ENNReal.ofReal (min L.val (2*b))^3 := by
    rw [volume_pi,box,Measure.pi_pi]
    simp_rw [AddCircle.volume_closedBall]
    simp
  rw [measureReal_def,he,min_eq_right hbL,ENNReal.toReal_pow,
    ENNReal.toReal_ofReal (by positivity)]

def mass (L : Length) (δ : ℝ) (x : Torus L) : ℝ := ∫ y : Torus L, (bump L δ x y)^2

lemma mass_lower {L : Length} {δ : ℝ} (hδ : 0<δ) (hδL : δ ≤ L.val) (x : Torus L) :
    δ^3 ≤ mass L δ x := by
  have hi : Integrable (fun y : Torus L ↦ (bump L δ x y)^2) volume :=
    ((bump_continuous L δ x).pow 2).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
  calc
    _ = volume.real (box L.val (δ/2) x) := by rw [box_volume_eq (by positivity) (by linarith)]; ring
    _ = ∫ y in box L.val (δ/2) x, (bump L δ x y)^2 := by
      rw [setIntegral_congr_fun (box_measurable _ _ _) (fun y hy ↦ by rw [bump_eq_one hδ x hy])]
      simp
    _ ≤ mass L δ x := setIntegral_le_integral hi (Filter.Eventually.of_forall fun _ ↦ sq_nonneg _)

lemma mass_pos {L : Length} {δ : ℝ} (hδ : 0<δ) (hδL : δ ≤ L.val) (x : Torus L) :
    0 < mass L δ x := lt_of_lt_of_le (by positivity) (mass_lower hδ hδL x)

lemma raw_fderiv (L : Length) (δ : ℝ) (x : Torus L) (R v : LiftedConfiguration 1) :
    fderiv ℝ (fun R ↦ (raw L δ x).toFun (project 1 L R)) R v =
      ((-Real.sin (TightCutoff.angleLift L.val δ (R 0-centerLift L x)) *
        ∑ j : Fin 3, TightCutoff.anglePartial L.val δ (R 0-centerLift L x) j*v 0 j : ℝ) : ℂ) := by
  have hd : HasDerivAt (fun t : ℝ ↦ R+t • v) v 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const v).const_add R
  have hf := ((((raw L δ x).smooth).differentiable (by simp)) R).hasFDerivAt.comp_hasDerivAt_of_eq 0 hd (by simp)
  have ha := TightCutoff.angleLift_derivative L.val δ
    (fun j t ↦ R 0 j+t*v 0 j-centerLift L x j) (fun j ↦ v 0 j) 0 (fun j ↦ by
      convert ((((hasDerivAt_id (0:ℝ)).mul_const (v 0 j)).const_add (R 0 j)).sub_const (centerLift L x j)) using 1 <;> first | rfl | simp only [one_mul])
  have hb := Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt 0 ha.cos
  have he : ((fun R ↦ (raw L δ x).toFun (project 1 L R)) ∘ fun t : ℝ ↦ R+t • v) =
      (fun t : ℝ ↦ (Real.cos (TightCutoff.angleLift L.val δ
        (fun j ↦ R 0 j+t*v 0 j-centerLift L x j)) : ℂ)) := by
    funext t
    exact congrArg Complex.ofReal (bump_project L δ x (R+t • v))
  rw [he] at hf
  convert hf.unique hb using 1
  simp only [zero_mul,add_zero,Complex.ofRealCLM_apply]
  rfl

lemma raw_partial (L : Length) (δ : ℝ) (x y : Torus L) (j : Fin 3) :
    coordDerivative 1 L (raw L δ x).toFun (0,j) (fun _ ↦ y)=
      ((-Real.sin (TightCutoff.angleLift L.val δ (centerLift L y-centerLift L x)) *
        TightCutoff.anglePartial L.val δ (centerLift L y-centerLift L x) j : ℝ) : ℂ) := by
  rw [coordDerivative,raw_fderiv]
  change (Complex.ofReal (-Real.sin _ * ∑ k : Fin 3, _ * (Pi.single j (1:ℝ)) k)) = _
  simp only [Pi.single_apply,mul_ite,mul_one,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  rfl

lemma raw_partial_sq_le {L : Length} {δ M : ℝ} (hδ : 0<δ) (hM : 0 ≤ M)
    (hb : ∀ t : ℝ, |deriv Real.smoothTransition t| ≤ M) (x y : Torus L) (j : Fin 3) :
    ‖coordDerivative 1 L (raw L δ x).toFun (0,j) (fun _ ↦ y)‖^2 ≤ 24*Real.pi^2*M^2/δ^2 := by
  rw [raw_partial,Complex.norm_real,Real.norm_eq_abs,sq_abs,mul_pow,neg_sq]
  calc
    _ ≤ 1*(TightCutoff.anglePartial L.val δ (centerLift L y-centerLift L x) j)^2 := by
      gcongr
      exact Real.sin_sq_le_one _
    _ ≤ _ := by simpa using TightCutoff.anglePartial_sq_le L.val hδ hM hb (centerLift L y-centerLift L x) j

lemma raw_partial_zero {L : Length} {δ : ℝ} (hδ : 0<δ) (x y : Torus L) (j : Fin 3)
    (hy : y∉TightCutoff.near L.val δ x) :
    coordDerivative 1 L (raw L δ x).toFun (0,j) (fun _ ↦ y)=0 := by
  have he : qLift L.val (centerLift L y-centerLift L x)=pairQ L.val y x := by
    rw [← pairQ_coe,centerLift_coe,centerLift_coe]
  have hn : qLift L.val (centerLift L y-centerLift L x)∉Icc ((5/4)*δ^2) ((3/2)*δ^2) := by
    rw [he]
    exact fun h ↦ hy h.2
  rw [raw_partial,TightCutoff.anglePartial_eq_zero L.val hδ hn,mul_zero,Complex.ofReal_zero]

lemma raw_energy_le {L : Length} {δ M : ℝ} (hδ : 0<δ) (hM : 0 ≤ M)
    (hb : ∀ t : ℝ, |deriv Real.smoothTransition t| ≤ M) (x : Torus L) :
    (raw L δ x).orbitalEnergy ≤ 3*(24*Real.pi^2*M^2/δ^2)*(4*δ)^3 := by
  have hpart (j : Fin 3) :
      (∫ y : Torus L, ‖coordDerivative 1 L (raw L δ x).toFun (0,j) (fun _ ↦ y)‖^2) ≤
        (24*Real.pi^2*M^2/δ^2)*(4*δ)^3 := by
    let f := fun y : Torus L ↦ ‖coordDerivative 1 L (raw L δ x).toFun (0,j) (fun _ ↦ y)‖^2
    have hf : Continuous f := ((continuous_coordDerivative (raw L δ x).smooth (0,j)).comp
      (continuous_pi fun _ ↦ continuous_id)).norm.pow 2
    have hi : Integrable f volume := hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have he : (∫ y, f y) = ∫ y in TightCutoff.near L.val δ x, f y := by
      symm
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro y hy
      simp [f,raw_partial_zero hδ x y j hy]
    rw [he]
    calc
      _ ≤ ∫ _y in TightCutoff.near L.val δ x, (24*Real.pi^2*M^2/δ^2) :=
        setIntegral_mono_on hi.integrableOn (integrableOn_const) (TightCutoff.near_measurable _ _ _)
          (fun y _ ↦ raw_partial_sq_le hδ hM hb x y j)
      _ = volume.real (TightCutoff.near L.val δ x)*(24*Real.pi^2*M^2/δ^2) := by simp
      _ ≤ _ := by
        simpa only [mul_comm] using mul_le_mul_of_nonneg_right (TightCutoff.near_volume_le L.val hδ x)
          (show 0 ≤ 24*Real.pi^2*M^2/δ^2 by positivity)
  unfold SmoothMultiplier.orbitalEnergy
  calc
    _ ≤ ∑ _j : Fin 3, (24*Real.pi^2*M^2/δ^2)*(4*δ)^3 := Finset.sum_le_sum fun j _ ↦ hpart j
    _ = _ := by simp; ring

def normalized (L : Length) (δ : ℝ) (x : Torus L) : SmoothMultiplier 1 L :=
  .ofSmooth (fun X ↦ (((Real.sqrt (mass L δ x))⁻¹ : ℝ) : ℂ)*(raw L δ x).toFun X)
    (contDiff_const.mul (raw L δ x).smooth)

lemma normalized_real (L : Length) (δ : ℝ) (x : Torus L) (X : Configuration 1 L) :
    conj ((normalized L δ x).toFun X)=(normalized L δ x).toFun X := by
  simp [normalized,raw,SmoothMultiplier.ofSmooth]

lemma normalized_norm_sq {L : Length} {δ : ℝ} (hδ : 0<δ) (hδL : δ ≤ L.val) (x y : Torus L) :
    ‖(normalized L δ x).orbital y‖^2=(mass L δ x)⁻¹*(bump L δ x y)^2 := by
  change ‖(((Real.sqrt (mass L δ x))⁻¹ : ℝ) : ℂ)*(bump L δ x y : ℂ)‖^2 = _
  rw [norm_mul,mul_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs,Complex.norm_real,Real.norm_eq_abs,sq_abs,
    inv_pow,Real.sq_sqrt (mass_pos hδ hδL x).le]

lemma normalized_mass {L : Length} {δ : ℝ} (hδ : 0<δ) (hδL : δ ≤ L.val) (x : Torus L) :
    (∫ y : Torus L, ‖(normalized L δ x).orbital y‖^2)=1 := by
  simp_rw [normalized_norm_sq hδ hδL]
  rw [integral_const_mul]
  exact inv_mul_cancel₀ (mass_pos hδ hδL x).ne'

lemma normalized_support {L : Length} {δ : ℝ} (hδ : 0<δ) (x : Torus L) :
    tsupport (normalized L δ x).orbital ⊆ TightCutoff.near L.val δ x := by
  apply closure_minimal
  · intro y hy
    by_contra hn
    apply hy
    change (((Real.sqrt (mass L δ x))⁻¹ : ℝ) : ℂ)*(bump L δ x y : ℂ)=0
    rw [bump_eq_zero hδ x hn,Complex.ofReal_zero,mul_zero]
  · exact isClosed_le ((pairQ_continuous L.val).comp
      (continuous_id.prodMk continuous_const)) continuous_const

lemma normalized_bound {L : Length} {δ : ℝ} (hδ : 0<δ) (hδL : δ ≤ L.val) (x : Torus L) :
    (normalized L δ x).orbitalBound ≤ (δ^3)⁻¹ := by
  have hs : 0<Real.sqrt (mass L δ x) := Real.sqrt_pos.mpr (mass_pos hδ hδL x)
  have hb : ‖(⟨(normalized L δ x).orbital,(normalized L δ x).orbital_continuous⟩ : C(Torus L,ℂ))‖ ≤
      (Real.sqrt (mass L δ x))⁻¹ := by
    apply (ContinuousMap.norm_le _ (by positivity)).mpr
    intro y
    change ‖(((Real.sqrt (mass L δ x))⁻¹ : ℝ) : ℂ)*(bump L δ x y : ℂ)‖ ≤ _
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hs),
      Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (bump_bounds L δ x y).1]
    exact mul_le_of_le_one_right (by positivity) (bump_bounds L δ x y).2
  calc
    _ ≤ ((Real.sqrt (mass L δ x))⁻¹)^2 := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hb
    _ = (mass L δ x)⁻¹ := by rw [inv_pow,Real.sq_sqrt (mass_pos hδ hδL x).le]
    _ ≤ _ := inv_anti₀ (by positivity) (mass_lower hδ hδL x)

lemma normalized_partial (L : Length) (δ : ℝ) (x y : Torus L) (j : Fin 3) :
    coordDerivative 1 L (normalized L δ x).toFun (0,j) (fun _ ↦ y)=
      (((Real.sqrt (mass L δ x))⁻¹ : ℝ) : ℂ)*coordDerivative 1 L (raw L δ x).toFun (0,j) (fun _ ↦ y) := by
  unfold coordDerivative
  change (fderiv ℝ (fun R ↦ (((Real.sqrt (mass L δ x))⁻¹ : ℝ) : ℂ)*(raw L δ x).toFun (project 1 L R)) _) _ = _
  rw [fderiv_const_mul (((raw L δ x).smooth.differentiable (by simp)) _)]
  rfl

lemma normalized_energy_le {L : Length} {δ M : ℝ} (hδ : 0<δ) (hδL : δ ≤ L.val)
    (hM : 0 ≤ M) (hb : ∀ t : ℝ, |deriv Real.smoothTransition t| ≤ M) (x : Torus L) :
    (normalized L δ x).orbitalEnergy ≤ (δ^3)⁻¹*(3*(24*Real.pi^2*M^2/δ^2)*(4*δ)^3) := by
  have he : (normalized L δ x).orbitalEnergy=(mass L δ x)⁻¹*(raw L δ x).orbitalEnergy := by
    unfold SmoothMultiplier.orbitalEnergy
    simp_rw [normalized_partial,norm_mul,mul_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs,
      inv_pow,Real.sq_sqrt (mass_pos hδ hδL x).le,integral_const_mul]
    rw [Finset.mul_sum]
  rw [he]
  apply mul_le_mul
  · exact inv_anti₀ (by positivity) (mass_lower hδ hδL x)
  · exact raw_energy_le hδ hM hb x
  · exact Finset.sum_nonneg fun j _ ↦ integral_nonneg fun _ ↦ sq_nonneg _
  · positivity

theorem uniform_orbitals : ∃ B E : ℝ, 0<B ∧ 0<E ∧
    ∀ L : Length, (1:ℝ)/100 ≤ L.val → ∀ x : Torus L,
    (∀ X, conj ((normalized L (1/100) x).toFun X)=(normalized L (1/100) x).toFun X) ∧
    (∫ y : Torus L, ‖(normalized L (1/100) x).orbital y‖^2)=1 ∧
    (normalized L (1/100) x).orbitalBound ≤ B ∧
    (normalized L (1/100) x).orbitalEnergy ≤ E ∧
    tsupport (normalized L (1/100) x).orbital ⊆ TightCutoff.near L.val (1/100) x := by
  obtain ⟨M,hM,hb⟩ := exists_transition_bound
  refine ⟨((1/100:ℝ)^3)⁻¹,((1/100:ℝ)^3)⁻¹*(3*(24*Real.pi^2*M^2/(1/100:ℝ)^2)*(4*(1/100:ℝ))^3),
    by positivity,by positivity,?_⟩
  intro L hL x
  exact ⟨normalized_real L _ x,normalized_mass (by norm_num) hL x,
    normalized_bound (by norm_num) hL x,normalized_energy_le (by norm_num) hL hM.le hb x,
    normalized_support (by norm_num) x⟩

end HardSphere.CellOrbital

end

end OAI
