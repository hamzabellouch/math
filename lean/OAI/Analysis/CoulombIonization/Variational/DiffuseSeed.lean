import Mathlib
import OAI.Analysis.CoulombIonization.RadialBounds.TruncationRadius
import OAI.Analysis.CoulombIonization.FormDomain.Form

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace ENNReal
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open Set Filter Topology InnerProductSpace Laplacian
open MeasureTheory Filter
open scoped Topology
open MeasureTheory Filter
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter
open scoped Topology BigOperators Pointwise
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open scoped Convolution
open scoped RealInnerProductSpace
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Set Filter Metric Topology InnerProductSpace Laplacian
open MeasureTheory Set Filter Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open Filter
open scoped Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace ContDiff BigOperators
open MeasureTheory Filter Set
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open scoped BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators

def diffuseSeed (R : ℝ) (x : Configuration 1) : ℂ := trialSeed 1 (R⁻¹ • x)

def diffuseRaw (R : ℝ) : FormVector 1 := smoothForm (diffuseSeed R)

lemma diffuseSeed_smooth (R : ℝ) : ContDiff ℝ ∞ (diffuseSeed R) :=
  (trialSeed_smooth 1).comp (R⁻¹ • ContinuousLinearMap.id ℝ (Configuration 1)).contDiff

lemma diffuseSeed_compact {R : ℝ} (hR : 0 < R) : HasCompactSupport (diffuseSeed R) :=
  (trialSeed_compact 1).comp_smul (inv_ne_zero hR.ne')

lemma diffuseRaw_sobolev (R : ℝ) (hR : 0 < R) : SobolevFermion (diffuseRaw R) := by
  refine ⟨fun _ => (diffuseSeed_smooth R).continuous.memLp_of_hasCompactSupport
    (diffuseSeed_compact hR),fun s i a => ?_,fun s i a φ hφ hcφ => ?_,?_⟩
  · exact (smooth_derivative_continuous (diffuseSeed_smooth R) _).memLp_of_hasCompactSupport
      (compact_derivative (diffuseSeed_compact hR) _)
  · exact smooth_weak_gradient (diffuseSeed_smooth R) (diffuseSeed_compact hR) hφ hcφ _
  · intro π s
    have hp : π = 1 := Subsingleton.elim _ _
    subst π
    exact Eventually.of_forall fun x => by simp [diffuseRaw,smoothForm]

lemma diffuseRaw_mass_pos {R : ℝ} (hR : 0 < R) : 0 < formMass (diffuseRaw R) := by
  have hn : diffuseSeed R (R • trialCenter 1) = 1 := by
    simp only [diffuseSeed,smul_smul,inv_mul_cancel₀ hR.ne',one_smul,trialSeed_center]
  have hi : 0 < ∫ x, ‖diffuseSeed R x‖^2 :=
    ((diffuseSeed_smooth R).continuous.norm.pow 2).integral_pos_of_hasCompactSupport_nonneg_nonzero
      (compact_norm_sq (diffuseSeed_compact hR)) (fun x => sq_nonneg _)
      (x := R • trialCenter 1) (by rw [hn]; norm_num)
  change 0 < ∑ _s : Spins 1, ∫ x, ‖diffuseSeed R x‖^2
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  exact mul_pos (Nat.cast_pos.mpr Fintype.card_pos) hi

lemma diffuseRaw_gradient (R : ℝ) (s : Spins 1) (i : Fin 1) (a : Fin 3) (x : Configuration 1) :
    (diffuseRaw R).gradient s i a x = R⁻¹ •
      (smoothForm (trialSeed 1)).gradient s i a (R⁻¹ • x) := by
  change fderiv ℝ ((trialSeed 1) ∘ ⇑(R⁻¹ • ContinuousLinearMap.id ℝ (Configuration 1))) x (direction i a) = _
  rw [fderiv_comp x ((trialSeed_smooth 1).differentiable (by simp)).differentiableAt
    (R⁻¹ • ContinuousLinearMap.id ℝ (Configuration 1)).differentiableAt]
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.fderiv,
    smul_apply,ContinuousLinearMap.id_apply,map_smul,smoothForm]

lemma diffuseRaw_mass (R : ℝ) (hR : 0 < R) :
    formMass (diffuseRaw R) = R ^ Module.finrank ℝ (Configuration 1) *
      formMass (smoothForm (trialSeed 1)) := by
  unfold formMass
  simp only [diffuseRaw,smoothForm,diffuseSeed]
  have hi := Measure.integral_comp_inv_smul_of_nonneg (volume : Measure (Configuration 1))
    (fun x => ‖trialSeed 1 x‖^2) hR.le
  simp only [smul_eq_mul] at hi
  simp_rw [hi,Finset.mul_sum]

lemma diffuseRaw_kinetic (R : ℝ) (hR : 0 < R) :
    formKinetic (diffuseRaw R) = R⁻¹^2 * R ^ Module.finrank ℝ (Configuration 1) *
      formKinetic (smoothForm (trialSeed 1)) := by
  unfold formKinetic
  simp_rw [diffuseRaw_gradient,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,integral_const_mul]
  have hi (s : Spins 1) (i : Fin 1) (a : Fin 3) :=
    Measure.integral_comp_inv_smul_of_nonneg (volume : Measure (Configuration 1))
      (fun x => ‖(smoothForm (trialSeed 1)).gradient s i a x‖^2) hR.le
  simp only [smul_eq_mul] at hi
  simp_rw [hi,← Finset.mul_sum]
  ring

lemma formKinetic_scale {N : ℕ} (c : ℝ) (ψ : FormVector N) :
    formKinetic (scaleForm c ψ) = c^2*formKinetic ψ := by
  unfold formKinetic
  simp only [scaleForm,norm_real_mul_sq,integral_const_mul,← Finset.mul_sum]
  ring

def diffuseOrbital (R : ℝ) : FormVector 1 :=
  scaleForm (Real.sqrt (formMass (diffuseRaw R)))⁻¹ (diffuseRaw R)

lemma diffuseOrbital_admissible {R : ℝ} (hR : 0 < R) : FormAdmissible (diffuseOrbital R) :=
  (diffuseRaw_sobolev R hR).normalize (diffuseRaw_mass_pos hR)

def diffuseKinetic : ℝ :=
  formKinetic (smoothForm (trialSeed 1)) / formMass (smoothForm (trialSeed 1))

lemma diffuseKinetic_nonneg : 0 ≤ diffuseKinetic :=
  div_nonneg (formKinetic_nonneg _) (by unfold formMass; positivity)

lemma diffuseOrbital_kinetic {R : ℝ} (hR : 0 < R) :
    formKinetic (diffuseOrbital R) = diffuseKinetic / R^2 := by
  have hmpos : 0 < formMass (smoothForm (trialSeed 1)) := by
    have hh := diffuseRaw_mass_pos (by norm_num : (0:ℝ)<1)
    rw [diffuseRaw_mass 1 (by norm_num), one_pow, one_mul] at hh
    exact hh
  rw [diffuseOrbital,formKinetic_scale,inv_pow,Real.sq_sqrt (diffuseRaw_mass_pos hR).le,
    diffuseRaw_mass R hR,diffuseRaw_kinetic R hR,diffuseKinetic]
  field_simp

lemma diffuseSeed_zero {R : ℝ} (hR : 0 < R) {x : Configuration 1} (hx : ‖x 0‖ < R) :
    diffuseSeed R x = 0 := by
  by_contra hn
  have hh := trialSeed_nucleus hn (0 : Fin 1)
  change 1 ≤ ‖R⁻¹ • x 0‖ at hh
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hR)] at hh
  have hl : R⁻¹ * ‖x 0‖ < 1 := by
    rw [← div_eq_inv_mul,div_lt_one hR]
    exact hx
  exact not_lt_of_ge hh hl

lemma diffuseRaw_zero {R : ℝ} (hR : 0 < R) {x : Configuration 1} (hx : ‖x 0‖ < R) :
    FormZeroAt (diffuseRaw R) x := by
  have he : diffuseSeed R =ᶠ[𝓝 x] fun _ => (0:ℂ) :=
    (((continuous_apply (0 : Fin 1)).norm.tendsto x).eventually (eventually_lt_nhds hx)).mono
      fun _ hy => diffuseSeed_zero hR hy
  intro s
  refine ⟨diffuseSeed_zero hR hx,fun i a => ?_⟩
  change fderiv ℝ (diffuseSeed R) x (direction i a) = 0
  rw [he.fderiv_eq]
  simp

lemma diffuseOrbital_zero {R : ℝ} (hR : 0 < R) {x : Configuration 1} (hx : ‖x 0‖ < R) :
    FormZeroAt (diffuseOrbital R) x := by
  intro s
  have hh := diffuseRaw_zero hR hx s
  constructor
  · change _ * (diffuseRaw R).value s x = 0
    rw [hh.1,mul_zero]
  · intro i a
    change _ * (diffuseRaw R).gradient s i a x = 0
    rw [hh.2,mul_zero]


open MeasureTheory Filter
open scoped Topology ContDiff BigOperators


lemma tensorCross_le {N : ℕ} {ψ : FormVector N} {φ : FormVector 1}
    (hψ : SobolevVector ψ) (hφ : SobolevVector φ) {R d : ℝ} (hd : 0 < d)
    (hc : ∀ s x i, R ≤ ‖x i‖ → ψ.value s x = 0)
    (he : ∀ s x, ‖x 0‖ < R+d → φ.value s x = 0) :
    tensorCross ψ φ ≤ (N : ℝ)/d * formMass ψ * formMass φ := by
  have hT := hψ.tensor hφ
  have hi (s : Spins N) (t : Spins 1) (i : Fin N) :
      (∫ z, ‖(tensorForm ψ φ).value (joinLists s t) z‖^2 / ‖z i.castSucc-z (Fin.last N)‖) ≤
      d⁻¹ * (∫ x, ‖ψ.value s x‖^2) * (∫ y, ‖φ.value t y‖^2) := by
    have hn : i.castSucc ≠ Fin.last N := Fin.castSucc_ne_last i
    calc
      _ ≤ ∫ z, d⁻¹ * ‖(tensorForm ψ φ).value (joinLists s t) z‖^2 := by
        apply integral_mono
          (pair_integrable _ _ hn (hT.1 _) (hT.2.1 _ _) (hT.2.2 _ _))
          (((hT.1 _).integrable_norm_pow (by norm_num)).const_mul d⁻¹)
        intro z
        dsimp only
        by_cases hz : (tensorForm ψ φ).value (joinLists s t) z = 0
        · simp only [hz,norm_zero,zero_pow (by norm_num : 2 ≠ 0),zero_div,mul_zero,le_refl]
        · have hz' : ψ.value s (leftList z) ≠ 0 ∧ φ.value t (rightList z) ≠ 0 := by
            simpa only [tensorForm,leftList_join,rightList_join,mul_ne_zero_iff] using hz
          have hin : ‖z i.castSucc‖ < R := lt_of_not_ge fun h => hz'.1 (hc _ _ i h)
          have hout : R+d ≤ ‖z (Fin.last N)‖ := le_of_not_gt fun h => hz'.2 (he _ _ h)
          have hg : d ≤ ‖z i.castSucc-z (Fin.last N)‖ := by
            have ht := norm_sub_norm_le (z (Fin.last N)) (z i.castSucc)
            rw [norm_sub_rev] at ht
            linarith
          rw [← div_eq_inv_mul]
          exact div_le_div_of_nonneg_left (sq_nonneg _) hd hg
      _ = _ := by
        rw [integral_const_mul]
        have hh : (∫ z, ‖(tensorForm ψ φ).value (joinLists s t) z‖^2) =
            (∫ x, ‖ψ.value s x‖^2)*(∫ y, ‖φ.value t y‖^2) := by
          simp only [tensorForm,leftList_join,rightList_join,norm_mul,mul_pow]
          exact integral_product_join (N := N) (M := 1)
            (fun x => ‖ψ.value s x‖^2) (fun y => ‖φ.value t y‖^2)
        rw [hh,mul_assoc]
  calc
    tensorCross ψ φ ≤ ∑ s : Spins N, ∑ t : Spins 1, ∑ _i : Fin N,
        d⁻¹ * (∫ x, ‖ψ.value s x‖^2) * (∫ y, ‖φ.value t y‖^2) := by
      exact Finset.sum_le_sum fun s _ => Finset.sum_le_sum fun t _ => Finset.sum_le_sum fun i _ => hi s t i
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
      unfold formMass
      simp_rw [mul_assoc,← Finset.mul_sum,← Finset.sum_mul]
      ring

lemma exterior_insertion_trial {N : ℕ} {ψ : FormVector N} (hψ : FormAdmissible ψ)
    {Z R r : ℝ} (hZ : 0 ≤ Z) (hR : 0 < R) (hr : 2*R ≤ r)
    (hc : ∀ x i, R ≤ ‖x i‖ → FormZeroAt ψ x) :
    ∃ F : FormVector (N+1), FormAdmissible F ∧
      formEnergy Z F ≤ formEnergy Z ψ + diffuseKinetic/r^2 + 2*(N : ℝ)/r := by
  have hrp : 0 < r := lt_of_lt_of_le (mul_pos (by norm_num) hR) hr
  have hφ := diffuseOrbital_admissible hrp
  obtain ⟨F,hF,hFE⟩ := normalized_wedge_trial hψ hφ R hc
    (fun x hx => diffuseOrbital_zero hrp (lt_of_lt_of_le hx (by linarith))) Z
  refine ⟨F,hF,?_⟩
  have hcross := tensorCross_le hψ.sobolevFermion.sobolevVector
    hφ.sobolevFermion.sobolevVector (R := R) (d := r/2) (half_pos hrp)
    (fun s x i hx => (hc x i hx s).1)
    (fun s x hx => (diffuseOrbital_zero hrp (lt_of_lt_of_le hx (by linarith)) s).1)
  have hmψ : formMass ψ = 1 := hψ.2.2.2.2.1
  have hmφ : formMass (diffuseOrbital r) = 1 := hφ.2.2.2.2.1
  rw [hmψ,hmφ,mul_one,mul_one] at hcross
  rw [hFE,formEnergy_tensor_one,hmψ,hmφ,mul_one,one_mul,diffuseOrbital_kinetic hrp]
  have hn := mul_nonneg hZ (formNuclear_nonneg (diffuseOrbital r))
  have hc' : (N : ℝ)/(r/2) = 2*(N : ℝ)/r := by ring
  rw [hc'] at hcross
  linarith

theorem quantum_energy_succ_le {Z : ℝ} (hZ : 0 ≤ Z) (N : ℕ) :
    energy Z (N+1) ≤ energy Z N := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨R,hR,ψ,hψ,hene,hc⟩ := quantum_sector_compact_near_minimizer Z N (half_pos hε)
  have ht : Tendsto (fun r : ℝ => diffuseKinetic/r^2 + 2*(N : ℝ)/r) atTop (𝓝 0) := by
    have hh := (tendsto_const_nhds (x := diffuseKinetic)).div_atTop
      (tendsto_pow_atTop (by norm_num : 2 ≠ 0))
    have hk := (tendsto_const_nhds (x := 2*(N : ℝ))).div_atTop tendsto_id
    simpa only [zero_add, id_eq] using hh.add hk
  have he : ∀ᶠ r : ℝ in atTop, diffuseKinetic/r^2 + 2*(N : ℝ)/r < ε/2 :=
    ht.eventually (eventually_lt_nhds (half_pos hε))
  obtain ⟨r,hlarge,herror⟩ := ((eventually_ge_atTop (2*R)).and he).exists
  obtain ⟨F,hF,hbound⟩ := exterior_insertion_trial hψ hZ hR hlarge
    (fun x i hx s => hc s x i hx)
  have hl := energy_le_form hZ hF
  linarith

theorem quantum_energy_antitone {Z : ℝ} (hZ : 0 ≤ Z) : Antitone (energy Z) :=
  antitone_nat_of_succ_le (quantum_energy_succ_le hZ)


open MeasureTheory Filter
open scoped Topology BigOperators

end CoulombAtom

end

end OAI
