import Mathlib
import OAI.Analysis.CoulombIonization.Localization.BarrierOrdinaryGlobalBarrier
import OAI.Analysis.CoulombIonization.RadialBounds.LocalFermionDensityBarrier
import OAI.Analysis.CoulombIonization.FieldAnalysis.FreshKineticBudgetBarrier
import OAI.Analysis.CoulombIonization.RadialBounds.FockKineticReindexBarrier

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_LocalOrdinaryLT_barrier_scope

open MeasureTheory Filter
open scoped BigOperators ENNReal

open CoulombPauli CoulombPackets CoulombLT

 def densityLocalizationError {N : ℕ} (ψ : FormVector N)
    (p : SmoothMultiplier spaceDirections) : ℝ :=
  ∑ a : Fin 3, weightedParticleCount ψ
    (fun x => (lineDeriv ℝ p.value x (spaceDirections a))^2)

 def localDensityBudget {N : ℕ} (ψ : FormVector N)
    (p : SmoothMultiplier spaceDirections) : ℝ :=
  32*weightedParticleCount ψ (fun x => p.value x^2)+
    (4096/3:ℝ)*(localGradientTrace ψ p+densityLocalizationError ψ p)

lemma weightedParticleCount_sq_nonneg {N : ℕ} (ψ : FormVector N) (r : Space → ℝ) :
    0 ≤ weightedParticleCount ψ (fun x => r x^2) := by
  unfold weightedParticleCount
  exact Finset.sum_nonneg (fun s _ => Finset.sum_nonneg
    (fun i _ => integral_nonneg (fun x => mul_nonneg (sq_nonneg _) (sq_nonneg _))))

lemma localDensityBudget_nonneg {N : ℕ} (ψ : FormVector N)
    (p : SmoothMultiplier spaceDirections) : 0 ≤ localDensityBudget ψ p := by
  have he : 0 ≤ densityLocalizationError ψ p :=
    Finset.sum_nonneg (fun a _ => weightedParticleCount_sq_nonneg ψ _)
  have hg : 0 ≤ localGradientTrace ψ p := by
    unfold localGradientTrace
    exact Finset.sum_nonneg (fun s _ => Finset.sum_nonneg (fun i _ => Finset.sum_nonneg
      (fun a _ => integral_nonneg (fun x => mul_nonneg (sq_nonneg _) (sq_nonneg _)))))
  have hm := weightedParticleCount_sq_nonneg ψ p.value
  unfold localDensityBudget
  positivity

namespace Pauli

 theorem form_local_density {N : ℕ} (ψ : FormVector (N+1))
    (hψ : FormAdmissible ψ) (p : SmoothMultiplier spaceDirections)
    (hp : ∀ x, |p.value x| ≤ 1) :
    (∫⁻ x, (ENNReal.ofReal (p.value x^2)*oneParticleDensity ψ hψ.1 x)^(5/3:ℝ)) ≤
      ENNReal.ofReal (localDensityBudget ψ p) := by
  have hn : ‖toMany ψ hψ.1‖^2 = 1 :=
    (toMany_norm_sq ψ hψ.1).trans hψ.2.2.2.2.1
  have ha (i j : Fin (N+1)) (hij : i ≠ j) :
      permute (Equiv.swap i j) (toMany ψ hψ.1) = -toMany ψ hψ.1 := by
    rw [toMany_permute ψ hψ.1 (Equiv.swap i j) (hψ.2.2.2.1 _)]
    simp [Equiv.Perm.sign_swap hij]
  have hw (i : Fin (N+1)) (a : Fin 3) := form_hasFermionGradient ψ hψ i a
  simp only [EuclideanSpace.basisFun_apply] at hw
  have hh := fermion_local_density (toMany ψ hψ.1) (gradientMany ψ hψ) hw hn ha p hp
  rw [coordinateWeightedTrace_square_mass hψ.1 p.value p.regular.continuous p.bound] at hh
  simp_rw [coordinateWeightedTrace_square_gradient ψ hψ _ p.value p.regular.continuous p.bound,
    coordinateWeightedTrace_square_mass hψ.1 _ (p.derivative_continuous _) (p.gradient_bound _)] at hh
  let G : Fin 3 → ℝ := fun a => ∑ s : Spins (N+1), ∑ i : Fin (N+1),
    ∫ x : Configuration (N+1), p.value (x i)^2*‖ψ.gradient s i a x‖^2
  let E : Fin 3 → ℝ := fun a => weightedParticleCount ψ
    (fun x => (lineDeriv ℝ p.value x (spaceDirections a))^2)
  have hG (a) : 0 ≤ G a := Finset.sum_nonneg (fun s _ => Finset.sum_nonneg
    (fun i _ => integral_nonneg (fun x => mul_nonneg (sq_nonneg _) (sq_nonneg _))))
  have hE (a) : 0 ≤ E a := weightedParticleCount_sq_nonneg ψ _
  have hs : (∑ a : Fin 3, (ENNReal.ofReal (G a)+ENNReal.ofReal (E a))) =
      ENNReal.ofReal (localGradientTrace ψ p+densityLocalizationError ψ p) := by
    have heq (a : Fin 3) : ENNReal.ofReal (G a)+ENNReal.ofReal (E a) =
        ENNReal.ofReal (G a+E a) := (ENNReal.ofReal_add (hG a) (hE a)).symm
    simp_rw [heq]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun a _ => add_nonneg (hG a) (hE a))]
    congr 1
    rw [Finset.sum_add_distrib]
    congr 1
    dsimp only [G,localGradientTrace]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro s _
    exact Finset.sum_comm
  change (∫⁻ x, (ENNReal.ofReal (p.value x^2)*oneParticleDensity ψ hψ.1 x)^(5/3:ℝ)) ≤
    32*ENNReal.ofReal (weightedParticleCount ψ (fun x => p.value x^2))+
      ENNReal.ofReal (4096/3:ℝ)*(∑ a : Fin 3, (ENNReal.ofReal (G a)+ENNReal.ofReal (E a))) at hh
  rw [hs] at hh
  have hn0 := weightedParticleCount_sq_nonneg ψ p.value
  have hge0 : 0 ≤ localGradientTrace ψ p+densityLocalizationError ψ p := by
    have hg : 0 ≤ localGradientTrace ψ p := by
      unfold localGradientTrace
      exact Finset.sum_nonneg (fun s _ => Finset.sum_nonneg (fun i _ => Finset.sum_nonneg
        (fun a _ => integral_nonneg (fun x => mul_nonneg (sq_nonneg _) (sq_nonneg _)))))
    exact add_nonneg hg (Finset.sum_nonneg (fun a _ => hE a))
  simpa only [localDensityBudget,ENNReal.ofReal_add (mul_nonneg (by norm_num : (0:ℝ) ≤ 32) hn0)
    (mul_nonneg (by norm_num : (0:ℝ) ≤ 4096/3) hge0),
    ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 32),
    ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 4096/3),ENNReal.ofReal_ofNat] using hh

 theorem form_local_density_real {N : ℕ} (ψ : FormVector (N+1))
    (hψ : FormAdmissible ψ) (p : SmoothMultiplier spaceDirections)
    (hp : ∀ x, |p.value x| ≤ 1) :
    (∫ x, (p.value x^2*density ψ hψ.1 x)^(5/3:ℝ)) ≤ localDensityBudget ψ p := by
  have hme := ((p.regular.continuous.pow 2).aemeasurable.ennreal_ofReal.mul
    (fermionDensity_aemeasurable (toMany ψ hψ.1))).pow_const (5/3:ℝ)
  have hb := form_local_density ψ hψ p hp
  have hn : (∫⁻ x, (ENNReal.ofReal (p.value x^2)*oneParticleDensity ψ hψ.1 x)^(5/3:ℝ)) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hb
  have he := integral_toReal hme (ae_lt_top' hme hn)
  simp only [Pi.mul_apply,Pi.pow_apply,← ENNReal.toReal_rpow,ENNReal.toReal_mul,ENNReal.toReal_ofReal (sq_nonneg _)] at he
  change (∫ x, (p.value x^2*(fermionDensity (toMany ψ hψ.1) x).toReal)^(5/3:ℝ)) ≤ _
  rw [he]
  exact (ENNReal.toReal_le_toReal hn ENNReal.ofReal_ne_top).2 hb |>.trans_eq
    (ENNReal.toReal_ofReal (localDensityBudget_nonneg ψ p))

end Pauli

 theorem ordinaryDensity_local_lt {N : ℕ} (ψ : FormVector N)
    (hψ : FormAdmissible ψ) (p : SmoothMultiplier spaceDirections)
    (hp : ∀ x, |p.value x| ≤ 1) :
    (∫ x, (p.value x^2*ordinaryDensity ψ x)^(5/3:ℝ)) ≤ localDensityBudget ψ p := by
  cases N with
  | zero =>
    have hae := Pauli.ordinaryDensity_eq_spatialDensity hψ.sobolevFermion.sobolevVector
    have he : (fun x => (p.value x^2*ordinaryDensity ψ x)^(5/3:ℝ)) =ᵐ[volume] fun _ => (0:ℝ) := by
      filter_upwards [hae] with x hx
      simp only [hx,Pauli.spatialDensity,Pi.zero_apply,mul_zero,Real.zero_rpow (by norm_num : (5/3:ℝ) ≠ 0)]
    rw [integral_congr_ae he,integral_zero]
    exact localDensityBudget_nonneg ψ p
  | succ N =>
    have hae := Pauli.ordinaryDensity_eq_density hψ.sobolevFermion.sobolevVector
    have he := integral_congr_ae (hae.mono (fun x hx =>
      congrArg (fun t : ℝ => (p.value x^2*t)^(5/3:ℝ)) hx))
    rw [he]
    exact Pauli.form_local_density_real ψ hψ p hp

end Work_LocalOrdinaryLT_barrier_scope

open MeasureTheory Filter Set
open scoped BigOperators

def sharpFreshKineticConstant : ℝ :=
  1+localizationIMSConstant*actualCellMomentConstant+
    sharpFreshFieldConstant*actualCellMomentConstant

lemma sharpFreshKineticConstant_one_le : 1 ≤ sharpFreshKineticConstant := by
  have := localizationIMSConstant_nonneg
  have := actualCellMomentConstant_one_le
  have := sharpFreshFieldConstant_one_le
  have hh : 0 ≤ localizationIMSConstant*actualCellMomentConstant+
      sharpFreshFieldConstant*actualCellMomentConstant := by positivity
  unfold sharpFreshKineticConstant
  linarith only [hh]

 theorem sharp_cell_fresh_kinetic {N : ℕ} {ψ : FormVector N}
    (hψ : SobolevFermion ψ) (hm : formMass ψ = 1) {y : Space} (hy : y ≠ 0)
    {b r Z lam : ℝ} (hb : 0 < b) (hba : b ≤ localCellRadius y)
    (hr : r ∈ Set.Icc (5*localCellRadius y) (6*localCellRadius y))
    (hZ : 0 ≤ Z) (hlam : 0 < lam)
    (hcollar : localCellRadius y ≤ b^2*localOffsetMass (max (corePriceExcess Z lam ψ) 0) y) :
    ∃ hr0 : 0 ≤ r,
      (∑ c : Fin N → Fin 2, outKinetic (orderedCutForm (coreFirstRadialCut y hr0 hb)
        (coreFirstRadialCut_partition y hr0 hb) ψ c)) ≤
          sharpFreshKineticConstant*(localOffsetMass (max (corePriceExcess Z lam ψ) 0) y)^2/localCellRadius y := by
  let a := localCellRadius y
  let D := max (corePriceExcess Z lam ψ) 0
  let m := localOffsetMass D y
  let C := actualCellMomentConstant
  let F := sharpFreshFieldConstant
  have ha : 0 < a := localCellRadius_pos hy
  have hm1 : 1 ≤ m := localOffsetMass_one_le D y
  have hm0 : 0 ≤ m := le_trans zero_le_one hm1
  have hC : 1 ≤ C := actualCellMomentConstant_one_le
  have hC0 : 0 ≤ C := le_trans zero_le_one hC
  have hF0 : 0 ≤ F := le_trans zero_le_one sharpFreshFieldConstant_one_le
  have hsep : r+2*b ≤ ‖y‖ := by
    have hae : 100000*a = ‖y‖ := by dsimp [a,localCellRadius]; ring
    linarith [hr.2]
  obtain ⟨hr0,hfield,-⟩ := sharp_cell_fresh_field_mass hψ hm hy hb hba hr hZ hlam hcollar
  refine ⟨hr0,?_⟩
  have hB := priced_enlarged_cell_count hψ hm hZ hlam hy
  have hroot : Real.sqrt (rawCountMoment ψ y (32*a)) ≤ C*m := by
    simpa using sqrt_count_scale (rawCountMoment_nonneg ψ y (32*a)) hC
      (by norm_num : (0:ℝ) ≤ 1) hm0 (by simpa using hB)
  have hrootF : Real.sqrt (freshOutMaximumSecondMoment (coreFirstRadialCut y hr0 hb)
      (coreFirstRadialCut_partition y hr0 hb) ψ Z lam) ≤ F*(m/a) :=
    Real.sqrt_le_iff.mpr ⟨by positivity,hfield⟩
  have hcut := radial_out_kinetic_coupling hψ y hr0 hb hsep
    (show r+b ≤ 32*a by linarith [hr.2]) hZ hlam
  have hims := radial_ims_le_sqrt_count hψ.sobolevVector y hr0 hb
    (show r+b < 32*a by linarith [hr.2])
  rw [hm,Real.sqrt_one,mul_one] at hims
  have hI := localizationIMSConstant_nonneg
  have hK : (3/2:ℝ)*(Real.pi*smoothTransitionBound/b)^2 = localizationIMSConstant/b^2 := by
    unfold localizationIMSConstant
    ring
  rw [hK] at hims
  have hma : m/b^2 ≤ m^2/a := by
    apply (div_le_div_iff₀ (sq_pos_of_pos hb) ha).mpr
    nlinarith only [mul_le_mul_of_nonneg_left hcollar hm0]
  have hims' : (1/2:ℝ)*weightedParticleCount ψ
      (spatialErrorWeight (coreFirstRadialCut y hr0 hb)) ≤
        localizationIMSConstant*C*(m^2/a) := by
    calc _ ≤ localizationIMSConstant/b^2*Real.sqrt (rawCountMoment ψ y (32*a)) := hims
         _ ≤ localizationIMSConstant/b^2*(C*m) := by gcongr
         _ = localizationIMSConstant*C*(m/b^2) := by ring
         _ ≤ _ := mul_le_mul_of_nonneg_left hma (mul_nonneg hI hC0)
  have hD : corePriceExcess Z lam ψ ≤ m^2/a :=
    (le_max_left _ _).trans ((le_div_iff₀ ha).mpr (localOffsetMass_offset (le_max_right _ _) hy))
  have hwork : Real.sqrt (freshOutMaximumSecondMoment (coreFirstRadialCut y hr0 hb)
      (coreFirstRadialCut_partition y hr0 hb) ψ Z lam)*Real.sqrt (rawCountMoment ψ y (32*a)) ≤
        F*C*(m^2/a) := by
    calc _ ≤ (F*(m/a))*(C*m) := mul_le_mul hrootF hroot (Real.sqrt_nonneg _) (by positivity)
         _ = _ := by ring
  calc _ ≤ corePriceExcess Z lam ψ+(1/2:ℝ)*weightedParticleCount ψ
        (spatialErrorWeight (coreFirstRadialCut y hr0 hb))+
        Real.sqrt (freshOutMaximumSecondMoment (coreFirstRadialCut y hr0 hb)
          (coreFirstRadialCut_partition y hr0 hb) ψ Z lam)*Real.sqrt (rawCountMoment ψ y (32*a)) := hcut
       _ ≤ m^2/a+localizationIMSConstant*C*(m^2/a)+F*C*(m^2/a) := add_le_add (add_le_add hD hims') hwork
       _ = _ := by dsimp [sharpFreshKineticConstant,C,F,m,D,a]; ring

end CoulombAtom

end

end OAI
