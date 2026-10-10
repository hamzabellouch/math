import Mathlib
import OAI.Analysis.HardSphere.Operators.FormResolventNormEnergy
import OAI.Analysis.HardSphere.Orbitals.FreePathLawFiniteDeletion

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal BigOperators
open scoped RealInnerProductSpace
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal BigOperators
namespace HardSphere
open MeasureTheory Wiener Set Filter
noncomputable section

def freePathExpectation {m : ℕ} {L : Length} (t : ℝ)
    (h : ConfigurationPath m L → ℝ≥0∞) (X : Configuration m L) : ℝ≥0∞ :=
  ∫⁻ w : CoordinatePaths m, h (freeTrajectory m L t w X) ∂coordinateWiener m

lemma freePathExpectation_measurable {m : ℕ} {L : Length} (t : ℝ)
    {h : ConfigurationPath m L → ℝ≥0∞} (hh : Measurable h) :
    Measurable (freePathExpectation t h) :=
  (hh.comp (freeTrajectory_continuous m L t).measurable).lintegral_prod_left'

lemma selected_start_integral {m n : ℕ} {L : Length} (u : ScalarL2 (m+n) L) (t : ℝ)
    {h : ConfigurationPath m L → ℝ≥0∞} (hh : Measurable h) :
    (∫⁻ ω : ConfigurationPath m L, h ω*ENNReal.ofReal (sliceNormSq u (ω 0)) ∂freePathLaw m L t)=
      ∫⁻ y : Configuration m L, freePathExpectation t h y*ENNReal.ofReal (sliceNormSq u y) ∂volume := by
  have hmeas : Measurable (fun ω : ConfigurationPath m L ↦
      h ω*ENNReal.ofReal (sliceNormSq u (ω 0))) := hh.mul (((sliceNormSq_measurable u).comp
    (continuous_eval_const (0:Time)).measurable).ennreal_ofReal)
  rw [freePathLaw,lintegral_map hmeas (freeTrajectory_continuous m L t).measurable]
  have heq : (fun p : CoordinatePaths m × Configuration m L ↦
      h (freeTrajectory m L t p.1 p.2)*ENNReal.ofReal (sliceNormSq u (freeTrajectory m L t p.1 p.2 0)))
      =ᵐ[(coordinateWiener m).prod volume] (fun p ↦
      h (freeTrajectory m L t p.1 p.2)*ENNReal.ofReal (sliceNormSq u p.2)) := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae (freeTrajectory_initial_ae m L t)] with p hp
    rw [hp p.2]
  have hp : Measurable (fun p : CoordinatePaths m × Configuration m L ↦
      h (freeTrajectory m L t p.1 p.2)*ENNReal.ofReal (sliceNormSq u p.2)) :=
    (hh.comp (freeTrajectory_continuous m L t).measurable).mul
      ((sliceNormSq_measurable u).comp measurable_snd).ennreal_ofReal
  rw [lintegral_congr_ae heq,lintegral_prod_symm _ hp.aemeasurable]
  apply lintegral_congr
  intro y
  simpa only [freePathExpectation] using lintegral_mul_const (μ:=coordinateWiener m)
    (ENNReal.ofReal (sliceNormSq u y)) (show Measurable (fun w : CoordinatePaths m ↦
    h (freeTrajectory m L t w y)) from hh.comp ((freeTrajectory_continuous m L t).measurable.comp
      (measurable_id.prodMk measurable_const)))

lemma slice_mass_integral {m n : ℕ} {L : Length} (u : Jet (m+n) L)
    {H : Configuration m L → ℝ≥0∞} (hH : Measurable H) :
    (∫⁻ y : Configuration m L, H y*ENNReal.ofReal (sliceNormSq u.1 y) ∂volume)=
      ∫⁻ X : Configuration (m+n) L, H (splitConfiguration m n L X).1 ∂groundPositionLaw (m+n) L u := by
  have hu := (Lp.stronglyMeasurable u.1).measurable
  have hmH : Measurable (fun X : Configuration (m+n) L ↦ H (splitConfiguration m n L X).1) :=
    hH.comp (splitConfiguration_continuous m n L).measurable.fst
  rw [groundPositionLaw,lintegral_withDensity_eq_lintegral_mul volume
    (hu.norm.pow_const 2).ennreal_ofReal hmH]
  have hD : Measurable (fun X : Configuration (m+n) L ↦
      ENNReal.ofReal (‖u.1 X‖^2)*H (splitConfiguration m n L X).1) :=
    (hu.norm.pow_const 2).ennreal_ofReal.mul hmH
  have hJ : Measurable (fun p : Configuration m L × Configuration n L ↦
      ENNReal.ofReal (‖u.1 (joinConfiguration m n L p)‖^2)*H p.1) :=
    (((hu.comp (joinConfiguration_continuous m n L).measurable).norm.pow_const 2).ennreal_ofReal).mul
      (hH.comp measurable_fst)
  have hj := (joinConfiguration_preserving m n L).lintegral_comp hD
  simp only [split_joinConfiguration] at hj
  simp only [Pi.mul_apply]
  rw [← hj,lintegral_prod _ hJ.aemeasurable]
  apply lintegral_congr_ae
  filter_upwards [memLp_slice_ae u.1] with y hy
  have hyM : Measurable (fun x : Configuration n L ↦
      ENNReal.ofReal (‖u.1 (joinConfiguration m n L (y,x))‖^2)) :=
    (((hu.comp (joinConfiguration_continuous m n L).measurable).comp
      (measurable_const.prodMk measurable_id)).norm.pow_const 2).ennreal_ofReal
  rw [sliceNormSq,ofReal_integral_eq_lintegral_ofReal
    (hy.integrable_norm_pow (show (2:ℕ)≠0 by norm_num)) (Eventually.of_forall fun _ ↦ sq_nonneg _)]
  rw [← lintegral_const_mul _ hyM]
  apply lintegral_congr
  intro x
  exact mul_comm _ _

lemma selected_start_ground_integral {m n : ℕ} {L : Length} (u : Jet (m+n) L) (t : ℝ)
    {h : ConfigurationPath m L → ℝ≥0∞} (hh : Measurable h) :
    (∫⁻ ω : ConfigurationPath m L, h ω*ENNReal.ofReal (sliceNormSq u.1 (ω 0)) ∂freePathLaw m L t)=
      ∫⁻ X : Configuration (m+n) L,
        freePathExpectation t h (splitConfiguration m n L X).1 ∂groundPositionLaw (m+n) L u := by
  rw [selected_start_integral u.1 t hh]
  exact slice_mass_integral u (freePathExpectation_measurable t hh)

lemma groundPathLaw_deletion : ∃ C : ℝ, 0<C ∧
    ∀ (m n : ℕ) (L : Length) (r t : ℝ), 0<r → 0<t →
    ((m+n:ℕ):ℝ)*(2*Real.pi*r)^3≤L.val^3/2 →
    ∀ u : Jet (m+n) L, IsGroundVector (m+n) L r u →
    ∀ h : ConfigurationPath m L → ℝ≥0∞, Measurable h →
    (∀ ω, h (reverseConfigurationPath m L ω)=h ω) →
      (∫⁻ ω : ConfigurationPath (m+n) L, h (splitConfigurationPath m n L ω).1
        ∂groundPathLaw (m+n) L r t u) ≤
      ENNReal.ofReal (Real.exp (t*C*(m:ℝ)*((m+n:ℕ):ℝ)*r/L.val^3))*
        ∫⁻ X : Configuration (m+n) L,
          freePathExpectation t h (splitConfiguration m n L X).1 ∂groundPositionLaw (m+n) L u := by
  obtain ⟨C,hC,hbath⟩ := bath_heat_bound
  refine ⟨C,hC,?_⟩
  intro m n L r t hr ht hs u hu h hh hrev
  have hb := hbath n m
  rw [Nat.add_comm n m] at hb
  have hb' := hb L r t hr ht hs u hu
  have hm := deleted_path_integral_le u.1 r t hh hrev
  rw [selected_start_ground_integral u t hh] at hm
  have hmH : Measurable (fun ω : ConfigurationPath (m+n) L ↦ h (splitConfigurationPath m n L ω).1) :=
    hh.comp (splitConfigurationPath_continuous m n L).measurable.fst
  have hend : Measurable (fun ω : ConfigurationPath (m+n) L ↦
      ENNReal.ofReal (‖u.1 (ω 0)‖*‖u.1 (ω 1)‖)) := by
    have hu := (Lp.stronglyMeasurable u.1).measurable
    exact ((hu.comp (continuous_eval_const (0:Time)).measurable).norm.mul
      (hu.comp (continuous_eval_const (1:Time)).measurable).norm).ennreal_ofReal
  rw [groundPathLaw,lintegral_withDensity_eq_lintegral_mul _
    (groundPathWeight_measurable u t).ennreal_ofReal hmH]
  simp only [Pi.mul_apply,groundPathWeight,ENNReal.ofReal_mul (Real.exp_pos _).le]
  calc
    _ = ENNReal.ofReal (Real.exp (t*energy u))*
        ∫⁻ ω : ConfigurationPath (m+n) L,
          h (splitConfigurationPath m n L ω).1*ENNReal.ofReal (‖u.1 (ω 0)‖*‖u.1 (ω 1)‖)
          ∂killedPathLaw (m+n) L r t := by
      rw [← lintegral_const_mul _ (show Measurable (fun ω : ConfigurationPath (m+n) L ↦
        h (splitConfigurationPath m n L ω).1*ENNReal.ofReal (‖u.1 (ω 0)‖*‖u.1 (ω 1)‖)) from hmH.mul hend)]
      apply lintegral_congr
      intro ω
      ac_rfl
    _ ≤ ENNReal.ofReal (Real.exp (t*energy u))*(ENNReal.ofReal ‖killedTransition n L r t‖*
        ∫⁻ X : Configuration (m+n) L,
          freePathExpectation t h (splitConfiguration m n L X).1 ∂groundPositionLaw (m+n) L u) :=
      mul_le_mul_right hm _
    _ ≤ ENNReal.ofReal (Real.exp (t*energy u))*ENNReal.ofReal
        (Real.exp (-t*(energy u-C*(m:ℝ)*((m+n:ℕ):ℝ)*r/L.val^3)))*
        ∫⁻ X : Configuration (m+n) L,
          freePathExpectation t h (splitConfiguration m n L X).1 ∂groundPositionLaw (m+n) L u := by
      rw [← mul_assoc]
      exact mul_le_mul_left (mul_le_mul_right (ENNReal.ofReal_le_ofReal hb') _) _
    _ = _ := by
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le,← Real.exp_add]
      congr 3
      ring
end
end HardSphere

end
end
end

section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere
open Wiener

def oneConfiguration {L : Length} (y : Torus L) : Configuration 1 L := fun _ ↦ y

def onePathAt {n : ℕ} {L : Length} (i : Fin n) (ω : ConfigurationPath n L) : ConfigurationPath 1 L :=
  ⟨fun s ↦ oneConfiguration (ω s i), by unfold oneConfiguration; fun_prop⟩

lemma onePathAt_continuous {n : ℕ} {L : Length} (i : Fin n) :
    Continuous (onePathAt (L:=L) i) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous (fun p : ConfigurationPath n L × Time ↦ fun _ : Fin 1 ↦ p.1 p.2 i)
  fun_prop

@[simp] lemma onePathAt_reverse {n : ℕ} {L : Length} (i : Fin n) (ω : ConfigurationPath n L) :
    onePathAt i (reverseConfigurationPath n L ω)=reverseConfigurationPath 1 L (onePathAt i ω) := rfl

@[simp] lemma onePathAt_single {L : Length} (ω : ConfigurationPath 1 L) : onePathAt 0 ω=ω := by
  ext s i j
  have hi : i=0 := Subsingleton.elim _ _
  subst i
  rfl

@[simp] lemma onePathAt_join_left {m n : ℕ} {L : Length} (i : Fin m)
    (p : ConfigurationPath m L × ConfigurationPath n L) :
    onePathAt (Fin.castAdd n i) (joinConfigurationPath m n L p)=onePathAt i p.1 := by
  ext s j k
  simp [onePathAt,oneConfiguration,joinConfigurationPath,joinConfiguration]

@[simp] lemma onePathAt_join_right {m n : ℕ} {L : Length} (i : Fin n)
    (p : ConfigurationPath m L × ConfigurationPath n L) :
    onePathAt (Fin.natAdd m i) (joinConfigurationPath m n L p)=onePathAt i p.2 := by
  ext s j k
  simp [onePathAt,oneConfiguration,joinConfigurationPath,joinConfiguration]

def oneFreeExpectation {L : Length} (t : ℝ) (h : ConfigurationPath 1 L → ℝ≥0∞)
    (y : Torus L) : ℝ≥0∞ := freePathExpectation t h (oneConfiguration y)

lemma oneFreeExpectation_measurable {L : Length} (t : ℝ)
    {h : ConfigurationPath 1 L → ℝ≥0∞} (hh : Measurable h) : Measurable (oneFreeExpectation t h) := by
  exact (freePathExpectation_measurable t hh).comp (by unfold oneConfiguration; fun_prop)

lemma pathProduct_measurable {n : ℕ} {L : Length} (S : Finset (Fin n))
    {h : ConfigurationPath 1 L → ℝ≥0∞} (hh : Measurable h) :
    Measurable (fun ω : ConfigurationPath n L ↦ ∏ i∈S, h (onePathAt i ω)) := by
  exact Finset.measurable_prod S fun i _ ↦ hh.comp (onePathAt_continuous i).measurable

lemma free_product_expectation {n : ℕ} {L : Length} (t : ℝ)
    {h : ConfigurationPath 1 L → ℝ≥0∞} (hh : Measurable h) (X : Configuration n L) :
    freePathExpectation t (fun ω : ConfigurationPath n L ↦ ∏ i, h (onePathAt i ω)) X=
      ∏ i,oneFreeExpectation t h (X i) := by
  induction n with
  | zero => simp [freePathExpectation]
  | succ n ih =>
    change (∫⁻ w : CoordinatePaths (n+1), ∏ i, h (onePathAt i (freeTrajectory (n+1) L t w X))
      ∂coordinateWiener (n+1))=_
    let Xm := (splitConfiguration n 1 L X).1
    let X1 := (splitConfiguration n 1 L X).2
    have hXm : Measurable (fun w : CoordinatePaths n ↦
        ∏ i, h (onePathAt i (freeTrajectory n L t w Xm))) :=
      (pathProduct_measurable Finset.univ hh).comp
        ((freeTrajectory_continuous n L t).measurable.comp (measurable_id.prodMk measurable_const))
    have hX1 : Measurable (fun w : CoordinatePaths 1 ↦ h (freeTrajectory 1 L t w X1)) :=
      hh.comp ((freeTrajectory_continuous 1 L t).measurable.comp (measurable_id.prodMk measurable_const))
    have hfull : Measurable (fun w : CoordinatePaths (n+1) ↦
        ∏ i, h (onePathAt i (freeTrajectory (n+1) L t w X))) :=
      (pathProduct_measurable Finset.univ hh).comp
        ((freeTrajectory_continuous (n+1) L t).measurable.comp (measurable_id.prodMk measurable_const))
    rw [←(joinCoordinatePaths_preserving n 1).lintegral_comp hfull]
    have he (w : CoordinatePaths n × CoordinatePaths 1) :
        freeTrajectory (n+1) L t (joinCoordinatePaths n 1 w) X=
          joinConfigurationPath n 1 L (freeTrajectory n L t w.1 Xm,freeTrajectory 1 L t w.2 X1) := by
      rw [←freeTrajectory_join,join_splitConfiguration]
    simp only [he,Fin.prod_univ_add,onePathAt_join_left,onePathAt_join_right,
      Fin.prod_univ_one,onePathAt_single]
    rw [lintegral_prod_mul hXm.aemeasurable hX1.aemeasurable]
    change freePathExpectation t (fun ω : ConfigurationPath n L ↦ ∏ i,h (onePathAt i ω)) Xm *
      freePathExpectation t h X1 = _
    rw [ih]
    congr 1
    change freePathExpectation t h X1 = freePathExpectation t h (oneConfiguration (X (Fin.natAdd n 0)))
    congr 1
    funext i
    have hi : i=0 := Subsingleton.elim _ _
    subst i
    rfl

end HardSphere

end
end

end

end OAI
