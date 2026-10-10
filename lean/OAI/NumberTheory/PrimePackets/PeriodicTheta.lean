import Mathlib
import OAI.NumberTheory.PrimePackets.CongruenceLattices

namespace OAI

section
noncomputable section
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal
open MeasureTheory Filter Set Module
universe u
open scoped TensorProduct
open Set Module
open MeasureTheory Set
open scoped ENNReal
open IsDiscreteValuationRing IsLocalRing
open scoped ENNReal BigOperators
open MeasureTheory Set IsDiscreteValuationRing
open Filter
open scoped BigOperators Topology
open NumberField
open scoped NumberField nonZeroDivisors
open scoped BigOperators ArithmeticFunction.zeta
open Finset
open scoped BigOperators Classical ArithmeticFunction.Moebius
open Finset Nat ArithmeticFunction BoundingSieve
open scoped BigOperators Classical
open Finset Nat
open scoped BigOperators
open Filter Topology
open scoped nonZeroDivisors
open Ideal NumberField Finset UniqueFactorizationMonoid
open Filter Set Topology NumberField
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace
open Filter Set Topology
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors RealInnerProductSpace
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace Matrix
open MeasureTheory Filter Set Module TopologicalSpace
open MeasureTheory Filter Set
open scoped BigOperators Topology ENNReal
open scoped BigOperators Topology ENNReal Classical
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix
open MeasureTheory ProbabilityTheory Filter Set
open Set Filter
open scoped Topology
open scoped Classical
open scoped Topology ENNReal Classical
open scoped ENNReal Classical
open MeasureTheory Set Topology UniformSpace TopologicalSpace
open scoped ENNReal Topology
open MeasureTheory Filter Set Matrix
open scoped Topology Classical
open scoped Matrix Classical
open scoped Topology Classical Matrix
open scoped Classical Pointwise
open scoped Topology Classical ENNReal
open scoped Matrix Topology Classical
open MeasureTheory ProbabilityTheory Set Filter
open scoped Matrix Topology Classical ENNReal ProbabilityTheory
open scoped ENNReal ProbabilityTheory
open Set Filter Topology
open Set Filter Topology MeasureTheory
open MeasureTheory Set Filter Topology
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped Matrix ENNReal NNReal ProbabilityTheory
open MeasureTheory
open scoped BigOperators ENNReal
open NumberField Finset
open NumberField Filter Set Topology
open MeasureTheory ProbabilityTheory Matrix
open scoped Classical BigOperators ENNReal
open MeasureTheory Set Filter Topology Module
open scoped BigOperators SchwartzMap
open MeasureTheory Set Filter Topology Module WithLp
open scoped BigOperators SchwartzMap ZeroAtInfty
open scoped FourierTransform
open scoped BigOperators SchwartzMap FourierTransform
open scoped BigOperators FourierTransform
open MeasureTheory Set Filter Topology Module WithLp Asymptotics
open Module WithLp MeasureTheory
open scoped BigOperators Matrix
open Module MeasureTheory
open MeasureTheory Module WithLp
open scoped BigOperators NumberField nonZeroDivisors ENNReal
open Complex Set Metric Filter
open Complex Set Metric Filter MeromorphicOn
open scoped Topology ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal BigOperators Topology
open MeasureTheory Set Module
open scoped BigOperators ENNReal NumberField nonZeroDivisors
open scoped BigOperators ENNReal NumberField nonZeroDivisors Topology
open Set
open Filter Set Module MeasureTheory
open scoped Topology NumberField
open Filter Set Module MeasureTheory WithLp
open scoped Topology NumberField BigOperators nonZeroDivisors
open scoped Topology NumberField BigOperators nonZeroDivisors ComplexConjugate
open MeasureTheory Set Filter Module WithLp
open scoped Topology BigOperators NumberField nonZeroDivisors
open Complex Set Filter Module
open Complex
open Complex Set Filter
open scoped Topology NumberField ComplexConjugate
open scoped Topology NumberField ComplexConjugate Classical
open Filter Set Topology Module
open MeasureTheory ProbabilityTheory Set Filter TopologicalSpace
open MeasureTheory MeasureTheory.Measure ProbabilityTheory Set Filter
open scoped Matrix Topology Classical ENNReal NNReal ProbabilityTheory
open scoped Matrix Topology Classical ENNReal
open scoped Topology ENNReal
open scoped Matrix Topology ENNReal ProbabilityTheory
open scoped Topology ENNReal CompactlySupported
open MeasureTheory Set Filter TopologicalSpace
open Module Set Matrix MeasureTheory Filter
open scoped NumberField
open CategoryTheory Module
open MeasureTheory Module Set Filter
open scoped BigOperators ENNReal RealInnerProductSpace
open Module Matrix
open scoped NumberField BigOperators
open Module MeasureTheory Set WithLp
open scoped NumberField BigOperators ENNReal
open IntermediateField Module
open Module IntermediateField
open scoped BigOperators NumberField Pointwise
open Module IntermediateField Set
open MeasureTheory Set Module Filter
open scoped BigOperators ENNReal NumberField nonZeroDivisors Topology ComplexConjugate
open Module
namespace PrimeDegreePackets.ThetaConstruction
variable {d : Type*} [Fintype d]
local instance periodicThetaDecidableEq : DecidableEq d := Classical.decEq d

def periodicPrimalWeight (N : ℕ) [NeZero N] (w : (d → Fin N) → ℂ) (z : d → ℤ) : ℂ :=
  w ((integerCongruenceEquiv N z).1)

def periodicDualWeight (N : ℕ) (w : (d → Fin N) → ℂ) : (d → ℤ) → ℂ :=
  congruenceThetaFourierWeight (congruencePoint N) w

def normalizedPeriodicTheta (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d)
    (N : ℕ) [NeZero N] (w : (d → Fin N) → ℂ) (t : ℝ) : ℂ :=
  periodicLatticeTheta B N w (Real.pi*t)

def periodicPrimalTail (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d)
    (N : ℕ) [NeZero N] (w : (d → Fin N) → ℂ) : ℝ → ℂ :=
  scaledWeightedThetaTail B (periodicPrimalWeight N w) (Real.pi/(N:ℝ)^2)

def periodicDualTail (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d)
    (N : ℕ) (w : (d → Fin N) → ℂ) : ℝ → ℂ :=
  scaledWeightedThetaTail (adjointEquiv B.symm) (periodicDualWeight N w) Real.pi

lemma periodicPrimalTail_convergent
    (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d)
    (N : ℕ) [NeZero N] (w : (d → Fin N) → ℂ) (s : ℂ) :
    MellinConvergent (periodicPrimalTail B N w) s :=
  scaledWeightedThetaTail_mellin_convergent B _ (∑ i, ‖w i‖)
    (fun _ => congruenceWeight_bound N w _) _
    (div_pos Real.pi_pos (sq_pos_of_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne N))))) s

lemma periodicDualTail_convergent
    (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d)
    (N : ℕ) (w : (d → Fin N) → ℂ) (s : ℂ) :
    MellinConvergent (periodicDualTail B N w) s :=
  scaledWeightedThetaTail_mellin_convergent _ _ (∑ i, ‖w i‖)
    (congruenceThetaFourierWeight_bound (congruencePoint N) w) _ Real.pi_pos s

lemma periodicPrimalTail_entire
    (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d)
    (N : ℕ) [NeZero N] (w : (d → Fin N) → ℂ) :
    Differentiable ℂ (mellin (periodicPrimalTail B N w)) :=
  scaledWeightedThetaTail_mellin_entire B _ (∑ i, ‖w i‖)
    (fun _ => congruenceWeight_bound N w _) _
    (div_pos Real.pi_pos (sq_pos_of_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne N)))))

lemma periodicDualTail_entire
    (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d)
    (N : ℕ) (w : (d → Fin N) → ℂ) :
    Differentiable ℂ (mellin (periodicDualTail B N w)) :=
  scaledWeightedThetaTail_mellin_entire _ _ (∑ i, ‖w i‖)
    (congruenceThetaFourierWeight_bound (congruencePoint N) w) _ Real.pi_pos

lemma normalizedPeriodicTheta_primal
    (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d)
    (N : ℕ) [NeZero N] (w : (d → Fin N) → ℂ) (t : ℝ) (ht : 0 < t) :
    normalizedPeriodicTheta B N w t = periodicPrimalWeight N w 0 +
      weightedThetaRemainder B (periodicPrimalWeight N w) ((Real.pi/(N:ℝ)^2)*t) := by
  rw [normalizedPeriodicTheta, periodicLatticeTheta_zero_mode B N w _ (mul_pos Real.pi_pos ht)]
  congr 1
  congr 1
  ring

lemma normalizedPeriodicTheta_dual
    (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d)
    (N : ℕ) [NeZero N] (w : (d → Fin N) → ℂ) (t : ℝ) (ht : 0 < t) :
    normalizedPeriodicTheta B N w t = ((|(LinearMap.det B.toLinearMap)⁻¹|:ℝ):ℂ) *
      (t:ℂ)^(-((Fintype.card d:ℂ)/2)) * ((∑ i, w i) +
        weightedThetaRemainder (adjointEquiv B.symm) (periodicDualWeight N w) (Real.pi*t⁻¹)) := by
  rw [normalizedPeriodicTheta, periodicLatticeTheta_eq_congruenceTheta B N w _
    (mul_pos Real.pi_pos ht), congruenceTheta_poisson_zero_mode B _ w _ (mul_pos Real.pi_pos ht)]
  have hπ : (Real.pi:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have ht' : (t:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  have h1 : (Real.pi:ℂ) / ((Real.pi*t:ℝ):ℂ) = (t:ℂ)⁻¹ := by
    rw [Complex.ofReal_mul]; field_simp
  have h2 : Real.pi^2/(Real.pi*t) = Real.pi*t⁻¹ := by field_simp
  rw [h1,h2,Complex.inv_cpow_ofReal_nonneg ht.le,←Complex.cpow_neg]
  rfl

 

lemma normalizedPeriodicTheta_decomposition
    (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d)
    (N : ℕ) [NeZero N] (w : (d → Fin N) → ℂ)
    (hzero : periodicPrimalWeight N w 0 = 0) (hsum : ∑ i, w i = 0)
    {t : ℝ} (ht : 0 < t) (hne : t ≠ 1) :
    normalizedPeriodicTheta B N w t = periodicPrimalTail B N w t +
      ((|(LinearMap.det B.toLinearMap)⁻¹|:ℝ):ℂ) *
        (t:ℂ)^(-((Fintype.card d:ℂ)/2)) * periodicDualTail B N w t⁻¹ := by
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hinv : 1 < t⁻¹ := (one_lt_inv₀ ht).mpr hlt
    rw [normalizedPeriodicTheta_dual B N w t ht, hsum, zero_add]
    simp [periodicPrimalTail, periodicDualTail, scaledWeightedThetaTail,
      not_lt.mpr hlt.le, hinv, max_eq_left hinv.le]
  · have hinv : t⁻¹ < 1 := (inv_lt_one₀ (zero_lt_one.trans hgt)).mpr hgt
    rw [normalizedPeriodicTheta_primal B N w t ht, hzero, zero_add]
    simp [periodicPrimalTail, periodicDualTail, scaledWeightedThetaTail,
      not_lt.mpr hinv.le, hgt, max_eq_left hgt.le]

 

def periodicThetaMellinEntire
    (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d)
    (N : ℕ) [NeZero N] (w : (d → Fin N) → ℂ) (s : ℂ) : ℂ :=
  mellin (periodicPrimalTail B N w) s + ((|(LinearMap.det B.toLinearMap)⁻¹|:ℝ):ℂ) *
    mellin (periodicDualTail B N w) ((Fintype.card d:ℂ)/2-s)

lemma periodicThetaMellinEntire_entire
    (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d)
    (N : ℕ) [NeZero N] (w : (d → Fin N) → ℂ) :
    Differentiable ℂ (periodicThetaMellinEntire B N w) :=
  (periodicPrimalTail_entire B N w).add
    (((periodicDualTail_entire B N w).comp
      ((differentiable_const _).sub differentiable_id)).const_mul _)

 

theorem normalizedPeriodicTheta_hasMellin
    (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d)
    (N : ℕ) [NeZero N] (w : (d → Fin N) → ℂ)
    (hzero : periodicPrimalWeight N w 0 = 0) (hsum : ∑ i, w i = 0) (s : ℂ) :
    HasMellin (normalizedPeriodicTheta B N w) s (periodicThetaMellinEntire B N w s) := by
  let a : ℂ := (Fintype.card d:ℂ)/2
  let c : ℂ := ((|(LinearMap.det B.toLinearMap)⁻¹|:ℝ):ℂ)
  let P := periodicPrimalTail B N w
  let Q := periodicDualTail B N w
  let q := fun t : ℝ => c • ((t:ℂ)^(-a) • Q t⁻¹)
  have hP : MellinConvergent P s := periodicPrimalTail_convergent B N w s
  have hQ : MellinConvergent (fun t => (t:ℂ)^(-a) • Q t⁻¹) s := by
    apply MellinConvergent.cpow_smul.mpr
    apply mellinConvergent_inv.mpr
    exact periodicDualTail_convergent B N w _
  have hq : MellinConvergent q s := hQ.const_smul c
  have HF := hasMellin_add hP hq
  have hqeq : mellin q s = c * mellin Q (a-s) := by
    calc
      mellin q s = c • mellin (fun t => (t:ℂ)^(-a) • Q t⁻¹) s :=
        mellin_const_smul _ s c
      _ = c * mellin Q (a-s) := by
        rw [mellin_cpow_smul,mellin_comp_inv,smul_eq_mul]
        congr 2
        ring
  have HFval : mellin (fun t => P t + q t) s = periodicThetaMellinEntire B N w s := by
    rw [HF.2, hqeq]
    rfl
  have Hne : ∀ᵐ t : ℝ ∂(volume.restrict (Set.Ioi 0)), t ≠ 1 := by
    apply ae_restrict_of_ae
    rw [ae_iff]
    simp
  have HE : normalizedPeriodicTheta B N w =ᵐ[volume.restrict (Set.Ioi 0)]
      (fun t => P t + q t) := by
    filter_upwards [Hne,ae_restrict_mem measurableSet_Ioi] with t hne ht
    simpa only [P,q,c,a,Q,smul_eq_mul,mul_assoc] using
      normalizedPeriodicTheta_decomposition B N w hzero hsum ht hne
  have HI : (fun t : ℝ => (t:ℂ)^(s-1) • normalizedPeriodicTheta B N w t)
      =ᵐ[volume.restrict (Set.Ioi 0)]
      (fun t : ℝ => (t:ℂ)^(s-1) • (P t+q t)) := by
    filter_upwards [HE] with t ht
    rw [ht]
  refine ⟨HF.1.congr HI.symm, ?_⟩
  exact (integral_congr_ae HI).trans HFval

 

theorem normalizedPeriodicTheta_mellin_entire
    (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d)
    (N : ℕ) [NeZero N] (w : (d → Fin N) → ℂ)
    (hzero : periodicPrimalWeight N w 0 = 0) (hsum : ∑ i, w i = 0) :
    Differentiable ℂ (mellin (normalizedPeriodicTheta B N w)) := by
  have H : mellin (normalizedPeriodicTheta B N w) = periodicThetaMellinEntire B N w := by
    funext s
    exact (normalizedPeriodicTheta_hasMellin B N w hzero hsum s).2
  rw [H]
  exact periodicThetaMellinEntire_entire B N w

end PrimeDegreePackets.ThetaConstruction


namespace PrimeDegreePackets.ThetaConstruction
variable {d R : Type*} [Fintype d] [CommRing R]
local instance rationalModulusDecidableEq : DecidableEq d := Classical.decEq d

 
def rationalModulusIdeal (R : Type*) [CommRing R] (N : ℕ) : Ideal R :=
  Ideal.span {(N : R)}

lemma rationalModulusIdeal_restrictScalars (N : ℕ) :
    (rationalModulusIdeal R N).restrictScalars ℤ =
      LinearMap.range (LinearMap.lsmul ℤ R N) := by
  ext x
  change x ∈ Ideal.span {(N : R)} ↔ _
  simp only [Ideal.mem_span_singleton, dvd_def, LinearMap.mem_range,
    LinearMap.lsmul_apply, zsmul_eq_mul, Int.cast_natCast, eq_comm]

 

def rationalModulusEquivModN (N : ℕ) : (R ⧸ rationalModulusIdeal R N) ≃+ ModN R N :=
  (Submodule.quotEquivOfEq _ _ (rationalModulusIdeal_restrictScalars (R := R) N)).toAddEquiv

 
def integralResidueEquiv (b : Basis d ℤ R) (N : ℕ) [NeZero N] :
    (d → Fin N) ≃ (R ⧸ rationalModulusIdeal R N) :=
  ((Equiv.piCongrRight fun _ : d => (ZMod.finEquiv N).toEquiv).trans
    (ModN.basis b).equivFun.symm.toEquiv).trans (rationalModulusEquivModN N).symm.toEquiv

lemma integralResidueEquiv_zero (b : Basis d ℤ R) (N : ℕ) [NeZero N] :
    integralResidueEquiv b N (0 : d → Fin N) = 0 := by
  have h : (Equiv.piCongrRight fun _ : d => (ZMod.finEquiv N).toEquiv)
      (0 : d → Fin N) = (0 : d → ZMod N) := by
    funext i
    exact (ZMod.finEquiv N).map_zero
  simp only [integralResidueEquiv, Equiv.trans_apply, h,
    LinearEquiv.coe_toEquiv, _root_.map_zero]
  exact (rationalModulusEquivModN (R := R) N).symm.map_zero

lemma mulChar_nontrivial_domain {S : Type*} [CommRing S]
    (χ : MulChar S ℂ) (hχ : χ ≠ 1) : Nontrivial S := by
  by_contra H
  have : Subsingleton S := not_nontrivial_iff_subsingleton.mp H
  apply hχ
  ext x
  have hx : x = 1 := Subsingleton.elim _ _
  simp [hx]

end PrimeDegreePackets.ThetaConstruction

open MeasureTheory Module
namespace PrimeDegreePackets.ThetaConstruction
variable {d R : Type*} [Fintype d] [CommRing R]
local instance integralCharacterDecidableEq : DecidableEq d := Classical.decEq d

def integralCharacterWeight (b : Basis d ℤ R) (N : ℕ) [NeZero N]
    (χ : MulChar (R ⧸ rationalModulusIdeal R N) ℂ) : (d → Fin N) → ℂ :=
  fun r => χ (integralResidueEquiv b N r)

lemma integralCharacterWeight_sum_zero (b : Basis d ℤ R) (N : ℕ) [NeZero N]
    (χ : MulChar (R ⧸ rationalModulusIdeal R N) ℂ) (hχ : χ ≠ 1) :
    ∑ r, integralCharacterWeight b N χ r = 0 := by
  let : Fintype (R ⧸ rationalModulusIdeal R N) :=
    Fintype.ofEquiv (d → Fin N) (integralResidueEquiv b N)
  change (∑ r, χ (integralResidueEquiv b N r)) = 0
  rw [(integralResidueEquiv b N).sum_comp]
  exact MulChar.sum_eq_zero_of_ne_one hχ

omit [Fintype d] in
lemma integerCongruenceEquiv_zero (N : ℕ) [NeZero N] :
    (integerCongruenceEquiv N (0 : d → ℤ)).1 = 0 := by
  funext i
  simp [integerCongruenceEquiv, Int.divModEquiv, Int.natMod]

lemma integralCharacterWeight_zero (b : Basis d ℤ R) (N : ℕ) [NeZero N]
    (χ : MulChar (R ⧸ rationalModulusIdeal R N) ℂ) (hχ : χ ≠ 1) :
    periodicPrimalWeight N (integralCharacterWeight b N χ) 0 = 0 := by
  have : Nontrivial (R ⧸ rationalModulusIdeal R N) := mulChar_nontrivial_domain χ hχ
  simp only [periodicPrimalWeight, integerCongruenceEquiv_zero, integralCharacterWeight,
    integralResidueEquiv_zero, MulChar.map_zero]

 

theorem integralCharacterTheta_hasMellin
    (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d)
    (b : Basis d ℤ R) (N : ℕ) [NeZero N]
    (χ : MulChar (R ⧸ rationalModulusIdeal R N) ℂ) (hχ : χ ≠ 1) (s : ℂ) :
    MellinConvergent (normalizedPeriodicTheta B N (integralCharacterWeight b N χ)) s ∧
    mellin (normalizedPeriodicTheta B N (integralCharacterWeight b N χ)) s =
      periodicThetaMellinEntire B N (integralCharacterWeight b N χ) s :=
  normalizedPeriodicTheta_hasMellin B N _
    (integralCharacterWeight_zero b N χ hχ) (integralCharacterWeight_sum_zero b N χ hχ) s

 

theorem integralCharacterTheta_mellin_entire
    (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d)
    (b : Basis d ℤ R) (N : ℕ) [NeZero N]
    (χ : MulChar (R ⧸ rationalModulusIdeal R N) ℂ) (hχ : χ ≠ 1) :
    Differentiable ℂ (mellin
      (normalizedPeriodicTheta B N (integralCharacterWeight b N χ))) :=
  normalizedPeriodicTheta_mellin_entire B N _
    (integralCharacterWeight_zero b N χ hχ) (integralCharacterWeight_sum_zero b N χ hχ)

end PrimeDegreePackets.ThetaConstruction


namespace PrimeDegreePackets.ThetaConstruction
variable {d R : Type*} [Fintype d] [CommRing R]
local instance modNBasisCoordinatesDecidableEq : DecidableEq d := Classical.decEq d

lemma modN_basis_coordinates (b : Basis d ℤ R) (N : ℕ) [NeZero N] (z : d → ℤ) :
    (ModN.basis b).equivFun.symm (fun i => (z i : ZMod N)) =
      ModN.mkQ N (b.equivFun.symm z) := by
  simp only [Basis.equivFun_symm_apply, _root_.map_sum, map_zsmul,
    ModN.basis_apply_eq_mkQ, Int.cast_smul_eq_zsmul]

open scoped Fin.IntCast in
lemma finEquiv_divMod (N : ℕ) [NeZero N] (z : ℤ) :
    ZMod.finEquiv N (Int.divModEquiv N z).2 = (z : ZMod N) := by
  cases N with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ N =>
    apply Fin.ext
    change (Int.divModEquiv (N+1) z).2.val = (z : Fin (N+1)).val
    simp [Int.divModEquiv, Int.natMod]
    have h := Int.emod_lt_of_pos z (show 0 < (N : ℤ)+1 by omega)
    omega

lemma integralResidueEquiv_coordinates (b : Basis d ℤ R) (N : ℕ) [NeZero N]
    (z : d → ℤ) :
    integralResidueEquiv b N (integerCongruenceEquiv N z).1 =
      Ideal.Quotient.mk (rationalModulusIdeal R N) (b.equivFun.symm z) := by
  apply (rationalModulusEquivModN (R := R) N).injective
  have hz : (Equiv.piCongrRight fun _ : d => (ZMod.finEquiv N).toEquiv)
      (integerCongruenceEquiv N z).1 = fun i => (z i : ZMod N) := by
    funext i
    exact finEquiv_divMod N (z i)
  change (rationalModulusEquivModN (R := R) N)
    ((rationalModulusEquivModN (R := R) N).symm
      ((ModN.basis b).equivFun.symm
        ((Equiv.piCongrRight fun _ : d => (ZMod.finEquiv N).toEquiv)
          (integerCongruenceEquiv N z).1))) = _
  rw [AddEquiv.apply_symm_apply, hz]
  change (ModN.basis b).equivFun.symm _ = ModN.mkQ N (b.equivFun.symm z)
  exact modN_basis_coordinates b N z

lemma integralCharacterWeight_coordinates (b : Basis d ℤ R) (N : ℕ) [NeZero N]
    (χ : MulChar (R ⧸ rationalModulusIdeal R N) ℂ) (z : d → ℤ) :
    periodicPrimalWeight N (integralCharacterWeight b N χ) z =
      χ (Ideal.Quotient.mk (rationalModulusIdeal R N) (b.equivFun.symm z)) := by
  simp only [periodicPrimalWeight, integralCharacterWeight, integralResidueEquiv_coordinates]

end PrimeDegreePackets.ThetaConstruction


namespace PrimeDegreePackets.ThetaConstruction
variable {d R : Type*} [Fintype d] [CommRing R]
local instance modulusScaledBasisDecidableEq : DecidableEq d := Classical.decEq d

 

def modulusScaledBasis (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d)
    (N : ℕ) [NeZero N] : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d :=
  ((LinearEquiv.smulOfNeZero ℝ (EuclideanSpace ℝ d) (N : ℝ)
    (Nat.cast_ne_zero.mpr (NeZero.ne N))).toContinuousLinearEquiv).trans B

lemma modulusScaledBasis_cancel (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d)
    (N : ℕ) [NeZero N] (v : EuclideanSpace ℝ d) :
    modulusScaledBasis B N ((N : ℝ)⁻¹ • v) = B v := by
  change B ((N : ℝ) • ((N : ℝ)⁻¹ • v)) = B v
  rw [smul_smul, mul_inv_cancel₀ (Nat.cast_ne_zero.mpr (NeZero.ne N)), one_smul]

 

def integralOrderTheta (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d)
    (b : Basis d ℤ R) (N : ℕ)
    (χ : MulChar (R ⧸ rationalModulusIdeal R N) ℂ) (t : ℝ) : ℂ :=
  ∑' a : R, χ (Ideal.Quotient.mk (rationalModulusIdeal R N) a) *
    Complex.exp (-((Real.pi*t : ℝ) : ℂ) * ‖B (euclideanInteger (b.equivFun a))‖^2)

lemma integralOrderTheta_eq_periodic
    (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d)
    (b : Basis d ℤ R) (N : ℕ) [NeZero N]
    (χ : MulChar (R ⧸ rationalModulusIdeal R N) ℂ) (t : ℝ) :
    integralOrderTheta B b N χ t =
      normalizedPeriodicTheta (modulusScaledBasis B N) N (integralCharacterWeight b N χ) t := by
  unfold integralOrderTheta normalizedPeriodicTheta periodicLatticeTheta
  rw [← b.equivFun.symm.toEquiv.tsum_eq]
  apply tsum_congr
  intro z
  simp only [LinearEquiv.coe_toEquiv, LinearEquiv.apply_symm_apply, modulusScaledBasis_cancel]
  rw [← integralCharacterWeight_coordinates b N χ z]
  rfl

lemma integralOrderTheta_summable
    (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d)
    (b : Basis d ℤ R) (N : ℕ) [NeZero N]
    (χ : MulChar (R ⧸ rationalModulusIdeal R N) ℂ) (t : ℝ) (ht : 0 < t) :
    Summable (fun a : R => χ (Ideal.Quotient.mk (rationalModulusIdeal R N) a) *
      Complex.exp (-((Real.pi*t : ℝ) : ℂ) * ‖B (euclideanInteger (b.equivFun a))‖^2)) := by
  apply b.equivFun.symm.toEquiv.summable_iff.mp
  simpa only [Function.comp_def, LinearEquiv.coe_toEquiv, LinearEquiv.apply_symm_apply,
    modulusScaledBasis_cancel, ← integralCharacterWeight_coordinates b N χ,
    periodicPrimalWeight] using periodicLatticeTheta_summable (modulusScaledBasis B N)
      N (integralCharacterWeight b N χ) (Real.pi*t) (mul_pos Real.pi_pos ht)

 

theorem integralOrderTheta_mellin_entire
    (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d)
    (b : Basis d ℤ R) (N : ℕ) [NeZero N]
    (χ : MulChar (R ⧸ rationalModulusIdeal R N) ℂ) (hχ : χ ≠ 1) :
    Differentiable ℂ (mellin (integralOrderTheta B b N χ)) := by
  have H : integralOrderTheta B b N χ =
      normalizedPeriodicTheta (modulusScaledBasis B N) N (integralCharacterWeight b N χ) := by
    funext t
    exact integralOrderTheta_eq_periodic B b N χ t
  rw [H]
  exact integralCharacterTheta_mellin_entire _ b N χ hχ

lemma integralOrderTheta_mellin_convergent
    (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d)
    (b : Basis d ℤ R) (N : ℕ) [NeZero N]
    (χ : MulChar (R ⧸ rationalModulusIdeal R N) ℂ) (hχ : χ ≠ 1) (s : ℂ) :
    MellinConvergent (integralOrderTheta B b N χ) s := by
  have H : integralOrderTheta B b N χ =
      normalizedPeriodicTheta (modulusScaledBasis B N) N (integralCharacterWeight b N χ) := by
    funext t
    exact integralOrderTheta_eq_periodic B b N χ t
  rw [H]
  exact (integralCharacterTheta_hasMellin _ b N χ hχ s).1

end PrimeDegreePackets.ThetaConstruction
end
end

end OAI
