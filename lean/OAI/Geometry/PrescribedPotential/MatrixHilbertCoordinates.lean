import Mathlib
import OAI.Geometry.PrescribedPotential.GlobalOperator
import OAI.Geometry.PrescribedPotential.KaehlerClosedDerivatives
import OAI.Geometry.PrescribedPotential.SymmetricPrincipalFrame

namespace OAI

/-! Matrix Hilbert Coordinates. -/

section

 

noncomputable section
open Set Filter Topology Matrix Finset
open scoped ContDiff ComplexOrder Matrix.Norms.Elementwise
namespace MetricSystem
open EllipticKernel FrozenPoisson HigherJet KaehlerCalculus
abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℂ
abbrev HM (n : ℕ) := EuclideanSpace ℂ (Fin n × Fin n)
local instance realECIP (n : ℕ) : InnerProductSpace ℝ (EC n) := InnerProductSpace.rclikeToReal ℂ (EC n)
local instance realHMIP (n : ℕ) : InnerProductSpace ℝ (HM n) := InnerProductSpace.rclikeToReal ℂ (HM n)

variable {n : ℕ}
def encodeLinear (n : ℕ) : Mat n ≃ₗ[ℝ] HM n where
  toFun M := WithLp.toLp 2 (fun p => M p.1 p.2)
  invFun u := fun i j => u (i,j)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def encode (n : ℕ) : Mat n ≃L[ℝ] HM n := (encodeLinear n).toContinuousLinearEquiv
@[simp] lemma encode_apply (M : Mat n) (i j : Fin n) : encode n M (i,j) = M i j := rfl
@[simp] lemma decode_apply (u : HM n) (i j : Fin n) : (encode n).symm u i j = u (i,j) := rfl

 
def rawTrace (M : Mat n) (H : Bilin (EC n)) : ℝ :=
  (M*PotentialKaehler.hermitianPartMatrix (pullBilin H)).trace.re
lemma rawTrace_add (M N : Mat n) (H : Bilin (EC n)) : rawTrace (M+N) H = rawTrace M H+rawTrace N H := by
  simp [rawTrace,add_mul,Matrix.trace_add]
lemma rawTrace_smul (c : ℝ) (M : Mat n) (H : Bilin (EC n)) : rawTrace (c • M) H = c*rawTrace M H := by
  simp [rawTrace,Matrix.trace_smul]
lemma rawTrace_inv (M : Mat n) (H : Bilin (EC n)) : rawTrace M⁻¹ H = traceBilin M H := rfl

variable {ι : Type*} [Fintype ι]
def principalLinear (e : OrthonormalBasis ι ℝ (EC n)) (M : Mat n) :
    (EC n →L[ℝ] EC n →L[ℝ] HM n) →ₗ[ℝ] HM n where
  toFun H := ∑ i, ∑ j, ((rawTrace M (rankTwo (e i) (e j))+rawTrace M (rankTwo (e j) (e i)))/2) • H (e i) (e j)
  map_add' H J := by simp only [_root_.add_apply,smul_add,Finset.sum_add_distrib]
  map_smul' c H := by
    simp only [_root_.smul_apply,Finset.smul_sum]
    exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => smul_comm _ _ _))

lemma principalLinear_add (e : OrthonormalBasis ι ℝ (EC n)) (M N : Mat n)
    (H : EC n →L[ℝ] EC n →L[ℝ] HM n) :
    principalLinear e (M+N) H = principalLinear e M H+principalLinear e N H := by
  change (∑ i, ∑ j, ((rawTrace (M+N) (rankTwo (e i) (e j))+rawTrace (M+N) (rankTwo (e j) (e i)))/2) • H (e i) (e j)) = _
  have he (a b c d : ℝ) : (a+b+(c+d))/2 = (a+c)/2+(b+d)/2 := by ring
  simp only [rawTrace_add,he,add_smul,Finset.sum_add_distrib]
  rfl
lemma principalLinear_smul (e : OrthonormalBasis ι ℝ (EC n)) (c : ℝ) (M : Mat n)
    (H : EC n →L[ℝ] EC n →L[ℝ] HM n) :
    principalLinear e (c • M) H = c • principalLinear e M H := by
  change (∑ i, ∑ j, ((rawTrace (c • M) (rankTwo (e i) (e j))+rawTrace (c • M) (rankTwo (e j) (e i)))/2) • H (e i) (e j)) = _
  have he (a b c : ℝ) : (c*a+c*b)/2 = c*((a+b)/2) := by ring
  simp only [rawTrace_smul,he,mul_smul,← Finset.smul_sum]
  rfl

local instance hessianNormedAdd (n : ℕ) : NormedAddCommGroup (EC n →L[ℝ] EC n →L[ℝ] HM n) := inferInstance
local instance hessianNormedSpace (n : ℕ) : NormedSpace ℝ (EC n →L[ℝ] EC n →L[ℝ] HM n) := inferInstance

def principalBilinear (e : OrthonormalBasis ι ℝ (EC n)) :
    Mat n →L[ℝ] ((EC n →L[ℝ] EC n →L[ℝ] HM n) →L[ℝ] HM n) :=
  ({ toFun M := (principalLinear e M).toContinuousLinearMap
     map_add' M N := by
       apply ContinuousLinearMap.ext
       intro H
       exact principalLinear_add e M N H
     map_smul' c M := by
       apply ContinuousLinearMap.ext
       intro H
       exact principalLinear_smul e c M H } :
       Mat n →ₗ[ℝ] ((EC n →L[ℝ] EC n →L[ℝ] HM n) →L[ℝ] HM n)).toContinuousLinearMap

lemma principalBilinear_inv (e : OrthonormalBasis ι ℝ (EC n)) (M : Mat n)
    (H : EC n →L[ℝ] EC n →L[ℝ] HM n) :
    principalBilinear e M⁻¹ H = principalApply e (traceBilin M) H := rfl

def inverseCoefficient (u : HM n) : Mat n := ((encode n).symm u)⁻¹

lemma inverseCoefficient_smooth {u : HM n} (hu : ((encode n).symm u).det ≠ 0) :
    ContDiffAt ℝ ∞ (inverseCoefficient (n := n)) u := by
  let U : Set (HM n) := {u | ((encode n).symm u).det ≠ 0}
  have hU : IsOpen U := (isClosed_eq ((encode n).symm.continuous.matrix_det) continuous_const).isOpen_compl
  exact (MatrixSmoothGeneral.inverse (encode n).symm.contDiff.contDiffOn (fun y hy => hy)).contDiffAt (hU.mem_nhds hu)

 
def W (a : ℂ) (v : V n) (J : EC n →L[ℝ] HM n) : Mat n :=
  (1/2:ℂ) • ((encode n).symm (J ((coordinateEquiv n).symm v))+
    a • (encode n).symm (J ((coordinateEquiv n).symm (Complex.I • v))))

def quadraticCoefficient (p : HM n × (EC n →L[ℝ] HM n)) : HM n :=
  encode n (∑ i, ∑ j, (inverseCoefficient p.1 i j) •
    (W Complex.I (e j) p.2*inverseCoefficient p.1*W (-Complex.I) (e i) p.2))
end MetricSystem

end
end

end OAI
