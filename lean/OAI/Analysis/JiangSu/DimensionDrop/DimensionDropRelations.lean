import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.Comparison.PropertySI
import OAI.Analysis.JiangSu.CentralSequences.UnitalNormCentralAlgebra
import OAI.Analysis.JiangSu.MatrixAlgebras.MatrixDiagonalTrace

namespace OAI

noncomputable section


namespace DirectComparison
open Pureness CurrentMain Filter Topology CompletelyPositiveOperations
open scoped ComplexOrder ENNReal CStarAlgebra

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable [Nontrivial A] [Nonempty (TracialState A)] [TopologicalSpace.SeparableSpace A]
variable (U : Ultrafilter ℕ)
local notation "N" => NormUltra.QuotientAlgebra (fun _ : ℕ => A) U
local notation "C" => unitalNormCentralizer (A := A) U
local notation "D" => FamilyUltrapower (fun τ : TracialState A => τ) U
local notation "q" => unitalCentralToTracial (A := A) U
local notation "L" => familyLimitTrace (fun τ : TracialState A => τ) U

 theorem comparison_dimension_drop_relations (hfree : (U : Filter ℕ)≤atTop)
    (hnuc : IsNuclear.{0,0} A) (hsimple : TopologicallySimple A) (hinf : ¬FiniteDimensional ℂ A)
    (hcmp : StrictComparison A) (n : ℕ) (hn : 0<n) :
    ∃ (φ : CStarMatrix (Fin n) (Fin n) ℂ →CP C) (s : C),
      (∀ M,‖φ M‖≤‖M‖) ∧ (∀ M P,φ M*φ P=φ (M*P)*φ 1) ∧
      ‖s‖≤1 ∧ star s*s=1-φ 1 ∧ φ (matrixUnit ⟨0,hn⟩ ⟨0,hn⟩)*s=s := by
  classical
  let p : Fin n := ⟨0,hn⟩
  let : Nonempty (Fin n) := ⟨p⟩
  obtain ⟨η,φ,hφ,hφn,hφrel⟩ := comparison_central_order_zero U hfree hsimple hinf hcmp hnuc n hn
  let E : C := 1-φ 1
  let F : C := φ (matrixUnit p p)
  have h1p : 0≤φ 1 := map_nonneg φ zero_le_one
  have h1n : ‖φ 1‖≤1 := by simpa only [norm_one] using hφn 1
  have h1le : φ 1≤1 := (CStarAlgebra.norm_le_one_iff_of_nonneg _ h1p).mp h1n
  have hEp : 0≤E := sub_nonneg.mpr h1le
  have hEn : ‖E‖≤1 := (CStarAlgebra.norm_le_one_iff_of_nonneg _ hEp).mpr (sub_le_self _ h1p)
  have hEq : q E=0 := by
    simp only [E,map_sub,map_one,hφ,map_one,sub_self]
  have hFp : 0≤F := map_nonneg φ (matrixUnit_projection p).nonneg
  have hFn : ‖F‖≤1 := (hφn _).trans (matrixUnit_projection p).norm_le
  have hFq : IsStarProjection (q F) := by rw [show q F=η (matrixUnit p p) from hφ _]; exact (matrixUnit_projection p).map η
  have htr (v : ℕ → TracialState A) : ((L v).functional (q F)).re=(n:ℝ)⁻¹ := by
    rw [show q F=η (matrixUnit p p) from hφ _,trace_matrix_corner η (L v) p,Fintype.card_fin]
    simp
  have hnr : 0<(n:ℝ) := by exact_mod_cast hn
  let t : ℝ := (n:ℝ)⁻¹/4
  have ht : 0<t := by dsimp [t]; positivity
  have hlarge (v : ℕ → TracialState A) : 2*t≤((L v).functional (q F)).re := by
    rw [htr]; dsimp [t]; nlinarith [inv_pos.mpr hnr]
  obtain ⟨s,hsn,hse,hsF,_hsex,hsc⟩ := comparison_property_SI_projection_large U hnuc hsimple hcmp hfree
    (E:N) (F:N) ((unitalNormCentralizer_nonneg_iff U E).mp hEp) hEn hEq
    (fun a => E.property a) ((unitalNormCentralizer_nonneg_iff U F).mp hFp) hFn
    (fun a => F.property a) hFq ht hlarge
  refine ⟨φ,⟨s,fun a => (hsc a).eq⟩,hφn,hφrel,hsn,?_,?_⟩
  · exact Subtype.ext hse
  · exact Subtype.ext hsF

end DirectComparison


namespace DimensionDropRelations
open CompletelyPositiveOperations
open scoped ComplexOrder CStarAlgebra

variable {I : Type*} [Fintype I] [DecidableEq I]
variable {B : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

lemma matrixUnit_mul_general (i j k l : I) :
    matrixUnit i j*matrixUnit k l = if j=k then matrixUnit i l else 0 := by
  ext a b
  by_cases hjk : j=k
  · subst k; simp [matrixUnit_mul]
  · simp [matrixUnit,CStarMatrix.mul_apply,Matrix.single_apply,hjk,ite_and]

structure Witness (p : I) where
  φ : CStarMatrix I I ℂ →CP B
  contractive : ∀ M, ‖φ M‖≤‖M‖
  orderZero : ∀ M P,φ M*φ P=φ (M*P)*φ 1
  s : B
  small : star s*s=1-φ 1
  support : φ (matrixUnit p p)*s=s

namespace Witness
variable {p : I} (w : Witness (B := B) p)
local notation "h" => w.φ 1
local notation "E" => 1-h
local notation "a" => fun i j : I => w.φ (matrixUnit i j)

def column (i : I) : B := a i p*w.s
def rangeMass : B := ∑ i,column w i*star (column w i)
def parameter : B := h-rangeMass w

lemma h_nonneg : 0≤h := map_nonneg w.φ zero_le_one
lemma h_le_one : h≤1 := by
  let : Nonempty I := ⟨p⟩
  apply (CStarAlgebra.norm_le_one_iff_of_nonneg _ w.h_nonneg).mp
  simpa only [norm_one] using w.contractive 1
lemma h_commute (M : CStarMatrix I I ℂ) : Commute h (w.φ M) := by
  change w.φ 1*w.φ M=w.φ M*w.φ 1
  simpa only [one_mul] using w.orderZero 1 M
lemma h_support : h*w.s=w.s := by
  apply CStarExcision.support_monotone w.h_le_one _ w.support
  exact OrderHomClass.monotone w.φ (matrixUnit_projection p).le_one
lemma E_support : E*w.s=0 := by rw [sub_mul,one_mul,w.h_support,sub_self]
lemma s_square : w.s*w.s=0 := by
  apply (CStarRing.star_mul_self_eq_zero_iff _).mp
  rw [star_mul, mul_assoc, ←mul_assoc (star w.s) w.s w.s, w.small,w.E_support,mul_zero]
lemma column_star (i : I) : star (column w i)=star w.s*a p i := by
  simp only [column,star_mul,←cp_map_star,matrixUnit_star]
lemma matrix_column (i j k : I) : a i j*column w k=if j=k then column w i else 0 := by
  rw [column,←mul_assoc,w.orderZero,matrixUnit_mul_general]
  split_ifs with hjk
  · rw [mul_assoc,w.h_support]
    rfl
  · simp
lemma h_column (i : I) : h*column w i=column w i := by
  rw [column,←mul_assoc,(w.h_commute _).eq,mul_assoc,w.h_support]
lemma E_column (i : I) : E*column w i=0 := by
  rw [sub_mul,one_mul,w.h_column,sub_self]
lemma column_inner (i j : I) : star (column w i)*column w j=if i=j then E else 0 := by
  rw [w.column_star,mul_assoc,w.matrix_column]
  split_ifs with hij
  · subst j
    rw [column,←mul_assoc]
    have he := congrArg star w.support
    simp only [star_mul,←cp_map_star,matrixUnit_star] at he
    rw [he,w.small]
  · simp
lemma column_s (i : I) : column w i*w.s=0 := by
  rw [column,mul_assoc,w.s_square,mul_zero]
lemma column_star_s (i : I) : star (column w i)*w.s=if i=p then E else 0 := by
  have hp : column w p=w.s := w.support
  rw [←hp,w.column_inner]
lemma mass_nonneg : 0≤rangeMass w := Finset.sum_nonneg fun _ _ => mul_star_self_nonneg _
lemma mass_star : star (rangeMass w)=rangeMass w := w.mass_nonneg.star_eq
lemma h_mass : h*rangeMass w=rangeMass w := by
  simp only [rangeMass,Finset.mul_sum,←mul_assoc,w.h_column]
lemma mass_h : rangeMass w*h=rangeMass w := by
  have he := congrArg star w.h_mass
  simpa only [star_mul,w.mass_star,w.h_nonneg.star_eq] using he
lemma mass_s : rangeMass w*w.s=w.s*E := by
  simp only [rangeMass,Finset.sum_mul,mul_assoc,w.column_star_s]
  simp only [mul_ite,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  rw [column,w.support]
lemma s_mass : w.s*rangeMass w=0 := by
  have hz (i : I) : w.s*column w i=0 := by
    apply (CStarRing.star_mul_self_eq_zero_iff _).mp
    rw [star_mul,mul_assoc,←mul_assoc (star w.s),w.small,w.E_column,mul_zero]
  simp only [rangeMass,Finset.mul_sum,←mul_assoc,hz,zero_mul,Finset.sum_const_zero]
lemma parameter_s : Commute (parameter w) w.s := by
  change (h-rangeMass w)*w.s=w.s*(h-rangeMass w)
  simp only [sub_mul,w.h_support,w.mass_s,mul_sub,w.s_mass,sub_zero]
  noncomm_ring
lemma mass_matrix (i j : I) : rangeMass w*a i j=column w i*star (column w j) := by
  have he (k : I) : star (column w k)*a i j=if k=i then star (column w j) else 0 := by
    have hh := congrArg star (w.matrix_column j i k)
    simpa only [star_mul,←cp_map_star,matrixUnit_star,apply_ite,star_zero,eq_comm] using hh
  simp only [rangeMass,Finset.sum_mul,mul_assoc,he,mul_ite,mul_zero]
  simp
lemma matrix_mass (i j : I) : a i j*rangeMass w=column w i*star (column w j) := by
  simp only [rangeMass,Finset.mul_sum,←mul_assoc,w.matrix_column,ite_mul,zero_mul]
  simp
lemma parameter_matrix (M : CStarMatrix I I ℂ) : Commute (parameter w) (w.φ M) := by
  have hm (i j : I) : Commute (rangeMass w) (a i j) := by
    change _*_= _*_
    rw [w.mass_matrix,w.matrix_mass]
  have hall : Commute (rangeMass w) (w.φ M) := by
    rw [matrix_decomposition M]
    simp only [map_sum,map_smul]
    exact Commute.sum_right _ _ _ fun i _ => Commute.sum_right _ _ _ fun j _ => (hm i j).smul_right _
  exact (w.h_commute M).sub_left hall

lemma mass_column (i : I) : rangeMass w*column w i=column w i*E := by
  simp only [rangeMass,Finset.sum_mul,mul_assoc,w.column_inner,mul_ite,mul_zero]
  simp
lemma mass_sq : rangeMass w*rangeMass w=∑ i,column w i*E*star (column w i) := by
  nth_rw 2 [rangeMass]
  simp only [Finset.mul_sum,←mul_assoc,w.mass_column]
lemma mass_sq_le : rangeMass w*rangeMass w≤rangeMass w := by
  rw [w.mass_sq,rangeMass]
  apply Finset.sum_le_sum
  intro i _
  simpa only [mul_one] using star_right_conjugate_le_conjugate
    (show E≤1 by simpa using w.h_nonneg) (column w i)
lemma mass_le_one : rangeMass w≤1 := by
  apply (CStarAlgebra.norm_le_one_iff_of_nonneg _ w.mass_nonneg).mp
  have hp : 0≤rangeMass w*rangeMass w := by
    simpa only [w.mass_star] using star_mul_self_nonneg (rangeMass w)
  have hn := CStarAlgebra.norm_le_norm_of_le_of_nonneg w.mass_sq_le hp
  rw [w.mass_nonneg.isSelfAdjoint.norm_mul_self] at hn
  nlinarith [norm_nonneg (rangeMass w)]
lemma parameter_nonneg : 0≤parameter w := by
  have hc : Commute h (1-rangeMass w) := (Commute.one_right h).sub_right
    (show Commute h (rangeMass w) by change _*_= _*_; rw [w.h_mass,w.mass_h])
  have hp := hc.mul_nonneg w.h_nonneg (sub_nonneg.mpr w.mass_le_one)
  simpa only [mul_sub,mul_one,w.h_mass,parameter] using hp
lemma parameter_le_one : parameter w≤1 := (sub_le_self _ w.mass_nonneg).trans w.h_le_one
lemma parameter_star : star (parameter w)=parameter w := w.parameter_nonneg.star_eq
lemma E_mass : E*rangeMass w=0 := by rw [sub_mul,one_mul,w.h_mass,sub_self]
lemma parameter_h : parameter w*h=h*h-rangeMass w := by rw [parameter,sub_mul,w.mass_h]
lemma parameter_equation : h*h-(1+parameter w)*h+parameter w=0 := by
  rw [add_mul,one_mul,w.parameter_h,parameter]
  abel

end Witness
end DimensionDropRelations

end

end OAI
