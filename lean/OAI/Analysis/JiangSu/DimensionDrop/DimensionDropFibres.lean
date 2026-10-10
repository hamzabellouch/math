import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.DimensionDrop.DimensionDropRelations

namespace OAI

noncomputable section


namespace DimensionDropRelations.Witness
open CompletelyPositiveOperations CurrentMain
open scoped ComplexOrder CStarAlgebra

variable {I : Type*} [Fintype I] [DecidableEq I]
variable {B : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
variable {p : I} (w : Witness (B := B) p)
local notation "h" => w.φ 1
local notation "E" => 1-h
local notation "k" => w.rangeMass
local notation "c" => w.parameter

lemma mass_E : k*E=0 := by rw [mul_sub,mul_one,w.mass_h,sub_self]
lemma parameter_E : c*E=h*E := by rw [parameter,sub_mul,w.mass_E,sub_zero]
lemma parameter_column (i : I) : c*w.column i=w.column i*h := by
  rw [parameter,sub_mul,w.h_column,w.mass_column]
  noncomm_ring

variable {t : ℝ} (hc : w.parameter=t • (1:B))
include hc
lemma fibre_h_E : h*E=t • E := by
  rw [←w.parameter_E,hc,smul_mul_assoc,one_mul]
lemma fibre_E_sq : E*E=(1-t) • E := by
  rw [sub_mul,one_mul,w.fibre_h_E hc,sub_smul,one_smul]
lemma fibre_column_E (i : I) : w.column i*E=(1-t) • w.column i := by
  have he := w.parameter_column i
  rw [hc,smul_mul_assoc,one_mul] at he
  rw [mul_sub,mul_one,←he,sub_smul,one_smul]

 def fibreAnchor (t : ℝ) : B := (1-t)⁻¹ • E
 def fibreColumn (t : ℝ) (i : I) : B := (Real.sqrt (1-t))⁻¹ • w.column i
 def fibreEntry (t : ℝ) : Option I → B
  | none => w.fibreAnchor t
  | some i => w.fibreColumn t i

omit hc in
lemma fibreAnchor_star (t : ℝ) : star (w.fibreAnchor t)=w.fibreAnchor t := by
  simp only [fibreAnchor,star_smul,star_trivial,star_sub,star_one,w.h_nonneg.star_eq]
lemma fibreAnchor_projection (ht : t<1) : IsStarProjection (w.fibreAnchor t) := by
  have hr : 1-t≠0 := ne_of_gt (sub_pos.mpr ht)
  refine ⟨?_,w.fibreAnchor_star t⟩
  change ((1-t)⁻¹ • E)*((1-t)⁻¹ • E)=(1-t)⁻¹ • E
  rw [smul_mul_assoc,mul_smul_comm,w.fibre_E_sq hc,smul_smul,smul_smul]
  congr 1
  field_simp
omit hc in
lemma fibreColumn_inner (ht : t<1) (i j : I) :
    star (w.fibreColumn t i)*w.fibreColumn t j=if i=j then w.fibreAnchor t else 0 := by
  have hr : 0≤1-t := (sub_pos.mpr ht).le
  have he : (Real.sqrt (1-t))⁻¹*(Real.sqrt (1-t))⁻¹=(1-t)⁻¹ := by
    rw [←mul_inv,←sq,Real.sq_sqrt hr]
  simp only [fibreColumn,star_smul,star_trivial,smul_mul_assoc,mul_smul_comm,smul_smul,w.column_inner]
  rw [he]
  split_ifs <;> simp [fibreAnchor]
omit hc in
lemma fibreAnchor_column (t : ℝ) (i : I) : w.fibreAnchor t*w.fibreColumn t i=0 := by
  simp only [fibreAnchor,fibreColumn,smul_mul_assoc,mul_smul_comm,w.E_column,smul_zero]
omit hc in
lemma fibreColumn_star_anchor (t : ℝ) (i : I) : star (w.fibreColumn t i)*w.fibreAnchor t=0 := by
  have he := congrArg star (w.fibreAnchor_column t i)
  simpa only [star_mul,w.fibreAnchor_star,star_zero] using he

 def fibreRow (ht : t<1) : ProjectionRow (Option I) (w.fibreAnchor t) where
  projection := w.fibreAnchor_projection hc ht
  entry := w.fibreEntry t
  gram_diag i := by
    cases i with
    | none => simpa only [fibreEntry,w.fibreAnchor_star] using (w.fibreAnchor_projection hc ht).isIdempotentElem.eq
    | some i => simpa only [fibreEntry,ite_true] using w.fibreColumn_inner ht i i
  gram_offdiag i j hij := by
    cases i with
    | none => cases j with
      | none => exact (hij rfl).elim
      | some j => simpa only [fibreEntry,w.fibreAnchor_star] using w.fibreAnchor_column t j
    | some i => cases j with
      | none => exact w.fibreColumn_star_anchor t i
      | some j => simpa only [fibreEntry,ite_eq_right (fun he => hij (congrArg some he))] using
          w.fibreColumn_inner ht i j

lemma fibreRow_range (ht : t<1) : (w.fibreRow hc ht).sample (w.fibreAnchor t)=1 := by
  have hr : 1-t≠0 := ne_of_gt (sub_pos.mpr ht)
  have he : (Real.sqrt (1-t))⁻¹*(Real.sqrt (1-t))⁻¹=(1-t)⁻¹ := by
    rw [←mul_inv,←sq,Real.sq_sqrt (le_of_lt (sub_pos.mpr ht))]
  have hs : (w.fibreRow hc ht).sample (w.fibreAnchor t)=
      w.fibreAnchor t+(1-t)⁻¹ • k := by
    change (∑ i : Option I,(w.fibreRow hc ht).entry i*w.fibreAnchor t*star ((w.fibreRow hc ht).entry i))=_
    simp only [(w.fibreRow hc ht).right_support]
    rw [Fintype.sum_option]
    change w.fibreAnchor t*star (w.fibreAnchor t)+
      ∑ i : I,w.fibreColumn t i*star (w.fibreColumn t i)=_
    rw [w.fibreAnchor_star,(w.fibreAnchor_projection hc ht).isIdempotentElem.eq]
    simp only [fibreColumn,star_smul,star_trivial,smul_mul_assoc,mul_smul_comm,smul_smul,he]
    rw [←Finset.smul_sum]
    rfl
  rw [hs,fibreAnchor,←smul_add]
  have hec : E+k=(1-t) • (1:B) := by
    have hp : E+k=1-c := by rw [parameter]; noncomm_ring
    rw [hp,hc,sub_smul,one_smul]
  rw [hec,smul_smul,inv_mul_cancel₀ hr,one_smul]

end DimensionDropRelations.Witness


namespace DimensionDropRelations.Witness
open CompletelyPositiveOperations CurrentMain ConcreteMatrixUnits
open scoped ComplexOrder CStarAlgebra

variable {I : Type*} [Fintype I] [DecidableEq I]
variable {B : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
variable {p : I} (w : Witness (B := B) p)

lemma fibreAnchor_commute (t : ℝ) (M : CStarMatrix I I ℂ) :
    Commute (w.φ M) (w.fibreAnchor t) := by
  exact ((Commute.one_right _).sub_right (w.h_commute M).symm).smul_right _

variable {t : ℝ} (hc : w.parameter=t • (1:B))
include hc
lemma h_fibreAnchor : w.φ 1*w.fibreAnchor t=t • w.fibreAnchor t := by
  simp only [fibreAnchor,mul_smul_comm,w.fibre_h_E hc,smul_smul]
  congr 1; ring

 def fibreInner (t : ℝ) (i j : I) : B := t⁻¹ • (w.φ (matrixUnit i j)*w.fibreAnchor t)

lemma fibreInner_left (ht : t<1) (i j : I) :
    w.fibreAnchor t*w.fibreInner t i j=w.fibreInner t i j := by
  rw [fibreInner,mul_smul_comm,←mul_assoc,(w.fibreAnchor_commute t _).eq.symm,mul_assoc,
    (w.fibreAnchor_projection hc ht).isIdempotentElem.eq]

lemma fibreInner_mul (ht0 : 0<t) (ht1 : t<1) (i j k l : I) :
    w.fibreInner t i j*w.fibreInner t k l=if j=k then w.fibreInner t i l else 0 := by
  have hq := (w.fibreAnchor_projection hc ht1).isIdempotentElem.eq
  have he : (w.φ (matrixUnit i j)*w.fibreAnchor t)*(w.φ (matrixUnit k l)*w.fibreAnchor t)=
      t • (w.φ (matrixUnit i j*matrixUnit k l)*w.fibreAnchor t) := by
    calc
      _ = w.φ (matrixUnit i j)*(w.fibreAnchor t*w.φ (matrixUnit k l))*w.fibreAnchor t := by noncomm_ring
      _ = (w.φ (matrixUnit i j)*w.φ (matrixUnit k l))*(w.fibreAnchor t*w.fibreAnchor t) := by
        rw [(w.fibreAnchor_commute t _).eq.symm]; noncomm_ring
      _ = _ := by
        rw [hq,w.orderZero,mul_assoc,w.h_fibreAnchor hc,mul_smul_comm]
  simp only [fibreInner,smul_mul_assoc,mul_smul_comm,smul_smul]
  rw [he,smul_smul]
  have hinv : (t⁻¹*t⁻¹)*t=t⁻¹ := by field_simp
  rw [hinv,matrixUnit_mul_general]
  split_ifs <;> simp only [map_zero,zero_mul,smul_zero]

omit hc in
lemma fibreInner_star (t : ℝ) (i j : I) : star (w.fibreInner t i j)=w.fibreInner t j i := by
  simp only [fibreInner,star_smul,star_trivial,star_mul,w.fibreAnchor_star,←cp_map_star,matrixUnit_star]
  rw [(w.fibreAnchor_commute t _).eq]

lemma fibreInner_sum (ht : 0<t) : (∑ i,w.fibreInner t i i)=w.fibreAnchor t := by
  simp only [fibreInner,←Finset.smul_sum,←Finset.sum_mul,←map_sum,matrixUnit_diag_sum,w.h_fibreAnchor hc,smul_smul,
    inv_mul_cancel₀ (ne_of_gt ht),one_smul]

 def interiorUnits (ht0 : 0<t) (ht1 : t<1) : System (Option I × I) B where
  entry x y := (w.fibreRow hc ht1).coeff (w.fibreInner t x.2 y.2) x.1 y.1
  mul_entry i j k l := by
    rw [(w.fibreRow hc ht1).coeff_mul _ _ (w.fibreInner_left hc ht1 _ _),w.fibreInner_mul hc ht0 ht1]
    by_cases h1 : j.1=k.1 <;> by_cases h2 : j.2=k.2
    · simp only [ite_eq_left h1,ite_eq_left h2,ite_eq_left (Prod.ext h1 h2)]
    · have hjk : j≠k := fun h => h2 (congrArg Prod.snd h)
      simp only [ite_eq_left h1,ite_eq_right h2,ite_eq_right hjk,ProjectionRow.coeff,mul_zero,zero_mul]
    · have hjk : j≠k := fun h => h1 (congrArg Prod.fst h)
      simp only [ite_eq_right h1,ite_eq_right hjk]
    · have hjk : j≠k := fun h => h1 (congrArg Prod.fst h)
      simp only [ite_eq_right h1,ite_eq_right hjk]
  star_entry i j := by rw [(w.fibreRow hc ht1).coeff_star,w.fibreInner_star]
  sum_diag := by
    rw [Fintype.sum_prod_type]
    change (∑ r : Option I,∑ i : I,(w.fibreRow hc ht1).entry r*w.fibreInner t i i*star ((w.fibreRow hc ht1).entry r))=1
    simp only [←Finset.sum_mul,←Finset.mul_sum,w.fibreInner_sum hc ht0]
    exact w.fibreRow_range hc ht1

 def interiorHom (ht0 : 0<t) (ht1 : t<1) : CStarMatrix (Option I × I) (Option I × I) ℂ →⋆ₐ[ℂ] B :=
  (w.interiorUnits hc ht0 ht1).hom

end DimensionDropRelations.Witness

end

end OAI
