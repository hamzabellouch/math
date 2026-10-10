import Mathlib
import OAI.Analysis.BoundedHochschild.CocycleNormalParts
import OAI.Analysis.BoundedHochschild.FactorFinitePaths
import OAI.Analysis.BoundedHochschild.FreeWords
import OAI.Analysis.BoundedHochschild.MatrixDisplacement
import OAI.Analysis.BoundedHochschild.UnitaryLifts
import OAI.Analysis.BoundedHochschild.FactorPrimitive
import OAI.Analysis.BoundedHochschild.TypeIICorners
import OAI.Analysis.BoundedHochschild.CenterPowers

namespace OAI

/-! Restriction and extension of cochains along central corners. -/

noncomputable section

open Filter Topology
open scoped ComplexOrder
namespace HochschildAtomic
open BoundedHochschild HochschildCorners
universe u
variable {M : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
variable (p : M) (hp : IsStarProjection p) (hc : ∀ a : M, Commute p a)

def cornerInclude : Corner p hp →L[ℂ] M where
  toFun := fun a => a
  map_add' := fun _ _ => rfl
  map_smul' := fun _ _ => rfl
  cont := continuous_subtype_val

def centralCornerMap : M →L[ℂ] Corner p hp :=
  LinearMap.mkContinuous
  { toFun := fun a => ⟨p*a,⟨by rw [← mul_assoc,hp.isIdempotentElem.eq],by
      rw [mul_assoc,← (hc a).eq,← mul_assoc,hp.isIdempotentElem.eq]⟩⟩
    map_add' := fun a b => Subtype.ext (mul_add p a b)
    map_smul' := fun c a => Subtype.ext (mul_smul_comm c p a) }
  1 (fun a => by
    change ‖p*a‖≤1*‖a‖
    exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right hp.norm_le (norm_nonneg _)))

@[simp] lemma centralCornerMap_coe {M : Type u} [CStarAlgebra M] [PartialOrder M]
    [StarOrderedRing M] (p : M) (hp : IsStarProjection p) (hc : ∀ a : M, Commute p a)
    (a : M) : ((centralCornerMap p hp hc a):M)=p*a := rfl
@[simp] lemma cornerInclude_coe {M : Type u} [CStarAlgebra M] [PartialOrder M]
    [StarOrderedRing M] (p : M) (hp : IsStarProjection p) (a : Corner p hp) :
    cornerInclude p hp a=(a:M) := rfl

lemma centralCornerMap_norm {M : Type u} [CStarAlgebra M] [PartialOrder M]
    [StarOrderedRing M] (p : M) (hp : IsStarProjection p) (hc : ∀ a : M, Commute p a)
    (a : M) : ‖centralCornerMap p hp hc a‖≤‖a‖ := by
  change ‖p*a‖≤‖a‖
  exact (norm_mul_le _ _).trans (by simpa using
    (mul_le_mul_of_nonneg_right hp.norm_le (norm_nonneg a)))

lemma centralCornerMap_mul {M : Type u} [CStarAlgebra M] [PartialOrder M]
    [StarOrderedRing M] (p : M) (hp : IsStarProjection p) (hc : ∀ a : M, Commute p a)
    (a b : M) :
    centralCornerMap p hp hc (a*b)=centralCornerMap p hp hc a*centralCornerMap p hp hc b := by
  apply Subtype.ext
  exact (central_idempotent_mul p hp.isIdempotentElem.eq (fun a => (hc a).eq) a b).symm

lemma centralCornerMap_left {M : Type u} [CStarAlgebra M] [PartialOrder M]
    [StarOrderedRing M] (p : M) (hp : IsStarProjection p) (hc : ∀ a : M, Commute p a)
    (a : Corner p hp) (b : M) :
    centralCornerMap p hp hc ((a:M)*b)=a*centralCornerMap p hp hc b := by
  apply Subtype.ext
  change p*((a:M)*b)=(a:M)*(p*b)
  rw [← mul_assoc,a.property.1,← mul_assoc,a.property.2]

lemma centralCornerMap_right {M : Type u} [CStarAlgebra M] [PartialOrder M]
    [StarOrderedRing M] (p : M) (hp : IsStarProjection p) (hc : ∀ a : M, Commute p a)
    (a : M) (b : Corner p hp) :
    centralCornerMap p hp hc (a*(b:M))=centralCornerMap p hp hc a*b := by
  apply Subtype.ext
  exact (mul_assoc p a (b:M)).symm

lemma cornerInclude_left {M : Type u} [CStarAlgebra M] [PartialOrder M]
    [StarOrderedRing M] (p : M) (hp : IsStarProjection p) (hc : ∀ a : M, Commute p a)
    (a : M) (b : Corner p hp) :
    a*cornerInclude p hp b=cornerInclude p hp (centralCornerMap p hp hc a*b) := by
  change a*(b:M)=(p*a)*(b:M)
  rw [(hc a).eq,mul_assoc,b.property.1]

lemma cornerInclude_right {M : Type u} [CStarAlgebra M] [PartialOrder M]
    [StarOrderedRing M] (p : M) (hp : IsStarProjection p) (hc : ∀ a : M, Commute p a)
    (a : Corner p hp) (b : M) :
    cornerInclude p hp a*b=cornerInclude p hp (a*centralCornerMap p hp hc b) := by
  change (a:M)*b=(a:M)*(p*b)
  rw [← mul_assoc,a.property.2]

def cornerRestrict {n : ℕ} (f : Cochain M n) : Cochain (Corner p hp) n :=
  (centralCornerMap p hp hc).compContinuousMultilinearMap
    (f.compContinuousLinearMap (fun _ => cornerInclude p hp))

def cornerExtend {n : ℕ} (g : Cochain (Corner p hp) n) : Cochain M n :=
  (cornerInclude p hp).compContinuousMultilinearMap
    (g.compContinuousLinearMap (fun _ => centralCornerMap p hp hc))

@[simp] lemma cornerRestrict_apply {M : Type u} [CStarAlgebra M] [PartialOrder M]
    [StarOrderedRing M] (p : M) (hp : IsStarProjection p) (hc : ∀ a : M, Commute p a)
    {n : ℕ} (f : Cochain M n) (x : Fin n → Corner p hp) :
    cornerRestrict p hp hc f x=centralCornerMap p hp hc (f (fun i => (x i:M))) := rfl
@[simp] lemma cornerExtend_apply {M : Type u} [CStarAlgebra M] [PartialOrder M]
    [StarOrderedRing M] (p : M) (hp : IsStarProjection p) (hc : ∀ a : M, Commute p a)
    {n : ℕ} (g : Cochain (Corner p hp) n) (x : Fin n → M) :
    cornerExtend p hp hc g x=cornerInclude p hp (g (fun i => centralCornerMap p hp hc (x i))) := rfl

lemma cornerRestrict_norm {n : ℕ} (f : Cochain M n) : ‖cornerRestrict p hp hc f‖≤‖f‖ := by
  apply ContinuousMultilinearMap.opNorm_le_bound (norm_nonneg _)
  intro x
  exact (centralCornerMap_norm p hp hc _).trans (f.le_opNorm (fun i => (x i:M)))

lemma cornerExtend_norm {n : ℕ} (g : Cochain (Corner p hp) n) : ‖cornerExtend p hp hc g‖≤‖g‖ := by
  apply ContinuousMultilinearMap.opNorm_le_bound (norm_nonneg _)
  intro x
  change ‖g (fun i => centralCornerMap p hp hc (x i))‖≤_
  exact (g.le_opNorm _).trans (mul_le_mul_of_nonneg_left
    (Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun _ _ => centralCornerMap_norm p hp hc _))
    (norm_nonneg _))

lemma merge_corner_include {M : Type u} [CStarAlgebra M] [PartialOrder M]
    [StarOrderedRing M] (p : M) (hp : IsStarProjection p)
    {n : ℕ} (x : Fin (n+1) → Corner p hp) (j : Fin n) :
    mergeInputs (fun i => (x i:M)) j=fun i => ((mergeInputs (M:=Corner p hp) x j i):M) := by
  funext i
  simp only [mergeInputs]
  split_ifs <;> rfl

lemma merge_corner_map {n : ℕ} (x : Fin (n+1) → M) (j : Fin n) :
    mergeInputs (fun i => centralCornerMap p hp hc (x i)) j=
      fun i => centralCornerMap p hp hc (mergeInputs x j i) := by
  funext i
  simp only [mergeInputs]
  split_ifs <;> first | rfl | exact (centralCornerMap_mul p hp hc _ _).symm

lemma differential_cornerRestrict {n : ℕ} (f : Cochain M n) (x : Fin (n+1) → Corner p hp) :
    differentialValue (cornerRestrict p hp hc f) x=
      centralCornerMap p hp hc (differentialValue f (fun i => (x i:M))) := by
  simp only [differentialValue,cornerRestrict_apply,map_add,map_sum,map_smul,
    centralCornerMap_left,centralCornerMap_right,merge_corner_include]

lemma differential_cornerExtend {n : ℕ} (g : Cochain (Corner p hp) n) (x : Fin (n+1) → M) :
    differentialValue (cornerExtend p hp hc g) x=
      cornerInclude p hp (differentialValue g (fun i => centralCornerMap p hp hc (x i))) := by
  simp only [differentialValue,cornerExtend_apply,merge_corner_map,map_add,map_sum,map_smul,
    cornerInclude_left p hp hc,cornerInclude_right p hp hc]

lemma cornerExtend_support {M : Type u} [CStarAlgebra M] [PartialOrder M]
    [StarOrderedRing M] (p : M) (hp : IsStarProjection p) (hc : ∀ a : M, Commute p a)
    {n : ℕ} (g : Cochain (Corner p hp) n) (x : Fin n → M) :
    p*cornerExtend p hp hc g x=cornerExtend p hp hc g x :=
  (g (fun i => centralCornerMap p hp hc (x i))).property.1

lemma cornerExtend_primitive {n : ℕ} (f : Cochain M (n+1)) (g : Cochain (Corner p hp) n)
    (hg : ∀ x, differentialValue g x=cornerRestrict p hp hc f x) :
    ∀ x, differentialValue (cornerExtend p hp hc g) x=centralCut p (centralOutput p f) x := by
  intro x
  rw [differential_cornerExtend,hg]
  rfl

end HochschildAtomic

end

end OAI
