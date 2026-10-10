import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.DimensionDrop.SequentialCStarChain
import OAI.Analysis.JiangSu.DimensionDrop.PermutationUnitary
import OAI.Analysis.JiangSu.DimensionDrop.DimensionDropScalarFunctions
import OAI.Analysis.JiangSu.CStarAlgebras.StarTermsNormLift

namespace OAI


noncomputable section
open scoped ComplexOrder CStarAlgebra

namespace DimensionDropRelations.Witness
open DimensionDropModel StarTerms

variable {I : Type*} [Fintype I] [DecidableEq I]
local instance functionCStar : CStarAlgebra C(Interval,Mat I) := ContinuousMap.instCStarAlgebra
variable {B : Type} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
variable {p : I} (w : Witness (B := B) p)
 def generatedHom : DimensionDropModel.generated p →⋆ₐ[ℂ] B :=
  closureLift (functionValues p) w.interpret w.polynomial_norm
lemma generatedHom_gen (g : Gen I) :
    w.generatedHom ⟨functionValues p g,StarSubalgebra.le_topologicalClosure _ ⟨.gen g,rfl⟩⟩=w.interpret g :=
  closureLift_gen (functionValues p) w.interpret w.polynomial_norm g
end DimensionDropRelations.Witness

end


noncomputable section
open scoped CStarAlgebra ComplexOrder Kronecker

local instance (n : ℕ) : Semiring (JiangSuConstruction.DimensionDrop (n+1) n) :=
  (inferInstance : CStarAlgebra (JiangSuConstruction.DimensionDrop (n+1) n)).toSemiring
namespace DimensionDropModel
open JiangSuConstruction

 def indexEquiv (n : ℕ) : (Fin (n+1)×Fin n)≃(Option (Fin n)×Fin n) :=
  Equiv.prodCongr (finSuccEquiv n) (Equiv.refl _)
 def twistAmbient (n : ℕ) : C(Interval,TensorMat (n+1) n) →⋆ₐ[ℂ] C(Interval,Mat (Fin n)) :=
  (continuousUnitaryConjugation (finiteMatrixUnitaryPath 1
    (permutationUnitary (flipInner (I := Fin n)))).toContinuousMap).comp
      (continuousReindex (indexEquiv n))
lemma reindex_left (n : ℕ) (a : JiangSuConstruction.Mat (n+1)) :
    CStarMatrix.reindexₐ ℂ ℂ (indexEquiv n) (leftAmplification (n+1) n a)=
      amplify (J := Fin n) (CStarMatrix.reindexₐ ℂ ℂ (finSuccEquiv n) a) := rfl
lemma reindex_right (n : ℕ) (a : JiangSuConstruction.Mat n) :
    CStarMatrix.reindexₐ ℂ ℂ (flipInner (I := Fin n))
      (CStarMatrix.reindexₐ ℂ ℂ (indexEquiv n) (rightAmplification (n+1) n a))=upperEmbed a := by
  change CStarMatrix.reindexₐ ℂ ℂ (flipInner (I := Fin n)) _=
    CStarMatrix.reindexₐ ℂ ℂ (flipInner (I := Fin n))
      (CStarMatrix.reindexₐ ℂ ℂ (Equiv.prodComm (Fin n) (Option (Fin n))) (amplify a))
  apply congrArg (CStarMatrix.reindexₐ ℂ ℂ (flipInner (I := Fin n)))
  ext ⟨b,i⟩ ⟨c,j⟩
  change (if (finSuccEquiv n).symm b=(finSuccEquiv n).symm c then (1:ℂ) else 0)*a i j=
    a i j*(if b=c then 1 else 0)
  simp only [(finSuccEquiv n).symm.injective.eq_iff, mul_comm]
lemma twist_left (n : ℕ) (f : C(Interval,TensorMat (n+1) n)) :
    twistAmbient n f leftEndpoint=CStarMatrix.reindexₐ ℂ ℂ (indexEquiv n) (f leftEndpoint) := by
  change unitaryConjugation ((finiteMatrixUnitaryPath 1
    (permutationUnitary (flipInner (I := Fin n)))) 0) _=_
  rw [Path.source]
  change (1 : Mat (Fin n))*CStarMatrix.reindexₐ ℂ ℂ (indexEquiv n) (f leftEndpoint)*
    star (1 : Mat (Fin n))=CStarMatrix.reindexₐ ℂ ℂ (indexEquiv n) (f leftEndpoint)
  simp
lemma twist_right (n : ℕ) (f : C(Interval,TensorMat (n+1) n)) :
    twistAmbient n f rightEndpoint=CStarMatrix.reindexₐ ℂ ℂ (flipInner (I := Fin n))
      (CStarMatrix.reindexₐ ℂ ℂ (indexEquiv n) (f rightEndpoint)) := by
  change unitaryConjugation ((finiteMatrixUnitaryPath 1
    (permutationUnitary (flipInner (I := Fin n)))) 1) _=_
  rw [Path.target,permutationUnitary_conjugation]
  rfl
 def concreteToGenerated {n : ℕ} (p : Fin n) : DimensionDrop (n+1) n →⋆ₐ[ℂ] generated p :=
  ((twistAmbient n).comp (dimensionDrop (n+1) n).subtype).codRestrict (generated p) (fun f => by
    apply endpoint_function_mem p
    · obtain ⟨a,ha⟩ := f.property.1
      change leftAmplification (n+1) n a=(f : C(Interval,TensorMat (n+1) n)) leftEndpoint at ha
      refine ⟨CStarMatrix.reindexₐ ℂ ℂ (finSuccEquiv n) a,?_⟩
      change _=twistAmbient n (f : C(Interval,TensorMat (n+1) n)) leftEndpoint
      rw [twist_left,←ha,reindex_left]
    · obtain ⟨a,ha⟩ := f.property.2
      change rightAmplification (n+1) n a=(f : C(Interval,TensorMat (n+1) n)) rightEndpoint at ha
      refine ⟨a,?_⟩
      change _=twistAmbient n (f : C(Interval,TensorMat (n+1) n)) rightEndpoint
      rw [twist_right,←ha,reindex_right])
end DimensionDropModel
namespace DimensionDropRelations.Witness
open JiangSuConstruction

variable {B : Type} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
variable {n : ℕ} {p : Fin n} (w : Witness (B := B) p)
 def dimensionDropHom : DimensionDrop (n+1) n →⋆ₐ[ℂ] B :=
  w.generatedHom.comp (DimensionDropModel.concreteToGenerated p)
end DimensionDropRelations.Witness

end


noncomputable section
namespace DirectComparison
open Pureness CurrentMain Filter Topology CompletelyPositiveOperations JiangSuConstruction
open scoped ComplexOrder ENNReal CStarAlgebra

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable [Nontrivial A] [Nonempty (TracialState A)] [TopologicalSpace.SeparableSpace A]
variable (U : Ultrafilter ℕ)
local instance (n : ℕ) : Semiring (DimensionDrop (n+1) n) :=
  (inferInstance : CStarAlgebra (DimensionDrop (n+1) n)).toSemiring

 theorem comparison_dimension_drop_hom (hfree : (U : Filter ℕ)≤atTop)
    (hnuc : IsNuclear.{0,0} A) (hsimple : TopologicallySimple A) (hinf : ¬FiniteDimensional ℂ A)
    (hcmp : StrictComparison A) (n : ℕ) (hn : 0<n) :
    Nonempty (DimensionDrop (n+1) n →⋆ₐ[ℂ] unitalNormCentralizer (A := A) U) := by
  obtain ⟨φ,s,hφn,hφrel,_hsn,hse,hsF⟩ :=
    comparison_dimension_drop_relations U hfree hnuc hsimple hinf hcmp n hn
  let w : DimensionDropRelations.Witness (B := unitalNormCentralizer (A := A) U) (⟨0,hn⟩ : Fin n) :=
    ⟨φ,hφn,hφrel,s,hse,hsF⟩
  exact ⟨w.dimensionDropHom⟩

end DirectComparison

end


noncomputable section
namespace JiangSuConstruction
local instance (priority := 2000) dropStarRing (p q : ℕ) : StarRing (DimensionDrop p q) :=
  CStarAlgebra.toStarRing
local instance (p q : ℕ) : Semiring (DimensionDrop p q) :=
  (inferInstance : CStarAlgebra (DimensionDrop p q)).toSemiring

local instance (priority := 2000) dropStar (p q : ℕ) : Star (DimensionDrop p q) :=
  (CStarAlgebra.toStarRing (A := DimensionDrop p q)).toStarMul.toInvolutiveStar.toStar

 theorem consecutive_multiplicities {p q : ℕ} (hp : 0<p) (hq : 0<q)
    (hco : p.Coprime q) : ∃ (n : ℕ),0<n ∧ ∃ m : Multiplicities p q,
      p*m.k=n+1 ∧ q*m.l=n := by
   let r := Nat.chineseRemainder hco 0 1
   let N := (r:ℕ)+16*p*q
   have hN : 16*p*q≤N := by dsimp [N]; omega
   have hNp : p∣N := by
     apply Nat.modEq_zero_iff_dvd.mp
     exact r.2.1.add ((show p∣16*p*q by use 16*q; ring).modEq_zero_nat)
   have hNq : N ≡ 1 [MOD q] := by
     have hh := r.2.2.add ((show q∣16*p*q by use 16*p; ring).modEq_zero_nat)
     simpa only [Nat.add_zero] using hh
   have hNpos : 1≤N := by have hh := Nat.mul_pos hp hq; nlinarith
   have hd : q∣N-1 := by
     apply Nat.modEq_zero_iff_dvd.mp
     simpa only [Nat.sub_self] using hNq.sub_right hNpos (by omega : 1≤1)
   obtain ⟨k,hkN⟩ := hNp
   obtain ⟨l,hlN⟩ := hd
   have he : p*k=q*l+1 := by omega
   have hk : 8*q≤k := by nlinarith
   have hl : 8*p≤l := by nlinarith
   let m := multiplicitiesOfLarge hp hq k l hk hl
   refine ⟨q*l,by have h := Nat.mul_pos hq (show 0<l by omega); exact h,m,he,rfl⟩

 theorem prime_drop_into_consecutive {p q : ℕ} (hp : 0<p) (hq : 0<q)
    (hco : p.Coprime q) : ∃ n : ℕ,0<n ∧
      Nonempty (DimensionDrop p q →⋆ₐ[ℂ] DimensionDrop (n+1) n) := by
   obtain ⟨n,hn,m,hle,hri⟩ := consecutive_multiplicities hp hq hco
   refine ⟨n,hn,?_⟩
   have h := concreteStep m
   rw [hle,hri] at h
   exact ⟨h⟩
end JiangSuConstruction

namespace DirectComparison
open Pureness CurrentMain Filter Topology CompletelyPositiveOperations JiangSuConstruction
open scoped ComplexOrder ENNReal CStarAlgebra

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable [Nontrivial A] [Nonempty (TracialState A)] [TopologicalSpace.SeparableSpace A]
variable (U : Ultrafilter ℕ)
local instance (p q : ℕ) : Semiring (DimensionDrop p q) :=
  (inferInstance : CStarAlgebra (DimensionDrop p q)).toSemiring

 theorem comparison_prime_drop_hom (hfree : (U : Filter ℕ)≤atTop)
    (hnuc : IsNuclear.{0,0} A) (hsimple : TopologicallySimple A) (hinf : ¬FiniteDimensional ℂ A)
    (hcmp : StrictComparison A) (p q : ℕ) (hp : 0<p) (hq : 0<q) (hco : p.Coprime q) :
    Nonempty (DimensionDrop p q →⋆ₐ[ℂ] unitalNormCentralizer (A := A) U) := by
  obtain ⟨n,hn,⟨ψ⟩⟩ := prime_drop_into_consecutive hp hq hco
  obtain ⟨φ⟩ := comparison_dimension_drop_hom U hfree hnuc hsimple hinf hcmp n hn
  exact ⟨φ.comp ψ⟩
end DirectComparison

end

end OAI
