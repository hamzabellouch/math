import OAI.NumberTheory.Ostmann.Supply.CenteredProjection
import OAI.NumberTheory.Ostmann.Supply.FiniteConvolution

namespace OAI

noncomputable section
namespace Ostmann.Supply
open scoped BigOperators ComplexConjugate
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
local notation "H" => EuclideanSpace ℂ ι

abbrev LocalCoordinates (S : Finset ι) := WithLp 2 (ℂ × centeredSpace S)

def coordinateLift (S : Finset ι) : LocalCoordinates S →L[ℂ] H := by
  let a : ℂ →L[ℂ] H := ContinuousLinearMap.toSpanSingleton ℂ (uniformVector S)
  let b : LocalCoordinates S →L[ℂ] ℂ := WithLp.fstL 2 ℂ ℂ (centeredSpace S)
  let c : LocalCoordinates S →L[ℂ] centeredSpace S := WithLp.sndL 2 ℂ ℂ (centeredSpace S)
  exact a.comp b + (centeredSpace S).subtypeL.comp c

def coordinateExtract (S : Finset ι) : H →L[ℂ] LocalCoordinates S :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ ℂ (centeredSpace S)).symm.toContinuousLinearMap.comp
    ((innerSL ℂ (uniformVector S)).prod (centeredSpace S).orthogonalProjectionOnto)

def localBlock (S T : Finset ι) (K : H →L[ℂ] H) :
    LocalCoordinates T →L[ℂ] LocalCoordinates S :=
  coordinateExtract S ∘L K ∘L coordinateLift T

@[simp] theorem coordinateLift_apply (S : Finset ι) (x : LocalCoordinates S) :
    coordinateLift S x = x.fst • uniformVector S + (x.snd : H) := rfl

@[simp] theorem coordinateExtract_fst (S : Finset ι) (x : H) :
    (coordinateExtract S x).fst = inner ℂ (uniformVector S) x := rfl

@[simp] theorem coordinateExtract_snd (S : Finset ι) (x : H) :
    ((coordinateExtract S x).snd : H) = centeredProjection S x := rfl

@[simp] theorem localBlock_fst (S T : Finset ι) (K : H →L[ℂ] H)
    (x : LocalCoordinates T) :
    (localBlock S T K x).fst =
      x.fst * inner ℂ (uniformVector S) (K (uniformVector T)) +
      inner ℂ (uniformVector S) (K (x.snd : H)) := by
    simp [localBlock, map_add, map_smul]

@[simp] theorem localBlock_snd (S T : Finset ι) (K : H →L[ℂ] H)
    (x : LocalCoordinates T) :
    ((localBlock S T K x).snd : H) =
      x.fst • centeredProjection S (K (uniformVector T)) +
      centeredProjection S (K (x.snd : H)) := by
  simp [localBlock, map_add, map_smul]

theorem localBlock_add (S T : Finset ι) (K L : H →L[ℂ] H) :
    localBlock S T (K+L) = localBlock S T K + localBlock S T L := by
  ext x
  simp [localBlock, map_add]

theorem localBlock_smul (S T : Finset ι) (c : ℂ) (K : H →L[ℂ] H) :
    localBlock S T (c • K) = c • localBlock S T K := by
  ext x
  simp [localBlock, map_smul]

end Ostmann.Supply

end

end OAI
