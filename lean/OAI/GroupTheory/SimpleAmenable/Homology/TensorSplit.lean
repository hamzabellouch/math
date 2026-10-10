import Mathlib
import OAI.GroupTheory.SimpleAmenable.Homology.ProductChains

namespace OAI

section

section
open CategoryTheory Limits MonoidalCategory HomologicalComplex
namespace TensorSplit
open FreeChains AugmentedSplit
attribute [local instance] preservesBinaryBiproducts_of_preservesBiproducts

variable {K L : ChainComplex A ℕ} (e : K ⟶ U) (s : U ⟶ K) (hs : s ≫ e=𝟙 U)
  (f : L ⟶ U) (t : U ⟶ L) (ht : t ≫ f=𝟙 U)
noncomputable def decompose :
    K ⊗ L ≅ ((red e ⊗ red f) ⊞ red e) ⊞ (red f ⊞ U) :=
  (AugmentedSplit.iso e s hs ⊗ᵢ AugmentedSplit.iso f t ht) ≪≫
    ChainTensor.rightDistrib _ _ _ ≪≫
    biprod.mapIso
      (ChainTensor.leftDistrib _ _ _ ≪≫ biprod.mapIso (Iso.refl _) (ρ_ _))
      (ChainTensor.leftDistrib _ _ _ ≪≫ biprod.mapIso (λ_ _) (λ_ _))

noncomputable def additiveIso [∀n,Module.Flat ℤ (K.X n)]
    (a b n : ℕ) (hn : 0<n) (hab : n<a+b)
    (hK : ∀i,i<a → IsZero ((red e).homology i))
    (hL : ∀i,i<b → IsZero ((red f).homology i))
    (hf : ∀i,i≤n → Module.Finite ℤ (L.homology i)) :
    (K⊗L).homology n ≅ K.homology n ⊞ L.homology n := by
  haveI : ∀i,Module.Flat ℤ ((red e).X i) := fun i => AugmentedSplit.flat e i
  have hf' : ∀i,i≤n → Module.Finite ℤ ((red f).homology i) := fun i hi => by
    have := hf i hi
    exact AugmentedSplit.finite f t ht i
  have hz : IsZero ((red e ⊗ red f).homology n) :=
    TensorProductHomology.isZero (red e) (red f) a b n hab hK hL hf'
  let H := homologyFunctor A c n
  exact H.mapIso (decompose e s hs f t ht) ≪≫ H.mapBiprod _ _ ≪≫
    biprod.mapIso (H.mapBiprod _ _ ≪≫ (isoZeroBiprod hz).symm)
      (H.mapBiprod _ _ ≪≫ (isoBiprodZero (AugmentedSplit.uni_isZero n (by omega))).symm) ≪≫
    biprod.mapIso (AugmentedSplit.homologyIso e s hs n (by omega)).symm
      (AugmentedSplit.homologyIso f t ht n (by omega)).symm
end TensorSplit

end

end

end OAI
