import OAI.NumberTheory.Ostmann.Supply.LocalBlock
import OAI.NumberTheory.Ostmann.Supply.UniformProjection

namespace OAI

noncomputable section
namespace Ostmann.Supply
open scoped BigOperators ComplexConjugate
variable {p : ℕ} [NeZero p]
local notation "H" => EuclideanSpace ℂ (ZMod p)

theorem sum_uniformVector_all (S : Finset (ZMod p)) (hS : S.Nonempty) :
    ∑ x, uniformVector S x = 1 := by
  simpa only [uniformVector_apply, Finset.sum_ite_mem,Finset.univ_inter,Finset.inter_self] using sum_uniformVector S hS

theorem sum_centered_all (S : Finset (ZMod p)) (f : centeredSpace S) :
    ∑ x, f.1 x = 0 := by
  calc
    _ = ∑ x ∈ S, f.1 x := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro x hx hxs
      exact f.2.1 x hxs
    _ = 0 := f.2.2

theorem convolution_one_apply (f : H) :
    convolutionOperator (fun _ : ZMod p => (1:ℂ)) f = (∑ y, f y) • oneVector := by
  ext x
  simp [convolutionOperator_matrix]

theorem centeredProjection_oneVector (S : Finset (ZMod p)) :
    centeredProjection S oneVector = 0 :=
  centeredProjection_eq_zero_of_constant S oneVector 1 (fun _ _ => rfl)

theorem uniformVector_oneVector (S : Finset (ZMod p)) (hS : S.Nonempty) :
    inner ℂ (uniformVector S) oneVector = 1 := by
  have hs : (S.card:ℂ) ≠ 0 := by exact_mod_cast Finset.card_ne_zero.mpr hS
  simp [uniformVector_inner,hs]

theorem localBlock_one_fst (S T : Finset (ZMod p)) (hS : S.Nonempty) (hT : T.Nonempty)
    (x : LocalCoordinates T) :
    (localBlock S T (convolutionOperator (fun _ : ZMod p => (1:ℂ))) x).fst = x.fst := by
  rw [localBlock_fst,convolution_one_apply,convolution_one_apply,
    sum_uniformVector_all T hT,sum_centered_all,one_smul,zero_smul,
    inner_zero_right,uniformVector_oneVector S hS,mul_one,add_zero]

theorem localBlock_one_snd (S T : Finset (ZMod p)) (hT : T.Nonempty)
    (x : LocalCoordinates T) :
    (localBlock S T (convolutionOperator (fun _ : ZMod p => (1:ℂ))) x).snd = 0 := by
  apply Subtype.ext
  rw [localBlock_snd,convolution_one_apply,convolution_one_apply,
    sum_uniformVector_all T hT,sum_centered_all,one_smul,zero_smul,
    centeredProjection_oneVector,map_zero,smul_zero,zero_add]
  rfl

end Ostmann.Supply

end

end OAI
