import Mathlib
import OAI.Analysis.FreeWords.CutAlgebra
import OAI.Analysis.FreeWords.FreeWordCore
import OAI.Analysis.FreeWords.TupleCombinatorics

namespace OAI

noncomputable section

namespace KKFreeWords

open scoped BigOperators ComplexOrder InnerProductSpace

noncomputable section

variable {A ι : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {τ : A →ₚ[ℂ] ℂ} {S : ι → StarSubalgebra ℂ A}

theorem letterOp_product {κ : Type*} (f : κ → A)
    (hf : ∀ i, Commute (τ.gnsStarAlgHom (f i)) (reducedSpace τ S).starProjection)
    (w : List κ) (hw : w ≠ []) :
    (w.map (fun i => letterOp τ S (f i))).prod =
      letterOp τ S ((w.map f).prod) := by
  let V := reducedSpace τ S
  let g : κ → reductionAlgebra τ V := fun i => ⟨f i, (mem_reductionAlgebra V _).mpr (hf i)⟩
  have hn : w.map g ≠ [] := by simpa using hw
  calc
    _ = ((w.map g).map (compressedHom V)).prod := by
      simp only [List.map_map]
      rfl
    _ = compressedHom V ((w.map g).prod) := List.prod_hom_nonempty _ hn
    _ = _ := by
      change τ.gnsStarAlgHom (((w.map g).prod : reductionAlgebra τ V) : A) *
        V.starProjection = _
      have h : (((w.map g).prod : reductionAlgebra τ V) : A) = (w.map f).prod := by
        change (reductionAlgebra τ V).subtype ((w.map g).prod) = _
        rw [map_list_prod, List.map_map]
        rfl
      rw [h]
      rfl

namespace FreePartitions

variable {r d : ℕ} (P : FreePartitions τ r d)

def create (j : Fin r) (a : Fin d) := creationOp τ P.S j (P.centered j a)

def annihilate (j : Fin r) (a : Fin d) := star (P.create j a)

def preserve (j : Fin r) (a : Fin d) := preservationOp τ P.S j (P.centered j a)

def letter (j : Fin r) (a : Fin d) := letterOp τ P.S (P.centered j a)

theorem letter_eq (hτ : τ 1 = 1) (j : Fin r) (a : Fin d) :
    P.letter j a = P.create j a + P.annihilate j a + P.preserve j a :=
  letterOp_decomposition P.free hτ ⟨P.centered_mem j a, P.centered_trace hτ j a⟩
    (P.centered_star j a)

theorem cutCompatible (hτ : τ 1 = 1) (a : Fin r → Fin d) {i j : Fin r} (hij : i ≠ j) :
    CutCompatible (fun j => P.create j (a j)) (fun j => P.annihilate j (a j))
      (fun j => P.preserve j (a j)) i j := by
  have hi := And.intro (P.centered_mem i (a i)) (P.centered_trace hτ i (a i))
  have hj := And.intro (P.centered_mem j (a j)) (P.centered_trace hτ j (a j))
  exact ⟨annihilation_mul_creation_zero P.free hτ hij hi hj,
    preservation_mul_creation_zero P.free hτ hij hj,
    annihilation_mul_preservation_zero P.free hτ hij hi,
    preservation_mul_preservation_zero P.free hτ hij _ _⟩

theorem product_letter_eq_cuts (hτ : τ 1 = 1) (a : Fin r → Fin d) :
    (List.ofFn (fun j => P.letter j (a j))).prod =
      (∑ q : Fin (r+1), noPresCut (fun j => P.create j (a j))
        (fun j => P.annihilate j (a j)) q) +
      ∑ j : Fin r, presCut (fun j => P.create j (a j))
        (fun j => P.annihilate j (a j)) (fun j => P.preserve j (a j)) j := by
  have hchain : (List.ofFn (id : Fin r → Fin r)).IsChain
      (CutCompatible (fun j => P.create j (a j)) (fun j => P.annihilate j (a j))
        (fun j => P.preserve j (a j))) := by
    apply List.Pairwise.isChain
    apply List.Pairwise.imp (fun hij => P.cutCompatible hτ a hij)
    exact List.nodup_ofFn.mpr Function.injective_id
  rw [← cutSum_eq_cuts, ← product_eq_cutSum _ _ _ _ hchain]
  simp only [List.map_ofFn, id_eq, Function.comp_def, P.letter_eq hτ]

def centeredSum (W : Multiset (Fin d)) : A :=
  ∑ a : Fin r → Fin d, if tupleLabels a = W then
    (List.ofFn (fun j => P.centered j (a j))).prod else 0

theorem centeredSum_mem_reduction (hτ : τ 1 = 1) (W : Multiset (Fin d)) :
    P.centeredSum W ∈ reductionAlgebra τ (reducedSpace τ P.S) := by
  apply sum_mem
  intro a ha
  split_ifs
  · apply list_prod_mem
    intro x hx
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hx
    exact (mem_reductionAlgebra _ _).mpr
      (copy_commutes_reducedProjection hτ (P.centered_mem j (a j)))
  · exact zero_mem _

theorem norm_centeredSum (hτ : FaithfulTracial τ) (hr : r ≠ 0) (W : Multiset (Fin d)) :
    ‖P.centeredSum W‖ =
      ‖∑ a : Fin r → Fin d, if tupleLabels a = W then
        (List.ofFn (fun j => P.letter j (a j))).prod else 0‖ := by
  rw [← norm_compressed (reducedSpace τ P.S) vacuum_mem_reducedSpace hτ.2.2
    (P.centeredSum W) ((mem_reductionAlgebra _ _).mp (P.centeredSum_mem_reduction hτ.1 W))]
  congr 1
  simp only [centeredSum, map_sum, Finset.sum_mul, apply_ite, map_zero, ite_mul, zero_mul]
  apply Finset.sum_congr rfl
  intro a ha
  split_ifs
  · have h := letterOp_product (fun j => P.centered j (a j))
      (fun j => copy_commutes_reducedProjection hτ.1 (P.centered_mem j (a j)))
      (List.ofFn (id : Fin r → Fin r)) (by simpa using hr)
    simpa only [List.map_ofFn, id_eq, Function.comp_def, letterOp, letter] using h.symm
  · rfl

end FreePartitions

end

end KKFreeWords
end

end OAI
