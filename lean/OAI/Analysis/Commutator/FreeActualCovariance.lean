import Mathlib
import OAI.Analysis.Commutator.FreeActionBlock
import OAI.Analysis.Commutator.FreeActionUnitary
import OAI.Analysis.Commutator.FreeCovariance
import OAI.Analysis.Commutator.FreeLetterIntertwine
import OAI.Analysis.Commutator.FreeSymmetry16

namespace OAI

noncomputable section

open scoped ComplexOrder InnerProductSpace TensorProduct

open UniformSpace

namespace Kadison.FreeBlocks

open FreeWordTensor FreeMoments FreeWordAction

variable {A D : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

variable (t : FaithfulState A) (ht : ∀ a b : A, t.functional (a*b)=t.functional (b*a))

variable (f : D →⋆ₐ[ℂ] A) (hf : Function.Injective f)

variable {ι : Type*} (S : ι → StarSubalgebra ℂ A) (i j : ι) (hS : S i=f.range)

variable (hfree : Free S t.functional.toLinearMap)
  (hgen : ∀ a : A, t.functional.gnsStarAlgHom a ∈
    Set.centralizer (Set.centralizer (generatedOperators t S : Set _)))

abbrev innerRepresentation : unitary D →* (t.functional.GNS ≃ₗᵢ[ℂ] t.functional.GNS) :=
  representation t S hfree hgen (innerFamily f i) (innerFamily_mem f S i hS)
    (innerFamily_trace t ht f i) (innerFamily_one f i) (innerFamily_mul f i)

omit [PartialOrder D] [StarOrderedRing D] in
lemma innerRepresentation_continuous (x : t.functional.GNS) :
    Continuous fun u => innerRepresentation t ht f S i hS hfree hgen u x :=
  representation_continuous t S hfree hgen (innerFamily f i) (innerFamily_mem f S i hS)
    (innerFamily_trace t ht f i) (innerFamily_one f i) (innerFamily_mul f i)
    (innerFamily_continuous f i) x

private abbrev sourceConjugation (u : unitary D) (n : ℕ) :
    sourceLevel t f hf S j n →L[ℂ] sourceLevel t f hf S j n :=
  HilbertTensor.map
    (PreHilbert.wordMap (factorFull t f hf) (factorZero t f hf)
      (TracialGNS.conjugation (factorTrace t f hf) (factorTrace_tracial t f hf ht) u)
      (centeredIsometry (TracialGNS.vacuum (factorTrace t f hf))
        (TracialGNS.conjugation (factorTrace t f hf) (factorTrace_tracial t f hf ht) u)
        (TracialGNS.conjugation_vacuum (factorTrace t f hf)
          (factorTrace_tracial t f hf ht) u)) n).toContinuousLinearMap
    (1 : multiplicityLevel t S j n →L[ℂ] multiplicityLevel t S j n)

lemma sumConjugation_levelWord (u : unitary D) (d : D) (n : ℕ)
    (x : BlockParams t S i j n) :
    sourceConjugation t ht f hf S j u n (levelWord t f hf S i j hS d n x) =
    levelWord t f hf S i j hS ((u:D)*d*star (u:D)) n
      (mapBlockD t S i j
        (letterIso t S (innerFamily f i u) (innerFamily_mem f S i hS u)
          (innerFamily_trace t ht f i u) i) n x) := by
  simp only [sourceConjugation, levelWord, HilbertTensor.map_pair,
    LinearIsometry.coe_toContinuousLinearMap, one_apply_eq_self,
    paramJ_mapBlockD,paramD_mapBlockD]
  apply congrArg (fun y : sourceScalar t f hf n =>
    HilbertTensor.pair y (paramJ t S n x : multiplicityLevel t S j n))
  have hw := PreHilbert.wordMap_word (factorFull t f hf) (factorZero t f hf)
    (TracialGNS.conjugation (factorTrace t f hf) (factorTrace_tracial t f hf ht) u)
    (centeredIsometry (TracialGNS.vacuum (factorTrace t f hf))
      (TracialGNS.conjugation (factorTrace t f hf) (factorTrace_tracial t f hf ht) u)
      (TracialGNS.conjugation_vacuum (factorTrace t f hf) (factorTrace_tracial t f hf ht) u))
    n (TracialGNS.algebraVector (factorTrace t f hf) d)
    (fun k => (letterGNSIso t f hf S i hS (paramD t S n x k : Completion (letterSpace t S i)) :
      TracialGNS.zeroSpace (factorTrace t f hf)))
  refine hw.trans ?_
  have hd := TracialGNS.conjugation_coe (factorTrace t f hf)
    (factorTrace_tracial t f hf ht) u d
  change TracialGNS.conjugation (factorTrace t f hf) (factorTrace_tracial t f hf ht) u
    (TracialGNS.algebraVector (factorTrace t f hf) d)=
      TracialGNS.algebraVector (factorTrace t f hf) ((u:D)*d*star (u:D)) at hd
  rw [hd]
  congr 1
  funext k
  exact (letterGNSIso_conjugation t f hf S i hS ht u (paramD t S n x k)).symm

variable (hij : i≠j)

lemma innerRepresentation_word (u : unitary D) (d : D) (n : ℕ)
    (x : BlockParams t S i j n) :
    innerRepresentation t ht f S i hS hfree hgen u
      (sourceLevelEmbedding t f hf S i j hS hfree hij n
        (levelWord t f hf S i j hS d n x)) =
    sourceLevelEmbedding t f hf S i j hS hfree hij n
      (levelWord t f hf S i j hS ((u:D)*d*star (u:D)) n
        (mapBlockD t S i j
          (letterIso t S (innerFamily f i u) (innerFamily_mem f S i hS u)
            (innerFamily_trace t ht f i u) i) n x)) := by
  rw [sourceLevelEmbedding_word,sourceLevelEmbedding_word]
  have hfd : f d∈S i := by rw [hS]; exact ⟨d,rfl⟩
  change action t S (innerFamily f i u) (innerFamily_mem f S i hS u)
      (innerFamily_trace t ht f i u) hfree hgen
      (t.functional.gnsStarAlgHom (f d)
        (TracialGNS.algebraVector t.functional (blockRead t S n (blockPure t S n x)))) = _
  rw [action_left_apply t S (innerFamily f i u) (innerFamily_mem f S i hS u)
    (innerFamily_trace t ht f i u) hfree hgen i (f d) hfd,
    action_blockRead_pure t S i j (innerFamily f i u) (innerFamily_mem f S i hS u)
      (innerFamily_trace t ht f i u) hfree hgen
      (fun a _ => innerFamily_other f i u hij.symm a) n x]
  congr 2
  simp only [innerFamily_self,map_mul]

lemma innerRepresentation_level (u : unitary D) (n : ℕ) :
    (innerRepresentation t ht f S i hS hfree hgen u).toLinearIsometry.toContinuousLinearMap.comp
      (sourceLevelEmbedding t f hf S i j hS hfree hij n).toContinuousLinearMap =
    (sourceLevelEmbedding t f hf S i j hS hfree hij n).toContinuousLinearMap.comp
      (sourceConjugation t ht f hf S j u n) := by
  apply sourceLevel_ext t f hf S i j hS
  intro d x
  change innerRepresentation t ht f S i hS hfree hgen u
      (sourceLevelEmbedding t f hf S i j hS hfree hij n
        (levelWord t f hf S i j hS d n x)) =
    sourceLevelEmbedding t f hf S i j hS hfree hij n
      (sourceConjugation t ht f hf S j u n (levelWord t f hf S i j hS d n x))
  exact (innerRepresentation_word t ht f hf S i j hS hfree hgen hij u d n x).trans
    (congrArg (sourceLevelEmbedding t f hf S i j hS hfree hij n)
      (sumConjugation_levelWord t ht f hf S i j hS u d n x).symm)

end Kadison.FreeBlocks

end

end OAI
