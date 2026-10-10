import OAI.NumberTheory.DukePrimeDegree.Geometry.OrderedEliminationChain

namespace OAI

/-!
# Actual charts for the full upper unipotent group

The complete Gaussian elimination chain supplies an open group chart.
Left translation and the discrete lattice covering then give local
product charts in the arithmetic quotient around every point. Every
time factor is an actual ordered product of positive-root matrices.
-/

noncomputable section
open Matrix Set
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

def completeRootChain (n : ℕ) : EliminationChain (∅ : Finset (Fin n × Fin n)) ∅ :=
  (exists_complete_elimination_chain n).choose

lemma completeRootChain_final (n : ℕ) : (completeRootChain n).finalEntries = allPositiveRoots n :=
  (exists_complete_elimination_chain n).choose_spec

abbrev UpperRootTransverse (n : ℕ) := (completeRootChain n).FinalSlice
abbrev UpperRootTime (n : ℕ) := (completeRootChain n).Time

def emptyEliminationHomeomorph (n : ℕ) :
    EliminationSlice (∅ : Finset (Fin n × Fin n)) ∅ ≃ₜ G n where
  toFun := Subtype.val
  invFun g := ⟨g, by constructor <;> simp [ZeroPattern, NonzeroPivots]⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := rfl
  continuous_toFun := continuous_subtype_val
  continuous_invFun := continuous_id.subtype_mk _

def upperRootParam (n : ℕ) (z : UpperRootTransverse n × UpperRootTime n) : G n :=
  ((completeRootChain n).param z).val

theorem upperRootParam_isOpenEmbedding (n : ℕ) :
    Topology.IsOpenEmbedding (upperRootParam n) :=
  (emptyEliminationHomeomorph n).isOpenEmbedding.comp
    (completeRootChain n).param_isOpenEmbedding

lemma upperRootParam_eq_mul (n : ℕ) (s : UpperRootTransverse n) (t : UpperRootTime n) :
    upperRootParam n (s, t) = s.val * (completeRootChain n).word t :=
  (completeRootChain n).param_val s t

lemma upperRootWord_mem (n : ℕ) (t : UpperRootTime n) :
    (completeRootChain n).word t ∈ positiveRootGeneratedGroup (allPositiveRoots n) := by
  apply (completeRootChain n).word_mem_generated
  rw [completeRootChain_final]

def upperRootIdentity (n : ℕ) : UpperRootTransverse n :=
  ⟨1, by
    constructor
    · rw [completeRootChain_final]
      intro p hp
      have hp' := (Finset.mem_filter.mp hp).2
      change (1 : Matrix (Fin n) (Fin n) ℝ) p.1 p.2 = 0
      simp [ne_of_lt hp']
    · intro r _
      change (1 : Matrix (Fin n) (Fin n) ℝ) r r ≠ 0
      simp⟩

@[simp] lemma upperRootParam_zero (n : ℕ) :
    upperRootParam n (upperRootIdentity n, (completeRootChain n).zeroTime) = 1 :=
  (completeRootChain n).param_zeroTime _

def upperRootQuotientParam (n : ℕ) (g : G n)
    (z : UpperRootTransverse n × UpperRootTime n) : X n :=
  Quotient.mk _ (g * upperRootParam n z)

theorem upperRootQuotientParam_localHomeomorph (n : ℕ) (g : G n) :
    IsLocalHomeomorph (upperRootQuotientParam n g) :=
  (quotient_covering n).isLocalHomeomorph.comp
    ((Homeomorph.mulLeft g).isLocalHomeomorph.comp
      (upperRootParam_isOpenEmbedding n).isLocalHomeomorph)

lemma upperRootQuotientParam_eq_action (n : ℕ) (g : G n)
    (s : UpperRootTransverse n) (t : UpperRootTime n) :
    upperRootQuotientParam n g (s, t) =
      rightAction (Quotient.mk _ (g * s.val)) ((completeRootChain n).word t) := by
  change Quotient.mk _ (g * upperRootParam n (s, t)) =
    Quotient.mk _ ((g * s.val) * (completeRootChain n).word t)
  rw [upperRootParam_eq_mul, mul_assoc]

structure UpperRootBox (n : ℕ) (g : G n) where
  transverse : Set (UpperRootTransverse n)
  time : Set (UpperRootTime n)
  transverse_open : IsOpen transverse
  time_open : IsOpen time
  embedding : Topology.IsOpenEmbedding
    ((transverse ×ˢ time).domRestrict (upperRootQuotientParam n g))

theorem exists_upperRootBox_at_coordinates (n : ℕ) (g : G n)
    (z : UpperRootTransverse n × UpperRootTime n) :
    ∃ B : UpperRootBox n g, z ∈ B.transverse ×ˢ B.time := by
  obtain ⟨U, hUz, hU⟩ := isLocalHomeomorph_iff_isOpenEmbedding_restrict.mp
    (upperRootQuotientParam_localHomeomorph n g) z
  obtain ⟨V, W, hVo, hVz, hWo, hWz, hsub⟩ := mem_nhds_prod_iff'.mp hUz
  have he := hU.comp (Topology.IsOpenEmbedding.inclusion hsub
    ((hVo.prod hWo).preimage continuous_subtype_val))
  exact ⟨⟨V, W, hVo, hWo, he⟩, hVz, hWz⟩

theorem exists_upperRootBox_at (n : ℕ) (x : X n) :
    ∃ (g : G n) (B : UpperRootBox n g),
      x ∈ Set.range ((B.transverse ×ˢ B.time).domRestrict (upperRootQuotientParam n g)) := by
  induction x using Quotient.inductionOn with
  | h g =>
    let z := (upperRootIdentity n, (completeRootChain n).zeroTime)
    obtain ⟨B, hB⟩ := exists_upperRootBox_at_coordinates n g z
    refine ⟨g, B, ⟨⟨z, hB⟩, ?_⟩⟩
    change Quotient.mk _ (g * upperRootParam n z) = _
    rw [upperRootParam_zero, mul_one]

end DukePrimeDegree

end

end OAI
