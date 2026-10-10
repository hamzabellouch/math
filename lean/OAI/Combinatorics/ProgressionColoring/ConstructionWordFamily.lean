import OAI.Combinatorics.ProgressionColoring.ConstructionModel
import OAI.Combinatorics.ProgressionColoring.MeshPartitions

namespace OAI

/-!
# A counted family covering the actual cyclic label words

The coordinate representatives of a cyclic progression are real affine
progressions modulo integers. Literal partition labels are integer-periodic,
so the actual label word belongs to the global family derived from affine
comparisons. The centered second-system start is shifted by `1/2`; its step
is not shifted. No independence of the cyclic coordinates is assumed.
-/

noncomputable section

namespace QuantitativeVanDerWaerden.ConstructionModel

open Parameters

variable {k : ℕ}

/-- Exact identification of the actual cyclic word with a word of the two
literal circle partitions, including their half-open boundary conventions. -/
theorem fullLabelWord_eq_partitionWord (s : Data k) (hk : 3 ≤ k)
    (ad : Group s × Group s) :
    fullLabelWord s hk ad =
      (uniformPartition (uniformCount k) (uniformCount_pos hk)).fullWord
        (adaptivePartition (mesh s hk)) (dimension k) k
        (xRep s.q (dimension k) ad.1)
        (xRep s.q (dimension k) ad.2)
        (fun i => yRep s.q (dimension k) (lambda k) ad.1 i + 1 / 2)
        (yRep s.q (dimension k) (lambda k) ad.2) := by
  funext j
  apply Prod.ext
  · funext i
    change UniformMesh.label (uniformCount k) (uniformCount_pos hk)
        (xRep s.q (dimension k) (ad.1 + (j.val : Group s) * ad.2) i) =
      (uniformPartition (uniformCount k) (uniformCount_pos hk)).label
        (xRep s.q (dimension k) ad.1 i +
          (j.val : ℝ) * xRep s.q (dimension k) ad.2 i)
    rw [← uniformPartition_label]
    obtain ⟨z, hz⟩ := xRep_ap_congr s.pos ad.1 ad.2 j.val i
    apply CirclePartition.label_eq_of_sub_int _ z
    simpa only [nsmul_eq_mul, sub_sub] using hz
  · funext i
    change (mesh s hk).meshLabel
        (yRep s.q (dimension k) (lambda k)
          (ad.1 + (j.val : Group s) * ad.2) i) =
      (adaptivePartition (mesh s hk)).label
        ((yRep s.q (dimension k) (lambda k) ad.1 i + 1 / 2) +
          (j.val : ℝ) * yRep s.q (dimension k) (lambda k) ad.2 i)
    rw [← adaptivePartition_label]
    obtain ⟨z, hz⟩ := yRep_ap_congr s.pos (lambda k) ad.1 ad.2 j.val i
    simp only [nsmul_eq_mul] at hz
    apply CirclePartition.label_eq_of_sub_int _ z
    linarith only [hz]

/-- A finite family covering every actual cyclic progression word. The
cardinality bound is proved from the two literal partitions, not supplied
as a hypothesis. The step may be zero. -/
theorem exists_fullLabelWord_family (s : Data k) (hk : 3 ≤ k) :
    ∃ words : Finset (Fin k → Label s hk),
      (∀ ad : Group s × Group s, fullLabelWord s hk ad ∈ words) ∧
      words.card ≤
        (16 * (3 * k ^ 2 *
          (uniformCount k + Fintype.card (mesh s hk).Label) + 1) ^ 6) ^
          (2 * dimension k) := by
  obtain ⟨words, hwords, hcard⟩ :=
    (uniformPartition (uniformCount k) (uniformCount_pos hk)).exists_fullWord_family
      (adaptivePartition (mesh s hk)) (dimension k) k
  refine ⟨words, ?_, ?_⟩
  · intro ad
    rw [fullLabelWord_eq_partitionWord]
    exact hwords _ _ _ _
  · simpa only [Fintype.card_fin] using hcard

/-- The same bound with the actual adaptive mesh cardinality substituted. -/
theorem exists_fullWordFamily (s : Data k) (hk : 3 ≤ k) :
    ∃ words : Finset (Fin k → Label s hk),
      words.card ≤
        (16 * (3 * k ^ 2 *
          (uniformCount k + 2 * scalarMeshSize k s.q) + 1) ^ 6) ^
          (2 * dimension k) ∧
      ∀ a d : Group s, fullLabelWord s hk (a, d) ∈ words := by
  obtain ⟨words, hwords, hcard⟩ := exists_fullLabelWord_family s hk
  refine ⟨words, ?_, fun a d => hwords (a, d)⟩
  simpa only [card_second_labels] using hcard

end QuantitativeVanDerWaerden.ConstructionModel

end

end OAI
