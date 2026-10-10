import OAI.GroupTheory.PolycyclicRecognition.Algebra.AdmissibleGeneratorWords

namespace OAI

/-! # Concatenating and reversing admissible generator paths -/

noncomputable section

namespace PolycyclicRecognition

open Set

variable {G V I : Type*} [Group G] [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem generatorWord_endpoint_mem
    (U : Set G) (Exp : V → G) (X : I → V) (w : List (I × ℝ))
    {g : G} (hg : g ∈ generatorWordBase U Exp X w) :
    g * generatorGroupWord X Exp w ∈ U := by
  induction w generalizing g with
  | nil => simpa [generatorWordBase] using hg
  | cons p w ih =>
    rcases p with ⟨i, t⟩
    simpa [generatorGroupWord_cons, mul_assoc] using ih hg.2

theorem mem_generatorWordBase_append
    (U : Set G) (Exp : V → G) (hExp0 : Exp 0 = 1) (X : I → V)
    (w z : List (I × ℝ)) (g : G) :
    g ∈ generatorWordBase U Exp X (w ++ z) ↔
      g ∈ generatorWordBase U Exp X w ∧
        g * generatorGroupWord X Exp w ∈ generatorWordBase U Exp X z := by
  induction w generalizing g with
  | nil =>
    simp only [List.nil_append, generatorWordBase, generatorGroupWord_nil, mul_one]
    exact ⟨fun h => ⟨generatorWordBase_subset U Exp hExp0 X z h, h⟩, And.right⟩
  | cons p w ih =>
    rcases p with ⟨i, t⟩
    simp only [List.cons_append, generatorWordBase, mem_inter_iff, mem_preimage,
      ih, generatorGroupWord_cons, mul_assoc]
    tauto

theorem generatorGroupWord_inverse_of_exp_neg
    (Exp : V → G) (hneg : ∀ v, Exp (-v) = (Exp v)⁻¹)
    (X : I → V) (w : List (I × ℝ)) :
    generatorGroupWord X Exp (inverseGeneratorWord w) = (generatorGroupWord X Exp w)⁻¹ := by
  induction w with
  | nil => simp [inverseGeneratorWord]
  | cons p w ih =>
    rcases p with ⟨i, t⟩
    have he : inverseGeneratorWord ((i, t) :: w) = inverseGeneratorWord w ++ [(i, -t)] := by
      simp only [inverseGeneratorWord, List.reverse_cons, List.map_append, List.map_cons,
        List.map_nil]
    rw [he]
    have ha : generatorGroupWord X Exp (inverseGeneratorWord w ++ [(i, -t)]) =
        generatorGroupWord X Exp (inverseGeneratorWord w) * Exp ((-t) • X i) := by
      simp [generatorGroupWord, List.map_append, List.prod_append]
    rw [ha, ih, generatorGroupWord_cons, mul_inv_rev]
    simp only [neg_smul, hneg]

theorem reverse_flowLineBase
    (U : Set G) (Exp : V → G)
    (hadd : ∀ v (s t : ℝ), Exp ((s + t) • v) = Exp (s • v) * Exp (t • v))
    (v : V) {g : G} (hg : g ∈ flowLineBase U Exp v 1) :
    g * Exp v ∈ flowLineBase U Exp (-v) 1 := by
  intro r hr
  have hmem := hg (1 - r) (show 1 - r ∈ Icc (0 : ℝ) 1 by constructor <;> linarith [hr.1, hr.2])
  have he : (g * Exp v) * Exp (r • -v) = g * Exp ((1 - r) • v) := by
    rw [mul_assoc]
    congr 1
    have hh := hadd v 1 (-r)
    simpa only [one_smul, sub_eq_add_neg, smul_neg, neg_smul] using hh.symm
  rwa [he]

theorem mem_generatorWordBase_inverse
    (U : Set G) (Exp : V → G) (hExp0 : Exp 0 = 1)
    (hneg : ∀ v, Exp (-v) = (Exp v)⁻¹)
    (hadd : ∀ v (s t : ℝ), Exp ((s + t) • v) = Exp (s • v) * Exp (t • v))
    (X : I → V) (w : List (I × ℝ)) {g : G}
    (hg : g ∈ generatorWordBase U Exp X w) :
    g * generatorGroupWord X Exp w ∈
      generatorWordBase U Exp X (inverseGeneratorWord w) := by
  induction w generalizing g with
  | nil => simpa [inverseGeneratorWord, generatorWordBase] using hg
  | cons p w ih =>
    rcases p with ⟨i, t⟩
    have hcons : inverseGeneratorWord ((i, t) :: w) = inverseGeneratorWord w ++ [(i, -t)] := by
      simp only [inverseGeneratorWord, List.reverse_cons, List.map_append, List.map_cons,
        List.map_nil]
    rw [hcons]
    rw [mem_generatorWordBase_append U Exp hExp0]
    constructor
    · simpa [generatorGroupWord_cons, mul_assoc] using ih hg.2
    · have he : (g * generatorGroupWord X Exp ((i, t) :: w)) *
          generatorGroupWord X Exp (inverseGeneratorWord w) = g * Exp (t • X i) := by
        rw [generatorGroupWord_cons, generatorGroupWord_inverse_of_exp_neg Exp hneg X w]
        group
      rw [he]
      constructor
      · simpa only [neg_smul] using reverse_flowLineBase U Exp hadd (t • X i) hg.1
      · change (g * Exp (t • X i)) * Exp ((-t) • X i) ∈ U
        have hgU := generatorWordBase_subset U Exp hExp0 X ((i, t) :: w) hg
        simpa [neg_smul, hneg] using hgU

end PolycyclicRecognition

end

end OAI
