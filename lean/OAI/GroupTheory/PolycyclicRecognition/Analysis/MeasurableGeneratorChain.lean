import OAI.GroupTheory.PolycyclicRecognition.Algebra.MeasurableGeneratorPrefixes

namespace OAI

/-! # Fixed-length measurable chains from the bounded template selectors -/

noncomputable section
namespace PolycyclicRecognition

/-- Padding uses a fixed zero letter. The selected letter pattern is
independent of the sampled endpoint, and every prefix is measurable. -/
theorem exists_measurable_generator_chain
    {A I L G : Type*} [MeasurableSpace A] [MeasurableSpace G]
    [AddCommMonoid L] [Module ℝ L] [Group G] [MeasurableMul₂ G]
    (X : I → L) (Exp : L → G) (hzero : Exp 0 = 1)
    (hf : ∀ i, Measurable (fun t : ℝ => Exp (t • X i)))
    (i₀ : I) (word : List (I × (A → ℝ)))
    (hw : ∀ z ∈ word, Measurable z.2)
    {N : ℕ} (hlen : word.length ≤ N) {C : ℝ} (hC : 0 ≤ C)
    (hamp : ∀ a, ∀ z ∈ word, |z.2 a| ≤ C)
    (base : A → G) (hbase : Measurable base) :
    ∃ (mode : Fin N → I) (coeff : A → Fin N → ℝ)
      (vertex : A → Fin (N + 1) → G),
      (∀ j, Measurable (fun a => coeff a j)) ∧
      (∀ j, Measurable (fun a => vertex a j)) ∧
      (∀ a j, |coeff a j| ≤ C) ∧
      (∀ a, vertex a 0 = base a) ∧
      (∀ a, vertex a (Fin.last N) = base a *
        generatorGroupWord X Exp (word.map (fun z => (z.1, z.2 a)))) ∧
      (∀ a j, vertex a j.succ = vertex a j.castSucc * Exp (coeff a j • X (mode j))) ∧
      (∀ a j, vertex a j = base a *
        generatorGroupWord X Exp ((word.map (fun z => (z.1, z.2 a))).take j.val)) := by
  classical
  let padded := word ++ List.replicate (N - word.length) (i₀, fun _ : A => (0 : ℝ))
  have hp : padded.length = N := by
    simp only [padded, List.length_append, List.length_replicate]
    omega
  have hpmeas : ∀ z ∈ padded, Measurable z.2 := by
    intro z hz
    rcases List.mem_append.mp hz with hz | hz
    · exact hw z hz
    · obtain rfl := List.eq_of_mem_replicate hz
      exact measurable_const
  have hpa : ∀ a, ∀ z ∈ padded, |z.2 a| ≤ C := by
    intro a z hz
    rcases List.mem_append.mp hz with hz | hz
    · exact hamp a z hz
    · obtain rfl := List.eq_of_mem_replicate hz
      simpa only [abs_zero] using hC
  let step (j : Fin N) := padded[j.val]'(by rw [hp]; exact j.isLt)
  let coeff (a : A) (j : Fin N) := (step j).2 a
  let vertex (a : A) (j : Fin (N + 1)) := base a *
    generatorGroupWord X Exp ((padded.map (fun z => (z.1, z.2 a))).take j.val)
  have hprefix (a : A) (j : ℕ) :
      generatorGroupWord X Exp ((padded.map (fun z => (z.1, z.2 a))).take j) =
        generatorGroupWord X Exp ((word.map (fun z => (z.1, z.2 a))).take j) := by
    simpa only [padded, List.map_append, List.map_replicate] using
      generatorGroupWord_zero_padding X Exp hzero i₀
        (word.map (fun z => (z.1, z.2 a))) (N - word.length) j
  refine ⟨fun j => (step j).1, coeff, vertex, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j
    exact hpmeas _ (List.getElem_mem _)
  · intro j
    apply hbase.mul
    have he (a : A) : generatorGroupWord X Exp
        ((padded.map (fun z => (z.1, z.2 a))).take j.val) =
        ((padded.take j.val).map (fun z => Exp (z.2 a • X z.1))).prod := by
      simp only [← List.map_take, generatorGroupWord, List.map_map, Function.comp_def]
    simp_rw [he]
    exact measurable_fixed_generator_word (fun i t => Exp (t • X i)) hf
      (padded.take j.val) (fun z hz => hpmeas z (List.mem_of_mem_take hz))
  · intro a j
    exact hpa a _ (List.getElem_mem _)
  · intro a
    simp only [vertex, Fin.val_zero, List.take_zero, generatorGroupWord_nil, mul_one]
  · intro a
    change base a * generatorGroupWord X Exp
      ((padded.map (fun z => (z.1, z.2 a))).take N) = _
    rw [hprefix]
    rw [List.take_of_length_le (by simpa only [List.length_map] using hlen)]
  · intro a j
    change base a * generatorGroupWord X Exp
      ((padded.map (fun z => (z.1, z.2 a))).take (j.val + 1)) =
      (base a * generatorGroupWord X Exp
        ((padded.map (fun z => (z.1, z.2 a))).take j.val)) * _
    have hs := generatorGroupWord_take_succ X Exp
      (padded.map (fun z => (z.1, z.2 a))) j.val (by
        simpa only [List.length_map, hp] using j.isLt)
    rw [hs, mul_assoc]
    simp only [List.getElem_map, coeff, step]
  · intro a j
    exact congrArg (base a * ·) (hprefix a j.val)

end PolycyclicRecognition

end

end OAI
