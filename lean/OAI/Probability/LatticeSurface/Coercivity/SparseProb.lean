import Mathlib

namespace OAI

noncomputable section

open Set MeasureTheory

open scoped BigOperators

namespace SparseWitness

attribute [local instance] Classical.propDecidable

lemma joint_witness_bound {Ω E I : Type*} [MeasurableSpace Ω]
    [Fintype I] [DecidableEq E] {T : I → Type*} [∀ i, Fintype (T i)]
    (μ : Measure Ω) [IsFiniteMeasure μ] (test : E → Set Ω)
    (edges : ∀ i, T i → Finset E) (q : ℝ) (_hq : 0 ≤ q)
    (joint : ∀ F : Finset E, μ.real {ω | ∀ e ∈ F, ω ∈ test e} ≤ q^F.card)
    (disj : ∀ i j, i ≠ j → ∀ s t, Disjoint (edges i s) (edges j t)) :
    μ.real {ω | ∀ i, ∃ t, ∀ e ∈ edges i t, ω ∈ test e} ≤
      ∏ i, ∑ t, q^(edges i t).card := by
  classical
  have hsub : {ω | ∀ i, ∃ t, ∀ e ∈ edges i t, ω ∈ test e} ⊆
      ⋃ t : ∀ i, T i, {ω | ∀ e ∈ Finset.univ.biUnion (fun i => edges i (t i)), ω ∈ test e} := by
    intro ω hω
    choose t ht using hω
    refine Set.mem_iUnion.mpr ⟨t,?_⟩
    intro e he
    obtain ⟨i,hi,he⟩ := Finset.mem_biUnion.mp he
    exact ht i e he
  calc
    _ ≤ μ.real (⋃ t : ∀ i, T i, {ω | ∀ e ∈ Finset.univ.biUnion (fun i => edges i (t i)), ω ∈ test e}) :=
      measureReal_mono hsub
    _ ≤ ∑ t : ∀ i, T i, μ.real {ω | ∀ e ∈ Finset.univ.biUnion (fun i => edges i (t i)), ω ∈ test e} :=
      measureReal_iUnion_fintype_le _
    _ ≤ ∑ t : ∀ i, T i, q^(Finset.univ.biUnion (fun i => edges i (t i))).card :=
      Finset.sum_le_sum (fun t _ => joint _)
    _ = ∑ t : ∀ i, T i, ∏ i, q^(edges i (t i)).card := by
      apply Finset.sum_congr rfl
      intro t _
      rw [Finset.card_biUnion (fun i _ j _ hij => disj i j hij (t i) (t j))]
      exact (Finset.prod_pow_eq_pow_sum _ _ _).symm
    _ = _ := by simpa using (Finset.prod_univ_sum (fun i => (Finset.univ : Finset (T i)))
      (fun i t => q^(edges i t).card)).symm

lemma large_fiber {I J : Type*} [Fintype I] [Fintype J] [Nonempty J]
    (f : I → J) : ∃ j, Fintype.card I ≤ Fintype.card J *
      (Finset.univ.filter (fun i => f i = j)).card := by
  classical
  obtain ⟨j,hj,hmax⟩ := Finset.exists_max_image Finset.univ
    (fun j => (Finset.univ.filter (fun i => f i = j)).card) Finset.univ_nonempty
  refine ⟨j,?_⟩
  calc
    Fintype.card I = ∑ c : J, (Finset.univ.filter (fun i => f i = c)).card := by
      simpa using (Finset.card_eq_sum_card_fiberwise (s := (Finset.univ : Finset I))
        (t := Finset.univ) (f := f) (fun _ _ => Finset.mem_univ _))
    _ ≤ ∑ _c : J, (Finset.univ.filter (fun i => f i = j)).card :=
      Finset.sum_le_sum (fun c hc => hmax c hc)
    _ = _ := by simp

lemma alternative_sparse_bound {Ω I J : Type*} [MeasurableSpace Ω]
    [Fintype I] [Fintype J] [Nonempty J]
    (μ : Measure Ω) [IsFiniteMeasure μ] (test : J → I → Set Ω)
    (q : ℝ) (hq : 0 < q) (hq1 : q ≤ 1)
    (joint : ∀ j (A : Finset I), μ.real {ω | ∀ i ∈ A, ω ∈ test j i} ≤ q^A.card) :
    μ.real {ω | ∀ i, ∃ j, ω ∈ test j i} ≤
      (Fintype.card J : ℝ)^(Fintype.card I) *
        q^((Fintype.card I : ℝ)/(Fintype.card J : ℝ)) := by
  classical
  have hsub : {ω | ∀ i, ∃ j, ω ∈ test j i} ⊆
      ⋃ f : I → J, {ω | ∀ i, ω ∈ test (f i) i} := by
    intro ω hω
    choose f hf using hω
    exact Set.mem_iUnion.mpr ⟨f,hf⟩
  have each (f : I → J) : μ.real {ω | ∀ i, ω ∈ test (f i) i} ≤
      q^((Fintype.card I : ℝ)/(Fintype.card J : ℝ)) := by
    obtain ⟨j,hj⟩ := large_fiber f
    let A := Finset.univ.filter (fun i => f i = j)
    have hb : {ω | ∀ i, ω ∈ test (f i) i} ⊆ {ω | ∀ i ∈ A, ω ∈ test j i} := by
      intro ω hω i hi
      simpa only [(Finset.mem_filter.mp hi).2] using hω i
    have hJ : (0 : ℝ) < Fintype.card J := Nat.cast_pos.mpr Fintype.card_pos
    have hsize : (Fintype.card I : ℝ)/(Fintype.card J : ℝ) ≤ A.card := by
      apply (div_le_iff₀ hJ).mpr
      have hh : (Fintype.card I : ℝ) ≤ (Fintype.card J : ℝ)*A.card := by exact_mod_cast hj
      nlinarith
    calc
      _ ≤ μ.real {ω | ∀ i ∈ A, ω ∈ test j i} := measureReal_mono hb
      _ ≤ q^A.card := joint j A
      _ = q^(A.card : ℝ) := (Real.rpow_natCast _ _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_ge hq hq1 hsize
  calc
    _ ≤ μ.real (⋃ f : I → J, {ω | ∀ i, ω ∈ test (f i) i}) := measureReal_mono hsub
    _ ≤ ∑ f : I → J, μ.real {ω | ∀ i, ω ∈ test (f i) i} := measureReal_iUnion_fintype_le _
    _ ≤ ∑ _ : I → J, q^((Fintype.card I : ℝ)/(Fintype.card J : ℝ)) :=
      Finset.sum_le_sum (fun f _ => each f)
    _ = _ := by simp

end SparseWitness

end

end OAI
