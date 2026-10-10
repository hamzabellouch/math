import OAI.Analysis.KadisonKastler.PublishedIndependence
import OAI.Analysis.KadisonKastler.TraceLimits
import OAI.Analysis.FactorGeneration.Bicommutant

namespace OAI

/-! # Adjoining one element preserves trace separability

Separate continuity of multiplication in the tracial two-norm makes the
two-norm closure of a star algebra another star algebra. A countable
approximation to the base then suffices for its algebraic extension by
one element.
-/

namespace KadisonKastler

open TopologicalSpace

noncomputable section

variable {B : Type*} [CStarAlgebra B]

/-- Trace separability passes to every subset. -/
theorem TraceSeparable.mono {τ : FaithfulTracialState B} {S T : Set B}
    (hS : TraceSeparable τ S) (hTS : T ⊆ S) : TraceSeparable τ T := by
  classical
  by_cases ht : T.Nonempty
  · obtain ⟨t₀, ht₀⟩ := ht
    obtain ⟨D, hDc, hDS, hDd⟩ := hS
    let I := D × ℕ
    have hex (i : I) : ∃ y ∈ T,
        (∃ z ∈ T, traceTwoNorm τ (z - i.1.val) < 1 / (i.2 + 1 : ℝ)) →
          traceTwoNorm τ (y - i.1.val) < 1 / (i.2 + 1 : ℝ) := by
      by_cases h : ∃ z ∈ T, traceTwoNorm τ (z - i.1.val) < 1 / (i.2 + 1 : ℝ)
      · obtain ⟨z, hz, hzd⟩ := h
        exact ⟨z, hz, fun _ => hzd⟩
      · exact ⟨t₀, ht₀, fun hh => (h hh).elim⟩
    choose y hyT hy using hex
    have hcount : (Set.range y).Countable := by
      let := hDc.to_subtype
      exact Set.countable_range y
    refine ⟨Set.range y, hcount, ?_, ?_⟩
    · rintro z ⟨i, rfl⟩
      exact hyT i
    · intro x hx ε hε
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (show 0 < ε / 2 by positivity)
      obtain ⟨d, hd, hxd⟩ := hDd x (hTS hx) (1 / (n + 1 : ℝ)) (by positivity)
      let i : I := (⟨d, hd⟩, n)
      have hiy := hy i ⟨x, hx, hxd⟩
      refine ⟨y i, ⟨i, rfl⟩, ?_⟩
      have he : x - y i = (x - d) + (d - y i) := by abel
      rw [he]
      have hrev : traceTwoNorm τ (d - y i) < 1 / (n + 1 : ℝ) := by
        simpa only [traceTwoNorm_sub_comm] using hiy
      exact (traceTwoNorm_add_le τ _ _).trans_lt (by dsimp [i] at hiy; linarith)
  · refine ⟨∅, Set.countable_empty, Set.empty_subset T, ?_⟩
    intro x hx
    exact (ht ⟨x, hx⟩).elim

/-- A trace-preserving star homomorphism preserves two-norm separability. -/
theorem TraceSeparable.map {C : Type*} [CStarAlgebra C]
    {τ : FaithfulTracialState B} {σ : FaithfulTracialState C} {S : Set B}
    (hS : TraceSeparable τ S) (φ : B →⋆ₐ[ℂ] C)
    (hφ : ∀ x, σ.toLinearMap (φ x) = τ.toLinearMap x) :
    TraceSeparable σ (φ '' S) := by
  obtain ⟨D, hDc, hDS, hDd⟩ := hS
  refine ⟨φ '' D, hDc.image φ, Set.image_mono hDS, ?_⟩
  rintro _ ⟨x, hx, rfl⟩ ε hε
  obtain ⟨y, hy, hxy⟩ := hDd x hx ε hε
  refine ⟨φ y, ⟨y, hy, rfl⟩, ?_⟩
  have he : traceTwoNorm σ (φ x - φ y) = traceTwoNorm τ (x - y) := by
    rw [← map_sub]
    simp only [traceTwoNorm, ← StarHomClass.map_star, ← map_mul, hφ]
  rwa [he]

/-- The algebra of all two-norm limits of elements of a star subalgebra. -/
def traceClosure (τ : FaithfulTracialState B) (A : StarSubalgebra ℂ B) :
    StarSubalgebra ℂ B where
  carrier := {x | ∀ ε : ℝ, 0 < ε → ∃ y ∈ A, traceTwoNorm τ (x - y) < ε}
  zero_mem' := by intro ε hε; exact ⟨0, A.zero_mem, by simpa using hε⟩
  one_mem' := by intro ε hε; exact ⟨1, A.one_mem, by simpa using hε⟩
  add_mem' := by
    intro x z hx hz ε hε
    obtain ⟨a, ha, hxa⟩ := hx (ε / 2) (by positivity)
    obtain ⟨b, hb, hzb⟩ := hz (ε / 2) (by positivity)
    refine ⟨a + b, A.add_mem ha hb, ?_⟩
    have he : x + z - (a + b) = (x - a) + (z - b) := by abel
    rw [he]
    exact (traceTwoNorm_add_le τ _ _).trans_lt (by linarith)
  mul_mem' := by
    intro x z hx hz ε hε
    obtain ⟨b, hb, hzb⟩ := hz (ε / (2 * (‖x‖ + 1))) (by positivity)
    obtain ⟨a, ha, hxa⟩ := hx (ε / (2 * (‖b‖ + 1))) (by positivity)
    have hzerr : ‖x‖ * traceTwoNorm τ (z - b) < ε / 2 := by
      have h := (lt_div_iff₀ (by positivity : 0 < 2 * (‖x‖ + 1))).mp hzb
      nlinarith [traceTwoNorm_nonneg τ (z - b)]
    have hxerr : traceTwoNorm τ (x - a) * ‖b‖ < ε / 2 := by
      have h := (lt_div_iff₀ (by positivity : 0 < 2 * (‖b‖ + 1))).mp hxa
      nlinarith [traceTwoNorm_nonneg τ (x - a)]
    refine ⟨a * b, A.mul_mem ha hb, ?_⟩
    have he : x * z - a * b = x * (z - b) + (x - a) * b := by noncomm_ring
    rw [he]
    calc
      _ ≤ traceTwoNorm τ (x * (z - b)) + traceTwoNorm τ ((x - a) * b) :=
        traceTwoNorm_add_le τ _ _
      _ ≤ ‖x‖ * traceTwoNorm τ (z - b) + traceTwoNorm τ (x - a) * ‖b‖ :=
        add_le_add (traceTwoNorm_mul_le_left τ _ _) (traceTwoNorm_mul_le_right τ _ _)
      _ < ε := by linarith
  algebraMap_mem' := by
    intro c ε hε
    exact ⟨algebraMap ℂ B c, A.algebraMap_mem c, by simpa using hε⟩
  star_mem' := by
    intro x hx ε hε
    obtain ⟨a, ha, hxa⟩ := hx ε hε
    refine ⟨star a, star_mem ha, ?_⟩
    simpa only [← star_sub, traceTwoNorm_star] using hxa

/-- Every element of the original algebra is in its two-norm closure. -/
theorem le_traceClosure (τ : FaithfulTracialState B) (A : StarSubalgebra ℂ B) :
    A ≤ traceClosure τ A := by
  intro x hx ε hε
  exact ⟨x, hx, by simpa using hε⟩

/-- Adjoining one element to a trace-separable algebra preserves trace
separability. The adjoined element need not be unitary. -/
theorem TraceSeparable.adjoin_singleton (τ : FaithfulTracialState B)
    (A : StarSubalgebra ℂ B) (hA : TraceSeparable τ (A : Set B)) (u : B) :
    TraceSeparable τ (StarAlgebra.adjoin ℂ ((A : Set B) ∪ {u}) : Set B) := by
  obtain ⟨D, hDc, hDA, hDdense⟩ := hA
  let E := StarAlgebra.adjoin ℂ (D ∪ {u})
  have hEsep : IsSeparable (E : Set B) :=
    Generator.separable_countable_star_adjoin (hDc.union (Set.countable_singleton u))
  have hEbig : E ≤ StarAlgebra.adjoin ℂ ((A : Set B) ∪ {u}) :=
    StarAlgebra.adjoin_mono (Set.union_subset_union hDA subset_rfl)
  have hbig : StarAlgebra.adjoin ℂ ((A : Set B) ∪ {u}) ≤ traceClosure τ E := by
    apply StarAlgebra.adjoin_le
    intro x hx
    rcases hx with hx | hx
    · intro ε hε
      obtain ⟨y, hy, hxy⟩ := hDdense x hx ε hε
      exact ⟨y, StarAlgebra.subset_adjoin ℂ (D ∪ {u}) (Or.inl hy), hxy⟩
    · exact le_traceClosure τ E (StarAlgebra.subset_adjoin ℂ (D ∪ {u}) (Or.inr hx))
  let : SeparableSpace (E : Set B) := hEsep.separableSpace
  obtain ⟨F, hFc, hFE, hFdense⟩ := exists_countable_dense_subset (E : Set B)
  refine ⟨F, hFc, hFE.trans hEbig, ?_⟩
  intro x hx ε hε
  obtain ⟨y, hy, hxy⟩ := hbig hx (ε / 2) (by positivity)
  obtain ⟨z, hz, hyz⟩ := Metric.mem_closure_iff.mp (hFdense hy) (ε / 2) (by positivity)
  refine ⟨z, hz, ?_⟩
  have hdist : traceTwoNorm τ (y - z) < ε / 2 :=
    (traceTwoNorm_le_norm τ _).trans_lt ((dist_eq_norm y z) ▸ hyz)
  have he : x - z = (x - y) + (y - z) := by abel
  rw [he]
  exact (traceTwoNorm_add_le τ _ _).trans_lt (by linarith)

end

end KadisonKastler

end OAI
