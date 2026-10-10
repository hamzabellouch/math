import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanFactorModel
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanWordLogarithms

namespace OAI

/-! # Lifting actual ambient word paths to the Cartan factors

One compact set of factor increments lifts every word over a compact ambient
increment set. The lift reproduces every prefix exactly, so height control
can be applied to the actual ambient path.
-/

noncomputable section

namespace PolycyclicRecognition

@[simp] theorem map_wordPrefix {A B : Type*} [Monoid A] [Monoid B]
    (f : A →* B) (u : ℕ → A) (m : ℕ) :
    f (wordPrefix u m) = wordPrefix (fun i => f (u i)) m := by
  induction m with
  | zero => simp only [wordPrefix_zero, map_one]
  | succ m ih => simp only [wordPrefix_succ, map_mul, ih]

/-- A fixed set of possible lifts supplies compatible lifts of every finite
word, with all prefix equalities retained. -/
theorem exists_lifted_word_prefixes {A B : Type*} [Monoid A] [Monoid B]
    (f : A →* B) (C : Set A) (K : Set B) (hK : K ⊆ f '' C)
    (u : ℕ → B) (m : ℕ) (hu : ∀ i < m, u i ∈ K) :
    ∃ v : ℕ → A, (∀ i < m, v i ∈ C) ∧
      ∀ j ≤ m, f (wordPrefix v j) = wordPrefix u j := by
  choose w hwC hwf using (fun i : Fin m => hK (hu i.val i.isLt))
  let v : ℕ → A := fun i => if h : i < m then w ⟨i, h⟩ else 1
  have hvC (i : ℕ) (hi : i < m) : v i ∈ C := by
    simpa only [v, dite_eq_left hi] using hwC ⟨i, hi⟩
  have hvf (i : ℕ) (hi : i < m) : f (v i) = u i := by
    simpa only [v, dite_eq_left hi] using hwf ⟨i, hi⟩
  refine ⟨v, hvC, ?_⟩
  intro j hj
  induction j with
  | zero => simp only [wordPrefix_zero, map_one]
  | succ j ih =>
    rw [wordPrefix_succ, map_mul, ih (Nat.le_of_succ_le hj),
      hvf j (Nat.lt_of_succ_le hj), wordPrefix_succ]

open scoped Manifold

variable {EG G : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G]
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G}
  (F : CartanFactorModel H ExpG)

/-- The actual ambient compact increments lift into one compact factor set,
uniformly over word length. All intermediate positions are reproduced. -/
theorem exists_compact_cartan_word_lifts {K : Set G} (hK : IsCompact K) :
    ∃ C : Set (F.N.carrier × F.D.carrier), IsCompact C ∧
      ∀ (u : ℕ → G) (m : ℕ), (∀ i < m, u i ∈ K) →
      ∃ (v : ℕ → F.N.carrier) (w : ℕ → F.D.carrier),
        (∀ i < m, (v i, w i) ∈ C) ∧
        ∀ j ≤ m, F.inclusionN
            (wordPrefix (fun i => (⟨v i, w i⟩ : F.N.carrier ⋊[F.action] F.D.carrier)) j).left *
          F.inclusionD (wordPrefix w j) = wordPrefix u j := by
  obtain ⟨C, hC, hcover⟩ := F.compactLifts K hK
  let q := cartanMultiplication F.inclusionN F.inclusionD F.action F.conjugation
  let C' : Set (F.N.carrier ⋊[F.action] F.D.carrier) :=
    {z | (z.left, z.right) ∈ C}
  have hcover' : K ⊆ q '' C' := by
    intro g hg
    obtain ⟨⟨n, d⟩, hnd, hprod⟩ := hcover hg
    exact ⟨⟨n, d⟩, hnd, hprod⟩
  refine ⟨C, hC, ?_⟩
  intro u m hu
  obtain ⟨z, hz, hprefix⟩ := exists_lifted_word_prefixes q C' K hcover' u m hu
  refine ⟨fun i => (z i).left, fun i => (z i).right, hz, ?_⟩
  intro j hj
  have he : (fun i => (⟨(z i).left, (z i).right⟩ : F.N.carrier ⋊[F.action] F.D.carrier)) = z := by
    funext i
    exact SemidirectProduct.ext rfl rfl
  rw [← semidirect_wordPrefix_right F.action (fun i => (z i).left)
    (fun i => (z i).right) j, he]
  exact hprefix j hj

end PolycyclicRecognition

end

end OAI
