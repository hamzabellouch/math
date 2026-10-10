import OAI.GroupTheory.PolycyclicRecognition.Analysis.SuccessfulWordPaths

namespace OAI

/-! # The exact path endpoint of a successful sample sequence -/

noncomputable section

namespace PolycyclicRecognition

open Set

variable {N G : Type*} [Group N] [Group G]

/-- Transport the visited sheets through a subgroup map and a fixed left translate. -/
theorem WordSheetsGood.map_mul_hom (ι : N →* G) (x : G)
    {A : Set N} {n : N} {u : List N} (h : WordSheetsGood A n u) :
    WordSheetsGood ((fun v => x * ι v) '' A) (x * ι n) (u.map ι) := by
  induction u generalizing n with
  | nil => exact ⟨n, h, rfl⟩
  | cons g u ih =>
    refine ⟨⟨n, h.1, rfl⟩, ?_⟩
    simpa only [map_mul, mul_assoc] using ih h.2

variable [PseudoMetricSpace G] [IsTopologicalGroup G]

/-- A successful independent sample sequence gives the specified geometric
word path to its actual group endpoint, with bounds inherited from its
single-letter visits on the good sheets. -/
theorem successful_sample_path
    (ι : N →* G) (x d₀ : G) (A : Set N) (S : Set G) (m : ℕ)
    (sample : ℕ → ℝ → N) (hsub : ∀ j s t, sample j s * (sample j t)⁻¹ = sample j (s - t))
    (d : Fin m → ℝ → G) (hd : ∀ i, Continuous (d i)) (hd₀ : ∀ i, d i 0 = 1)
    (hf : ∀ i : Fin m, Continuous (fun t => ι (sample i.val t)))
    (hf₀ : ∀ i : Fin m, ι (sample i.val 0) = 1)
    (r : ℝ) {L κ ρ : ℝ} (hL : 0 ≤ L) (hκ : 0 ≤ κ)
    (hbase : ∀ n ∈ A, x * ι n * d₀ ∈ S)
    (hstep : ∀ n ∈ A, ∀ i : Fin m, ∀ b : ℝ, |b| ≤ 2 * ρ → n * sample i.val b ∈ A →
      PathMetricBound (supportVisitPath (d i) (hd i) (hd₀ i)
        (fun t => ι (sample i.val t)) (hf i) (hf₀ i) (x * ι n) d₀ r b) L κ ∧
      ∀ t, supportVisitPath (d i) (hd i) (hd₀ i)
        (fun t => ι (sample i.val t)) (hf i) (hf₀ i) (x * ι n) d₀ r b t ∈ S)
    (hinj : Function.Injective ι)
    (n : N) (hn : n ∈ A) (t : Fin (m + m) → ℝ) (ht : ‖t‖ ≤ ρ)
    (hs : SwitchSuccessful (fun _ => A) 0 m n (sampledSwitchParameters sample m t)) :
    ∃ γ : Path (x * ι n * d₀)
      (x * ι (switchEndpoint m n (sampledSwitchParameters sample m t)) * d₀),
      PathMetricBound γ (L * 2 ^ m) (κ * 2 ^ m) ∧ ∀ u, γ u ∈ S := by
  let f : Fin m → ℝ → G := fun j b => ι (sample j.val b)
  let word := List.ofFn (fun j : Fin m => (j, t (Fin.castAdd m j) - t (Fin.natAdd m j)))
  have hgood := (wordSheetsGood_sampled A sample hsub m t n hn hs).map_mul_hom ι x
  have hgood' : WordSheetsGood ((fun v => x * ι v) '' A) (x * ι n)
      (word.map (fun z => f z.1 z.2)) := by
    simpa only [word, List.map_ofFn, f, Function.comp_def] using hgood
  have hparam : ∀ z ∈ word, |z.2| ≤ 2 * ρ := by
    intro z hz
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hz
    have h₁ := (norm_le_pi_norm t (Fin.castAdd m j)).trans ht
    have h₂ := (norm_le_pi_norm t (Fin.natAdd m j)).trans ht
    have hh := abs_sub (t (Fin.castAdd m j)) (t (Fin.natAdd m j))
    rw [Real.norm_eq_abs] at h₁ h₂
    linarith
  obtain ⟨hbound, hrange⟩ := supportWordPath_good_bound d f hd hf hd₀ hf₀ d₀ r
    ((fun v => x * ι v) '' A) S (fun _ b => |b| ≤ 2 * ρ) hL hκ
    (by rintro _ ⟨v, hv, rfl⟩; exact hbase v hv)
    (by
      rintro _ ⟨v, hv, rfl⟩ i b hb ⟨w, hw, he⟩
      have hv' : v * sample i.val b ∈ A := by
        have he' : w = v * sample i.val b := hinj (by simpa [map_mul, mul_assoc] using he)
        exact he' ▸ hw
      exact hstep v hv i b hb hv') word hparam (x * ι n) hgood'
  let γ := supportWordPath d f hd hf hd₀ hf₀ d₀ r word (x * ι n)
  have hend : x * ι (switchEndpoint m n (sampledSwitchParameters sample m t)) * d₀ =
      (x * ι n) * indexedWordProduct f word * d₀ := by
    rw [sampledSwitchEndpoint_eq sample m hsub]
    simp only [map_mul, map_list_prod, List.map_ofFn, indexedWordProduct, word, f, Function.comp_def, mul_assoc]
  refine ⟨γ.cast rfl hend, ?_, hrange⟩
  change PathMetricBound γ (L * 2 ^ m) (κ * 2 ^ m)
  simpa only [word, List.length_ofFn] using hbound

end PolycyclicRecognition

end

end OAI
