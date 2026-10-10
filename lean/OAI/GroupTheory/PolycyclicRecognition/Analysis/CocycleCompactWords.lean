import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanWordLogarithms
import OAI.GroupTheory.PolycyclicRecognition.Algebra.CocycleCombing

namespace OAI

/-! # Height and cocycle bounds on compact words -/

noncomputable section
namespace PolycyclicRecognition

theorem norm_height_wordPrefix_le {G W : Type*} [Group G]
    [NormedAddCommGroup W] (π : G →* Multiplicative W)
    (u : ℕ → G) (m : ℕ) {R : ℝ}
    (hu : ∀ i < m, ‖(π (u i)).toAdd‖ ≤ R) :
    ‖(π (wordPrefix u m)).toAdd‖ ≤ (m : ℝ) * R := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [wordPrefix_succ, map_mul]
    change ‖(π (wordPrefix u m)).toAdd + (π (u m)).toAdd‖ ≤ _
    calc
      _ ≤ ‖(π (wordPrefix u m)).toAdd‖ + ‖(π (u m)).toAdd‖ := norm_add_le _ _
      _ ≤ (m : ℝ) * R + R :=
        add_le_add (ih (fun i hi => hu i (Nat.lt_succ_of_lt hi))) (hu m (Nat.lt_succ_self m))
      _ = _ := by push_cast; ring

variable {G D E : Type*} [Group G] [Group D]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {ρ : G →* (E ≃ₗᵢ[ℝ] E)} {b : G → E}

theorem IsUnitaryCocycle.norm_mapped_wordPrefix_le_of_coboundary
    (hb : IsUnitaryCocycle ρ b) (i : D →* G) (Q : Set D) (φ : E) {δ : ℝ}
    (hQ : ∀ d ∈ Q, ‖b (i d) + ρ (i d) φ - φ‖ ≤ δ)
    (u : ℕ → D) (m : ℕ) (hu : ∀ j < m, u j ∈ Q) :
    ‖b (i (wordPrefix u m))‖ ≤ (m : ℝ) * δ + 2 * ‖φ‖ := by
  let := unitaryDistribMulAction ρ
  let : IsIsometricSMul G E := ⟨fun g => (ρ g).isometry⟩
  have h := IsCocycle.norm_word_le_of_coboundary hb (i '' Q) φ
    (by rintro g ⟨d, hd, rfl⟩; exact hQ d hd)
    ((List.ofFn (fun j : Fin m => u j.val)).map i) (by
      intro g hg
      obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hg
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hd
      exact ⟨u j, hu j j.isLt, rfl⟩)
  simpa only [List.length_map, List.length_ofFn, ← map_list_prod, wordPrefix] using h

omit [InnerProductSpace ℝ E] in
theorem sublinear_of_compact_word_estimates (b : G → E) (K : Set G)
    (hsub : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, 0 ≤ B ∧ ∀ (u : ℕ → G) (m : ℕ),
      (∀ i < m, u i ∈ K) → ‖b (wordPrefix u m)‖ ≤ ε * (m : ℝ) + B)
    (length : G → ℝ) (hlen : ∀ g, 0 ≤ length g) {a : ℝ} (ha : 0 ≤ a)
    (hword : ∀ g, ∃ l : List G, (∀ q ∈ l, q ∈ K) ∧ l.prod = g ∧
      (l.length : ℝ) ≤ a * length g + a) :
    ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, 0 ≤ B ∧ ∀ g, ‖b g‖ ≤ ε * length g + B := by
  classical
  intro ε hε
  let δ := ε / (a + 1)
  have hδ : 0 < δ := div_pos hε (by positivity)
  obtain ⟨B, hB, hb⟩ := hsub δ hδ
  have hcoef : δ * a ≤ ε := by
    have he : δ * (a + 1) = ε := div_mul_cancel₀ _ (by positivity)
    nlinarith
  refine ⟨δ * a + B, by positivity, fun g => ?_⟩
  obtain ⟨l, hl, he, hn⟩ := hword g
  let u : ℕ → G := fun i => if h : i < l.length then l[i] else 1
  have hprod : wordPrefix u l.length = g := by
    rw [wordPrefix, show List.ofFn (fun i : Fin l.length => u i.val) = l from ?_, he]
    simpa only [u, dite_eq_left, Fin.isLt] using (List.ofFn_getElem (xs := l))
  have hbound := hb u l.length (fun i hi => by
    simpa only [u, dite_eq_left hi] using hl l[i] (List.getElem_mem hi))
  rw [hprod] at hbound
  calc
    ‖b g‖ ≤ δ * (l.length : ℝ) + B := hbound
    _ ≤ δ * (a * length g + a) + B :=
      add_le_add (mul_le_mul_of_nonneg_left hn hδ.le) le_rfl
    _ = (δ * a) * length g + (δ * a + B) := by ring
    _ ≤ ε * length g + (δ * a + B) :=
      add_le_add (mul_le_mul_of_nonneg_right hcoef (hlen g)) le_rfl

end PolycyclicRecognition

end

end OAI
