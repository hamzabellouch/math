import OAI.GroupTheory.PolycyclicRecognition.Finiteness.NilpotentReducedCohomology
import OAI.GroupTheory.PolycyclicRecognition.Algebra.UnitaryMautner

namespace OAI

/-! # Sublinear cocycles from a nilpotent subgroup and bounded combing

The geometric premise is an explicit product of a bounded number of compact
factors and subgroup factors, with a linear bound on their total subgroup
length. No cohomological conclusion is included in this premise.
-/

noncomputable section

namespace PolycyclicRecognition

open Set

variable {G H E : Type*} [Group G] [Group H]

def HasBoundedSubgroupCombing (i : H →* G) (lengthG : G → ℝ)
    (lengthH : H → ℝ) (K : Set G) : Prop :=
  ∃ (k : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ g : G, ∃ l : List (G × H),
    (∀ p ∈ l, p.1 ∈ K) ∧
    (l.map (fun p => p.1 * i p.2)).prod = g ∧ l.length ≤ k ∧
    (l.map (fun p => lengthH p.2)).sum ≤ C * lengthG g + C

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {ρ : G →* (E ≃ₗᵢ[ℝ] E)} {b : G → E}

theorem IsUnitaryCocycle.norm_mul_le (hb : IsUnitaryCocycle ρ b) (g h : G) :
    ‖b (g * h)‖ ≤ ‖b g‖ + ‖b h‖ := by
  rw [hb g h]
  exact (norm_add_le _ _).trans_eq (congrArg (fun t => ‖b g‖ + t) ((ρ g).norm_map _))

theorem IsUnitaryCocycle.norm_paired_word_le (hb : IsUnitaryCocycle ρ b)
    (i : H →* G) (lengthH : H → ℝ) (K : Set G)
    {M δ B : ℝ} (hK : ∀ q ∈ K, ‖b q‖ ≤ M)
    (hH : ∀ h, ‖b (i h)‖ ≤ δ * lengthH h + B)
    (l : List (G × H)) (hl : ∀ p ∈ l, p.1 ∈ K) :
    ‖b (l.map (fun p => p.1 * i p.2)).prod‖ ≤
      δ * (l.map (fun p => lengthH p.2)).sum + (l.length : ℝ) * (M + B) := by
  induction l with
  | nil => simp [hb.map_one]
  | cons p l ih =>
    have hp := (hb.norm_mul_le p.1 (i p.2)).trans
      (add_le_add (hK _ (hl p (by simp))) (hH p.2))
    have ht := ih (fun q hq => hl q (by simp [hq]))
    have hs := (hb.norm_mul_le (p.1 * i p.2)
      (l.map (fun p => p.1 * i p.2)).prod).trans (add_le_add hp ht)
    exact hs.trans_eq (by
      simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
      ring)

theorem IsUnitaryCocycle.sublinear_of_bounded_combing (hb : IsUnitaryCocycle ρ b)
    (i : H →* G) (lengthG : G → ℝ) (lengthH : H → ℝ) (K : Set G)
    (hlen : ∀ g, 0 ≤ lengthG g) (hcomb : HasBoundedSubgroupCombing i lengthG lengthH K)
    (hK : ∃ M : ℝ, 0 ≤ M ∧ ∀ q ∈ K, ‖b q‖ ≤ M)
    (hsub : ∀ δ : ℝ, 0 < δ → ∃ B : ℝ, 0 ≤ B ∧
      ∀ h, ‖b (i h)‖ ≤ δ * lengthH h + B) :
    ∀ ε : ℝ, 0 < ε → ∃ D : ℝ, 0 ≤ D ∧ ∀ g, ‖b g‖ ≤ ε * lengthG g + D := by
  obtain ⟨k, C, hC, hcomb⟩ := hcomb
  obtain ⟨M, hM, hK⟩ := hK
  intro ε hε
  let δ := ε / (C + 1)
  have hδ : 0 < δ := div_pos hε (by linarith)
  have hcoef : δ * C ≤ ε := by
    have heq : δ * (C + 1) = ε := div_mul_cancel₀ _ (by linarith)
    nlinarith
  obtain ⟨B, hB, hbH⟩ := hsub δ hδ
  refine ⟨δ * C + (k : ℝ) * (M + B), by positivity, ?_⟩
  intro g
  obtain ⟨l, hl, he, hk, hsum⟩ := hcomb g
  have hword := hb.norm_paired_word_le i lengthH K hK hbH l hl
  rw [he] at hword
  calc
    ‖b g‖ ≤ δ * (l.map (fun p => lengthH p.2)).sum + (l.length : ℝ) * (M + B) := hword
    _ ≤ δ * (C * lengthG g + C) + (k : ℝ) * (M + B) :=
      add_le_add (mul_le_mul_of_nonneg_left hsum hδ.le)
        (mul_le_mul_of_nonneg_right (by exact_mod_cast hk) (add_nonneg hM hB))
    _ = (δ * C) * lengthG g + (δ * C + (k : ℝ) * (M + B)) := by ring
    _ ≤ ε * lengthG g + (δ * C + (k : ℝ) * (M + B)) :=
      add_le_add (mul_le_mul_of_nonneg_right hcoef (hlen g)) le_rfl

theorem IsUnitaryCocycle.sublinear_of_approximation (hb : IsUnitaryCocycle ρ b)
    (Q : Set G) (length : G → ℝ) (hlen : ∀ g, 0 ≤ length g)
    {a : ℝ} (ha : 0 ≤ a)
    (hword : ∀ g, ∃ l : List G, (∀ q ∈ l, q ∈ Q) ∧ l.prod = g ∧
      (l.length : ℝ) ≤ a * length g + a)
    (happrox : ∀ ε : ℝ, 0 < ε → ∃ φ : E, ∀ q ∈ Q, ‖b q + ρ q φ - φ‖ ≤ ε) :
    ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, 0 ≤ B ∧ ∀ g, ‖b g‖ ≤ ε * length g + B := by
  let := unitaryDistribMulAction ρ
  let : IsIsometricSMul G E := ⟨fun g => (ρ g).isometry⟩
  exact IsCocycle.sublinear_of_coboundary_approximation hb Q length hlen ha hword happrox

variable [TopologicalSpace G] [IsTopologicalGroup G] [CompleteSpace E]

theorem IsUnitaryCocycle.sublinear_of_nilpotent_combing (hb : IsUnitaryCocycle ρ b)
    (hbc : Continuous b) (hρ : ∀ v, Continuous (fun g => ρ g v))
    (hfix : ∀ v, (∀ g, ρ g v = v) → v = 0)
    (N : Subgroup G) [Group.IsNilpotent N]
    (hgen : (Subgroup.closure ((N : Set G) ∪ contractedBy N)).topologicalClosure = ⊤)
    (lengthG : G → ℝ) (lengthN : N → ℝ)
    (hlenG : ∀ g, 0 ≤ lengthG g) (hlenN : ∀ h, 0 ≤ lengthN h)
    (Q : Set N) (hQ : IsCompact Q) {a : ℝ} (ha : 0 ≤ a)
    (hword : ∀ h, ∃ l : List N, (∀ q ∈ l, q ∈ Q) ∧ l.prod = h ∧
      (l.length : ℝ) ≤ a * lengthN h + a)
    (K : Set G) (hK : IsCompact K)
    (hcomb : HasBoundedSubgroupCombing N.subtype lengthG lengthN K) :
    ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, 0 ≤ B ∧ ∀ g, ‖b g‖ ≤ ε * lengthG g + B := by
  have hfixN := unitary_no_fixed_on_contracting_subgroup ρ hρ hfix N hgen
  let ρN := ρ.comp N.subtype
  let bN : N → E := b ∘ Subtype.val
  have hbN : IsUnitaryCocycle ρN bN := fun g h => hb g h
  have hsub : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, 0 ≤ B ∧
      ∀ h : N, ‖bN h‖ ≤ ε * lengthN h + B := by
    apply hbN.sublinear_of_approximation Q lengthN hlenN ha hword
    intro ε hε
    exact unitaryReducedVanishing_nilpotent N E ρN hfixN
      (fun v => (hρ v).comp continuous_subtype_val) bN
      (hbc.comp continuous_subtype_val) hbN Q hQ ε hε
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hbc.continuousOn
  exact hb.sublinear_of_bounded_combing N.subtype lengthG lengthN K hlenG hcomb
    ⟨max M 0, le_max_right _ _, fun q hq => (hM q hq).trans (le_max_left _ _)⟩ hsub

end PolycyclicRecognition

end

end OAI
