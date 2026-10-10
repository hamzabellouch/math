import OAI.Geometry.TranslativeCovering.MeasureCut

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology

universe u_1 u_2

namespace BlockSets
open MeasureTheory Finset BlockGeometry
open scoped BigOperators
variable {Ω : Type u_1} {I : Type u_2} [MeasurableSpace Ω]

noncomputable def clipped (μ : Measure Ω) (C : I → Set Ω) (i : I) : ℝ :=
  min (μ.real (C i)) (1/2)
noncomputable def cost (μ : Measure Ω) (C : I → Set Ω) (i : I) : ℝ :=
  -Real.log (clipped μ C i)

def common (C : I → Set Ω) (S : Finset I) : Set Ω := ⋂ i ∈ S, C i

lemma clipped_pos (μ : Measure Ω) (C : I → Set Ω) (hc : ∀ i, 0 < μ.real (C i))
    (i : I) : 0 < clipped μ C i := lt_min (hc i) (by norm_num)

lemma cost_ge (μ : Measure Ω) (C : I → Set Ω) (hc : ∀ i, 0 < μ.real (C i))
    (i : I) : Real.log 2 ≤ cost μ C i := by
  have hb := Real.log_le_log (clipped_pos μ C hc i) (min_le_right (μ.real (C i)) (1/2))
  change _ ≤ -Real.log (clipped μ C i)
  rw [Real.log_div one_ne_zero (by norm_num), Real.log_one] at hb
  linarith

lemma common_measurable (C : I → Set Ω) (hC : ∀ i, MeasurableSet (C i)) (S : Finset I) :
    MeasurableSet (common C S) := by
  exact MeasurableSet.biInter S.finite_toSet.countable (fun i _ => hC i)

omit [MeasurableSpace Ω] in
lemma common_subset (C : I → Set Ω) {S : Finset I} {i : I} (hi : i ∈ S) :
    common C S ⊆ C i := by
  intro x hx
  exact Set.mem_iInter₂.mp hx i hi

lemma choose_sets [StandardBorelSpace Ω] [Fintype I] [DecidableEq I] (μ : Measure Ω) [IsFiniteMeasure μ] [NullSingletonClass μ]
    (C : I → Set Ω) (hC : ∀ i, MeasurableSet (C i))
    (hc : ∀ i, 0 < μ.real (C i)) {L R : ℝ}
    (d : I → I → ℝ) (P : Finpartition (univ : Finset I))
    (a : Finset I → I) (ha : ∀ S ∈ P.parts, a S ∈ S)
    (hR : ∀ S ∈ P.parts, radius d S ≤ R)
    (hlens : ∀ S ∈ P.parts, radius d S ≤ R →
      Real.exp (-L*(1+radius d S+Real.log S.card))*clipped μ C (a S) ≤ μ.real (common C S)) :
    ∃ E : Finset I → Set Ω, ∀ S ∈ P.parts,
      MeasurableSet (E S) ∧ E S ⊆ common C S ∧
      μ.real (E S) = Real.exp (-loss L d S)*clipped μ C (a S) := by
  classical
  have hex (S : Finset I) (hS : S ∈ P.parts) :
      ∃ E : Set Ω, MeasurableSet E ∧ E ⊆ common C S ∧
        μ.real E = Real.exp (-loss L d S)*clipped μ C (a S) := by
    apply MeasureCut.exists_subset_measure μ (common_measurable C hC S)
    · exact mul_nonneg (Real.exp_pos _).le (clipped_pos μ C hc _).le
    · by_cases hsmall : S.card ≤ 1
      · have hnon := P.nonempty_of_mem_parts hS
        have hc1 : S.card = 1 := by have := card_pos.mpr hnon; omega
        obtain ⟨i,hi⟩ := card_eq_one.mp hc1
        have hai : a S = i := by simpa [hi] using ha S hS
        simp only [loss, ite_eq_left hsmall, neg_zero, Real.exp_zero, one_mul, hai]
        have hcommon : common C S = C i := by simp [common,hi]
        rw [hcommon]
        exact min_le_left _ _
      · rw [loss, ite_eq_right hsmall]
        convert hlens S hS (hR S hS) using 1
        congr 2
        ring
  choose E hE using hex
  let F : Finset I → Set Ω := fun S => if hS : S ∈ P.parts then E S hS else ∅
  refine ⟨F, fun S hS => ?_⟩
  simpa only [F,dite_eq_left hS] using hE S hS

lemma intensity_cost {ell b : ℝ} (hell : 0 ≤ ell) (hb : 0 < b) (hb' : b ≤ 1/2) :
    0 < Real.exp (-ell)*b ∧ Real.exp (-ell)*b ≤ 1/2 ∧
      -Real.log (Real.exp (-ell)*b) = -Real.log b+ell := by
  have he : Real.exp (-ell) ≤ 1 := by simpa using Real.exp_le_exp.mpr (neg_nonpos.mpr hell)
  refine ⟨mul_pos (Real.exp_pos _) hb, (mul_le_of_le_one_left hb.le he).trans hb', ?_⟩
  rw [Real.log_mul (Real.exp_ne_zero _) hb.ne', Real.log_exp]
  ring

lemma sum_cost [Fintype I] [DecidableEq I] (μ : Measure Ω) (C : I → Set Ω) (hc : ∀ i, 0 < μ.real (C i))
    {L ζ : ℝ} (d : I → I → ℝ) (P : Finpartition (univ : Finset I))
    (a : Finset I → I) (ha : ∀ S ∈ P.parts, a S ∈ S)
    (hloss : ∀ S ∈ P.parts, loss L d S ≤ ζ*S.card) :
    ∑ S ∈ P.parts, (cost μ C (a S)+loss L d S) ≤
      ∑ i, cost μ C i + ζ*Fintype.card I := by
  have hn (i : I) : 0 ≤ cost μ C i :=
    (Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2)).trans (cost_ge μ C hc i)
  calc
    _ ≤ ∑ S ∈ P.parts, ((∑ i ∈ S, cost μ C i)+ζ*S.card) := by
      apply sum_le_sum
      intro S hS
      exact add_le_add (single_le_sum (fun i _ => hn i) (ha S hS)) (hloss S hS)
    _ = _ := by
      have hsum := sum_biUnion (f := cost μ C) P.disjoint
      simp only [id_eq,P.biUnion_parts] at hsum
      rw [sum_add_distrib, ← hsum, ← mul_sum]
      congr 1
      have hh := congrArg (fun x : ℕ => (x:ℝ)) P.sum_card_parts
      simpa only [Nat.cast_sum, card_univ] using congrArg (fun x : ℝ => ζ*x) hh

end BlockSets

end OAI
