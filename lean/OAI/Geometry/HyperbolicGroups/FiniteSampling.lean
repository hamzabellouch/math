import Mathlib
import OAI.Geometry.HyperbolicGroups.TableSelection

namespace OAI

section
section


noncomputable section
open scoped BigOperators
open Filter Topology
namespace HyperbolicObstruction
namespace IncidenceTemplate

namespace ConditionalTest
variable {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]
lemma satisfies_mono (t : ConditionalTest) {w : TableModel.Entry (A := A) rowSupport → Bool}
    {η ξ : ℝ} (h : t.Satisfies w η) (hη : η ≤ ξ) : t.Satisfies w ξ := by
  obtain ⟨hne,κ,hb,hl⟩ := h
  exact ⟨hne,κ,fun i => (hb i).trans hη,hl.trans hη⟩
end ConditionalTest

/-- The sampling conclusions at any requested positive accuracy are realized on
all sufficiently large signed alphabets, after fixing the parameters. -/
theorem eventually_exists_tables_precision {J : Type*} [Fintype J]
    (T : J → ConditionalTest) {α β δ ξ τ : ℝ}
    (ha : 0 ≤ α) (hb : 7*α ≤ β) (hd : 0 ≤ δ) (hd1 : δ < 1)
    (hsmall : ∀ j, ((T j).k+1:ℝ)*(β+90*δ) ≤ 1/2)
    (hξ : 0 < ξ) (hτ0 : 0 < τ) (hτ2 : τ ≤ 2) :
    ∀ᶠ n in atTop, ∃ (w : TableModel.Entry (A := SymmetricAlphabet n) rowSupport → Bool)
      (d : (Fin 6 → SymmetricAlphabet n) → Bool),
      ¬SixTable.BadPairs δ τ d ∧ ∀ j, (T j).Satisfies w ξ := by
  let ε : ℝ := min (ξ/4) (1/4)
  have he0 : 0 < ε := lt_min (by positivity) (by norm_num)
  have he4 : ε ≤ 1/4 := min_le_right _ _
  have he1 : ε < 1 := lt_of_le_of_lt he4 (by norm_num)
  have hq : ε/(1-ε) ≤ ξ/2 := by
    have hε : ε ≤ ξ/4 := min_le_left _ _
    have hh : ε/(1-ε) ≤ 2*ε := by
      rw [div_le_iff₀ (by linarith : 0 < 1-ε)]
      nlinarith
    exact hh.trans (by linarith)
  have hd' : ∀ᶠ n in atTop, ∀ j : J,
      1 - ((Fintype.card (SymmetricAlphabet n)).descFactorial ((T j).k+1):ℝ)/
        (Fintype.card (SymmetricAlphabet n):ℝ)^((T j).k+1) < ξ/2 := by
    rw [Filter.eventually_all]
    intro j
    exact ((FiniteLaw.distinct_error_tendsto ((T j).k+1)).comp alphabet_size_tendsto).eventually
      (gt_mem_nhds (by positivity))
  filter_upwards [eventually_exists_tables T ha hb hd hd1 hsmall he0 he1 hτ0 hτ2,hd'] with n hn hdn
  obtain ⟨w,d,hw,ht⟩ := hn
  refine ⟨w,d,hw,fun j => (T j).satisfies_mono (ht j) ?_⟩
  linarith [hdn j]

lemma admissible_singleton (e : Field) : Admissible {e} := by
  rcases e with e | ⟨τ,j⟩
  · left
    have hl : ({Sum.inl e} : Finset Field).toLeft = {e} := by ext; simp
    have hr : ({Sum.inl e} : Finset Field).toRight = ∅ := by ext; simp
    refine ⟨hr,?_,?_⟩
    · rw [hl]; simp
    · intro i
      rw [hl]
      have h := Finset.card_le_card (Finset.inter_subset_left : {e} ∩ fan i ⊆ {e})
      exact h.trans (by simp)
  · right
    refine ⟨τ,?_,by simp⟩
    rw [Finset.singleton_subset_iff]
    fin_cases j <;> simp [squareSupport]

/-- The finite named-field part of a conditional test. -/
abbrev ConditionalData := {p : Finset Field × Field // p.2 ∉ p.1 ∧ Admissible (insert p.2 p.1)}
instance : Fintype ConditionalData := Fintype.ofFinite _

abbrev ConditionalData.test (p : ConditionalData) (k : ℕ) : ConditionalTest :=
  ⟨p.val.1,p.val.2,p.property.1,p.property.2,k⟩

abbrev singletonData (e : Field) : ConditionalData :=
  ⟨(∅,e),by simp,by simpa using admissible_singleton e⟩

lemma ConditionalTest.singleton_bound {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]
    (e : Field) {w : TableModel.Entry (A := A) rowSupport → Bool} {η : ℝ}
    (h : ((singletonData e).test 0).Satisfies w η) :
    ∃ hne : Nonempty (StarModel.Matches rowSupport w), letI := hne
      ((FiniteLaw.uniform : FiniteLaw (StarModel.Matches rowSupport w)).map (fun a => a.val e)).totalVariation
        FiniteLaw.uniform ≤ 2*η := by
  classical
  obtain ⟨hne,κ,hb,hl⟩ := h
  let := hne
  refine ⟨hne,?_⟩
  let f : StarModel.Matches rowSupport w → A := fun a => a.val e
  let g : (Fin 1 → A) → A := fun a => a 0
  have hu : (FiniteLaw.uniform : FiniteLaw (Fin 1 → A)).map g = FiniteLaw.uniform :=
    FiniteLaw.map_uniform_equiv (Equiv.funUnique (Fin 1) A)
  have ha := FiniteLaw.totalVariation_map_le
    (FiniteLaw.uniform : FiniteLaw (StarModel.Matches rowSupport w))
    (κ.map (ConditionalStar.branch 0)) f
  have hb' : (FiniteLaw.uniform : FiniteLaw (StarModel.Matches rowSupport w)).totalVariation
      (κ.map (ConditionalStar.branch 0)) ≤ η := by
    rw [FiniteLaw.totalVariation_comm]
    exact hb 0
  have hc := FiniteLaw.totalVariation_map_le
    (κ.map (fun z j => (ConditionalStar.branch j z).val e))
    (FiniteLaw.uniform : FiniteLaw (Fin 1 → A)) g
  rw [hu,FiniteLaw.map_map] at hc
  rw [FiniteLaw.map_map] at ha
  have hh := FiniteLaw.totalVariation_triangle
    ((FiniteLaw.uniform : FiniteLaw (StarModel.Matches rowSupport w)).map f)
    (κ.map (g ∘ (fun z j => (ConditionalStar.branch j z).val e))) FiniteLaw.uniform
  change _ ≤ 2*η
  exact hh.trans (by dsimp only [g,f,Function.comp_def] at *; linarith)

end IncidenceTemplate
end HyperbolicObstruction
end
end

section

end
end

end OAI
