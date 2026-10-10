import OAI.NumberTheory.TwoPoint.Bounds.OccurrenceCounts
import OAI.NumberTheory.TwoPoint.Bounds.PrimeReciprocalLaw

namespace OAI

/-! Summing numerical prime labels after the equality pattern has been fixed. -/

namespace TwoPointCorrelations

open Finset

variable {ι Λ P : Type*} [Fintype ι] [Fintype Λ] [Fintype P]
  [DecidableEq ι] [DecidableEq Λ] [DecidableEq P]

omit [Fintype ι] [DecidableEq ι] in
/-- Once every occurrence is recovered from its class representative,
only one numerical prime per class is summed. -/
lemma representative_weighted_sum (F : Finset (ι → P)) (classify : ι → Λ)
    (rep : Λ → ι) (a : P → ℝ) (ha : ∀ p, 0 ≤ a p)
    (hconstant : ∀ w ∈ F, ∀ i, w i = w (rep (classify i))) :
    (∑ w ∈ F, ∏ c, a (w (rep c))) ≤ (∑ p, a p) ^ Fintype.card Λ := by
  classical
  let encode : (ι → P) → (Λ → P) := fun w c => w (rep c)
  have hinj : Set.InjOn encode F := by
    intro w hw z hz he
    funext i
    exact (hconstant w hw i).trans ((congrFun he (classify i)).trans (hconstant z hz i).symm)
  calc
    _ = ∑ z ∈ F.image encode, ∏ c, a (z c) := by
      rw [sum_image hinj]
    _ ≤ ∑ z : Λ → P, ∏ c, a (z c) := by
      apply sum_le_sum_of_subset_of_nonneg (subset_univ _)
      intro z _ _
      exact prod_nonneg (fun c _ => ha (z c))
    _ = _ := by rw [← Fintype.prod_sum]; simp

omit [DecidableEq ι] in
/-- All words in one decoded equality-pattern fiber have the same bound,
even though the actual numerical primes vary from word to word. -/
theorem same_pattern_weighted_sum (F : Finset (ι → P)) (template : ι → P)
    (a : P → ℝ) (ha : ∀ p, 0 ≤ a p)
    (hpattern : ∀ w ∈ F, ∀ i j, w i = w j ↔ template i = template j) :
    (∑ w ∈ F, ∏ p ∈ univ.image w, a p) ≤
      (∑ p, a p) ^ (univ.image template).card := by
  classical
  let C := univ.image template
  let rep : C → ι := fun c => Classical.choose (mem_image.mp c.property)
  have hrep (c : C) : template (rep c) = c.val :=
    (Classical.choose_spec (mem_image.mp c.property)).2
  let classify : ι → C := fun i => ⟨template i, mem_image.mpr ⟨i, mem_univ _, rfl⟩⟩
  have hconstant (w : ι → P) (hw : w ∈ F) (i : ι) :
      w i = w (rep (classify i)) := by
    apply (hpattern w hw i (rep (classify i))).mpr
    exact (hrep (classify i)).symm
  have hweight (w : ι → P) (hw : w ∈ F) :
      (∏ p ∈ univ.image w, a p) = ∏ c : C, a (w (rep c)) := by
    have himage : (univ.image (fun c : C => w (rep c))) = univ.image w := by
      ext p
      constructor
      · rintro hp
        obtain ⟨c, _, rfl⟩ := mem_image.mp hp
        exact mem_image.mpr ⟨rep c, mem_univ _, rfl⟩
      · intro hp
        obtain ⟨i, _, rfl⟩ := mem_image.mp hp
        exact mem_image.mpr ⟨classify i, mem_univ _, (hconstant w hw i).symm⟩
    rw [← himage, prod_image]
    intro c _ d _ hcd
    apply Subtype.ext
    exact (hrep c).symm.trans (((hpattern w hw _ _).mp hcd).trans (hrep d))
  calc
    _ = ∑ w ∈ F, ∏ c : C, a (w (rep c)) := sum_congr rfl hweight
    _ ≤ (∑ p, a p) ^ Fintype.card C :=
      representative_weighted_sum F classify rep a ha hconstant
    _ = _ := by rw [Fintype.card_coe]

omit [DecidableEq ι] in
/-- Specialization to the reciprocal mass of an actual finite prime pool. -/
theorem same_pattern_reciprocal_sum (P : Finset ℕ) (F : Finset (ι → P))
    (template : ι → P)
    (hpattern : ∀ w ∈ F, ∀ i j, w i = w j ↔ template i = template j) :
    (∑ w ∈ F, ∏ p ∈ univ.image w, (p.val : ℝ)⁻¹) ≤
      (primeHarmonicMass P) ^ (univ.image template).card := by
  exact same_pattern_weighted_sum F template (fun p : P => (p.val : ℝ)⁻¹)
    (fun p => by positivity) hpattern

omit [DecidableEq ι] in
/-- Invalid codes contribute zero. For every valid fiber the reciprocal
sum costs one prime mass per observed label, independently of repetitions. -/
theorem covered_pattern_weighted_sum {C : Type*} [Fintype C]
    (F : Finset (ι → P)) (decode : C → ι → ι → Bool)
    (a : P → ℝ) (ha : ∀ p, 0 ≤ a p) (M : ℕ)
    (hV : 1 ≤ ∑ p, a p)
    (hlabels : ∀ w ∈ F, (univ.image w).card ≤ M)
    (hcover : ∀ w ∈ F, ∃ c, ∀ i j, decode c i j = decide (w i = w j)) :
    (∑ w ∈ F, ∏ p ∈ univ.image w, a p) ≤
      (Fintype.card C : ℝ) * (∑ p, a p) ^ M := by
  classical
  let mass (w : ι → P) : ℝ := ∏ p ∈ univ.image w, a p
  let fiber (c : C) := F.filter (fun w => ∀ i j, decode c i j = decide (w i = w j))
  have hmass (w : ι → P) : 0 ≤ mass w := prod_nonneg (fun p _ => ha p)
  have hsum : (∑ w ∈ F, mass w) ≤ ∑ c, ∑ w ∈ fiber c, mass w := by
    calc
      _ ≤ ∑ w ∈ F, ∑ c, if ∀ i j, decode c i j = decide (w i = w j) then mass w else 0 := by
        apply sum_le_sum
        intro w hw
        obtain ⟨c, hc⟩ := hcover w hw
        calc
          _ = if ∀ i j, decode c i j = decide (w i = w j) then mass w else 0 := by simp [hc]
          _ ≤ _ := single_le_sum (s := (univ : Finset C))
            (f := fun d : C => if ∀ i j, decode d i j = decide (w i = w j) then mass w else 0)
            (fun d _ => ite_nonneg (hmass w) le_rfl) (mem_univ c)
      _ = _ := by rw [sum_comm]; simp only [fiber, sum_filter]
  have hfiber (c : C) : (∑ w ∈ fiber c, mass w) ≤ (∑ p, a p) ^ M := by
    by_cases he : (fiber c).Nonempty
    · obtain ⟨v, hv⟩ := he
      have hvF : v ∈ F := (mem_filter.mp hv).1
      have hp : ∀ w ∈ fiber c, ∀ i j, w i = w j ↔ v i = v j := by
        intro w hw i j
        have heq := ((mem_filter.mp hw).2 i j).symm.trans ((mem_filter.mp hv).2 i j)
        exact decide_eq_decide.mp heq
      exact (same_pattern_weighted_sum (fiber c) v a ha hp).trans
        (pow_le_pow_right₀ hV (hlabels v hvF))
    · simp only [not_nonempty_iff_eq_empty.mp he, sum_empty]
      positivity
  calc
    _ ≤ _ := hsum
    _ ≤ ∑ _c : C, (∑ p, a p) ^ M := sum_le_sum (fun c _ => hfiber c)
    _ = _ := by simp

end TwoPointCorrelations

end OAI
