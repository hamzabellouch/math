import OAI.NumberTheory.TwoPoint.Bounds.PatternHarmonicSum
import OAI.NumberTheory.TwoPoint.Bounds.SplitBadWordSum

namespace OAI

/-! Sum each column in its own prime pool after fixing the common pattern code. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

abbrev ColumnPrimeAssignment (J R : ℕ) (P : Fin J → Finset ℕ) :=
  (j : Fin J) → Fin R → P j

noncomputable def columnReciprocalWeight {J R : ℕ} {P : Fin J → Finset ℕ}
    (w : ColumnPrimeAssignment J R P) : ℝ :=
  ∏ j, ∏ p ∈ univ.image (w j), (p.val : ℝ)⁻¹

lemma columnReciprocalWeight_nonneg {J R : ℕ} {P : Fin J → Finset ℕ}
    (w : ColumnPrimeAssignment J R P) : 0 ≤ columnReciprocalWeight w := by
  unfold columnReciprocalWeight
  positivity

theorem same_column_patterns_reciprocal_sum {J R : ℕ} (P : Fin J → Finset ℕ)
    (F : Finset (ColumnPrimeAssignment J R P)) (template : ColumnPrimeAssignment J R P)
    (hpattern : ∀ w ∈ F, ∀ j i k, w j i = w j k ↔ template j i = template j k) :
    (∑ w ∈ F, columnReciprocalWeight w) ≤
      ∏ j, primeHarmonicMass (P j) ^ (univ.image (template j)).card := by
  let C (j : Fin J) := univ.image (template j)
  let rep (j : Fin J) (c : C j) : Fin R := Classical.choose (mem_image.mp c.property)
  have hrep (j : Fin J) (c : C j) : template j (rep j c) = c.val :=
    (Classical.choose_spec (mem_image.mp c.property)).2
  let classify (j : Fin J) (i : Fin R) : C j :=
    ⟨template j i, mem_image.mpr ⟨i, mem_univ _, rfl⟩⟩
  have hconstant (w : ColumnPrimeAssignment J R P) (hw : w ∈ F) (j : Fin J) (i : Fin R) :
      w j i = w j (rep j (classify j i)) :=
    (hpattern w hw j i _).mpr (hrep j (classify j i)).symm
  let encode (w : ColumnPrimeAssignment J R P) : (j : Fin J) → C j → P j :=
    fun j c => w j (rep j c)
  have hinj : Set.InjOn encode F := by
    intro w hw v hv he
    funext j i
    exact (hconstant w hw j i).trans
      ((congrFun (congrFun he j) (classify j i)).trans (hconstant v hv j i).symm)
  have hweight (w : ColumnPrimeAssignment J R P) (hw : w ∈ F) :
      columnReciprocalWeight w = ∏ j, ∏ c : C j, ((encode w j c).val : ℝ)⁻¹ := by
    apply prod_congr rfl
    intro j _
    have himage : univ.image (fun c : C j => w j (rep j c)) = univ.image (w j) := by
      ext p
      constructor
      · rintro hp
        obtain ⟨c, _, rfl⟩ := mem_image.mp hp
        exact mem_image.mpr ⟨rep j c, mem_univ _, rfl⟩
      · rintro hp
        obtain ⟨i, _, rfl⟩ := mem_image.mp hp
        exact mem_image.mpr ⟨classify j i, mem_univ _, (hconstant w hw j i).symm⟩
    rw [← himage, prod_image]
    intro c _ d _ hcd
    apply Subtype.ext
    exact (hrep j c).symm.trans (((hpattern w hw j _ _).mp hcd).trans (hrep j d))
  calc
    _ = ∑ z ∈ F.image encode, ∏ j, ∏ c : C j, ((z j c).val : ℝ)⁻¹ := by
      rw [sum_image hinj]
      exact sum_congr rfl hweight
    _ ≤ ∑ z : (j : Fin J) → C j → P j, ∏ j, ∏ c : C j, ((z j c).val : ℝ)⁻¹ := by
      apply sum_le_sum_of_subset_of_nonneg (subset_univ _)
      intro z _ _
      positivity
    _ = ∏ j, ∑ z : C j → P j, ∏ c, ((z c).val : ℝ)⁻¹ := by rw [Fintype.prod_sum]
    _ = _ := by
      apply prod_congr rfl
      intro j _
      simpa only [Fintype.card_coe, C] using sum_reciprocal_assignments (ι := C j) (P j)

/-- A code covers the joint pattern, but the numerical prime sums retain
the separate harmonic mass of each column. There is no factor from the
number of columns in the base of the power. -/
theorem covered_column_patterns_reciprocal_sum {J R : ℕ} {Code : Type*} [Fintype Code]
    (P : Fin J → Finset ℕ) (F : Finset (ColumnPrimeAssignment J R P))
    (decode : Code → Fin J → Fin R → Fin R → Bool) (A : ℝ) (M : ℕ)
    (hA : 1 ≤ A) (hmass : ∀ j, primeHarmonicMass (P j) ≤ A)
    (hlabels : ∀ w ∈ F, (∑ j, (univ.image (w j)).card) ≤ M)
    (hcover : ∀ w ∈ F, ∃ c, ∀ j i k, decode c j i k = decide (w j i = w j k)) :
    (∑ w ∈ F, columnReciprocalWeight w) ≤ (Fintype.card Code : ℝ) * A ^ M := by
  let fiber (c : Code) := F.filter (fun w => ∀ j i k, decode c j i k = decide (w j i = w j k))
  have hsum : (∑ w ∈ F, columnReciprocalWeight w) ≤
      ∑ c, ∑ w ∈ fiber c, columnReciprocalWeight w := by
    calc
      _ ≤ ∑ w ∈ F, ∑ c, if ∀ j i k, decode c j i k = decide (w j i = w j k)
          then columnReciprocalWeight w else 0 := by
        apply sum_le_sum
        intro w hw
        obtain ⟨c, hc⟩ := hcover w hw
        exact le_trans (by simp only [ite_eq_left hc]; exact le_rfl)
          (single_le_sum (s := (univ : Finset Code))
            (f := fun d => if ∀ j i k, decode d j i k = decide (w j i = w j k)
              then columnReciprocalWeight w else 0)
            (fun d _ => ite_nonneg (columnReciprocalWeight_nonneg w) le_rfl) (mem_univ c))
      _ = _ := by rw [sum_comm]; simp only [fiber, sum_filter]
  have hfiber (c : Code) : (∑ w ∈ fiber c, columnReciprocalWeight w) ≤ A ^ M := by
    by_cases he : (fiber c).Nonempty
    · obtain ⟨v, hv⟩ := he
      have hp : ∀ w ∈ fiber c, ∀ j i k, w j i = w j k ↔ v j i = v j k := by
        intro w hw j i k
        exact decide_eq_decide.mp (((mem_filter.mp hw).2 j i k).symm.trans
          ((mem_filter.mp hv).2 j i k))
      apply (same_column_patterns_reciprocal_sum P (fiber c) v hp).trans
      calc
        _ ≤ ∏ j, A ^ (univ.image (v j)).card := by
          apply prod_le_prod₀
          · intro j _
            exact pow_nonneg (by unfold primeHarmonicMass; positivity) _
          · intro j _
            exact pow_le_pow_left₀ (by unfold primeHarmonicMass; positivity) (hmass j) _
        _ = A ^ (∑ j, (univ.image (v j)).card) := prod_pow_eq_pow_sum _ _ _
        _ ≤ A ^ M := pow_le_pow_right₀ hA (hlabels v (mem_filter.mp hv).1)
    · simp only [not_nonempty_iff_eq_empty.mp he, sum_empty]
      positivity
  exact hsum.trans (by
    calc
      _ ≤ ∑ _c : Code, A ^ M := sum_le_sum (fun c _ => hfiber c)
      _ = _ := by simp)

end TwoPointCorrelations

end OAI
