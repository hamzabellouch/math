import OAI.Analysis.GroupDeterminants.CyclicAverage

namespace OAI

universe uB uC uI

noncomputable section
open scoped BigOperators Pointwise

namespace SupportDraft
variable {B : Type uB} {C : Type uC} {I : Type uI} [CommGroup B] [Group C]
variable (coord : I → B →* C)

def SupportedOn (s : Set I) (a : MonoidAlgebra ℚ B) : Prop :=
  ∀ b, a.coeff b ≠ 0 → ∀ i, i ∉ s → coord i b = 1

lemma supportedOn_mono {s t : Set I} {a : MonoidAlgebra ℚ B}
    (ha : SupportedOn coord s a) (hst : s ⊆ t) : SupportedOn coord t a :=
  fun b hb i hi => ha b hb i (fun hs => hi (hst hs))

lemma supportedOn_single (s : Set I) (b : B) (q : ℚ)
    (hb : ∀ i, i ∉ s → coord i b = 1) : SupportedOn coord s (MonoidAlgebra.single b q) := by
  classical
  intro g hg i hi
  by_cases hgb : g = b
  · subst g; exact hb i hi
  · simp [MonoidAlgebra.coeff_single, Ne.symm hgb] at hg

lemma supportedOn_one (s : Set I) : SupportedOn coord s (1 : MonoidAlgebra ℚ B) := by
  rw [MonoidAlgebra.one_def]
  exact supportedOn_single coord s 1 1 (by simp)

lemma supportedOn_add {s : Set I} {a b : MonoidAlgebra ℚ B}
    (ha : SupportedOn coord s a) (hb : SupportedOn coord s b) : SupportedOn coord s (a + b) := by
  intro g hg i hi
  by_cases hga : a.coeff g = 0
  · apply hb g _ i hi
    simpa [hga] using hg
  · exact ha g hga i hi

lemma supportedOn_neg {s : Set I} {a : MonoidAlgebra ℚ B}
    (ha : SupportedOn coord s a) : SupportedOn coord s (-a) := by
  intro g hg i hi
  exact ha g (by simpa using hg) i hi

lemma supportedOn_sub {s : Set I} {a b : MonoidAlgebra ℚ B}
    (ha : SupportedOn coord s a) (hb : SupportedOn coord s b) : SupportedOn coord s (a - b) := by
  rw [sub_eq_add_neg]
  exact supportedOn_add coord ha (supportedOn_neg coord hb)

lemma supportedOn_smul {s : Set I} {a : MonoidAlgebra ℚ B}
    (ha : SupportedOn coord s a) (q : ℚ) : SupportedOn coord s (q • a) := by
  intro g hg i hi
  apply ha g _ i hi
  intro h
  apply hg
  simp [h]

lemma supportedOn_mul {s t : Set I} {a b : MonoidAlgebra ℚ B}
    (ha : SupportedOn coord s a) (hb : SupportedOn coord t b) :
    SupportedOn coord (s ∪ t) (a * b) := by
  classical
  intro g hg i hi
  have hm := MonoidAlgebra.support_coeff_mul_subset a b (Finsupp.mem_support_iff.mpr hg)
  obtain ⟨x, hx, y, hy, rfl⟩ := Finset.mem_mul.mp hm
  rw [map_mul, ha x (Finsupp.mem_support_iff.mp hx) i (fun h => hi (Or.inl h)),
    hb y (Finsupp.mem_support_iff.mp hy) i (fun h => hi (Or.inr h)), one_mul]

lemma coeff_one_mul_of_disjoint (hinj : ∀ b : B, (∀ i, coord i b = 1) → b = 1)
    {s t : Set I} (hst : Disjoint s t) (a b : MonoidAlgebra ℚ B)
    (ha : SupportedOn coord s a) (hb : SupportedOn coord t b) :
    (a * b).coeff 1 = a.coeff 1 * b.coeff 1 := by
  classical
  rw [MonoidAlgebra.coeff_mul_apply_left]
  simp only [mul_one]
  rw [a.coeff.sum_eq_single 1]
  · simp
  · intro g hg hgne
    by_cases hbg : b.coeff g⁻¹ = 0
    · simp [hbg]
    · exfalso
      apply hgne
      apply hinj
      intro i
      by_cases his : i ∈ s
      · have hit : i ∉ t := fun h => Set.disjoint_left.mp hst his h
        have hh := hb g⁻¹ hbg i hit
        simpa using hh
      · exact ha g hg i his
  · intro _
    simp

lemma supportedOn_prod (s : Finset I) (a : I → MonoidAlgebra ℚ B)
    (ha : ∀ i ∈ s, SupportedOn coord {i} (a i)) : SupportedOn coord (s : Set I) (∏ i ∈ s, a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using supportedOn_one coord ∅
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi]
    simpa using supportedOn_mul coord (ha i (by simp)) (ih (by aesop))

lemma coeff_one_prod (hinj : ∀ b : B, (∀ i, coord i b = 1) → b = 1)
    (s : Finset I) (a : I → MonoidAlgebra ℚ B)
    (ha : ∀ i ∈ s, SupportedOn coord {i} (a i)) :
    (∏ i ∈ s, a i).coeff 1 = ∏ i ∈ s, (a i).coeff 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi,
      coeff_one_mul_of_disjoint coord hinj (by simpa using hi) _ _ (ha i (by simp))
        (supportedOn_prod coord s a (by aesop)), ih (by aesop)]

end SupportDraft

end

end OAI
