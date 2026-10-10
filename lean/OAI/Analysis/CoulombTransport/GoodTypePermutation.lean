import OAI.Analysis.CoulombTransport.CenterCertificate
import OAI.Analysis.CoulombTransport.TriplePermutation

namespace OAI

noncomputable section
open scoped ENNReal

namespace Problem356.GoodTypePermutation

/-- A supporting certificate on an ordered component product, with the
one-way contact localization needed for excluding deterministic optimizers. -/
def LocalTypeCertificate (U : Fin 5 → Set E3) (v : Fin 5 → E3 → ℝ)
    (Contact : Triple → Prop) (i j k : Fin 5) : Prop :=
  ∀ x ∈ U i, ∀ y ∈ U j, ∀ z ∈ U k,
    ENNReal.ofReal (v i x + v j y + v k z) ≤ coulombCost (x, (y, z)) ∧
    (ENNReal.ofReal (v i x + v j y + v k z) = coulombCost (x, (y, z)) →
      Contact (x, (y, z)))

variable {U : Fin 5 → Set E3} {v : Fin 5 → E3 → ℝ}
  {Contact : Triple → Prop}

/-- Contact localization is transported along a swap of the first two entries. -/
theorem LocalTypeCertificate.swap_first {i j k : Fin 5}
    (h : LocalTypeCertificate U v Contact i j k)
    (hperm : ∀ {x y z a b c : E3}, List.Perm [x, y, z] [a, b, c] →
      Contact (x, (y, z)) → Contact (a, (b, c))) :
    LocalTypeCertificate U v Contact j i k := by
  intro x hx y hy z hz
  have hc := h y hy x hx z hz
  rw [add_comm (v i y) (v j x), TriplePermutation.cost_swap_first y x z] at hc
  exact ⟨hc.1, fun heq => hperm (List.Perm.swap x y [z]) (hc.2 heq)⟩

/-- Contact localization is transported along a swap of the last two entries. -/
theorem LocalTypeCertificate.swap_last {i j k : Fin 5}
    (h : LocalTypeCertificate U v Contact i j k)
    (hperm : ∀ {x y z a b c : E3}, List.Perm [x, y, z] [a, b, c] →
      Contact (x, (y, z)) → Contact (a, (b, c))) :
    LocalTypeCertificate U v Contact i k j := by
  intro x hx y hy z hz
  have hc := h x hx z hz y hy
  have hsum : v i x + v j z + v k y = v i x + v k y + v j z := by ac_rfl
  rw [hsum, TriplePermutation.cost_swap_last x z y] at hc
  exact ⟨hc.1, fun heq => hperm ((List.Perm.swap y z []).cons x) (hc.2 heq)⟩

/-- The two canonical component orders supply every good component type.
No converse from the abstract contact predicate to equality is assumed. -/
theorem certificate_of_good
    (hperm : ∀ {x y z a b c : E3}, List.Perm [x, y, z] [a, b, c] →
      Contact (x, (y, z)) → Contact (a, (b, c)))
    (h012 : LocalTypeCertificate U v Contact 0 1 2)
    (h034 : LocalTypeCertificate U v Contact 0 3 4)
    (i j k : Fin 5) (hgood : CenterCertificate.Good i j k) :
    LocalTypeCertificate U v Contact i j k := by
  have h102 := h012.swap_first hperm
  have h021 := h012.swap_last hperm
  have h120 := h102.swap_last hperm
  have h201 := h021.swap_first hperm
  have h210 := h201.swap_last hperm
  have h304 := h034.swap_first hperm
  have h043 := h034.swap_last hperm
  have h340 := h304.swap_last hperm
  have h403 := h043.swap_first hperm
  have h430 := h403.swap_last hperm
  fin_cases i <;> fin_cases j <;> fin_cases k
  all_goals first | assumption | (exfalso; revert hgood; unfold CenterCertificate.Good; decide)

/-- Neighborhood form directly usable by a finite component gluing argument. -/
theorem eventually_certificate_of_good
    (p : Fin 5 → E3) (hU : ∀ i, U i ∈ nhds (p i))
    (hperm : ∀ {x y z a b c : E3}, List.Perm [x, y, z] [a, b, c] →
      Contact (x, (y, z)) → Contact (a, (b, c)))
    (h012 : LocalTypeCertificate U v Contact 0 1 2)
    (h034 : LocalTypeCertificate U v Contact 0 3 4)
    (i j k : Fin 5) (hgood : CenterCertificate.Good i j k) :
    ∀ᶠ t : Triple in nhds (p i, (p j, p k)),
      ENNReal.ofReal (v i t.1 + v j t.2.1 + v k t.2.2) ≤ coulombCost t ∧
      (ENNReal.ofReal (v i t.1 + v j t.2.1 + v k t.2.2) = coulombCost t →
        Contact t) := by
  have h1 : ∀ᶠ t : Triple in nhds (p i, (p j, p k)), t.1 ∈ U i :=
    (continuous_fst.tendsto _).eventually (hU i)
  have h2 : ∀ᶠ t : Triple in nhds (p i, (p j, p k)), t.2.1 ∈ U j :=
    ((continuous_fst.comp continuous_snd).tendsto _).eventually (hU j)
  have h3 : ∀ᶠ t : Triple in nhds (p i, (p j, p k)), t.2.2 ∈ U k :=
    ((continuous_snd.comp continuous_snd).tendsto _).eventually (hU k)
  filter_upwards [h1, h2, h3] with t ht1 ht2 ht3
  exact certificate_of_good hperm h012 h034 i j k hgood
    t.1 ht1 t.2.1 ht2 t.2.2 ht3

end Problem356.GoodTypePermutation

end

end OAI
