import OAI.NumberTheory.Ostmann.Construction.OffDiagonalParentFrame

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Construction

theorem initial_seed_types_pos (m k : ℕ) :
    ∀ q ∈ Template.initial m k, ∀ j, q.role = .compensation j → 0 < j := by
  intro q hq j hrole
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hq
  change (Template.initialRoles m k)[i] = .compensation j at hrole
  have hi : SlotRole.compensation j ∈ Template.initialRoles m k :=
    hrole ▸ List.getElem_mem i.isLt
  simp only [Template.initialRoles,List.mem_append,List.mem_replicate,List.mem_flatMap,
    List.mem_range] at hi
  rcases hi with (hb | ht) | ⟨a,ha,han,haj⟩
  · cases hb.2
  · cases ht.2
  · have hj : j = a+1 := by simpa only [SlotRole.compensation.injEq] using haj
    omega

theorem canonicalFrame_joined_valid_of_actualCoefficient_ne_zero
    (sources : SourceFamily) (seed : List SourceSlot) (V : ℕ → ℕ) (giant : PrimeSource)
    (X G : ℝ) (g : (q : ℕ) → ZMod q → ℂ) (bins : List ℕ → State → ℝ)
    (outside : List ℕ) (l p : ℕ)
    (x y : RemainingSample sources (Template.remainder (l+1) (Template.current seed l)) giant)
    (s : ℤ) (v w : AllowedFrequency V l)
    (u : SourceAssignment sources (Template.extracted (l+1) (Template.current seed l)))
    (hseed : ∀ q ∈ seed, ∀ j, q.role = .compensation j → 0 < j)
    (hp : 0 < p) (hs : s ≠ 0) (hsV : s.natAbs ≤ V (l+1))
    (hgiants : ∀ j ≤ l+1, V j < x.1.val ∧ V j < y.1.val)
    (hlarge : ∀ q ∈ assignedSlots sources (Template.remainder (l+1) (Template.current seed l)) x.2,
      V (l+1) < q.value)
    (hx : actualCoefficient sources seed V X G g bins outside l
      (remainingState sources (Template.current seed l) (l+1) giant p u x v.val) ≠ 0)
    (hy : actualCoefficient sources seed V X G g bins outside l
      (remainingState sources (Template.current seed l) (l+1) giant p u y w.val) ≠ 0)
    (heq : joinedNumerator sources (Template.remainder (l+1) (Template.current seed l)) giant x y v.val w.val =
      s * ((assignedSlots sources (Template.extracted (l+1) (Template.current seed l)) u).map SmallSlot.value).prod * (p : ℤ)) :
    (canonicalFrame sources seed V l
      (joinedRemainingState sources (Template.remainder (l+1) (Template.current seed l)) giant x y s)
      v w u).Valid V outside l := by
  apply canonicalFrame_joined_valid_of_old_coprime sources seed V giant outside l p x y s v w u
    hseed hp hs hsV (hgiants (l+1) le_rfl) hlarge _ _ heq
  · exact (actualCoefficient_root_support sources seed V X G g bins outside l _ hx).2.2.2.1
  · exact (actualCoefficient_root_support sources seed V X G g bins outside l _ hy).2.2.2.1

theorem canonicalFrame_joined_valid_of_remainingIntegrand_ne_zero
    (d : Decomposition) (P : Finset ℕ) (sources : SourceFamily) (seed : List SourceSlot)
    (V : ℕ → ℕ) (giant : PrimeSource) (X G : ℝ) (bins : List ℕ → State → ℝ)
    (outside : List ℕ) (l p : ℕ)
    (x y : RemainingSample sources (Template.remainder (l+1) (Template.current seed l)) giant)
    (s : ℤ) (v w : AllowedFrequency V l)
    (u : SourceAssignment sources (Template.extracted (l+1) (Template.current seed l)))
    (hseed : ∀ q ∈ seed, ∀ j, q.role = .compensation j → 0 < j)
    (hp : 0 < p) (hs : s ≠ 0) (hsV : s.natAbs ≤ V (l+1))
    (hgiants : ∀ j ≤ l+1, V j < x.1.val ∧ V j < y.1.val)
    (hlarge : ∀ q ∈ assignedSlots sources (Template.remainder (l+1) (Template.current seed l)) x.2,
      V (l+1) < q.value)
    (hx : remainingIntegrand d P sources seed V giant X G bins outside l p u x v ≠ 0)
    (hy : remainingIntegrand d P sources seed V giant X G bins outside l p u y w ≠ 0)
    (heq : joinedNumerator sources (Template.remainder (l+1) (Template.current seed l)) giant x y v.val w.val =
      s * ((assignedSlots sources (Template.extracted (l+1) (Template.current seed l)) u).map SmallSlot.value).prod * (p : ℤ)) :
    (canonicalFrame sources seed V l
      (joinedRemainingState sources (Template.remainder (l+1) (Template.current seed l)) giant x y s)
      v w u).Valid V outside l := by
  apply canonicalFrame_joined_valid_of_actualCoefficient_ne_zero sources seed V giant X G
    (residueTransform d) bins outside l p x y s v w u hseed hp hs hsV hgiants hlarge
      (mul_ne_zero_iff.mp hx).2 (mul_ne_zero_iff.mp hy).2 heq

end Ostmann.Construction

end

end OAI
