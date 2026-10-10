import OAI.Analysis.Pureness.GroupAlgebra.FreeGroupFiniteSeparation
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Filter.Finite
import Mathlib.Basic.Countable.Basic

namespace OAI
noncomputable section
namespace CuntzPureness
open Filter
variable (G : Type*) [Group G] [Countable G] [Group.ResiduallyFinite G]

theorem exists_separating_normal_sequence :
    ∃ H : ℕ → FiniteIndexNormalSubgroup G, Antitone H ∧
      ∀ g : G, g ≠ 1 → ∀ᶠ n in atTop, g ∉ H n := by
  classical
  obtain ⟨e,he⟩ := exists_surjective_nat G
  have hs (g : G) : ∃ H : FiniteIndexNormalSubgroup G, g ≠ 1 → g ∉ H := by
    by_cases hg : g=1
    · exact ⟨FiniteIndexNormalSubgroup.ofSubgroup ⊤,fun h => False.elim (h hg)⟩
    · obtain ⟨H,hH⟩ := Group.exists_finiteIndexNormalSubgroup_notMem g hg
      exact ⟨H,fun _ => hH⟩
  choose K hK using hs
  let H : ℕ → FiniteIndexNormalSubgroup G := fun n =>
    Nat.rec (K (e 0)) (fun n H => H ⊓ K (e (n+1))) n
  have hmono : Antitone H := antitone_nat_of_succ_le (fun n => inf_le_left)
  have hle (n : ℕ) : H n ≤ K (e n) := by
    cases n with
    | zero => exact le_rfl
    | succ n => exact inf_le_right
  refine ⟨H,hmono,fun g hg => ?_⟩
  obtain ⟨k,hk⟩ := he g
  filter_upwards [eventually_ge_atTop k] with n hn
  intro hgn
  have hh := hle k ((hmono hn) hgn)
  rw [hk] at hh
  exact hK g hg hh

def separatingNormalSequence : ℕ → FiniteIndexNormalSubgroup G :=
  Classical.choose (exists_separating_normal_sequence G)

lemma separatingNormalSequence_antitone : Antitone (separatingNormalSequence G) :=
  (Classical.choose_spec (exists_separating_normal_sequence G)).1

lemma separatingNormalSequence_eventually (g : G) (hg : g ≠ 1) :
    ∀ᶠ n in atTop, g ∉ separatingNormalSequence G n :=
  (Classical.choose_spec (exists_separating_normal_sequence G)).2 g hg

abbrev SeparatingFiniteQuotient (n : ℕ) := G ⧸ (separatingNormalSequence G n).toSubgroup

def separatingQuotientMap (n : ℕ) : G →* SeparatingFiniteQuotient G n :=
  QuotientGroup.mk' _

instance separatingFiniteQuotient_finite (n : ℕ) : Finite (SeparatingFiniteQuotient G n) :=
  inferInstanceAs (Finite (G ⧸ (separatingNormalSequence G n).toSubgroup))

lemma separatingQuotientMap_eventually_ne (g h : G) (hgh : g ≠ h) :
    ∀ᶠ n in atTop, separatingQuotientMap G n g ≠ separatingQuotientMap G n h := by
  have hne : g⁻¹*h ≠ 1 := fun hh => hgh (inv_mul_eq_one.mp hh)
  filter_upwards [separatingNormalSequence_eventually G (g⁻¹*h) hne] with n hn
  intro he
  apply hn
  apply (QuotientGroup.eq_one_iff (N := (separatingNormalSequence G n).toSubgroup) (g⁻¹*h)).mp
  change separatingQuotientMap G n (g⁻¹*h) = 1
  rw [map_mul, map_inv, he, inv_mul_cancel]

theorem separatingQuotientMap_eventually_injOn (S : Finset G) :
    ∀ᶠ n in atTop, Set.InjOn (separatingQuotientMap G n) (S : Set G) := by
  classical
  have hp (g h : G) : ∀ᶠ n in atTop,
      separatingQuotientMap G n g = separatingQuotientMap G n h → g=h := by
    by_cases he : g=h
    · exact Eventually.of_forall (fun _ _ => he)
    · exact (separatingQuotientMap_eventually_ne G g h he).mono (fun _ hneq heq => False.elim (hneq heq))
  have h := (S.eventually_all).2 (fun g _ => (S.eventually_all).2 (fun h _ => hp g h))
  filter_upwards [h] with n hn
  exact fun g hg h hh heq => hn g hg h hh heq

theorem freeGroup_nat_finite_quotients :
    ∃ H : ℕ → FiniteIndexNormalSubgroup (FreeGroup ℕ), Antitone H ∧
      ∀ g : FreeGroup ℕ, g ≠ 1 → ∀ᶠ n in atTop, g ∉ H n := by
  let : Group.ResiduallyFinite (FreeGroup ℕ) := freeGroup_residuallyFinite
  let : Countable (FreeGroup ℕ) := inferInstanceAs (Countable (Quot (@FreeGroup.Red.Step ℕ)))
  exact exists_separating_normal_sequence (FreeGroup ℕ)
end CuntzPureness

end

end OAI
