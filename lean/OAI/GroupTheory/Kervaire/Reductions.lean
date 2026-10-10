import OAI.GroupTheory.Kervaire.Model

namespace OAI

namespace Kervaire

universe u

/-- The main theorem is exactly the trivial-intersection claim below. -/
theorem coefficient_injective_iff {A : Type u} [Group A] (w : WordGroup A) :
    Function.Injective (coefficientMap w) ↔
      ∀ a : A, Monoid.Coprod.inl a ∈ relatorClosure w → a = 1 := by
  rw [← MonoidHom.ker_eq_bot_iff]
  rw [eq_bot_iff]
  constructor
  · intro h a ha
    apply h
    change QuotientGroup.mk _ = 1
    exact (QuotientGroup.eq_one_iff _).mpr ha
  · intro h a ha
    change a = 1
    apply h a
    change (QuotientGroup.mk (Monoid.Coprod.inl a) : RelatorQuotient w) = 1 at ha
    exact (QuotientGroup.eq_one_iff _).mp ha

def exponentMod {A : Type u} [Group A] (w : WordGroup A) :
    WordGroup A →* Multiplicative (ZMod (exponentSum w).natAbs) :=
  (Int.castAddHom (ZMod (exponentSum w).natAbs)).toMultiplicative.comp Monoid.Coprod.snd

@[simp] theorem exponentMod_relator {A : Type u} [Group A] (w : WordGroup A) :
    exponentMod w w = 1 := by
  change ((exponentSum w : ℤ) : ZMod (exponentSum w).natAbs) = 0
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr (Int.natAbs_dvd.mpr (dvd_refl _))

/-- The quotient always surjects onto the expected cyclic exponent quotient. -/
def cyclicQuotientMap {A : Type u} [Group A] (w : WordGroup A) :
    RelatorQuotient w →* Multiplicative (ZMod (exponentSum w).natAbs) :=
  QuotientGroup.lift (relatorClosure w) (exponentMod w) (by
    apply Subgroup.normalClosure_le_normal
    intro x hx
    have hxw : x = w := Set.mem_singleton_iff.mp hx
    subst x
    exact exponentMod_relator w)

@[simp] theorem cyclicQuotientMap_generator {A : Type u} [Group A] (w : WordGroup A) :
    cyclicQuotientMap w (QuotientGroup.mk (Monoid.Coprod.inr (Multiplicative.ofAdd (1 : ℤ)))) =
      Multiplicative.ofAdd (1 : ZMod (exponentSum w).natAbs) := by
  change exponentMod w (Monoid.Coprod.inr (Multiplicative.ofAdd (1 : ℤ))) = _
  simp [exponentMod]

theorem quotient_nontrivial_of_not_unimodular {A : Type u} [Group A] (w : WordGroup A)
    (hw : ¬ Unimodular w) : Nontrivial (RelatorQuotient w) := by
  have hn : (exponentSum w).natAbs ≠ 1 := by
    intro h
    apply hw
    simpa [Unimodular] using Int.natAbs_eq_iff.mp h
  refine ⟨⟨QuotientGroup.mk (Monoid.Coprod.inr (Multiplicative.ofAdd (1 : ℤ))), 1, ?_⟩⟩
  intro h
  have hh := congrArg (cyclicQuotientMap w) h
  rw [cyclicQuotientMap_generator, (cyclicQuotientMap w).map_one] at hh
  exact hn (ZMod.one_eq_zero_iff.mp (congrArg Multiplicative.toAdd hh))

end Kervaire

end OAI
