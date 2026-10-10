import OAI.NumberTheory.Ostmann.Characters.SymbolicHistoryResidues
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedCancellationSubstitution

namespace OAI

noncomputable section
namespace Ostmann.Characters.TemplateOneSidedCancellation
open SymbolicHistory TemplateSupportRemoval
variable {ι : Type*}

structure ResidueGuard (ι : Type*) where
  expression : Expr ι
  frequency : ℕ

def ResidueGuard.Valid (g : ResidueGuard ι) : Prop :=
  g.expression.Valid ∧ 0 < g.frequency

def ResidueGuard.holds (g : ResidueGuard ι) (a : ι → ℤ) : Prop :=
  g.expression.IntegralAt a ∧ IsUnit (g.expression.integerEval a : ZMod g.frequency)

def ResidueGuard.modulus (g : ResidueGuard ι) : ℤ :=
  g.expression.supportModulus*(g.expression.denominator*(g.frequency:ℤ))

theorem ResidueGuard.modulus_ne_zero (g : ResidueGuard ι) (hg : g.Valid) :
    g.modulus ≠ 0 := by
  exact mul_ne_zero (g.expression.supportModulus_ne_zero hg.1)
    (mul_ne_zero (g.expression.denominator_ne_zero hg.1) (by exact_mod_cast hg.2.ne'))

theorem ResidueGuard.holds_iff_of_modEq (g : ResidueGuard ι) (hg : g.Valid)
    (a b : ι → ℤ) (h : ∀ i, a i ≡ b i [ZMOD g.modulus]) :
    g.holds a ↔ g.holds b := by
  have hi := g.expression.integralAt_iff_of_modEq hg.1 a b
    (fun i => (h i).of_dvd (dvd_mul_right _ _))
  constructor
  · intro ha
    have hb := hi.mp ha.1
    have he := g.expression.integerEval_modEq a b g.frequency hg.1 ha.1 hb
      (fun i => (h i).of_dvd (dvd_mul_left _ _))
    refine ⟨hb,?_⟩
    rw [← (ZMod.intCast_eq_intCast_iff _ _ _).mpr he]
    exact ha.2
  · intro hb
    have ha := hi.mpr hb.1
    have he := g.expression.integerEval_modEq a b g.frequency hg.1 ha hb.1
      (fun i => (h i).of_dvd (dvd_mul_left _ _))
    refine ⟨ha,?_⟩
    rw [(ZMod.intCast_eq_intCast_iff _ _ _).mpr he]
    exact hb.2

def residueModulus (g : List (ResidueGuard ι)) : ℤ := (g.map ResidueGuard.modulus).prod

theorem residueModulus_ne_zero (g : List (ResidueGuard ι)) (hg : ∀ q ∈ g, q.Valid) :
    residueModulus g ≠ 0 := by
  apply List.prod_ne_zero
  intro hm
  obtain ⟨q,hq,heq⟩ := List.mem_map.mp hm
  exact q.modulus_ne_zero (hg q hq) heq

theorem residueGuard_modulus_dvd {g : List (ResidueGuard ι)} {q : ResidueGuard ι} (hq : q ∈ g) :
    q.modulus ∣ residueModulus g := List.dvd_prod (List.mem_map.mpr ⟨q,hq,rfl⟩)

theorem residueGuards_iff_of_modEq (g : List (ResidueGuard ι))
    (hg : ∀ q ∈ g, q.Valid) (a b : ι → ℤ)
    (h : ∀ i, a i ≡ b i [ZMOD residueModulus g]) :
    (∀ q ∈ g, q.holds a) ↔ (∀ q ∈ g, q.holds b) := by
  apply forall_congr'
  intro q
  apply forall_congr'
  intro hq
  exact q.holds_iff_of_modEq (hg q hq) a b
    (fun i => (h i).of_dvd (residueGuard_modulus_dvd hq))

theorem residueGuards_progression [DecidableEq ι] (g : List (ResidueGuard ι))
    (hg : ∀ q ∈ g, q.Valid) (i : ι) (x : Other i → ℤ) (r n : ℤ) :
    (∀ q ∈ g, q.holds (insertCoordinate i x (residueModulus g*n+r))) ↔
      (∀ q ∈ g, q.holds (insertCoordinate i x r)) := by
  apply residueGuards_iff_of_modEq g hg
  intro j
  by_cases hj : j=i
  · subst j
    simp only [insertCoordinate_self]
    apply Int.modEq_iff_dvd.mpr
    exact ⟨-n,by ring⟩
  · simp only [insertCoordinate,hj,dite_false]
    exact Int.ModEq.refl _

end Ostmann.Characters.TemplateOneSidedCancellation

end

end OAI
