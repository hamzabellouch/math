import Mathlib
import OAI.Combinatorics.Chromatic.QuantumTorus.InfinityExpansionFaithful
import OAI.Combinatorics.Chromatic.GradedAlgebra.LaurentRegradeFinite

namespace OAI

section
namespace ElementaryPositivity.RationalFiber
open QuantumTorus PowerSeries
noncomputable section
variable {K M : Type*} [Field K] [AddCommGroup M]
variable (v : Kˣ) (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (k : M →+ ℤ) (p : M) (hp : k p=1)
local instance infinityLaurentFiniteRing : Ring (Torus v Ω) := Torus.instRing v Ω
local instance infinityLaurentFiniteAddCommMonoid : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
local instance infinityLaurentFiniteAddGroup : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
local instance infinityLaurentFiniteNonUnitalSemiring : NonUnitalSemiring (Torus v Ω) := (Torus.instRing v Ω).toNonUnitalSemiring
local instance infinityLaurentFiniteNonUnitalNonAssocSemiring : NonUnitalNonAssocSemiring (Torus v Ω) :=
  (Torus.instRing v Ω).toNonUnitalNonAssocSemiring

include hp in
lemma expandFiberInfinity_off_diagonal
    (f : FiberTorus v (complementOmega k Ω) (complementAlpha k p Ω))
    (z : ℤ) (m : M) (h : z≠-k m) :
    ((expandFiberInfinity v Ω hΩ k p f).coeff z) m=0 := by
  induction f using Finsupp.induction_linear with
  | zero=>simp
  | add f g hf hg=>simp only [map_add,HahnSeries.coeff_add,Finsupp.add_apply,hf,hg,add_zero]
  | single l a=>
    change ((expandFiberInfinity v Ω hΩ k p (FiberTorus.monomial v _ _ l a)).coeff z) m=0
    rw [expandFiberInfinity_monomial_coeff v Ω hΩ k p l a z]
    apply Finsupp.single_eq_of_ne
    intro hm
    apply h
    have H:=congrArg k hm
    have hl : k (l:M)=0 := l.property
    simp only [map_add,map_zsmul,map_neg,hp,hl,smul_eq_mul,add_zero,mul_neg,mul_one] at H
    omega

lemma expandFiberInfinity_embed_coeff (f : Torus v Ω) (z : ℤ) (m : M) :
    ((expandFiberInfinity v Ω hΩ k p (embed v Ω hΩ k p hp f)).coeff z) m=
      if z=-k m then f m else 0 := by
  by_cases hz : z=-k m
  · rw [ite_eq_left hz,hz,expandFiberInfinity_read v Ω hΩ k p hp]
    exact readFiberInfinity_embedAdd v Ω k p hp f m
  · rw [ite_eq_right hz]
    exact expandFiberInfinity_off_diagonal v Ω hΩ k p hp _ z m hz

lemma expandInfinity_rationalRegrade (δ : M →+ ℤ) (B D : ℕ)
    (f : PowerSeries (Torus v Ω)) (hf : LaurentBounded v Ω δ (-k) B f)
    (hg : RegradeBound v Ω δ D f) :
    PowerSeries.map (expandFiberInfinity v Ω hΩ k p)
      (rationalRegrade v Ω hΩ k p hp δ D f)=laurentRegrade v Ω δ (-k) B f hf := by
  apply PowerSeries.ext
  intro d
  apply HahnSeries.ext
  funext z
  ext m
  rw [coeff_map,rationalRegrade,coeff_map,expandFiberInfinity_embed_coeff,
    laurentRegrade_finite_read v Ω δ (-k) B D hf hg]
  rfl
end
end ElementaryPositivity.RationalFiber

end

end OAI
