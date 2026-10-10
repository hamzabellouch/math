import OAI.Algebra.OddKaplansky.Parameters

namespace OAI

universe portUniverse1

section
noncomputable section
open scoped Classical
open Polynomial
namespace OddKaplansky.QuadraticTower

variable {F : Type portUniverse1} [Field F]

def polynomial (a : F) : F[X] := X^2 - C a

lemma polynomial_monic (a : F) : (polynomial a).Monic :=
  monic_X_pow_sub_C a (by decide : 2 ≠ 0)

lemma polynomial_degree (a : F) : (polynomial a).natDegree = 2 :=
  natDegree_X_pow_sub_C

lemma polynomial_irreducible {a : F} (ha : ¬ IsSquare a) :
    Irreducible (polynomial a) := by
  apply X_pow_sub_C_irreducible_of_prime Nat.prime_two
  intro b hb
  exact ha ⟨b, by simpa only [pow_two] using hb.symm⟩

def basis (a : F) : PowerBasis F (AdjoinRoot (polynomial a)) :=
  AdjoinRoot.powerBasis (polynomial_monic a).ne_zero

lemma basis_dim (a : F) : (basis a).dim = 2 := polynomial_degree a
lemma basis_gen (a : F) : (basis a).gen = AdjoinRoot.root (polynomial a) := rfl

instance finiteDimensional (a : F) : FiniteDimensional F (AdjoinRoot (polynomial a)) :=
  (basis a).finite

lemma finrank (a : F) : Module.finrank F (AdjoinRoot (polynomial a)) = 2 := by
  rw [(basis a).finrank, basis_dim]

lemma root_sq (a : F) : AdjoinRoot.root (polynomial a)^2 =
    algebraMap F (AdjoinRoot (polynomial a)) a := by
  have h := AdjoinRoot.mk_self (f := polynomial a)
  change AdjoinRoot.mk (polynomial a) (X^2 - C a) = 0 at h
  rw [map_sub, map_pow, AdjoinRoot.mk_X, AdjoinRoot.mk_C, sub_eq_zero] at h
  exact h

lemma norm_root (a : F) :
    Algebra.norm F (AdjoinRoot.root (polynomial a)) = -a := by
  rw [← basis_gen a, Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly, basis_dim]
  have hm := AdjoinRoot.minpoly_powerBasis_gen_of_monic (polynomial_monic a)
  change minpoly F (basis a).gen = polynomial a at hm
  rw [hm]
  simp [polynomial]

lemma root_not_isSquare {a : F} (ha : ¬ IsSquare a) (hminus : IsSquare (-1 : F)) :
    ¬ IsSquare (AdjoinRoot.root (polynomial a)) := by
  intro hr
  have hn : IsSquare (-a) := by
    rw [← norm_root a]
    exact hr.map (Algebra.norm F)
  exact ha (by simpa only [neg_one_mul, neg_neg] using hminus.mul hn)

instance finite [Finite F] (a : F) : Finite (AdjoinRoot (polynomial a)) :=
  Module.finite_of_finite F

lemma card [Fintype F] (a : F) [Fintype (AdjoinRoot (polynomial a))] :
    Fintype.card (AdjoinRoot (polynomial a)) = (Fintype.card F)^2 := by
  rw [Module.card_eq_pow_finrank (K := F), finrank]

section PrimeField
variable (p : ℕ) [Fact p.Prime]

lemma exists_nonsquare_representative (hp : p ≠ 2) :
    ∃ n : ℕ, n < p ∧ ¬ IsSquare (n : ZMod p) := by
  obtain ⟨a, ha⟩ := FiniteField.exists_nonsquare (F := ZMod p) (by rw [ringChar.eq (ZMod p) p]; exact hp)
  exact ⟨a.val, a.val_lt, by simpa using ha⟩

def nonsquareIndex (hp : p ≠ 2) : ℕ := Nat.find (exists_nonsquare_representative p hp)
def eta (hp : p ≠ 2) : ZMod p := (nonsquareIndex p hp : ZMod p)

lemma eta_not_isSquare (hp : p ≠ 2) : ¬ IsSquare (eta p hp) :=
  (Nat.find_spec (exists_nonsquare_representative p hp)).2
lemma eta_ne_zero (hp : p ≠ 2) : eta p hp ≠ 0 := by
  intro h
  exact eta_not_isSquare p hp (h ▸ IsSquare.zero)
lemma nonsquareIndex_lt (hp : p ≠ 2) : nonsquareIndex p hp < p :=
  (Nat.find_spec (exists_nonsquare_representative p hp)).1
lemma nonsquareIndex_min (hp : p ≠ 2) (n : ℕ) (hn : n < nonsquareIndex p hp) :
    n < p → IsSquare (n : ZMod p) := by
  intro hnp
  by_contra h
  exact Nat.find_min (exists_nonsquare_representative p hp) hn ⟨hnp, h⟩

abbrev FirstField (hp : p ≠ 2) := AdjoinRoot (polynomial (eta p hp))
instance first_irreducible (hp : p ≠ 2) : Fact (Irreducible (polynomial (eta p hp))) :=
  ⟨polynomial_irreducible (eta_not_isSquare p hp)⟩
instance first_fintype (hp : p ≠ 2) : Fintype (FirstField p hp) := Fintype.ofFinite _

def xi (hp : p ≠ 2) : FirstField p hp := AdjoinRoot.root (polynomial (eta p hp))

abbrev CoeffField (hp : p ≠ 2) := AdjoinRoot (polynomial (xi p hp))
theorem second_irreducible (hp : p ≠ 2) (hminus : IsSquare (-1 : ZMod p)) :
    Irreducible (polynomial (xi p hp)) :=
  polynomial_irreducible (root_not_isSquare (eta_not_isSquare p hp) hminus)

@[instance_reducible]
def coeffField (hp : p ≠ 2) (hminus : IsSquare (-1 : ZMod p)) : Field (CoeffField p hp) := by
  letI : Fact (Irreducible (polynomial (xi p hp))) := ⟨second_irreducible p hp hminus⟩
  infer_instance
instance tower_fintype (hp : p ≠ 2) : Fintype (CoeffField p hp) := Fintype.ofFinite _

lemma first_card (hp : p ≠ 2) : Fintype.card (FirstField p hp) = p^2 := by
  rw [card, ZMod.card]
lemma tower_card (hp : p ≠ 2) : Fintype.card (CoeffField p hp) = p^4 := by
  rw [card, first_card, ← pow_mul]

end PrimeField
end OddKaplansky.QuadraticTower

end
end

end OAI
