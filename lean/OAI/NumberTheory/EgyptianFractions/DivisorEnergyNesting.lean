import OAI.NumberTheory.EgyptianFractions.CompositeUnitMixing

namespace OAI
noncomputable section
open scoped BigOperators Pointwise

namespace Problem337

/-- Multiplication bijects the divisor lists of two coprime integers with
the divisor list of their product. -/
def coprimeDivisorProductEquiv {P R : ℕ} (hPR : P.Coprime R) :
    (↥P.divisors × ↥R.divisors) ≃ ↥(P * R).divisors := by
  classical
  let f : (↥P.divisors × ↥R.divisors) → ↥(P * R).divisors := fun z =>
    ⟨z.1.val * z.2.val, Nat.mem_divisors.mpr
      ⟨Nat.mul_dvd_mul (Nat.dvd_of_mem_divisors z.1.property)
        (Nat.dvd_of_mem_divisors z.2.property),
        mul_ne_zero (Nat.ne_zero_of_mem_divisors z.1.property)
          (Nat.ne_zero_of_mem_divisors z.2.property)⟩⟩
  apply Equiv.ofBijective f
  constructor
  · intro a b hab
    have hval := congrArg Subtype.val hab
    have hpair : (a.1.val, a.2.val) = (b.1.val, b.2.val) :=
      hPR.mul_injOn_divisors
        (Finset.mem_product.mpr ⟨a.1.property, a.2.property⟩)
        (Finset.mem_product.mpr ⟨b.1.property, b.2.property⟩) hval
    exact Prod.ext (Subtype.ext (congrArg Prod.fst hpair))
      (Subtype.ext (congrArg Prod.snd hpair))
  · intro d
    have hd := d.property
    simp only [Nat.divisors_mul, Finset.mem_mul] at hd
    obtain ⟨a, ha, b, hb, hab⟩ := hd
    exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), Subtype.ext hab⟩

@[simp] theorem coprimeDivisorProductEquiv_val {P R : ℕ} (hPR : P.Coprime R)
    (z : ↥P.divisors × ↥R.divisors) :
    (coprimeDivisorProductEquiv hPR z).val = z.1.val * z.2.val := rfl

/-- Reindexing an indexed sample preserves each normalized fiber mass. -/
theorem fiber_mass_equiv {I J X : Type*} [Fintype I] [Fintype J]
    [DecidableEq X] (e : I ≃ J) (f : J → X) (x : X) :
    ((Finset.univ.filter (fun i : I => f (e i) = x)).card : ℝ) /
        (Fintype.card I : ℝ) =
      ((Finset.univ.filter (fun j : J => f j = x)).card : ℝ) /
        (Fintype.card J : ℝ) := by
  classical
  have hcard : (Finset.univ.filter (fun i : I => f (e i) = x)).card =
      (Finset.univ.filter (fun j : J => f j = x)).card := by
    simp only [Finset.card_filter]
    exact Equiv.sum_comp e (fun j => if f j = x then 1 else 0)
  rw [hcard, Fintype.card_congr e]

/-- The normalized residue-fiber energy of the complete positive divisor list. -/
def divisorResidueEnergy (P q : ℕ) [NeZero q] : ℝ :=
  ∑ x : ZMod q,
    (((Finset.univ.filter (fun d : ↥P.divisors => (d.val : ZMod q) = x)).card : ℝ) /
      (Fintype.card ↥P.divisors : ℝ)) ^ 2

/-- Appending coprime factors which are units modulo `q` cannot increase the
normalized collision energy of the actual complete divisor list. -/
theorem divisorResidueEnergy_mul_le {P R q : ℕ} [NeZero q]
    (hPR : P.Coprime R) (hRq : R.Coprime q) :
    divisorResidueEnergy (P * R) q ≤ divisorResidueEnergy P q := by
  classical
  let c : ↥R.divisors → (ZMod q)ˣ := fun d =>
    ZMod.unitOfCoprime d.val (hRq.coprime_dvd_left (Nat.dvd_of_mem_divisors d.property))
  have hc (d : ↥R.divisors) : (c d : ZMod q) = (d.val : ZMod q) :=
    ZMod.coe_unitOfCoprime _ _
  have hmass (x : ZMod q) :
      ((Finset.univ.filter (fun z : ↥P.divisors × ↥R.divisors =>
        (c z.2 : ZMod q) * (z.1.val : ZMod q) = x)).card : ℝ) /
          (Fintype.card (↥P.divisors × ↥R.divisors) : ℝ) =
      ((Finset.univ.filter (fun d : ↥(P * R).divisors =>
        (d.val : ZMod q) = x)).card : ℝ) /
          (Fintype.card ↥(P * R).divisors : ℝ) := by
    simpa only [coprimeDivisorProductEquiv_val, Nat.cast_mul, hc, mul_comm] using
      fiber_mass_equiv (coprimeDivisorProductEquiv hPR)
        (fun d : ↥(P * R).divisors => (d.val : ZMod q)) x
  have h := indexed_energy_unit_mixing (fun d : ↥P.divisors => (d.val : ZMod q)) c
  simpa only [hmass, divisorResidueEnergy] using h

/-- The form used for nested prime-prefix products: at a modulus coprime to
 the larger squarefree supply, enlarging the supply decreases energy. -/
theorem divisorResidueEnergy_le_of_dvd_squarefree {P Q q : ℕ} [NeZero q]
    (hPQ : P ∣ Q) (hQ : Squarefree Q) (hQq : Q.Coprime q) :
    divisorResidueEnergy Q q ≤ divisorResidueEnergy P q := by
  have hmul : P * (Q / P) = Q := Nat.mul_div_cancel' hPQ
  have hcop : P.Coprime (Q / P) :=
    Nat.coprime_of_squarefree_mul (by simpa only [hmul] using hQ)
  have hdiv : Q / P ∣ Q := Nat.div_dvd_of_dvd hPQ
  simpa only [hmul] using divisorResidueEnergy_mul_le hcop (hQq.coprime_dvd_left hdiv)

end Problem337

end

end OAI
