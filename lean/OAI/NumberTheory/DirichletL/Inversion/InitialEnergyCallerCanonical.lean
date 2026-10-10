import OAI.NumberTheory.DirichletL.Inversion.InitialEnergyCaller

namespace OAI

noncomputable section

open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss IdealMobiusDivisorSum
open SevenEighths.InverseMoment SevenEighths.InverseInitialArithmetic
open SevenEighths.InverseInitialQuotientGeometry SevenEighths.InverseInitialClippedColumns
namespace SevenEighths.InverseInitialEnergyCallerCanonical
local notation "Eis" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i, p i≠0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

def child (pool : Finset ι) (Ψ : Eis →* ℂ) (j : Eis)
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (W : ℝ → ℂ) (X : ℝ) (c : InitialChild) : ℂ :=
  finiteCanonicalMarkedRow p hp hcop hg pool Ψ (j*primaryGenerator c.1)
    (primaryGenerator c.2.1) c.2.2 slots lists a W X

omit [DecidableEq σ] in
theorem energy_eq_normalized (pool : Finset ι) (Ψ : Eis →* ℂ) (j : Eis)
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (W : ℝ → ℂ) (X : ℝ) (J : ℕ) (T : Finset (Ideal Eis))
    (labels : Finset (Ideal Eis)) (rows : Finset Eis)
    {Z : ℝ} (hZ : 0<Z) (F : ℝ) :
    (∑ t ∈ T, ((idealDivisors t).card:ℝ)^J *
      ∑ f ∈ labels, ((idealDivisors f).card:ℝ)^(J+1) *
        ∑ k ∈ rows, ‖child p hp hcop hg pool Ψ j slots lists a W X (t,f,k)‖^2) =
    Z^F * ∑ t ∈ T, ((idealDivisors t).card:ℝ)^J *
      normalizedColumnEnergy p hp hcop hg pool Ψ (j*primaryGenerator t)
        slots lists a labels rows (fun f=>((idealDivisors f).card:ℝ)^(J+1)) W X Z F := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t ht
  change ((idealDivisors t).card:ℝ)^J *
    columnEnergy p hp hcop hg pool Ψ (j*primaryGenerator t) slots lists a
      labels rows (fun f=>((idealDivisors f).card:ℝ)^(J+1)) W X = _
  rw [columnEnergy_normalization p hp hcop hg pool Ψ (j*primaryGenerator t)
    slots lists a labels rows _ W X hZ F]
  ring

omit [DecidableEq σ] in
theorem energy_le_moment (pool : Finset ι) (Ψ : Eis →* ℂ) (j : Eis)
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (W : ℝ → ℂ) (X : ℝ) (J : ℕ) (T : Finset (Ideal Eis))
    (labels : Finset (Ideal Eis)) (rows : Finset Eis)
    {Z : ℝ} (hZ : 0<Z) (F B : ℝ)
    (hmoment : ∀ t ∈ T,
      normalizedColumnEnergy p hp hcop hg pool Ψ (j*primaryGenerator t)
        slots lists a labels rows (fun f=>((idealDivisors f).card:ℝ)^(J+1)) W X Z F ≤ B) :
    (∑ t ∈ T, ((idealDivisors t).card:ℝ)^J *
      ∑ f ∈ labels, ((idealDivisors f).card:ℝ)^(J+1) *
        ∑ k ∈ rows, ‖child p hp hcop hg pool Ψ j slots lists a W X (t,f,k)‖^2) ≤
    (Z^F * ∑ t ∈ T, ((idealDivisors t).card:ℝ)^J) * B := by
  rw [energy_eq_normalized p hp hcop hg pool Ψ j slots lists a W X J T labels rows hZ F,
    mul_assoc, Finset.sum_mul]
  apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hZ.le _)
  exact Finset.sum_le_sum fun t ht =>
    mul_le_mul_of_nonneg_left (hmoment t ht) (by positivity)

theorem sqrt_pair_mass (M B₁ B₂ : ℝ) (hM : 0≤M) :
    Real.sqrt (M*B₁)*Real.sqrt (M*B₂) = M*(Real.sqrt B₁*Real.sqrt B₂) := by
  rw [Real.sqrt_mul hM,Real.sqrt_mul hM]
  calc
    _ = (Real.sqrt M*Real.sqrt M)*(Real.sqrt B₁*Real.sqrt B₂) := by ring
    _ = _ := by rw [Real.mul_self_sqrt hM]

omit [DecidableEq σ] in
theorem signed_canonical_pair_moment {J : ℕ}
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    (S : Finset (Source (ι:=ι) J)) (u : Eisˣ)
    (assignedLists : Fin J → Finset ι) (assignedCoeff : Fin J → ι → ℂ)
    (hdiv : ∀ x ∈ S, x.divisor ⊆ x.common)
    (hterm : ∀ x ∈ S, assignedTerm assignedLists assignedCoeff
      (x.common ∪ x.overlap) x.assigned ≠ 0)
    (labels : Finset (Ideal Eis)) (rows : Finset Eis)
    (hlabels : ∀ f ∈ labels, f ≠ 0)
    (hchild : ∀ x ∈ S,
      (initialChild (toTuple p (sectorSource u x))).2.1 ∈ labels ∧
      (initialChild (toTuple p (sectorSource u x))).2.2 ∈ rows)
    (c : Source (ι:=ι) J → ℂ) (A : ℝ) (hA : 0≤A)
    (hc : ∀ x ∈ S, ‖c x‖≤A)
    (pool : Finset ι) (Ψ₁ Ψ₂ : Eis →* ℂ) (j : Eis)
    (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι)
    (a₁ a₂ : σ → ι → ℂ) (W₁ W₂ : ℝ → ℂ) (X₁ X₂ : ℝ)
    {Z : ℝ} (hZ : 0<Z) (F B : ℝ) (hB : 0≤B)
    (hmoment₁ : ∀ t ∈ quotientSet p S,
      normalizedColumnEnergy p hp hcop hg pool Ψ₁ (j*primaryGenerator t)
        slots₁ lists₁ a₁ labels rows (fun f=>((idealDivisors f).card:ℝ)^(J+1)) W₁ X₁ Z F ≤ B)
    (hmoment₂ : ∀ t ∈ quotientSet p S,
      normalizedColumnEnergy p hp hcop hg pool Ψ₂ (j*primaryGenerator t)
        slots₂ lists₂ a₂ labels rows (fun f=>((idealDivisors f).card:ℝ)^(J+1)) W₂ X₂ Z F ≤ B) :
    ‖∑ x ∈ S, c x *
      star (child p hp hcop hg pool Ψ₁ j slots₁ lists₁ a₁ W₁ X₁
        (initialChild (toTuple p (sectorSource u x)))) *
      child p hp hcop hg pool Ψ₂ j slots₂ lists₂ a₂ W₂ X₂
        (initialChild (toTuple p (sectorSource u x)))‖ ≤
      A * (Z^F * ∑ t ∈ quotientSet p S, ((idealDivisors t).card:ℝ)^J) * B := by
  have h₁ := energy_le_moment p hp hcop hg pool Ψ₁ j slots₁ lists₁ a₁ W₁ X₁
    J (quotientSet p S) labels rows hZ F B hmoment₁
  have h₂ := energy_le_moment p hp hcop hg pool Ψ₂ j slots₂ lists₂ a₂ W₂ X₂
    J (quotientSet p S) labels rows hZ F B hmoment₂
  apply (InverseInitialEnergyCaller.actual_sector_signed_pair p hp hinj hpr S u
    assignedLists assignedCoeff hdiv hterm labels rows hlabels hchild c A hA hc
    (child p hp hcop hg pool Ψ₁ j slots₁ lists₁ a₁ W₁ X₁)
    (child p hp hcop hg pool Ψ₂ j slots₂ lists₂ a₂ W₂ X₂)).trans
  calc
    _ ≤ A * (Real.sqrt ((Z^F * ∑ t ∈ quotientSet p S, ((idealDivisors t).card:ℝ)^J)*B) *
        Real.sqrt ((Z^F * ∑ t ∈ quotientSet p S, ((idealDivisors t).card:ℝ)^J)*B)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul (Real.sqrt_le_sqrt h₁)
        (Real.sqrt_le_sqrt h₂) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) hA
    _ = _ := by
      rw [Real.mul_self_sqrt (mul_nonneg (mul_nonneg (Real.rpow_nonneg hZ.le _)
        (Finset.sum_nonneg fun t ht=>by positivity)) hB)]
      ring

end SevenEighths.InverseInitialEnergyCallerCanonical

end

end OAI
