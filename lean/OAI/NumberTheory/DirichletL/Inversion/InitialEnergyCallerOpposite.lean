import OAI.NumberTheory.DirichletL.Inversion.InitialEnergyCallerCanonical

namespace OAI

noncomputable section

open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss IdealMobiusDivisorSum
open SevenEighths.InverseMoment SevenEighths.InverseInitialArithmetic
open SevenEighths.InverseInitialQuotientGeometry SevenEighths.InverseInitialClippedColumns
open SevenEighths.InverseInitialEnergyCallerCanonical
namespace SevenEighths.InverseInitialEnergyCallerOpposite
local notation "Eis" => ActualEisensteinCubic.O

def negativeChild (c : InitialChild) : InitialChild := (c.1,c.2.1,-c.2.2)

theorem energy_neg_rows (T labels : Finset (Ideal Eis)) (rows : Finset Eis)
    (hneg : ∀ k∈rows,-k∈rows) (J : ℕ) (F : InitialChild→ℂ) :
    (∑ t∈T,((idealDivisors t).card:ℝ)^J *
      ∑ f∈labels,((idealDivisors f).card:ℝ)^(J+1) *
        ∑ k∈rows,‖F (negativeChild (t,f,k))‖^2) =
    ∑ t∈T,((idealDivisors t).card:ℝ)^J *
      ∑ f∈labels,((idealDivisors f).card:ℝ)^(J+1) *
        ∑ k∈rows,‖F (t,f,k)‖^2 := by
  apply Finset.sum_congr rfl
  intro t ht
  congr 1
  apply Finset.sum_congr rfl
  intro f hf
  congr 1
  apply Finset.sum_bij (fun k _=>-k)
  · exact hneg
  · intro a ha b hb he
    exact neg_injective he
  · intro b hb
    exact ⟨-b,hneg b hb,neg_neg b⟩
  · intro k hk
    rfl

variable {ι σ : Type*} [DecidableEq ι]
  (p : ι → Eis) (hp : ∀ i, p i≠0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

theorem signed_opposite_pair_moment {J : ℕ}
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    (S : Finset (Source (ι:=ι) J)) (u : Eisˣ)
    (assignedLists : Fin J → Finset ι) (assignedCoeff : Fin J → ι → ℂ)
    (hdiv : ∀ x ∈ S, x.divisor ⊆ x.common)
    (hterm : ∀ x ∈ S, assignedTerm assignedLists assignedCoeff
      (x.common ∪ x.overlap) x.assigned ≠ 0)
    (labels : Finset (Ideal Eis)) (rows : Finset Eis)
    (hneg : ∀ k∈rows,-k∈rows)
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
        (negativeChild (initialChild (toTuple p (sectorSource u x))))‖ ≤
      A * (Z^F * ∑ t ∈ quotientSet p S, ((idealDivisors t).card:ℝ)^J) * B := by
  have h₁ := energy_le_moment p hp hcop hg pool Ψ₁ j slots₁ lists₁ a₁ W₁ X₁
    J (quotientSet p S) labels rows hZ F B hmoment₁
  have h₂ := energy_le_moment p hp hcop hg pool Ψ₂ j slots₂ lists₂ a₂ W₂ X₂
    J (quotientSet p S) labels rows hZ F B hmoment₂
  have h₂neg := h₂
  rw [← energy_neg_rows (quotientSet p S) labels rows hneg J
    (child p hp hcop hg pool Ψ₂ j slots₂ lists₂ a₂ W₂ X₂)] at h₂neg
  apply (InverseInitialEnergyCaller.actual_sector_signed_pair p hp hinj hpr S u
    assignedLists assignedCoeff hdiv hterm labels rows hlabels hchild c A hA hc
    (child p hp hcop hg pool Ψ₁ j slots₁ lists₁ a₁ W₁ X₁)
    (fun c=>child p hp hcop hg pool Ψ₂ j slots₂ lists₂ a₂ W₂ X₂ (negativeChild c))).trans
  calc
    _ ≤ A * (Real.sqrt ((Z^F * ∑ t ∈ quotientSet p S, ((idealDivisors t).card:ℝ)^J)*B) *
        Real.sqrt ((Z^F * ∑ t ∈ quotientSet p S, ((idealDivisors t).card:ℝ)^J)*B)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul (Real.sqrt_le_sqrt h₁)
        (Real.sqrt_le_sqrt h₂neg) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) hA
    _ = _ := by
      rw [Real.mul_self_sqrt (mul_nonneg (mul_nonneg (Real.rpow_nonneg hZ.le _)
        (Finset.sum_nonneg fun t ht=>by positivity)) hB)]
      ring

end SevenEighths.InverseInitialEnergyCallerOpposite

end

end OAI
