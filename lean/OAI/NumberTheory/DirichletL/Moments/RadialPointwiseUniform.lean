import OAI.NumberTheory.DirichletL.Moments.RadialPointwiseEnergy

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentRadialPointwiseUniform
open CenteredMomentEligibleEnergy CenteredMomentRadialEligibleEnergy
open CenteredMomentRadialPointwiseEnergy CenteredMomentUniformDivisorShell
open CenteredMomentSlotRatios
local notation "O" => ActualEisensteinCubic.O
variable {ι:Type*} [Fintype ι] [DecidableEq ι]

def Bound (ι:Type*) [Fintype ι] [DecidableEq ι] (C ε:ℝ) : Prop :=
  ∀(s:Data ι) (r:Radial) (D:Ideal O),Squarefree D →
    ∀E Z:ℝ,0≤E → 1<Z → (∀a∈s.toSource.active D,childEnergy s r D a≤E) →
    energy s r D≤C*(Ideal.absNorm D:ℝ)^(2*ε)*Z^(s.toSource.allowance Z)*
      (s.profileFactor*E)/(Ideal.absNorm D:ℝ)

 theorem uniform_subset (ε:ℝ) (hε:0<ε) : ∃C:ℝ,0<C ∧ ∀J:Finset ι,Bound J C ε := by
  have he (J:Finset ι):∃C:ℝ,0<C ∧ Bound J C ε:=
    actual_pointwise_divisor (Fintype.card ι) (by simpa using Finset.card_le_univ J) ε hε
  choose C hC hb using he
  let D:ℝ:=1+∑J:Finset ι,C J
  have hs:0≤∑J:Finset ι,C J:=Finset.sum_nonneg (fun J _=>(hC J).le)
  refine ⟨D,by dsimp [D];linarith,?_⟩
  intro J s r I hI E Z hE hZ hc
  have hd:C J≤D:=by
    have hh:=Finset.single_le_sum (fun J _=>(hC J).le) (Finset.mem_univ J)
    dsimp [D];linarith
  apply (hb J s r I hI E Z hE hZ hc).trans
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply mul_le_mul_of_nonneg_right _ (mul_nonneg s.profile_nonneg hE)
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (by linarith) _)
  exact mul_le_mul_of_nonneg_right hd (Real.rpow_nonneg (Nat.cast_nonneg _) _)

 theorem actual_uniform_divisor (lo hi:ι→ℝ) (B δ:ℝ) (hB:0≤B) (hδ:0<δ) :
    ∃C:ℝ,0<C ∧ ∀(J:Finset ι) (s:Data J),(∀i:J,s.lo i=lo i) → (∀i:J,s.hi i=hi i) →
      ∀(r:Radial) (D:Ideal O),Squarefree D → ∀E Z:ℝ,0≤E → 1<Z →
      (Ideal.absNorm D:ℝ)≤Z^B → (∀a∈s.toSource.active D,childEnergy s r D a≤E) →
      energy s r D≤C*Z^δ*(s.profileFactor*E)/(Ideal.absNorm D:ℝ) := by
  let ε:ℝ:=δ/(2*(B+1))
  have hε:0<ε:=div_pos hδ (by positivity)
  obtain ⟨C,hC,hbound⟩:=uniform_subset (ι:=ι) ε hε
  let A:ℝ:=Real.exp (∑i,logWindow (lo i) (hi i))
  refine ⟨C*A,by dsimp [A];positivity,?_⟩
  intro J s hlo hhi r D hD E Z hE hZ hN hc
  have hz:0<Z:=zero_lt_one.trans hZ
  have ha:Z^(s.toSource.allowance Z)≤A:=by
    dsimp [A]
    rw [←numerical_allowance Z _ hZ]
    exact Real.rpow_le_rpow_of_exponent_le hZ.le (subset_allowance J s.toSource lo hi hlo hhi Z hZ)
  have hp:(Ideal.absNorm D:ℝ)^(2*ε)≤Z^δ:=by
    apply (Real.rpow_le_rpow (Nat.cast_nonneg _) hN (by positivity)).trans
    rw [←Real.rpow_mul hz.le]
    apply Real.rpow_le_rpow_of_exponent_le hZ.le
    have he:ε*(2*(B+1))=δ:=div_mul_cancel₀ δ (by positivity)
    nlinarith
  apply (hbound J s r D hD E Z hE hZ hc).trans
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply mul_le_mul_of_nonneg_right _ (mul_nonneg s.profile_nonneg hE)
  calc
    _≤C*Z^δ*A:=mul_le_mul (mul_le_mul_of_nonneg_left hp hC.le) ha
      (Real.rpow_nonneg hz.le _) (by positivity)
    _=_:=by ring

end SevenEighths.CenteredMomentRadialPointwiseUniform

end

end OAI
