import Mathlib
import OAI.Computability.MinUncut.Search.RationalInner
import OAI.Computability.MinUncut.Estimates.WeightedTestLaw

namespace OAI

noncomputable section
open scoped BigOperators
namespace MinUncut.Outer
open MinUncut.Inner MinUncut.FiniteGaussian MinUncut.FiniteProof OuterSmoothness
attribute [local instance] Classical.propDecidable coordsDecEq
variable {Name I S : Type*} [Fintype I] [Fintype S]

abbrev AllElementary (equations : S → Equation Name) (k m n : ℕ) (g : GridData) :=
  Test × Elementary (I := I) equations k m n g

def allWeight (equations : S → Equation Name) {k m n : ℕ} (g : GridData) (a : ℚ) (b : Test → ℚ)
    (e : AllElementary (I := I) equations k m n g) : ℚ :=
  elementaryWeight equations g a (b e.1) e.1 e.2

def allDemand (equations : S → Equation Name) {k m n : ℕ} (g : GridData) (σ η : ℚ)
    (e : AllElementary (I := I) equations k m n g) : PathRealization.Demand (FamilyVariable Name I) :=
  (elementaryQuery equations g σ η e.1 e.2).signed familyBase

def rationalRate (J : ℕ) (d : InnerData) : ℚ := (rationalEta J)^2/d.m

lemma rationalRate_cast (J : ℕ) (d : InnerData) :
    (rationalRate J d:ℝ)=(sourceEta J)^2/d.m := by
  simp only [rationalRate,Rat.cast_div,Rat.cast_pow,Rat.cast_natCast,rationalEta_cast]

lemma rationalRate_bounds {J : ℕ} (hJ : 1≤J) (d : InnerData) (hd : d.Check J) :
    0≤rationalRate J d ∧ rationalRate J d≤1 := by
  have ha := source_row_rate (by exact_mod_cast hJ : (1:ℝ)≤J)
    (by have := (d.realize hJ hd).hm; change 2≤d.m at this; omega : 0<d.m)
  rw [← rationalRate_cast] at ha
  exact ⟨by exact_mod_cast ha.1,by exact_mod_cast ha.2.1⟩

lemma allFailure_eq {J : ℕ} (hJ : 1≤J) (d : InnerData) (hd : d.Check J)
    (o : OuterData) (ho : o.Check J d) (g : GridData) (equations : S → Equation Name)
    (y : FamilyVariable Name I → Bool) :
    (∑ e : AllElementary (I := I) equations o.k d.m d.n g,
      (allWeight equations g (rationalRate J d) (rationalBudgets J d o) e:ℝ)*
        (PathRealization.failure (allDemand equations g (rationalSigma J) (rationalEta J) e) y:ℝ)) =
      (variableProof y).finiteCost (d.realize hJ hd) (o.realize hJ d hd ho) g equations := by
  rw [Fintype.sum_prod_type]
  unfold ProofFamily.finiteCost
  apply Finset.sum_congr rfl
  intro j _
  simp only [allWeight,allDemand,QueryDemand.failure_signed,← variableProof_queryAnswer]
  rw [elementary_weighted_sum]
  cases j <;> simp only [ProofFamily.finiteErrors,rationalBudgets_cast hJ d hd o ho,
    rationalRate_cast]
  all_goals
    change edgeMean equations o.k (fun U h pos => _ / _) =
      edgeMean equations o.k (fun U h pos => _) / _
    unfold edgeMean
    simp only [Finset.expect_div]
    rfl
end MinUncut.Outer

namespace MinUncut.Outer
open MinUncut.Inner MinUncut.FiniteGaussian MinUncut.FiniteProof OuterSmoothness
attribute [local instance] Classical.propDecidable coordsDecEq
variable {m n : ℕ}

lemma noiseWeight_mean {V A : Type*} [AddCommGroup V] [Module F₂ V] [AddTorsor V A] [Fintype A]
    (a : ℚ) (B : FaceArray A m n) (j : Test) : (𝔼 C, (noiseWeight a B C j:ℝ))=1 := by
  cases j with
  | second =>
    have hh := RowNoise.rationalDensity_mean a B
    have hc := congrArg (fun x : ℚ => (x:ℝ)) hh
    simpa only [Fintype.expect_eq_sum_div_card,Rat.cast_div,Rat.cast_sum,Rat.cast_natCast,
      Rat.cast_one,noiseWeight] using hc
  | first => simp only [noiseWeight,Rat.cast_one,Fintype.expect_const]
  | third => simp only [noiseWeight,Rat.cast_one,Fintype.expect_const]
  | fourth => simp only [noiseWeight,Rat.cast_one,Fintype.expect_const]

lemma gridWeight_mass (g : GridData) (hT : 0<g.T) (hL : 0<g.L) :
    (∑ q : TestCoordinates m n → Fin g.L, (gridWeight g q:ℝ))=1 := by
  exact_mod_cast sum_gridWeight (m := m) (n := n) g hT hL

lemma localWeight_mass {V A : Type*} [AddCommGroup V] [Module F₂ V] [AddTorsor V A] [Fintype A]
    (g : GridData) (hT : 0<g.T) (hL : 0<g.L) (a b : ℚ) (j : Test) :
    (∑ p : LocalSample A m n g, (localWeight g a b j p:ℝ))=(b:ℝ)⁻¹ := by
  have hh := localWeight_sum (A := A) (m := m) (n := n) g a b j (fun _ => 1)
  simp only [mul_one,← Finset.sum_mul,gridWeight_mass g hT hL,one_mul,Fintype.expect_const,
    noiseWeight_mean,one_div] at hh
  exact hh

variable {Name I S : Type*} [Fintype I] [Fintype S] [Nonempty S] {k : ℕ}
lemma elementaryWeight_mass (equations : S → Equation Name) (hk : k≤Fintype.card I)
    (g : GridData) (hT : 0<g.T) (hL : 0<g.L) (a b : ℚ) (j : Test) :
    (∑ e : Elementary (I := I) equations k m n g, (elementaryWeight equations g a b j e:ℝ))=(b:ℝ)⁻¹ := by
  let : Nonempty (FixedSets I k) := fixedSets_nonempty hk
  change (∑ e : Sigma _, _) = _
  rw [Fintype.sum_sigma]
  simp only [elementaryWeight,Rat.cast_mul,Rat.cast_inv,Rat.cast_natCast,← Finset.mul_sum,
    localWeight_mass g hT hL]
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  have hc : (Fintype.card (OuterSample I S k):ℝ)≠0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  field_simp
end MinUncut.Outer

end

end OAI
