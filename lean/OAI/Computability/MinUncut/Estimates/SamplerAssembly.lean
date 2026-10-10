import Mathlib
import OAI.Computability.MinUncut.Estimates.SamplerCost
import OAI.Computability.MinUncut.Search.RationalDenominatorArithmetic

namespace OAI

section
noncomputable section
open scoped BigOperators
namespace MinUncut.Outer
open MinUncut.Inner MinUncut.FiniteGaussian MinUncut.FiniteProof OuterSmoothness
attribute [local instance] Classical.propDecidable coordsDecEq
variable {Name I S : Type*} [Fintype I] [Fintype S] [Nonempty S]

lemma allWeight_mass (equations : S → Equation Name) {k m n : ℕ} (hk : k≤Fintype.card I)
    (g : GridData) (hT : 0<g.T) (hL : 0<g.L) (a : ℚ) (b : Test → ℚ) :
    (∑ e : AllElementary (I := I) equations k m n g, allWeight equations g a b e)=∑ j, (b j)⁻¹ := by
  apply (Rat.cast_injective (α := ℝ))
  simp only [Rat.cast_sum,Rat.cast_inv,Fintype.sum_prod_type,allWeight,
    elementaryWeight_mass equations hk g hT hL]

structure Parameters (J : ℕ) where
  hJ : 1≤J
  d : InnerData
  hd : d.Check J
  o : OuterData
  ho : o.Check J d

namespace Parameters

def select (J : ℕ) (hJ : 1≤J) : Parameters J :=
  let d := InnerData.search J hJ
  let hd := InnerData.search_check J hJ
  let o := OuterData.search J hJ d hd
  ⟨hJ,d,hd,o,OuterData.search_check J hJ d hd⟩

def grid {J : ℕ} (P : Parameters J) : GridData :=
  tableGrid P.d.m P.d.n (tableAccuracy J P.d P.o) (tableAccuracy_pos P.hJ P.d P.hd P.o P.ho)

lemma grid_pos {J : ℕ} (P : Parameters J) : 0<P.grid.T ∧ 0<P.grid.L := by
  have h := tableGrid_check P.d.m P.d.n (tableAccuracy J P.d P.o)
    (tableAccuracy_pos P.hJ P.d P.hd P.o P.ho)
  exact ⟨h.1,h.2.1⟩

lemma t_pos {J : ℕ} (P : Parameters J) : 0<P.o.t := P.ho.2.2.2.1
lemma k_le {J : ℕ} (P : Parameters J) : P.o.k≤P.o.t := P.ho.2.2.2.2.1

def denominator {J : ℕ} (P : Parameters J) (S : Type*) [Fintype S] : ℕ :=
  samplerDenominator (Fin P.o.t) S P.o.k P.d.m P.d.n P.grid
    (rationalRate J P.d) (rationalBudgets J P.d P.o)

lemma denominator_pos {J : ℕ} (P : Parameters J) : 0<P.denominator S :=
  samplerDenominator_pos (by simpa only [Fintype.card_fin] using P.k_le) _ _ _

abbrev Sample {J : ℕ} (P : Parameters J) (equations : S → Equation Name) :=
  AllElementary (I := Fin P.o.t) equations P.o.k P.d.m P.d.n P.grid

def weight {J : ℕ} (P : Parameters J) (equations : S → Equation Name) (e : P.Sample equations) : ℚ :=
  allWeight equations P.grid (rationalRate J P.d) (rationalBudgets J P.d P.o) e

def demand {J : ℕ} (P : Parameters J) (equations : S → Equation Name) (e : P.Sample equations) :
    PathRealization.Demand (FamilyVariable Name (Fin P.o.t)) :=
  allDemand equations P.grid (rationalSigma J) (rationalEta J) e

omit [Nonempty S] in
lemma weight_nonneg {J : ℕ} (P : Parameters J) (equations : S → Equation Name) (e : P.Sample equations) :
    0≤P.weight equations e :=
  elementaryWeight_nonneg equations P.grid P.grid_pos.1 P.grid_pos.2
    (rationalRate_bounds P.hJ P.d P.hd).1 (rationalRate_bounds P.hJ P.d P.hd).2
    (rationalBudgets_pos P.hJ P.d P.hd P.o P.ho e.1) e.1 e.2

lemma weight_den {J : ℕ} (P : Parameters J) (equations : S → Equation Name) (e : P.Sample equations) :
    (P.weight equations e).den∣P.denominator S :=
  elementaryWeight_den equations (by simpa only [Fintype.card_fin] using P.k_le) _ _ _ e.1 e.2

lemma weight_sum {J : ℕ} (P : Parameters J) (equations : S → Equation Name) :
    (∑ e, P.weight equations e)=rationalWeight J P.d P.o :=
  allWeight_mass equations (by simpa only [Fintype.card_fin] using P.k_le) _ P.grid_pos.1 P.grid_pos.2 _ _

omit [Nonempty S] in
lemma failure_eq {J : ℕ} (P : Parameters J) (equations : S → Equation Name)
    (y : FamilyVariable Name (Fin P.o.t) → Bool) :
    (∑ e, (P.weight equations e:ℝ)*(PathRealization.failure (P.demand equations e) y:ℝ))=
      (variableProof y).finiteCost (P.d.realize P.hJ P.hd) (P.o.realize P.hJ P.d P.hd P.ho) P.grid equations :=
  allFailure_eq P.hJ P.d P.hd P.o P.ho P.grid equations y

end Parameters
end MinUncut.Outer

end
end

end OAI
