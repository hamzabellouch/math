import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantReferenceMeanSelected
import OAI.NumberTheory.Ostmann.Construction.DiagonalExternalMeasure

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators Classical
namespace Ostmann.Arithmetic.HistoryGiantReferenceMean
open Construction HistorySignedXiTransport HistorySignedResidues

abbrev PrimeDraw (giant : PrimeSource) := giant.Sample×giant.Sample
abbrev MixedDraw (G : ℝ) (giant : PrimeSource) := {p : ℕ // p∈integerPivotCell G}×giant.Sample

def primeP (giant : PrimeSource) (z : PrimeDraw giant) : ℤ := z.1.val
def primeQ (giant : PrimeSource) (z : PrimeDraw giant) : ℤ := z.2.val
def primeWeight (giant : PrimeSource) (z : PrimeDraw giant) : ℝ := giant.law.mass z.1*giant.law.mass z.2

def mixedP (G : ℝ) (giant : PrimeSource) (z : MixedDraw G giant) : ℤ := z.1.val
def mixedQ (G : ℝ) (giant : PrimeSource) (z : MixedDraw G giant) : ℤ := z.2.val
def mixedWeight (G : ℝ) (giant : PrimeSource) (z : MixedDraw G giant) : ℝ :=
  externalPivotWeight G z.1.val*giant.law.mass z.2

theorem primeWeight_nonneg (giant : PrimeSource) (z : PrimeDraw giant) : 0 ≤ primeWeight giant z :=
  mul_nonneg (giant.law.mass_nonneg _) (giant.law.mass_nonneg _)
theorem primeDraw_positive (giant : PrimeSource) (z : PrimeDraw giant) :
    0 < primeP giant z ∧ 0 < primeQ giant z := by
  dsimp only [primeP,primeQ]
  constructor
  · exact_mod_cast (giant.prime _ z.1.property).pos
  · exact_mod_cast (giant.prime _ z.2.property).pos

theorem mixedWeight_nonneg (G : ℝ) (giant : PrimeSource) (z : MixedDraw G giant) :
    0 ≤ mixedWeight G giant z :=
  mul_nonneg (externalPivotWeight_nonneg _ _) (giant.law.mass_nonneg _)
theorem mixedDraw_positive (G : ℝ) (giant : PrimeSource) (z : MixedDraw G giant) :
    0 < mixedP G giant z ∧ 0 < mixedQ G giant z := by
  dsimp only [mixedP,mixedQ]
  constructor
  · exact_mod_cast (Finset.mem_Ioc.mp z.1.property).1
  · exact_mod_cast (giant.prime _ z.2.property).pos

def primeMean (giant : PrimeSource) (F : ℤ→ℤ→ℂ) : ℂ :=
  giant.law.cmean (fun p => giant.law.cmean (fun q => F p.val q.val))

def mixedMean (G : ℝ) (giant : PrimeSource) (F : ℤ→ℤ→ℂ) : ℂ :=
  ∑p∈integerPivotCell G,(externalPivotWeight G p:ℂ)*giant.law.cmean (fun q => F p q.val)

theorem primeMean_eq_weighted (giant : PrimeSource) (F : ℤ→ℤ→ℂ) :
    primeMean giant F=∑z : PrimeDraw giant,(primeWeight giant z:ℂ)*F (primeP giant z) (primeQ giant z) := by
  simp only [primeMean,FinitePrior.cmean,Fintype.sum_prod_type,primeWeight,primeP,primeQ,
    Complex.ofReal_mul,Finset.mul_sum,mul_assoc]

theorem mixedMean_eq_weighted (G : ℝ) (giant : PrimeSource) (F : ℤ→ℤ→ℂ) :
    mixedMean G giant F=∑z : MixedDraw G giant,(mixedWeight G giant z:ℂ)*F (mixedP G giant z) (mixedQ G giant z) := by
  simp only [mixedMean,FinitePrior.cmean,Fintype.sum_prod_type,mixedWeight,mixedP,mixedQ,
    Complex.ofReal_mul,Finset.mul_sum,mul_assoc]
  exact (Finset.sum_coe_sort (integerPivotCell G) (fun p : ℕ =>
    ∑q : giant.Sample,(externalPivotWeight G p:ℂ)*((giant.law.mass q:ℂ)*F p q.val))).symm

def sourceIntegrand (d : Decomposition) (sources : SourceFamily) (seed : List SourceSlot)
    (V : ℕ→ℕ) (outside : List ℕ) (l : ℕ) (a b : State)
    (c e : HistoryChoices sources seed V l) (J : ℤ→ℤ→ℂ)
    (bc sc : ℕ) (X tb td G : ℝ) (P Q : ℤ) : ℂ :=
  J P Q*supportedHistoryPairXi d V outside bc sc X tb td G
    (decodeHistory sources seed V l (giantState a P Q) c)
    (decodeHistory sources seed V l (giantState b P Q) e)

theorem weightedMean_prime (d : Decomposition) (sources : SourceFamily) (seed : List SourceSlot)
    (V : ℕ→ℕ) (outside : List ℕ) (l : ℕ) (a b : State)
    (c e : HistoryChoices sources seed V l) (giant : PrimeSource) (J : ℤ→ℤ→ℂ)
    (bc sc : ℕ) (X tb td G : ℝ) :
    weightedMean d sources seed V outside l a b c e (primeP giant) (primeQ giant) (primeWeight giant)
      (fun z => J (primeP giant z) (primeQ giant z)) bc sc X tb td G=
    primeMean giant (sourceIntegrand d sources seed V outside l a b c e J bc sc X tb td G) := by
  rw [primeMean_eq_weighted]
  simp only [weightedMean,sourceIntegrand,drawHistory,mul_assoc]

theorem weightedMean_mixed (d : Decomposition) (sources : SourceFamily) (seed : List SourceSlot)
    (V : ℕ→ℕ) (outside : List ℕ) (l : ℕ) (a b : State)
    (c e : HistoryChoices sources seed V l) (giant : PrimeSource) (J : ℤ→ℤ→ℂ)
    (bc sc : ℕ) (X tb td G : ℝ) :
    weightedMean d sources seed V outside l a b c e (mixedP G giant) (mixedQ G giant) (mixedWeight G giant)
      (fun z => J (mixedP G giant z) (mixedQ G giant z)) bc sc X tb td G=
    mixedMean G giant (sourceIntegrand d sources seed V outside l a b c e J bc sc X tb td G) := by
  rw [mixedMean_eq_weighted]
  simp only [weightedMean,sourceIntegrand,drawHistory,mul_assoc]

end Ostmann.Arithmetic.HistoryGiantReferenceMean

end

end OAI
