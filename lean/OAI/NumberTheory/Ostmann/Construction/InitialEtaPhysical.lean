import OAI.NumberTheory.Ostmann.Construction.InitialEtaDefs

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Construction.InitialEta

def tupleLocalTest (d : Decomposition) (P : Finset ℕ) {b s : ℕ} {ι : Type*}
    (i : Position b s ι) (q : ℕ) : ZMod q → ℂ :=
  match i.2 with
  | .inl _ => favorableGiantResidueTest d P q
  | .inr _ => residueTest d q

def halfBins {giant bulk spectator : PrimeSource} {ι : Type*}
    {aux : ι → PrimeSource} {b s : ℕ} (tb td : ℤ)
    (x : HalfListSample giant bulk spectator aux b s) : ℝ :=
  Ostmann.smoothPartition (primeGroupLog bulk b x.2.1-tb)*
    Ostmann.smoothPartition (primeGroupLog spectator s x.2.2.1-td)

def tupleBins {giant bulk spectator : PrimeSource} {ι : Type*}
    {aux : ι → PrimeSource} {b s : ℕ} (tb td : ℤ)
    (x : JointSample giant bulk spectator aux b s) : ℝ :=
  halfBins tb td x.1 * halfBins tb td x.2

theorem halfBins_nonneg {giant bulk spectator : PrimeSource} {ι : Type*}
    {aux : ι → PrimeSource} {b s : ℕ} (tb td : ℤ)
    (x : HalfListSample giant bulk spectator aux b s) : 0 ≤ halfBins tb td x :=
  mul_nonneg (Ostmann.smoothPartition_nonneg _) (Ostmann.smoothPartition_nonneg _)

theorem halfBins_le_one {giant bulk spectator : PrimeSource} {ι : Type*}
    {aux : ι → PrimeSource} {b s : ℕ} (tb td : ℤ)
    (x : HalfListSample giant bulk spectator aux b s) : halfBins tb td x ≤ 1 := by
  exact (mul_le_of_le_one_left (Ostmann.smoothPartition_nonneg _)
    (Ostmann.smoothPartition_le_one _)).trans (Ostmann.smoothPartition_le_one _)

theorem tupleBins_nonneg {giant bulk spectator : PrimeSource} {ι : Type*}
    {aux : ι → PrimeSource} {b s : ℕ} (tb td : ℤ)
    (x : JointSample giant bulk spectator aux b s) : 0 ≤ tupleBins tb td x :=
  mul_nonneg (halfBins_nonneg tb td x.1) (halfBins_nonneg tb td x.2)

theorem tupleBins_le_one {giant bulk spectator : PrimeSource} {ι : Type*}
    {aux : ι → PrimeSource} {b s : ℕ} (tb td : ℤ)
    (x : JointSample giant bulk spectator aux b s) : tupleBins tb td x ≤ 1 :=
  (mul_le_of_le_one_left (halfBins_nonneg tb td x.2)
    (halfBins_le_one tb td x.1)).trans (halfBins_le_one tb td x.2)

theorem residueTest_ofReal_re (d : Decomposition) (q : ℕ) (z : ZMod q) :
    ((residueTest d q z).re : ℂ) = residueTest d q z := by
  by_cases hq : q=0
  · simp [residueTest,hq]
  · let : NeZero q := ⟨hq⟩
    simp only [residueTest_eq,Complex.ofReal_re]

theorem favorableTest_ofReal_re (d : Decomposition) (P : Finset ℕ)
    (q : ℕ) (z : ZMod q) :
    ((favorableGiantResidueTest d P q z).re : ℂ) = favorableGiantResidueTest d P q z := by
  by_cases hP : q∈P
  · simp only [favorableGiantResidueTest,hP,ite_true]
    by_cases hq : q=0
    · simp [giantResidueTest,hq]
    · let : NeZero q := ⟨hq⟩
      apply Complex.ext <;> simp [giantResidueTest_eq,giantTest_real]
  · simp [favorableGiantResidueTest,hP]

theorem tupleValues_giant {giant bulk spectator : PrimeSource} {ι : Type*}
    {aux : ι → PrimeSource} {b s : ℕ}
    (x : JointSample giant bulk spectator aux b s) (h : Bool) :
    tupleValues x (h,.inl ()) = ((halfAt x h).1 : ℕ) := rfl

theorem tupleValues_bulk {giant bulk spectator : PrimeSource} {ι : Type*}
    {aux : ι → PrimeSource} {b s : ℕ}
    (x : JointSample giant bulk spectator aux b s) (h : Bool) (i : Fin b) :
    tupleValues x (h,.inr (.inl i)) = ((halfAt x h).2.1 i : ℕ) := rfl

theorem tupleValues_spectator {giant bulk spectator : PrimeSource} {ι : Type*}
    {aux : ι → PrimeSource} {b s : ℕ}
    (x : JointSample giant bulk spectator aux b s) (h : Bool) (i : Fin s) :
    tupleValues x (h,.inr (.inr (.inl i))) = ((halfAt x h).2.2.1 i : ℕ) := rfl

theorem tupleValues_aux {giant bulk spectator : PrimeSource} {ι : Type*}
    {aux : ι → PrimeSource} {b s : ℕ}
    (x : JointSample giant bulk spectator aux b s) (h : Bool) (i : ι) :
    tupleValues x (h,.inr (.inr (.inr i))) = ((halfAt x h).2.2.2 i : ℕ) := rfl

theorem tupleTest_eq (d : Decomposition) (P : Finset ℕ) (giant bulk spectator : PrimeSource)
    {ι : Type*} [Fintype ι] (aux : ι → PrimeSource) (b s : ℕ) (tb td n : ℤ)
    (x : JointSample giant bulk spectator aux b s) :
    ((halfListTupleTest d P giant bulk spectator aux b s tb td n x.1 : ℝ):ℂ) *
      ((halfListTupleTest d P giant bulk spectator aux b s tb td n x.2 : ℝ):ℂ) =
    (tupleBins tb td x:ℂ) * ∏i,tupleLocalTest d P i (tupleValues x i)
      (n:ZMod (tupleValues x i)) := by
  classical
  let H := fun y : HalfListSample giant bulk spectator aux b s =>
    favorableGiantResidueTest d P y.1 (n:ZMod (y.1:ℕ)) *
      ((∏i,residueTest d (y.2.1 i) (n:ZMod (y.2.1 i:ℕ))) *
        ((∏i,residueTest d (y.2.2.1 i) (n:ZMod (y.2.2.1 i:ℕ))) *
          ∏i,residueTest d (y.2.2.2 i) (n:ZMod (y.2.2.2 i:ℕ))))
  have hp : (∏i,tupleLocalTest d P i (tupleValues x i)
      (n:ZMod (tupleValues x i))) = H x.2 * H x.1 := by
    rw [Fintype.prod_prod_type,Fintype.prod_bool]
    simp only [Fintype.prod_sum_type,Fintype.prod_unique]
    rfl
  rw [hp]
  simp only [halfListTupleTest,Complex.ofReal_mul,Complex.ofReal_prod,
    favorableTest_ofReal_re,residueTest_ofReal_re,tupleBins,halfBins,H]
  ring

theorem tuplePhysical_eq (d : Decomposition) (P : Finset ℕ) (giant bulk spectator : PrimeSource)
    {ι : Type*} [Fintype ι] (aux : ι → PrimeSource) (b s : ℕ) (tb td : ℤ) (X : ℝ)
    (x : JointSample giant bulk spectator aux b s) :
    tuplePhysical d P giant bulk spectator aux b s tb td X x =
      (tupleBins tb td x:ℂ) * (∑' n : ℤ,
        (∏i,tupleLocalTest d P i (tupleValues x i) (n:ZMod (tupleValues x i))) *
          SchwartzCutoff.psi ((n:ℝ)/X)) / (Real.sqrt X:ℂ) := by
  unfold tuplePhysical
  congr 1
  rw [← tsum_mul_left]
  apply tsum_congr
  intro n
  rw [mul_assoc,tupleTest_eq]
  ring

end Ostmann.Construction.InitialEta

end

end OAI
