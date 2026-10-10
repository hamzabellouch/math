import OAI.NumberTheory.Ostmann.Construction.OffDiagonalSumExchange

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Construction

theorem extendedOffDiagonal_eq_actualAmplitude
    (d : Decomposition) (P : Finset ℕ) (sources : SourceFamily) (seed : List SourceSlot)
    (V : ℕ→ℕ) (giant spectator : PrimeSource) (m : ℕ) (X G : ℝ)
    (bins : List ℕ→State→ℝ) (l : ℕ)
    (hseed : ∀q∈seed,∀j,q.role=.compensation j → 0<j)
    (hgiants : ∀x:RemainingSample sources (Template.remainder (l+1) (Template.current seed l)) giant,
      (remainingPrior sources (Template.remainder (l+1) (Template.current seed l)) giant).mass x≠0 →
      ∀j≤l+1,V j<x.1.val)
    (hlarge : ∀x:RemainingSample sources (Template.remainder (l+1) (Template.current seed l)) giant,
      (remainingPrior sources (Template.remainder (l+1) (Template.current seed l)) giant).mass x≠0 →
      ∀q∈assignedSlots sources (Template.remainder (l+1) (Template.current seed l)) x.2,V (l+1)<q.value)
    (hcut : ∀outside:List ℕ,
      ∀u:SourceAssignment sources (Template.extracted (l+1) (Template.current seed l)),
      (assignmentPrior sources (Template.extracted (l+1) (Template.current seed l))).mass u≠0 →
      ∀x y:RemainingSample sources (Template.remainder (l+1) (Template.current seed l)) giant,
      (remainingPrior sources (Template.remainder (l+1) (Template.current seed l)) giant).mass x≠0 →
      (remainingPrior sources (Template.remainder (l+1) (Template.current seed l)) giant).mass y≠0 →
      ∀v w:AllowedFrequency V l,∀p∈integerPivotCell G,∀s:ℤ,
      joinedNumerator sources (Template.remainder (l+1) (Template.current seed l)) giant x y v.val w.val=
        s*((assignedSlots sources (Template.extracted (l+1) (Template.current seed l)) u).map SmallSlot.value).prod*(p:ℤ) →
      pivotPairWeight d P sources seed V giant X G bins outside l u x y v w p≠0 → s.natAbs≤V (l+1)) :
    extendedOffDiagonal d P sources seed V giant spectator m X G bins l=
      actualAmplitude sources seed V giant spectator m X G
        (residueTransform d) (favorableGiantResidueTransform d P) bins (l+1) := by
  unfold extendedOffDiagonal
  rw [actualAmplitude_joined]
  apply congrArg (FinitePrior.cmean (spectatorPrior spectator m))
  funext ds
  simp_rw [offDiagonal_weighted_pair_expansion]
  rw [FinitePrior.cmean_pair_counted_exchange]
  apply FinitePrior.cmean_congr_support
  intro x hx
  apply FinitePrior.cmean_congr_support
  intro y hy
  let outside := spectatorList spectator ds
  let R := Template.remainder (l+1) (Template.current seed l)
  let E := Template.extracted (l+1) (Template.current seed l)
  let μ := assignmentPrior sources E
  let a (s : AllowedFrequency V (l+1)) := joinedRemainingState sources R giant x y s.val
  let A (s : AllowedFrequency V (l+1)) (v w : AllowedFrequency V l)
      (u : SourceAssignment sources E) :=
    actualNodeTerm sources seed V X G (residueTransform d) bins outside l (a s) v w u
  let Gnew (s : AllowedFrequency V (l+1)) :=
    regularTransform (residueTransform d) (favorableGiantResidueTransform d P) outside (a s)
  have hpairs (v w : AllowedFrequency V l) :
      μ.cmean (fun u => ∑p∈integerPivotCell G,
        let N := joinedNumerator sources R giant x y v.val w.val
        if ((assignedSlots sources E u).map SmallSlot.value).prod*(p:ℤ)∣N ∧ N≠0
        then pivotPairWeight d P sources seed V giant X G bins outside l u x y v w p else 0)=
      μ.cmean (fun u => ∑s:AllowedFrequency V (l+1),Gnew s*A s v w u) := by
    apply FinitePrior.cmean_congr_support
    intro u hu
    rw [pivotPair_frequency_reindex d P sources seed V giant X G bins outside l u x y v w
      (hcut outside u hu x y hx hy v w)]
    apply Finset.sum_congr rfl
    intro s hs
    exact pivotPair_frequency_term d P sources seed V giant X G bins outside l u x y v w s
      hseed (fun j hj => ⟨hgiants x hx j hj,hgiants y hy j hj⟩) (hlarge x hx)
  change (∑v:AllowedFrequency V l,∑w:AllowedFrequency V l,
      μ.cmean (fun u => ∑p∈integerPivotCell G,
        let N := joinedNumerator sources R giant x y v.val w.val
        if ((assignedSlots sources E u).map SmallSlot.value).prod*(p:ℤ)∣N ∧ N≠0
        then pivotPairWeight d P sources seed V giant X G bins outside l u x y v w p else 0))=
    ∑s:AllowedFrequency V (l+1),Gnew s*
      actualCoefficient sources seed V X G (residueTransform d) bins outside (l+1) (a s)
  simp_rw [hpairs]
  rw [FinitePrior.counted_pair_frequency_exchange]
  apply Finset.sum_congr rfl
  intro s hs
  congr 1
  exact (actualCoefficient_prime_node sources seed V X G (residueTransform d) bins outside l (a s)
    (giant.prime _ x.1.property) (giant.prime _ y.1.property)
    (fun j hj => ⟨hgiants x hx j (by omega),hgiants y hy j (by omega)⟩)).symm

end Ostmann.Construction

end

end OAI
