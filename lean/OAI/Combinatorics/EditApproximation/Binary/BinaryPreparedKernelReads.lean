import OAI.Combinatorics.EditApproximation.Binary.BinaryLocalGroupReads
import OAI.Combinatorics.EditApproximation.Binary.BinaryLocalOnlineReads
import OAI.Combinatorics.EditApproximation.Binary.BinaryContinuationReads
import OAI.Combinatorics.EditApproximation.Binary.BinaryRepresentativeReads
import OAI.Combinatorics.EditApproximation.Binary.BinaryPreparedLocalKernel

namespace OAI

/-! Complete reader-aware local refinement. Initial, mass, historical,
and current values are obtained through costed finite-buffer readers;
the complete Boolean continuation has exactly the original return word. -/

namespace EditApproximation
namespace BinaryFraction

section Kernel
variable {α : Type*} (source target : List α) {M : ℕ}
  (parent : TargetInterval source.length) (N P F exponent H Q eM eF : ℕ)
  (hP : 0 < P) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF)
  (tau a eta kappa delta : BinaryFraction)
  (parentInitial : TargetInterval target.length → BinaryFraction × ℕ)
  (childMass childInitial : Fin M → TargetInterval target.length → BinaryFraction × ℕ)
  (old current : Fin M × TargetInterval target.length → BinaryFraction × ℕ)
  (history : ℕ → Fin M × TargetInterval target.length → BinaryFraction × ℕ)
  (R : ℕ) (hm : ∀ i q, (childMass i q).2 ≤ R) (hi : ∀ i q, (childInitial i q).2 ≤ R)
  (t : ℕ) (draw : CellGroupDraws M F Q) (integer : ℕ → TargetInterval target.length → ℕ)
  (query : TargetInterval target.length)

def preparedLocalKernelReadWithWork : BinaryFraction × ℕ :=
  let fallback := parentInitial query
  let representatives := localRepresentativeReadWithWork N P F a parentInitial query
  let groups := preparedLocalCellGroupsReadWithWork source target parent P F exponent Q eM eF
    hM hF hP tau a parentInitial childMass childInitial (fun i r => current (i, r)) R hm hi N draw query
  let online := preparedLocalOnlineActionsReadWithWork source target parent P F exponent H hP tau a eta kappa
    parentInitial childMass childInitial history R hm hi t integer N query
  let result := physicalContinuationReadWithWork parent representatives.1 P F delta fallback.1
    old current groups.1 online.1 query
  (result.1, fallback.2 + representatives.2 + groups.2 + online.2 + result.2 + 4)

theorem preparedLocalKernelReadWithWork_eq
    (hp : ∀ r, (parentInitial r).2 ≤ R) (ho : ∀ s, (old s).2 ≤ R)
    (hn : ∀ s, (current s).2 ≤ R) (hh : ∀ s ≤ t + 1, ∀ i, (history s i).2 ≤ R) :
    (preparedLocalKernelReadWithWork source target parent N P F exponent H Q eM eF hP hM hF
      tau a eta kappa delta parentInitial childMass childInitial old current history R hm hi t draw integer query).1 =
    (preparedLocalKernelWithWork source target parent N P F exponent H Q eM eF hP hM hF
      tau a eta kappa delta (fun r => (parentInitial r).1) (fun i r => (childMass i r).1)
      (fun i r => (childInitial i r).1) (fun s => (old s).1) (fun s => (current s).1)
      (fun t s => (history t s).1) t draw integer query).1 := by
  have hr := (localRepresentativeReadWithWork_eq_cost N P F a parentInitial query R hp).1
  have hg := preparedLocalCellGroupsReadWithWork_eq source target parent P F exponent Q eM eF
    hM hF hP tau a parentInitial childMass childInitial (fun i r => current (i, r)) R hm hi
    N draw query hp (fun i r => hn (i, r))
  have honline := preparedLocalOnlineActionsReadWithWork_eq source target parent P F exponent H hP
    tau a eta kappa parentInitial childMass childInitial history R hm hi t integer N query hh
  unfold preparedLocalKernelReadWithWork preparedLocalKernelWithWork
  dsimp only
  rw [hr, hg, honline]
  exact (physicalContinuationReadWithWork_eq_cost parent _ P F delta (parentInitial query).1
    old current _ _ query R ho hn).1

def cachedPreparedLocalKernelReadWithWork (base : List Bool)
    (hbase : 0 < bitWordValue base) (remaining : ℕ) : BinaryFraction × ℕ :=
  finishCachedWithWork
    (preparedLocalKernelReadWithWork source target parent N P F exponent H Q eM eF hP hM hF
      tau a eta kappa delta parentInitial childMass childInitial old current history R hm hi t draw integer query)
    base hbase remaining

theorem cachedPreparedLocalKernelReadWithWork_eq (base : List Bool)
    (hbase : 0 < bitWordValue base) (remaining : ℕ)
    (hp : ∀ r, (parentInitial r).2 ≤ R) (ho : ∀ s, (old s).2 ≤ R)
    (hn : ∀ s, (current s).2 ≤ R) (hh : ∀ s ≤ t + 1, ∀ i, (history s i).2 ≤ R) :
    (cachedPreparedLocalKernelReadWithWork source target parent N P F exponent H Q eM eF hP hM hF
      tau a eta kappa delta parentInitial childMass childInitial old current history R hm hi t draw integer query
      base hbase remaining).1 =
    (cachedPreparedLocalKernelWithWork source target parent N P F exponent H Q eM eF hP hM hF
      tau a eta kappa delta (fun r => (parentInitial r).1) (fun i r => (childMass i r).1)
      (fun i r => (childInitial i r).1) (fun s => (old s).1) (fun s => (current s).1)
      (fun t s => (history t s).1) t draw integer query base hbase remaining).1 := by
  simp only [cachedPreparedLocalKernelReadWithWork, cachedPreparedLocalKernelWithWork,
    finishCachedWithWork, preparedLocalKernelReadWithWork_eq source target parent N P F exponent H Q eM eF
      hP hM hF tau a eta kappa delta parentInitial childMass childInitial old current history R hm hi
      t draw integer query hp ho hn hh]

end Kernel
end BinaryFraction
end EditApproximation

end OAI
