import OAI.Combinatorics.EditApproximation.Binary.BinaryLocalGroupSource
import OAI.Combinatorics.EditApproximation.Binary.BinaryLocalOnlineSource
import OAI.Combinatorics.EditApproximation.Binary.BinaryPreparedKernelReads

namespace OAI

/-! The full local continuation with both data reads and scalar source
reads charged. Its binary return word agrees with the refinement kernel. -/

namespace EditApproximation.BinaryFraction
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
  (t : ℕ) (draw : CellGroupReadDraws M F Q)
  (integer : ℕ → TargetInterval target.length → ℕ × ℕ)
  (query : TargetInterval target.length)

def preparedLocalSourceKernelWithWork : BinaryFraction × ℕ :=
  let fallback := parentInitial query
  let representatives := localRepresentativeReadWithWork N P F a parentInitial query
  let groups := preparedLocalCellGroupsSourceWithWork source target parent P F exponent Q eM eF
    hM hF hP tau a parentInitial childMass childInitial (fun i r => current (i, r)) R hm hi N draw query
  let online := preparedLocalOnlineActionsSourceWithWork source target parent P F exponent H hP tau a eta kappa
    parentInitial childMass childInitial history R hm hi t integer N query
  let result := physicalContinuationReadWithWork parent representatives.1 P F delta fallback.1
    old current groups.1 online.1 query
  (result.1, fallback.2 + representatives.2 + groups.2 + online.2 + result.2 + 4)

theorem preparedLocalSourceKernelWithWork_eq_cost (S : ℕ)
    (hd : ∀ b cell s i, (draw b cell s i).2 ≤ S) (hs : ∀ b q, (integer b q).2 ≤ S) :
    (preparedLocalSourceKernelWithWork source target parent N P F exponent H Q eM eF hP hM hF
      tau a eta kappa delta parentInitial childMass childInitial old current history R hm hi t
      draw integer query).1 =
      (preparedLocalKernelReadWithWork source target parent N P F exponent H Q eM eF hP hM hF
        tau a eta kappa delta parentInitial childMass childInitial old current history R hm hi t
        (fun b cell s i => (draw b cell s i).1) (fun b q => (integer b q).1) query).1 ∧
    (preparedLocalSourceKernelWithWork source target parent N P F exponent H Q eM eF hP hM hF
      tau a eta kappa delta parentInitial childMass childInitial old current history R hm hi t
      draw integer query).2 ≤
      (preparedLocalKernelReadWithWork source target parent N P F exponent H Q eM eF hP hM hF
        tau a eta kappa delta parentInitial childMass childInitial old current history R hm hi t
        (fun b cell s i => (draw b cell s i).1) (fun b q => (integer b q).1) query).2 * (S + 4) := by
  have hg := preparedLocalCellGroupsSourceWithWork_eq_cost source target parent P F exponent Q eM eF
    hM hF hP tau a parentInitial childMass childInitial (fun i r => current (i, r)) R hm hi
    N draw query S hd
  have ho := preparedLocalOnlineActionsSourceWithWork_eq_cost source target parent P F exponent H hP
    tau a eta kappa parentInitial childMass childInitial history R hm hi t integer N query S hs
  unfold preparedLocalSourceKernelWithWork preparedLocalKernelReadWithWork
  dsimp only
  rw [hg.1, ho.1]
  exact ⟨rfl, by nlinarith only [hg.2, ho.2]⟩

end Kernel
end EditApproximation.BinaryFraction

end OAI
