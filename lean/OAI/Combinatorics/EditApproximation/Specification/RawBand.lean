import OAI.Combinatorics.EditApproximation.AlmostLinear
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI.EditApproximation

/-- The finite data used after accepting an unskipped band. -/


def UnskippedBand.raw {α : Type*} {source target : List α} {M : ℕ}
    {parent : TargetInterval source.length} {b P exponent : ℕ}
    {tau F : ℚ} {child initial : Fin M → TargetInterval target.length → ℚ}
    (member : UnskippedBand source target parent b P exponent tau F child initial) :
    RawUnskippedBand M target.length :=
  ⟨member.center, member.actions, member.nonempty⟩

namespace BinaryFraction



theorem preparedUnskippedReadWithWorkRaw_eq {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (b P exponent : ℕ) (hb : 0 < b) (hP : 0 < P)
    (tau F : BinaryFraction)
    (read initial : Fin M → TargetInterval target.length → BinaryFraction × ℕ)
    (R C : ℕ) (hr : ∀ i q, (read i q).2 ≤ R) (hi : ∀ i q, (initial i q).2 ≤ C)
    (center : TargetInterval target.length) :
    preparedUnskippedReadWithWorkRaw parent b P exponent tau F read initial center =
      Prod.map (Option.map UnskippedBand.raw) id
        (preparedUnskippedReadWithWork source target parent b P exponent hb hP tau F
          read initial R C hr hi center) := by
  have hbandValue : (preparedRepresentativeReadWithWork parent center (parent.hi - parent.lo)
      b P tau (inversePowerTwo exponent) read).1 =
      representativeBandActions source target parent center b P tau.value
        ((2 : ℚ) ^ (-(exponent : ℤ))) (fun i q => (read i q).1.value) := by
    apply (preparedRepresentativeReadWithWork_eq_cost parent center (parent.hi - parent.lo)
      b P tau (inversePowerTwo exponent) read R hr).1.trans
    simpa only [inversePowerTwo_value] using preparedRepresentativeWithWork_value source target
      parent center b P hP tau (inversePowerTwo exponent) (fun i q => (read i q).1)
  unfold preparedUnskippedReadWithWorkRaw preparedUnskippedReadWithWork
  dsimp only
  split_ifs with hempty hguard
  · rfl
  · simp only [Prod.map, Option.map_some, id_eq, UnskippedBand.raw, UnskippedBand.actions]
    congr 3
  · rfl

end BinaryFraction
end OAI.EditApproximation
