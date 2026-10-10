import OAI.Geometry.PeriodicTiling.OrdinaryModel
import OAI.Geometry.PeriodicTiling.BlockActivationInverse

namespace OAI

noncomputable section

namespace PeriodicTilingThree.CommonModel

variable {p : ℕ} [NeZero p] (E : EncodingParameters p)

def ordinaryForward (n : Column p) (x : Plane) (k : K E (.inl n))
    (j : ActivationIndex E (.inl n)) : P E (.inl n) × K E (.inl n) :=
  (ordinaryUseful E n (x - ordinaryOffset E n j) (k - j.1) +
    shift (E.a (.inl n)) (E.b (.inl n)) j.2,
    ordinaryHigh E n (x - ordinaryOffset E n j) (k - j.1))

theorem ordinaryForward_bijective (n : Column p) (x : Plane) (k : K E (.inl n)) :
    Function.Bijective (ordinaryForward E n x k) := by
  let D := channelDigitBlocks E (.inl n) (ordinarySymbol E n x)
  let S := BlockShiftData.ofMultiplicity
    (E.a_two_le (.inl n)) (E.b_two_le (.inl n))
  let e := BlockShiftData.blockInverseEquiv D S
    (fun j => (ordinaryOffset E n j).1)
    (fun j => ordinaryOffset_rhoA E n j)
    (fun j => ordinaryOffset_rhoB E n j) x.1 k
  have he : ordinaryForward E n x k = e := by
    funext j
    simp only [ordinaryForward, ordinaryUseful_offset, ordinaryHigh_offset]
    rfl
  rw [he]
  exact e.bijective

end PeriodicTilingThree.CommonModel

end

end OAI
