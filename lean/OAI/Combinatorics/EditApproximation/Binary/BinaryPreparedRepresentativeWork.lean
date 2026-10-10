import OAI.Combinatorics.EditApproximation.Binary.BinaryPreparedRepresentative

namespace OAI

/-! Complete representative work, with every endpoint grid construction
and every score/prefix predicate charged. Only input word bounds occur. -/

namespace EditApproximation
namespace BinaryFraction

def wideMaterializationBitBudget (M P B : ℕ) : ℕ :=
  M * (wideChildGridBitBudget P B + 6) +
    (M + 1) * (6 * M + 10) * ((40 * P + 2) ^ 2 + 1) ^ (M + 1) + 1

theorem wideActionGridWithWork_complete_cost {nx ny : ℕ} (M : ℕ)
    (parent : TargetInterval nx) (center : TargetInterval ny) (b P B : ℕ)
    (hPpos : 0 < P) (hnx : Nat.size nx ≤ B) (hny : Nat.size ny ≤ B)
    (hM : Nat.size M ≤ B) (hb : Nat.size b ≤ B) (hP : Nat.size P ≤ B) :
    (wideActionGridWithWork M parent center b P).2 ≤ wideMaterializationBitBudget M P B :=
  wideActionGridWithWork_cost M parent center b P _ hPpos
    (fun i => wideChildGridWithWork_cost parent center b P B i hPpos hnx hny hM hb hP)

theorem preparedRepresentativeWithWork_complete_cost {nx ny M : ℕ}
    (parent : TargetInterval nx) (center : TargetInterval ny) (b P B : ℕ)
    (hPpos : 0 < P) (tau theta : BinaryFraction)
    (child : Fin M → TargetInterval ny → BinaryFraction)
    (hnx : Nat.size nx ≤ B) (hny : Nat.size ny ≤ B)
    (hM : Nat.size M ≤ B) (hb : Nat.size b ≤ B) (hP : Nat.size P ≤ B)
    (htau : tau.width ≤ B) (htheta : theta.width ≤ B)
    (hchild : ∀ i q, (child i q).width ≤ B) :
    (preparedRepresentativeWithWork parent center (parent.hi - parent.lo) b P tau theta child).2 ≤
      wideMaterializationBitBudget M P B +
      representativeCompleteBitBudget M (wideActionGridWithWork M parent center b P).1.length (4 * B + 20) +
      (wideActionGridWithWork M parent center b P).1.length + 1 := by
  let wide := wideActionGridWithWork M parent center b P
  let C := 4 * B + 20
  have hBC : B + 5 ≤ C := by dsimp only [C]; omega
  have hcenterlo : Nat.size center.lo ≤ B :=
    (Nat.size_le_size (center.ordered.trans center.valid)).trans hny
  have hcenterhi : Nat.size center.hi ≤ B := (Nat.size_le_size center.valid).trans hny
  have hparentlo : Nat.size parent.lo ≤ B :=
    (Nat.size_le_size (parent.ordered.trans parent.valid)).trans hnx
  have hparenthi : Nat.size parent.hi ≤ B := (Nat.size_le_size parent.valid).trans hnx
  have hsource (i : Fin M) : Nat.size (sourceChild parent i).lo ≤ B ∧
      Nat.size (sourceChild parent i).hi ≤ B :=
    ⟨(Nat.size_le_size ((sourceChild parent i).ordered.trans (sourceChild parent i).valid)).trans hnx,
      (Nat.size_le_size (sourceChild parent i).valid).trans hnx⟩
  have hanchor (x : ℕ) (hx : Nat.size x ≤ B) :
      Nat.size (center.lo + (x - parent.lo)) + 2 ≤ C := by
    have hs : Nat.size (x - parent.lo) ≤ B := (Nat.size_le_size (Nat.sub_le _ _)).trans hx
    have ha := binaryNaturalAdd_size_le center.lo (x - parent.lo)
    omega
  have hradius : Nat.size (6 * b) + 2 ≤ C := by
    have hp := natural_product_bit_length 6 b
    have h6 : Nat.size 6 = 3 := by decide
    omega
  have htail := representativeFromActionsWithWork_complete_cost parent center
    (parent.hi - parent.lo) b tau theta child (wide.1.map Vector.get) C
    (by omega) (by omega)
    (by have h := (Nat.size_le_size (Nat.sub_le parent.hi parent.lo)).trans hparenthi; omega)
    (by omega) (by omega) (by omega) (by omega) (by omega)
    (fun i => ⟨by have h := (hsource i).1; omega, by have h := (hsource i).2; omega⟩)
    (fun i => ⟨hanchor _ (hsource i).1, hanchor _ (hsource i).2⟩) hradius
    (fun states _ i =>
      ⟨by have h := (Nat.size_le_size ((states i).ordered.trans (states i).valid)).trans hny; omega,
       by have h := (Nat.size_le_size (states i).valid).trans hny; omega⟩)
    (fun _ _ i => (hchild i _).trans (by omega))
  have hwide := wideActionGridWithWork_complete_cost M parent center b P B hPpos hnx hny hM hb hP
  simp only [List.length_map] at htail
  change wide.2 + (representativeFromActionsWithWork parent center (parent.hi - parent.lo)
    b tau theta child (wide.1.map Vector.get)).2 + wide.1.length + 1 ≤ _
  exact Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add hwide htail) _) _

end BinaryFraction
end EditApproximation

end OAI
