import OAI.Combinatorics.MatchingPSD.CutGeometry

namespace OAI

universe u_1 u_2 u_3 u_4 u_5 u_6

namespace MatchingSmoothing
open scoped BigOperators
attribute [local instance] Classical.propDecidable
section CellAverages
variable {A : Type u_1} {B : Type u_2} {C : Type u_3} {I : Type u_4} [Fintype A] [Fintype B] [Fintype C] [Fintype I] [DecidableEq I]

noncomputable def extensionAverage (i : I) (f : Pairing ((A ⊕ B) ⊕ (I × C)) → ℝ)
    (M : Pairing ((A ⊕ B) ⊕ C)) : ℝ :=
  𝔼 N : {j : I // j ≠ i} → Pairing C, f (extendLocal i M N)

noncomputable def cellAverage (i : I) (f : Pairing ((A ⊕ B) ⊕ (I × C)) → ℝ)
    (x : Fin 3 → ℝ) : ℝ :=
  predicateAverage (fun M => crossVector threeColor M = x) (extensionAverage i f)

omit [Fintype A] [Fintype B] in
lemma extensionAverage_relabel (i : I) (p : Equiv.Perm ((A ⊕ B) ⊕ C))
    (f : Pairing ((A ⊕ B) ⊕ (I × C)) → ℝ) (M : Pairing ((A ⊕ B) ⊕ C)) :
    extensionAverage i f (Pairing.relabel p M) =
      extensionAverage i (fun N => f (Pairing.relabel (liftLocal i p) N)) M := by
  simp only [extensionAverage, extendLocal_relabel]

lemma expect_pair_product {X : Type u_5} {Y : Type u_6} [Fintype X] [Fintype Y] (f : X × Y → ℝ) :
    (𝔼 p : X × Y, f p) = 𝔼 x : X, 𝔼 y : Y, f (x,y) := by
  rw [← Finset.univ_product_univ, Finset.expect_product]

lemma cellAverage_star (i : I) (f : Pairing ((A ⊕ B) ⊕ (I × C)) → ℝ) (x : ℝ) :
    cellAverage i f ![x,0,0] =
      𝔼 M : {M : Pairing (A ⊕ B) // tableCoordinate abColor (0,1) M = x},
        𝔼 N : I → Pairing C, f (Pairing.sum M.1 (Pairing.cellwise N)) := by
  classical
  rw [cellAverage, predicateAverage_eq_expect]
  have he := Fintype.expect_equiv (starFiberEquiv (A := A) (B := B) (C := C) x)
    (fun p => extensionAverage i f (Pairing.sum p.1.1 p.2))
    (fun p => extensionAverage i f p.1) (fun _ => rfl)
  calc
    _ = 𝔼 p : {M : Pairing (A ⊕ B) // tableCoordinate abColor (0,1) M = x} × Pairing C,
        extensionAverage i f (Pairing.sum p.1.1 p.2) := by
          convert he.symm using 1
          congr 1
          ext; simp
    _ = _ := ?_
  rw [expect_pair_product]
  apply Finset.expect_congr rfl
  intro M _
  simp only [extensionAverage]
  calc
    _ = 𝔼 p : Pairing C × ({j : I // j ≠ i} → Pairing C),
        f (extendLocal i (Pairing.sum M.1 p.1) p.2) := by
      convert (expect_pair_product (fun p : Pairing C × ({j : I // j ≠ i} → Pairing C) =>
        f (extendLocal i (Pairing.sum M.1 p.1) p.2))).symm using 1
    _ = _ := (Fintype.expect_equiv (Equiv.piSplitAt i (fun _ : I => Pairing C))
      (fun N => f (Pairing.sum M.1 (Pairing.cellwise N)))
      (fun p => f (extendLocal i (Pairing.sum M.1 p.1) p.2))
      (fun N => by rw [Equiv.piSplitAt_apply, extendLocal_sum])).symm

lemma cellAverage_const (i : I) (f : Pairing ((A ⊕ B) ⊕ (I × C)) → ℝ)
    (x : Fin 3 → ℝ) (c : ℝ) (hM : ∃ M : Pairing ((A ⊕ B) ⊕ C), crossVector threeColor M = x)
    [Nonempty (Pairing C)]
    (hf : ∀ M, crossVector threeColor M = x → ∀ N, f (extendLocal i M N) = c) :
    cellAverage i f x = c := by
  apply predicateAverage_of_constant _ _ hM
  intro M hM
  simp only [extensionAverage, hf M hM, Finset.expect_const, Finset.univ_nonempty]

end CellAverages
end MatchingSmoothing

end OAI
