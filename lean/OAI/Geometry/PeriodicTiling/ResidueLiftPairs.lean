import OAI.Geometry.PeriodicTiling.ResidueCoordinates

namespace OAI

universe uA uB

namespace PeriodicTilingThree

noncomputable def PairGood (m : ℕ) (d : Lattice 3) (u v : Residue3 m) :
    Finset (LiftAlphabet × LiftAlphabet) := by
  classical
  exact Finset.univ.filter (fun p => ∀ i,
    can v i + (m : ℤ) * signed p.2 i - (can u i + (m : ℤ) * signed p.1 i) = d i)

@[simp] theorem mem_PairGood {m : ℕ} {d : Lattice 3} {u v : Residue3 m}
    {p : LiftAlphabet × LiftAlphabet} :
    p ∈ PairGood m d u v ↔ ∀ i,
      can v i + (m : ℤ) * signed p.2 i - (can u i + (m : ℤ) * signed p.1 i) = d i := by
  classical
  simp only [PairGood, Finset.mem_filter, Finset.mem_univ, true_and]

theorem pairGood_assignment_iff {m : ℕ} [NeZero m] {d : Lattice 3}
    (ω : LiftAssignment m) (u v : Residue3 m) :
    (ω u, ω v) ∈ PairGood m d u v ↔ representative m ω v - representative m ω u = d := by
  rw [mem_PairGood, funext_iff]
  rfl

private def coordinateLiftPair (z : ℤ) (hz : -2 ≤ z ∧ z ≤ 2) (j : Fin 3) :
    Fin 5 × Fin 5 :=
  (⟨j.val + (-z).toNat, by have hj := j.isLt; omega⟩,
   ⟨j.val + z.toNat, by have hj := j.isLt; omega⟩)

private theorem coordinateLiftPair_difference (z : ℤ) (hz : -2 ≤ z ∧ z ≤ 2)
    (j : Fin 3) :
    ((coordinateLiftPair z hz j).2.val : ℤ) - (coordinateLiftPair z hz j).1.val = z := by
  dsimp [coordinateLiftPair]
  omega

private theorem coordinateLiftPair_injective (z : ℤ) (hz : -2 ≤ z ∧ z ≤ 2) :
    Function.Injective (coordinateLiftPair z hz) := by
  intro a b hab
  apply Fin.ext
  have h := congrArg (fun p : Fin 5 × Fin 5 => p.1.val) hab
  dsimp [coordinateLiftPair] at h
  exact Nat.add_right_cancel h

private def liftPairForDifference (z : Lattice 3) (hz : ∀ i, -2 ≤ z i ∧ z i ≤ 2)
    (a : Fin 3 → Fin 3) : LiftAlphabet × LiftAlphabet :=
  (fun i => (coordinateLiftPair (z i) (hz i) (a i)).1,
   fun i => (coordinateLiftPair (z i) (hz i) (a i)).2)

private theorem liftPairForDifference_injective (z : Lattice 3)
    (hz : ∀ i, -2 ≤ z i ∧ z i ≤ 2) : Function.Injective (liftPairForDifference z hz) := by
  intro a b hab
  funext i
  apply coordinateLiftPair_injective (z i) (hz i)
  apply Prod.ext
  · exact congrArg (fun p : LiftAlphabet × LiftAlphabet => p.1 i) hab
  · exact congrArg (fun p : LiftAlphabet × LiftAlphabet => p.2 i) hab

private theorem liftPairForDifference_signed_sub (z : Lattice 3)
    (hz : ∀ i, -2 ≤ z i ∧ z i ≤ 2) (a : Fin 3 → Fin 3) (i : Fin 3) :
    signed (liftPairForDifference z hz a).2 i -
      signed (liftPairForDifference z hz a).1 i = z i := by
  have h := coordinateLiftPair_difference (z i) (hz i) (a i)
  dsimp [signed, liftPairForDifference]
  omega

private theorem card_le_finset_of_injective {A : Type uA} {B : Type uB} [Fintype A]
    (s : Finset B) (f : A → B) (hfinj : Function.Injective f)
    (hmem : ∀ a, f a ∈ s) : Fintype.card A ≤ s.card := by
  classical
  let g : A → ↥s := fun a => ⟨f a, hmem a⟩
  have hginj : Function.Injective g := by
    intro a b hab
    exact hfinj (congrArg Subtype.val hab)
  have hc := Fintype.card_le_of_injective g hginj
  simpa only [Fintype.card_coe] using hc

theorem card_PairGood_ge {m : ℕ} [NeZero m] {d : Lattice 3} {u v : Residue3 m}
    (hd : Requested m d) (hv : v = u + residueMod m d) :
    27 ≤ (PairGood m d u v).card := by
  classical
  let z := liftDifference m d u v
  have hz : ∀ i, -2 ≤ z i ∧ z i ≤ 2 := by
    intro i
    have h := liftDifference_bounds hd hv i
    change -2 ≤ liftDifference m d u v i ∧ liftDifference m d u v i ≤ 2
    omega
  let f : (Fin 3 → Fin 3) → LiftAlphabet × LiftAlphabet := liftPairForDifference z hz
  have hfinj : Function.Injective f := liftPairForDifference_injective z hz
  have hf : ∀ a, f a ∈ PairGood m d u v := by
    intro a
    rw [mem_PairGood]
    intro i
    have hdiff := liftPairForDifference_signed_sub z hz a i
    have hcarry := liftDifference_eq hv i
    change (m : ℤ) * z i = d i - (can v i - can u i) at hcarry
    change can v i + (m : ℤ) * signed (liftPairForDifference z hz a).2 i -
      (can u i + (m : ℤ) * signed (liftPairForDifference z hz a).1 i) = d i
    rw [← hdiff] at hcarry
    nlinarith
  generalize hS : PairGood m d u v = S at hf ⊢
  have hc : Fintype.card (Fin 3 → Fin 3) ≤ S.card :=
    card_le_finset_of_injective S f hfinj hf
  have h27 : Fintype.card (Fin 3 → Fin 3) = 27 := by norm_num
  rwa [h27] at hc

end PeriodicTilingThree

end OAI
