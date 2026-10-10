import OAI.NumberTheory.EgyptianFractions.GoldbachSieveLocal

namespace OAI
noncomputable section

open scoped BigOperators

namespace Problem337

instance goldbachSieveRootFintype (u d : ℕ) [NeZero d] :
    Fintype (GoldbachSieveRoot u d) :=
  inferInstanceAs (Fintype {x : ZMod d // x * ((u : ZMod d) - x) = 0})

instance goldbachSieveRootNonempty (u d : ℕ) : Nonempty (GoldbachSieveRoot u d) :=
  ⟨⟨0, by simp⟩⟩

/-- Reduction modulo two possibly noncoprime moduli is injective when the
source modulus is their least common multiple. This remains true on roots. -/
def goldbachSieveRootLCMEmbedding (u a b : ℕ) :
    GoldbachSieveRoot u (a.lcm b) ↪
      GoldbachSieveRoot u a × GoldbachSieveRoot u b := by
  let e : ZMod (a.lcm b) →+* ZMod a × ZMod b :=
    ZMod.castHom (dvd_refl (a.lcm b)) _
  have einj : Function.Injective e := ZMod.castHom_injective _
  have he (x : GoldbachSieveRoot u (a.lcm b)) :
      (e x.val).1 * ((u : ZMod a) - (e x.val).1) = 0 ∧
        (e x.val).2 * ((u : ZMod b) - (e x.val).2) = 0 := by
    have h := congrArg e x.property
    simpa only [map_mul, map_sub, map_natCast, map_zero, Prod.mul_def,
      Prod.sub_def, Prod.ext_iff, Prod.fst_natCast, Prod.snd_natCast,
      Prod.fst_zero, Prod.snd_zero] using h
  refine ⟨fun x => (⟨(e x.val).1, (he x).1⟩, ⟨(e x.val).2, (he x).2⟩), ?_⟩
  intro x y hxy
  apply Subtype.ext
  apply einj
  apply Prod.ext
  · exact congrArg (fun z : GoldbachSieveRoot u a × GoldbachSieveRoot u b => z.1.val) hxy
  · exact congrArg (fun z : GoldbachSieveRoot u a × GoldbachSieveRoot u b => z.2.val) hxy

/-- LCM-submultiplicativity of the root count. This needs no squarefreeness. -/
theorem goldbachSieveRootCount_lcm_le (u a b : ℕ) [NeZero a] [NeZero b] :
    goldbachSieveRootCount u (a.lcm b) ≤
      goldbachSieveRootCount u a * goldbachSieveRootCount u b := by
  unfold goldbachSieveRootCount
  rw [← Nat.card_prod]
  exact Nat.card_le_card_of_injective (goldbachSieveRootLCMEmbedding u a b)
    (goldbachSieveRootLCMEmbedding u a b).injective

/-- Zero is always a root, so each positive modulus has positive local count. -/
theorem goldbachSieveRootCount_pos (u d : ℕ) [NeZero d] :
    0 < goldbachSieveRootCount u d := by
  exact Nat.card_pos

/-- The local root count cannot exceed the modulus. -/
theorem goldbachSieveRootCount_le (u d : ℕ) [NeZero d] :
    goldbachSieveRootCount u d ≤ d := by
  calc
    goldbachSieveRootCount u d ≤ Nat.card (ZMod d) :=
      Nat.card_le_card_of_injective (fun x : GoldbachSieveRoot u d => x.val)
        Subtype.val_injective
    _ = d := Nat.card_zmod d

/-- Exact exponent of two in a squarefree local root count. -/
theorem goldbachSieveRootCount_eq_two_pow (u d : ℕ) (hd : Squarefree d) :
    goldbachSieveRootCount u d =
      2 ^ (d.primeFactors.filter (fun p => ¬p ∣ u)).card := by
  rw [goldbachSieveRootCount_squarefree u d hd]
  have hf : (∏ p ∈ d.primeFactors, if p ∣ u then 1 else 2) =
      ∏ p ∈ d.primeFactors.filter (fun p => ¬p ∣ u), (2 : ℕ) := by
    rw [Finset.prod_filter]
    apply Finset.prod_congr rfl
    intro p hp
    split_ifs <;> simp_all
  rw [hf, Finset.prod_const]

/-- Squarefree local root counts are bounded by the number of subsets of
prime factors, uniformly in the target. -/
theorem goldbachSieveRootCount_le_two_pow (u d : ℕ) (hd : Squarefree d) :
    goldbachSieveRootCount u d ≤ 2 ^ d.primeFactors.card := by
  rw [goldbachSieveRootCount_eq_two_pow u d hd]
  exact Nat.pow_le_pow_right (by omega) (Finset.card_filter_le _ _)

end Problem337

end

end OAI
