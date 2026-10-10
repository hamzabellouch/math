import OAI.NumberTheory.PiExponent.Polynomials.GradedLocalizationExact

namespace OAI

namespace PiExponent.GradedLocalizationFree

noncomputable section
open scoped BigOperators
open GradedLocalizationExact

variable {R J σR : Type*} [CommRing R] [Fintype J]
  [SetLike σR R] [AddSubgroupClass σR R]

def coordinateMap (a : R) :
    LocalizedModule (Submonoid.powers a) (J → R) →ₗ[R]
      (J → LocalizedModule (Submonoid.powers a) R) :=
  LinearMap.pi (fun j => localizedMap a (LinearMap.proj j))

omit [Fintype J] in
@[simp] theorem coordinateMap_fraction (a : R) (v : J → R) (n : ℕ) (j : J) :
    coordinateMap a (fraction a v n) j = fraction a (v j) n := by
  change localizedMap a (LinearMap.proj (φ := fun _ : J => R) j) (fraction a v n) = _
  exact localizedMap_fraction a (LinearMap.proj (φ := fun _ : J => R) j) v n

theorem coordinateMap_injective (a : R) : Function.Injective (coordinateMap (J := J) a) := by
  classical
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm ?_ bot_le
  intro z hz
  change coordinateMap a z = 0 at hz
  change z = 0
  induction z using LocalizedModule.induction_on with
  | _ v s =>
    obtain ⟨n, hn⟩ := s.property
    have hs : s = powerDenominator a n := Subtype.ext hn.symm
    subst s
    change coordinateMap a (fraction a v n) = 0 at hz
    have hcoord : ∀ j, ∃ k : ℕ, a ^ k • v j = 0 := by
      intro j
      apply (fraction_eq_zero a (v j) n).mp
      have h := congrFun hz j
      simpa only [coordinateMap_fraction, Pi.zero_apply] using h
    choose k hk using hcoord
    let K : ℕ := ∑ j, k j
    apply (fraction_eq_zero a v n).mpr
    refine ⟨K, ?_⟩
    funext j
    have hj : k j ≤ K := Finset.single_le_sum (fun i _ => Nat.zero_le (k i))
      (Finset.mem_univ j)
    change a ^ K • v j = 0
    calc
      a ^ K • v j = (a ^ (K - k j) * a ^ k j) • v j := by
        rw [← pow_add, Nat.sub_add_cancel hj]
      _ = 0 := by rw [mul_smul, hk j, smul_zero]

variable (𝒜 : ℤ → σR) [SetLike.GradedMonoid 𝒜]
  (w : J → ℤ) (a : R) (e : ℤ) (ha : a ∈ 𝒜 e) (d : ℤ)

def coordinatePieces :
    degreePiece 𝒜 (ShiftedFreeGrading.piece 𝒜 w) a e ha d →+
      (∀ j, degreePiece 𝒜 𝒜 a e ha (d - w j)) where
  toFun z j := ⟨coordinateMap a z.val j, by
    obtain ⟨n, v, hv, hz⟩ := z.property
    refine ⟨n, v j, ?_, ?_⟩
    · have h := hv j
      change v j ∈ 𝒜 (d + (n : ℤ) * e - w j) at h
      convert h using 1
      ring_nf
    · rw [hz, coordinateMap_fraction]⟩
  map_zero' := by
    funext j
    exact Subtype.ext (congrFun (map_zero (coordinateMap a)) j)
  map_add' z z' := by
    funext j
    exact Subtype.ext (congrFun (map_add (coordinateMap a) z.val z'.val) j)

@[simp] theorem coordinatePieces_coe
    (z : degreePiece 𝒜 (ShiftedFreeGrading.piece 𝒜 w) a e ha d) (j : J) :
    (coordinatePieces 𝒜 w a e ha d z j).val = coordinateMap a z.val j := rfl

theorem coordinatePieces_injective : Function.Injective (coordinatePieces 𝒜 w a e ha d) := by
  intro z z' h
  apply Subtype.ext
  apply coordinateMap_injective a
  funext j
  exact congrArg Subtype.val (congrFun h j)

theorem coordinatePieces_surjective : Function.Surjective (coordinatePieces 𝒜 w a e ha d) := by
  classical
  intro z
  have hz : ∀ j, ∃ (n : ℕ) (m : R),
      m ∈ 𝒜 (d - w j + (n : ℤ) * e) ∧ (z j).val = fraction a m n :=
    fun j => (z j).property
  choose n m hm hzm using hz
  let N : ℕ := ∑ j, n j
  have hn (j : J) : n j ≤ N := Finset.single_le_sum
    (fun i _ => Nat.zero_le (n i)) (Finset.mem_univ j)
  let v : J → R := fun j => a ^ (N - n j) • m j
  have hv : v ∈ ShiftedFreeGrading.piece 𝒜 w (d + (N : ℤ) * e) := by
    intro j
    have h := power_smul_mem 𝒜 𝒜 a e ha (hm j) (N - n j)
    change v j ∈ 𝒜 (d + (N : ℤ) * e - w j)
    dsimp only [v]
    convert h using 1
    rw [Nat.cast_sub (hn j)]
    ring_nf
  refine ⟨⟨fraction a v N, N, v, hv, rfl⟩, ?_⟩
  funext j
  apply Subtype.ext
  change coordinateMap a (fraction a v N) j = (z j).val
  rw [coordinateMap_fraction, hzm]
  change fraction a (a ^ (N - n j) • m j) N = fraction a (m j) (n j)
  have hc := fraction_cancel a (m j) (n j) (N - n j)
  simpa only [Nat.add_sub_of_le (hn j)] using hc

def shiftedFreeEquiv :
    degreePiece 𝒜 (ShiftedFreeGrading.piece 𝒜 w) a e ha d ≃+
      (∀ j, degreePiece 𝒜 𝒜 a e ha (d - w j)) :=
  AddEquiv.ofBijective (coordinatePieces 𝒜 w a e ha d)
    ⟨coordinatePieces_injective 𝒜 w a e ha d,
      coordinatePieces_surjective 𝒜 w a e ha d⟩

@[simp] theorem shiftedFreeEquiv_apply
    (z : degreePiece 𝒜 (ShiftedFreeGrading.piece 𝒜 w) a e ha d) (j : J) :
    (shiftedFreeEquiv 𝒜 w a e ha d z j).val = coordinateMap a z.val j := rfl

end
end PiExponent.GradedLocalizationFree

end OAI
