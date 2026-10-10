import OAI.LinearAlgebra.CirculantHadamard.CyclicRing

namespace OAI

universe uR uS

/-!
# Quotients of actual cyclic group rings

For `m ∣ n`, reduction of indices defines the quotient map from the cyclic
group ring of order `n` to that of order `m`. In particular it sends the
distinguished generator to the distinguished generator and fixes scalars.
The definition is the convolution ring homomorphism induced by `ZMod.castHom`.
-/

noncomputable section

namespace CirculantHadamard

open CyclicRing

variable (R : Type uR) [Semiring R] {m n l : ℕ}

/-- The quotient of cyclic group rings induced by reduction of indices. -/
def cyclicProjection (h : m ∣ n) : Elem R n →+* Elem R m :=
  AddMonoidAlgebra.mapDomainRingHom R (ZMod.castHom h (ZMod m)).toAddMonoidHom

variable {R}

theorem cyclicProjection_apply (h : m ∣ n) (F : Elem R n) :
    cyclicProjection R h F = AddMonoidAlgebra.mapDomain (ZMod.castHom h (ZMod m)) F := rfl

@[simp] theorem cyclicProjection_single (h : m ∣ n) (a : ZMod n) (r : R) :
    cyclicProjection R h (AddMonoidAlgebra.single a r) =
      AddMonoidAlgebra.single (ZMod.castHom h (ZMod m) a) r :=
  AddMonoidAlgebra.mapDomain_single

@[simp] theorem cyclicProjection_single_zero (h : m ∣ n) (r : R) :
    cyclicProjection R h (AddMonoidAlgebra.single 0 r) = AddMonoidAlgebra.single 0 r := by
  simp

@[simp] theorem cyclicProjection_scalar (h : m ∣ n) (r : R) :
    cyclicProjection R h (scalar n r) = scalar m r := by
  exact cyclicProjection_single_zero h r

@[simp] theorem cyclicProjection_generator (h : m ∣ n) :
    cyclicProjection R h (AddMonoidAlgebra.single 1 1) = AddMonoidAlgebra.single 1 1 := by
  simp only [cyclicProjection_single, map_one]

@[simp] theorem cyclicProjection_single_natCast (h : m ∣ n) (a : ℕ) (r : R) :
    cyclicProjection R h (AddMonoidAlgebra.single (a : ZMod n) r) =
      AddMonoidAlgebra.single (a : ZMod m) r := by
  simp

@[simp] theorem cyclicProjection_self (F : Elem R n) :
    cyclicProjection R (dvd_refl n) F = F := by
  apply AddMonoidAlgebra.coeff_injective
  change Finsupp.mapDomain (ZMod.castHom (dvd_refl n) (ZMod n)) F.coeff = F.coeff
  simp [ZMod.castHom_self]

theorem cyclicProjection_comp (h₁ : l ∣ m) (h₂ : m ∣ n) (F : Elem R n) :
    cyclicProjection R h₁ (cyclicProjection R h₂ F) =
      cyclicProjection R (dvd_trans h₁ h₂) F := by
  apply AddMonoidAlgebra.coeff_injective
  change Finsupp.mapDomain (ZMod.castHom h₁ (ZMod l))
      (Finsupp.mapDomain (ZMod.castHom h₂ (ZMod m)) F.coeff) =
    Finsupp.mapDomain (ZMod.castHom (dvd_trans h₁ h₂) (ZMod l)) F.coeff
  rw [← Finsupp.mapDomain_comp]
  have hcomp : (ZMod.castHom h₁ (ZMod l) : ZMod m → ZMod l) ∘
      (ZMod.castHom h₂ (ZMod m) : ZMod n → ZMod m) =
      (ZMod.castHom (dvd_trans h₁ h₂) (ZMod l) : ZMod n → ZMod l) :=
    congrArg (fun f : ZMod n →+* ZMod l => (f : ZMod n → ZMod l))
      (ZMod.castHom_comp h₁ h₂)
  rw [hcomp]

/-- Any additive coefficient evaluation factors through the quotient exactly
when its index function is pulled back along reduction. -/
theorem sum_cyclicProjection {S : Type uS} [AddCommMonoid S]
    (h : m ∣ n) (F : Elem R n) (v : ZMod m → R →+ S) :
    (cyclicProjection R h F).coeff.sum (fun a r => v a r) =
      F.coeff.sum (fun a r => v (ZMod.castHom h (ZMod m) a) r) :=
  Finsupp.sum_mapDomain_index_addMonoidHom v

/-- Evaluation at the trivial character is unchanged by the cyclic quotient. -/
@[simp] theorem augmentation_cyclicProjection (h : m ∣ n) (F : Elem R n) :
    augmentation m (cyclicProjection R h F) = augmentation n F := by
  change (cyclicProjection R h F).coeff.sum (fun _ r => r * 1) =
    F.coeff.sum (fun _ r => r * 1)
  simp only [mul_one]
  exact sum_cyclicProjection h F (fun _ => AddMonoidHom.id R)

section Star

variable [StarRing R] [NeZero m] [NeZero n]

/-- Quotienting the indices commutes with conjugation and index reversal. -/
@[simp] theorem cyclicProjection_ringStar (h : m ∣ n) (F : Elem R n) :
    cyclicProjection R h (ringStar F) = ringStar (cyclicProjection R h F) := by
  refine AddMonoidAlgebra.induction_linear F ?_ ?_ ?_
  · simp
  · intro F G hF hG
    change cyclicProjection R h (ringStar ((F : Elem R n) + G)) =
      ringStar (cyclicProjection R h ((F : Elem R n) + G))
    calc
      _ = cyclicProjection R h (ringStar F + ringStar G) :=
        congrArg (cyclicProjection R h) (ringStar_add F G)
      _ = cyclicProjection R h (ringStar F) + cyclicProjection R h (ringStar G) :=
        (cyclicProjection R h).map_add _ _
      _ = ringStar (cyclicProjection R h F) + ringStar (cyclicProjection R h G) :=
        congrArg₂ (· + ·) hF hG
      _ = ringStar (cyclicProjection R h F + cyclicProjection R h G) :=
        (ringStar_add _ _).symm
      _ = _ := congrArg ringStar ((cyclicProjection R h).map_add F G).symm
  · intro a r
    simp only [ringStar_single, cyclicProjection_single, map_neg]

/-- A scalar convolution norm descends to the quotient cyclic group. -/
theorem cyclicProjection_norm (h : m ∣ n) {F : Elem R n} {r : R}
    (hnorm : F * ringStar F = scalar n r) :
    cyclicProjection R h F * ringStar (cyclicProjection R h F) = scalar m r := by
  have hq := congrArg (cyclicProjection R h) hnorm
  simpa only [map_mul, cyclicProjection_ringStar, cyclicProjection_scalar] using hq

end Star

end CirculantHadamard

end

end OAI
