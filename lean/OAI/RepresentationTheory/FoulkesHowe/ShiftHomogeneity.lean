import OAI.RepresentationTheory.FoulkesHowe.BlockDerivation

namespace OAI

noncomputable section

open scoped BigOperators
open MvPolynomial

namespace Problem346

/-- Differentiating a weighted homogeneous polynomial lowers its weighted degree
by the weight of the differentiated variable. The statement also covers degree
zero, since a zero derivative is homogeneous in every degree. -/
theorem weightedHomogeneous_pderiv
    {σ R : Type*} [CommSemiring R] {w : σ → ℕ}
    {f : MvPolynomial σ R} {m : ℕ}
    (hf : IsWeightedHomogeneous w f m) (i : σ) :
    IsWeightedHomogeneous w (pderiv i f) (m - w i) := by
  classical
  intro d hd
  rw [coeff_pderiv] at hd
  have h := hf (left_ne_zero_of_mul hd)
  rw [map_add, Finsupp.weight_single, one_smul] at h
  omega

/-- A weighted directional derivative has the expected homogeneous degree
when all source variables and all destination variables have common weights. -/
theorem weightedHomogeneous_directional
    {σ κ R : Type*} [Fintype κ] [CommSemiring R]
    {w : σ → ℕ} {f : MvPolynomial σ R} {m a b : ℕ}
    (hf : IsWeightedHomogeneous w f m) (s t : κ → σ)
    (hs : ∀ i, w (s i) = a) (ht : ∀ i, w (t i) = b) :
    IsWeightedHomogeneous w (∑ i, X (t i) * pderiv (s i) f) (b + (m - a)) := by
  apply IsWeightedHomogeneous.sum
  intro i hi
  simpa [hs i, ht i] using
    (isWeightedHomogeneous_X R w (t i)).mul (weightedHomogeneous_pderiv hf (s i))

private theorem derivation_sum_apply
    {σ κ R : Type*} [CommRing R] (s : Finset κ)
    (D : κ → Derivation R (MvPolynomial σ R) (MvPolynomial σ R))
    (f : MvPolynomial σ R) : (∑ i ∈ s, D i) f = ∑ i ∈ s, D i f := by
  change Derivation.coeFnAddMonoidHom (∑ i ∈ s, D i) f = _
  rw [map_sum]
  simp

/-- The generator-defined block shift agrees with the usual sum of partial
 derivatives over its coordinate block. -/
theorem blockShift_eq_sum_pderiv
    {ι κ R : Type*} [DecidableEq ι] [Fintype κ] [CommRing R] (u v : ι) :
    blockShift (κ := κ) R u v =
      ∑ i : κ, (X (v, i) : MvPolynomial (ι × κ) R) • pderiv (u, i) := by
  classical
  apply MvPolynomial.derivation_ext
  rintro ⟨k, l⟩
  simp only [blockShift_X, derivation_sum_apply, Derivation.smul_apply, pderiv_X]
  by_cases h : k = u
  · subst k
    simp [Pi.single_apply, Prod.mk.injEq]
  · simp [Prod.mk.injEq, h]

@[simp] theorem blockShift_apply_eq_sum
    {ι κ R : Type*} [DecidableEq ι] [Fintype κ] [CommRing R]
    (u v : ι) (f : MvPolynomial (ι × κ) R) :
    blockShift R u v f = ∑ i : κ, X (v, i) * pderiv (u, i) f := by
  rw [blockShift_eq_sum_pderiv]
  simp only [derivation_sum_apply, Derivation.smul_apply, smul_eq_mul]

/-- A block shift changes the degree in an observed block by adding one for
the destination and subtracting one for the source. -/
theorem blockShift_isWeightedHomogeneous
    {ι κ R : Type*} [DecidableEq ι] [Fintype κ] [CommRing R]
    (u v k : ι) {f : MvPolynomial (ι × κ) R} {m : ℕ}
    (hf : IsWeightedHomogeneous (fun z : ι × κ => if z.1 = k then 1 else 0) f m) :
    IsWeightedHomogeneous (fun z : ι × κ => if z.1 = k then 1 else 0)
      (blockShift R u v f)
      ((if v = k then 1 else 0) + (m - (if u = k then 1 else 0))) := by
  rw [blockShift_apply_eq_sum]
  exact weightedHomogeneous_directional hf (fun i => (u, i)) (fun i => (v, i))
    (fun _ => rfl) (fun _ => rfl)

/-- The source block loses one unit of degree under a directional shift. -/
theorem blockShift_source_homogeneous
    {ι κ R : Type*} [DecidableEq ι] [Fintype κ] [CommRing R]
    (u v : ι) (huv : u ≠ v) {f : MvPolynomial (ι × κ) R} {m : ℕ}
    (hf : IsWeightedHomogeneous (fun z : ι × κ => if z.1 = u then 1 else 0) f m) :
    IsWeightedHomogeneous (fun z : ι × κ => if z.1 = u then 1 else 0)
      (blockShift R u v f) (m - 1) := by
  simpa [huv, Ne.symm huv] using blockShift_isWeightedHomogeneous u v u hf

/-- The destination block gains one unit of degree under a directional shift. -/
theorem blockShift_destination_homogeneous
    {ι κ R : Type*} [DecidableEq ι] [Fintype κ] [CommRing R]
    (u v : ι) (huv : u ≠ v) {f : MvPolynomial (ι × κ) R} {m : ℕ}
    (hf : IsWeightedHomogeneous (fun z : ι × κ => if z.1 = v then 1 else 0) f m) :
    IsWeightedHomogeneous (fun z : ι × κ => if z.1 = v then 1 else 0)
      (blockShift R u v f) (m + 1) := by
  simpa [huv, Nat.add_comm] using blockShift_isWeightedHomogeneous u v v hf

/-- Spectator block degrees are unchanged by a directional shift. -/
theorem blockShift_spectator_homogeneous
    {ι κ R : Type*} [DecidableEq ι] [Fintype κ] [CommRing R]
    (u v k : ι) (hu : u ≠ k) (hv : v ≠ k)
    {f : MvPolynomial (ι × κ) R} {m : ℕ}
    (hf : IsWeightedHomogeneous (fun z : ι × κ => if z.1 = k then 1 else 0) f m) :
    IsWeightedHomogeneous (fun z : ι × κ => if z.1 = k then 1 else 0)
      (blockShift R u v f) m := by
  simpa [hu, hv] using blockShift_isWeightedHomogeneous u v k hf

/-- Repeated shifts lower the source degree by the number of operations. -/
theorem blockShift_pow_source_homogeneous
    {ι κ R : Type*} [DecidableEq ι] [Fintype κ] [CommRing R]
    (u v : ι) (huv : u ≠ v) {f : MvPolynomial (ι × κ) R} {m : ℕ}
    (hf : IsWeightedHomogeneous (fun z : ι × κ => if z.1 = u then 1 else 0) f m)
    (n : ℕ) :
    IsWeightedHomogeneous (fun z : ι × κ => if z.1 = u then 1 else 0)
      (((blockShift R u v).toLinearMap ^ n) f) (m - n) := by
  induction n with
  | zero => simpa using hf
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply]
    simpa [Nat.sub_sub] using blockShift_source_homogeneous u v huv ih

/-- Repeated shifts increase the destination degree by the number of operations. -/
theorem blockShift_pow_destination_homogeneous
    {ι κ R : Type*} [DecidableEq ι] [Fintype κ] [CommRing R]
    (u v : ι) (huv : u ≠ v) {f : MvPolynomial (ι × κ) R} {m : ℕ}
    (hf : IsWeightedHomogeneous (fun z : ι × κ => if z.1 = v then 1 else 0) f m)
    (n : ℕ) :
    IsWeightedHomogeneous (fun z : ι × κ => if z.1 = v then 1 else 0)
      (((blockShift R u v).toLinearMap ^ n) f) (m + n) := by
  induction n with
  | zero => simpa using hf
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply]
    simpa [Nat.add_assoc] using blockShift_destination_homogeneous u v huv ih

/-- Repeated shifts leave all spectator block degrees unchanged. -/
theorem blockShift_pow_spectator_homogeneous
    {ι κ R : Type*} [DecidableEq ι] [Fintype κ] [CommRing R]
    (u v k : ι) (hu : u ≠ k) (hv : v ≠ k)
    {f : MvPolynomial (ι × κ) R} {m : ℕ}
    (hf : IsWeightedHomogeneous (fun z : ι × κ => if z.1 = k then 1 else 0) f m)
    (n : ℕ) :
    IsWeightedHomogeneous (fun z : ι × κ => if z.1 = k then 1 else 0)
      (((blockShift R u v).toLinearMap ^ n) f) m := by
  induction n with
  | zero => simpa using hf
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply]
    exact blockShift_spectator_homogeneous u v k hu hv ih

end Problem346

end

end OAI
