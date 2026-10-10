import Mathlib
import OAI.Computability.MaxCut.Games.Derivatives

namespace OAI

/-!
# Partition frequencies by their actual image

A map with image `W` is uniquely a surjection onto `W`, followed by the
subspace inclusion. Consequently a sum over rank-`q` frequencies splits
exactly over dimension-`q` image subspaces and surjections onto each image.
The identities hold for arbitrary real weights and use no analytic estimate.
-/

noncomputable section

namespace MaxCutGames.Inverse.KMSAnalyticHybridEnergy

open scoped BigOperators Classical

variable {R B U : Type*} [Ring R]
  [AddCommGroup B] [Module R B] [AddCommGroup U] [Module R U]

/-- The inclusion of the target subspace preserves the prescribed image of
a surjective map. -/
theorem range_subtype_comp_of_surjective (W : Submodule R U)
    (z : B →ₗ[R] W) (hz : Function.Surjective z) :
    (W.subtype.comp z).range = W := by
  ext u
  constructor
  · rintro ⟨b, rfl⟩
    exact (z b).property
  · intro hu
    obtain ⟨b, hb⟩ := hz ⟨u, hu⟩
    exact ⟨b, congrArg Subtype.val hb⟩

/-- The full fixed-image fiber, with its canonical surjective coordinates. -/
def fixedImageEquivSurjection (W : Submodule R U) :
    {z : B →ₗ[R] U // z.range = W} ≃
      {z : B →ₗ[R] W // Function.Surjective z} where
  toFun z := ⟨z.val.codRestrict W (fun b => z.property.le (LinearMap.mem_range_self z.val b)), by
    intro w
    have hw : w.val ∈ z.val.range := z.property.symm ▸ w.property
    obtain ⟨b, hb⟩ := hw
    exact ⟨b, Subtype.ext hb⟩⟩
  invFun z := ⟨W.subtype.comp z.val, range_subtype_comp_of_surjective W z.val z.property⟩
  left_inv z := by
    apply Subtype.ext
    apply LinearMap.ext
    intro b
    rfl
  right_inv z := by
    apply Subtype.ext
    apply LinearMap.ext
    intro b
    apply Subtype.ext
    rfl

@[simp] theorem fixedImageEquivSurjection_symm_val (W : Submodule R U)
    (z : {z : B →ₗ[R] W // Function.Surjective z}) :
    ((fixedImageEquivSurjection W).symm z).val = W.subtype.comp z.val := rfl

@[simp] theorem fixedImageEquivSurjection_apply_coe (W : Submodule R U)
    (z : {z : B →ₗ[R] U // z.range = W}) (b : B) :
    ((fixedImageEquivSurjection W z).val b : U) = z.val b := rfl

/-- Frequencies of an exact rank. -/
abbrev ImageRankFrequency (q : ℕ) :=
  {z : B →ₗ[R] U // Module.finrank R z.range = q}

/-- Actual image subspaces of the required dimension. -/
abbrev RankImage (R U : Type*) [Ring R] [AddCommGroup U] [Module R U] (q : ℕ) :=
  {W : Submodule R U // Module.finrank R W = q}

/-- The image classification of an exact-rank frequency. -/
def frequencyImage (q : ℕ) (z : ImageRankFrequency (R := R) (B := B) (U := U) q) :
    RankImage R U q := ⟨z.val.range, z.property⟩

/-- Removing the redundant rank certificate from a fixed-image fiber. -/
def frequencyImageFiberEquiv (q : ℕ) (W : RankImage R U q) :
    {z : ImageRankFrequency (R := R) (B := B) (U := U) q // frequencyImage q z = W} ≃
      {z : B →ₗ[R] U // z.range = W.val} where
  toFun z := ⟨z.val.val, congrArg Subtype.val z.property⟩
  invFun z := ⟨⟨z.val, by rw [z.property]; exact W.property⟩, Subtype.ext z.property⟩
  left_inv z := by apply Subtype.ext; apply Subtype.ext; rfl
  right_inv z := by apply Subtype.ext; rfl

/-- Exact rank frequencies are in bijection with a choice of actual image
and a surjective map onto it. -/
def rankFrequencyImageEquiv (q : ℕ) :
    ImageRankFrequency (R := R) (B := B) (U := U) q ≃
      Σ W : RankImage R U q, {z : B →ₗ[R] W.val // Function.Surjective z} :=
  (Equiv.sigmaFiberEquiv (frequencyImage (R := R) (B := B) (U := U) q)).symm.trans
    (Equiv.sigmaCongrRight fun W =>
      (frequencyImageFiberEquiv q W).trans (fixedImageEquivSurjection W.val))

@[simp] theorem rankFrequencyImageEquiv_symm_val (q : ℕ)
    (p : Σ W : RankImage R U q, {z : B →ₗ[R] W.val // Function.Surjective z}) :
    ((rankFrequencyImageEquiv q).symm p).val = p.1.val.subtype.comp p.2.val := rfl

section Sums

variable [Fintype (B →ₗ[R] U)] [Fintype (Submodule R U)]
  [∀ W : Submodule R U, Fintype (B →ₗ[R] W)]

omit [Fintype (Submodule R U)] in
/-- Exact fixed-image reindexing for arbitrary real weights. -/
theorem sum_fixedImage_eq_sum_surjection (W : Submodule R U)
    (weight : (B →ₗ[R] U) → ℝ) :
    (∑ z : {z : B →ₗ[R] U // z.range = W}, weight z.val) =
      ∑ z : {z : B →ₗ[R] W // Function.Surjective z}, weight (W.subtype.comp z.val) := by
  symm
  apply Fintype.sum_equiv (fixedImageEquivSurjection W).symm
  intro z
  rfl

/-- Partition the exact-rank frequency sum by the actual image subspace. -/
theorem sum_rankFrequency_eq_sum_image (q : ℕ) (weight : (B →ₗ[R] U) → ℝ) :
    (∑ z : ImageRankFrequency (R := R) (B := B) (U := U) q, weight z.val) =
      ∑ W : RankImage R U q,
        ∑ z : {z : B →ₗ[R] W.val // Function.Surjective z},
          weight (W.val.subtype.comp z.val) := by
  calc
    _ = ∑ p : Σ W : RankImage R U q,
        {z : B →ₗ[R] W.val // Function.Surjective z},
        weight (p.1.val.subtype.comp p.2.val) := by
      symm
      apply Fintype.sum_equiv (rankFrequencyImageEquiv q).symm
      intro p
      rfl
    _ = _ := Fintype.sum_sigma _

/-- The same partition in filtered-sum form, convenient for Fourier support
conditions that are expressed as vanishing away from one rank. -/
theorem sum_filter_rank_eq_sum_image (q : ℕ) (weight : (B →ₗ[R] U) → ℝ) :
    (∑ z : B →ₗ[R] U with Module.finrank R z.range = q, weight z) =
      ∑ W : RankImage R U q,
        ∑ z : {z : B →ₗ[R] W.val // Function.Surjective z},
          weight (W.val.subtype.comp z.val) := by
  rw [Finset.sum_subtype (p := fun z : B →ₗ[R] U => Module.finrank R z.range = q)
    (Finset.univ.filter fun z : B →ₗ[R] U =>
    Module.finrank R z.range = q) (by simp) weight]
  exact sum_rankFrequency_eq_sum_image q weight

/-- If a weight vanishes outside rank `q`, the full sum has the same exact
image partition. No positivity assumption on the weight is needed. -/
theorem sum_eq_sum_image_of_rank_support (q : ℕ) (weight : (B →ₗ[R] U) → ℝ)
    (hsupport : ∀ z, Module.finrank R z.range ≠ q → weight z = 0) :
    (∑ z : B →ₗ[R] U, weight z) =
      ∑ W : RankImage R U q,
        ∑ z : {z : B →ₗ[R] W.val // Function.Surjective z},
          weight (W.val.subtype.comp z.val) := by
  rw [← sum_filter_rank_eq_sum_image, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro z _
  by_cases hz : Module.finrank R z.range = q
  · simp [hz]
  · simp [hz, hsupport z hz]

end Sums

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- Coordinates adapted to a prescribed image and any chosen complement. -/
def imageCoordinates (W D : Submodule K V) (h : IsCompl W D) : V ≃ₗ[K] (W × D) :=
  (Submodule.prodEquivOfIsCompl W D h).symm

/-- Vectors in the prescribed image have zero complementary coordinate. -/
@[simp] theorem imageCoordinates_subtype (W D : Submodule K V) (h : IsCompl W D)
    (w : W) : imageCoordinates W D h (w : V) = (w, 0) :=
  Submodule.prodEquivOfIsCompl_symm_apply_left W D h w

/-- Each fixed-image frequency has exactly the block form used by the
compressed Hybrid-coordinate parametrization. -/
theorem imageCoordinates_frequency {X : Type*} [AddCommGroup X] [Module K X]
    (W D : Submodule K V) (h : IsCompl W D) (z : X →ₗ[K] W) :
    (imageCoordinates W D h).toLinearMap.comp (W.subtype.comp z) =
      z.prod (0 : X →ₗ[K] D) := by
  apply LinearMap.ext
  intro x
  exact imageCoordinates_subtype W D h (z x)

/-- A complement contributes exactly the remaining ambient dimension. -/
theorem imageCoordinates_finrank [FiniteDimensional K V]
    (W D : Submodule K V) (h : IsCompl W D) :
    Module.finrank K W + Module.finrank K D = Module.finrank K V := by
  simpa only [Module.finrank_prod] using (Submodule.prodEquivOfIsCompl W D h).finrank_eq

/-- Every image subspace admits the required product coordinates. -/
theorem exists_imageCoordinates (W : Submodule K V) :
    ∃ D : Submodule K V, ∃ e : V ≃ₗ[K] (W × D), ∀ w : W, e (w : V) = (w, 0) := by
  obtain ⟨D, h⟩ := W.exists_isCompl
  exact ⟨D, imageCoordinates W D h, imageCoordinates_subtype W D h⟩

end MaxCutGames.Inverse.KMSAnalyticHybridEnergy

end

namespace MaxCutGames.Inverse.KMSAnalyticHybridCoordinates

variable {R A W D B C : Type*} [Ring R]
  [AddCommGroup A] [Module R A] [AddCommGroup W] [Module R W]
  [AddCommGroup D] [Module R D] [AddCommGroup B] [Module R B]
  [AddCommGroup C] [Module R C]

/-- The chosen block compression: restrict to `B`, then forget `A`. -/
def compressBlock (S : (B × C) →ₗ[R] (A × (W × D))) : B →ₗ[R] (W × D) :=
  (LinearMap.snd R A (W × D)).comp (S.comp (LinearMap.inl R B C))

@[simp] theorem compressBlock_apply
    (S : (B × C) →ₗ[R] (A × (W × D))) (b : B) :
    compressBlock S b = (S (b, 0)).2 := rfl

/-- Coordinates of a map whose compression is `(z,0)`. -/
structure Coordinates (z : B →ₗ[R] W) where
  alpha : (B × C) →ₗ[R] A
  psi : (B × C) →ₗ[R] W
  psi_left : psi.comp (LinearMap.inl R B C) = z
  v : C →ₗ[R] D

@[ext] theorem Coordinates.ext {z : B →ₗ[R] W} {p q : Coordinates (A := A) (D := D)
    (C := C) z} (ha : p.alpha = q.alpha) (hp : p.psi = q.psi) (hv : p.v = q.v) : p = q := by
  cases p
  cases q
  cases ha
  cases hp
  cases hv
  rfl

/-- Assemble the three blocks. The last coordinate vanishes on `B`. -/
def assemble {z : B →ₗ[R] W} (p : Coordinates (A := A) (D := D) (C := C) z) :
    (B × C) →ₗ[R] (A × (W × D)) :=
  p.alpha.prod (p.psi.prod (p.v.comp (LinearMap.snd R B C)))

@[simp] theorem assemble_apply {z : B →ₗ[R] W}
    (p : Coordinates (A := A) (D := D) (C := C) z) (x : B × C) :
    assemble p x = (p.alpha x, p.psi x, p.v x.2) := rfl

@[simp] theorem compressBlock_assemble {z : B →ₗ[R] W}
    (p : Coordinates (A := A) (D := D) (C := C) z) :
    compressBlock (assemble p) = z.prod (0 : B →ₗ[R] D) := by
  apply LinearMap.ext
  intro b
  have hp : p.psi (b, 0) = z b :=
    congrArg (fun L : (B →ₗ[R] W) => L b) p.psi_left
  simp [compressBlock, assemble, hp]

/-- Extract the unique coordinates from an actual compressed-fiber element. -/
def extract (z : B →ₗ[R] W)
    (S : {S : (B × C) →ₗ[R] (A × (W × D)) //
      compressBlock S = z.prod (0 : B →ₗ[R] D)}) :
    Coordinates (A := A) (D := D) (C := C) z where
  alpha := (LinearMap.fst R A (W × D)).comp S.val
  psi := (LinearMap.fst R W D).comp ((LinearMap.snd R A (W × D)).comp S.val)
  psi_left := by
    apply LinearMap.ext
    intro b
    exact congrArg (fun L : B →ₗ[R] (W × D) => (L b).1) S.property
  v := (LinearMap.snd R W D).comp
    ((LinearMap.snd R A (W × D)).comp (S.val.comp (LinearMap.inr R B C)))

@[simp] theorem assemble_extract (z : B →ₗ[R] W)
    (S : {S : (B × C) →ₗ[R] (A × (W × D)) //
      compressBlock S = z.prod (0 : B →ₗ[R] D)}) :
    assemble (extract z S) = S.val := by
  apply LinearMap.ext
  rintro ⟨b, c⟩
  have hzero : (S.val (b, 0)).2.2 = 0 :=
    congrArg (fun L : B →ₗ[R] (W × D) => (L b).2) S.property
  have hlast : (S.val (b, c)).2.2 = (S.val (0, c)).2.2 := by
    calc
      _ = (S.val ((b, 0) + (0, c))).2.2 := by simp
      _ = (S.val (b, 0)).2.2 + (S.val (0, c)).2.2 := by rw [map_add]; rfl
      _ = _ := by rw [hzero, zero_add]
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · rfl
    · exact hlast.symm

@[simp] theorem extract_assemble {z : B →ₗ[R] W}
    (p : Coordinates (A := A) (D := D) (C := C) z) :
    extract z ⟨assemble p, compressBlock_assemble p⟩ = p := by
  apply Coordinates.ext
  · apply LinearMap.ext
    intro x
    rfl
  · apply LinearMap.ext
    intro x
    rfl
  · apply LinearMap.ext
    intro c
    rfl

/-- An exact compressed-fiber parametrization, valid over any ring. -/
def compressedFiberEquiv (z : B →ₗ[R] W) :
    {S : (B × C) →ₗ[R] (A × (W × D)) //
      compressBlock S = z.prod (0 : B →ₗ[R] D)} ≃
      Coordinates (A := A) (D := D) (C := C) z where
  toFun := extract z
  invFun p := ⟨assemble p, compressBlock_assemble p⟩
  left_inv S := Subtype.ext (assemble_extract z S)
  right_inv := extract_assemble

/-- Equality of assembled maps forces equality of every chosen coordinate;
there are no hidden change-of-basis fibers in this parametrization. -/
theorem assemble_injective (z : B →ₗ[R] W) :
    Function.Injective (assemble (R := R) (A := A) (D := D) (C := C) (z := z)) := by
  intro p q h
  have hh : (compressedFiberEquiv (A := A) (D := D) (C := C) z).symm p =
      (compressedFiberEquiv (A := A) (D := D) (C := C) z).symm q := Subtype.ext h
  exact (compressedFiberEquiv (A := A) (D := D) (C := C) z).symm.injective hh

end MaxCutGames.Inverse.KMSAnalyticHybridCoordinates

/-!
# The actual hybrid selector in compressed-fiber coordinates

When the prescribed compression is onto `W`, the hybrid image and preimage
conditions are equivalent to injectivity of the complementary target map
and surjectivity of the remaining coordinate map. These are conditions on
the actual assembled linear map, with no rank or analytic hypothesis.
-/

namespace MaxCutGames.Inverse.KMSAnalyticHybridCoordinates

variable {R A W D B C : Type*} [Field R]
  [AddCommGroup A] [Module R A] [AddCommGroup W] [Module R W]
  [AddCommGroup D] [Module R D] [AddCommGroup B] [Module R B]
  [AddCommGroup C] [Module R C]

open MaxCutGames.Appendix

private theorem psi_split_inline_KMSAnalyticHybridCoordinatesConditions {z : B →ₗ[R] W}
    (p : Coordinates (A := A) (D := D) (C := C) z) (b : B) (c : C) :
    p.psi (b, c) = z b + p.psi (0, c) := by
  have hleft : p.psi (b, 0) = z b :=
    congrArg (fun L : B →ₗ[R] W => L b) p.psi_left
  calc
    p.psi (b, c) = p.psi ((b, 0) + (0, c)) := by simp
    _ = p.psi (b, 0) + p.psi (0, c) := p.psi.map_add _ _
    _ = z b + p.psi (0, c) := by rw [hleft]

/-- The genuine hybrid selector is exactly the two independent coordinate
conditions. In particular the full-rank coordinate condition does not
depend on the chosen injective map into the complementary target. -/
theorem hybrid_assemble_iff {z : B →ₗ[R] W}
    (p : Coordinates (A := A) (D := D) (C := C) z)
    (hz : Function.Surjective z) :
    LinearIdentities.Hybrid (assemble p)
        (LinearMap.range (LinearMap.inl R A (W × D)))
        (LinearMap.range (LinearMap.inl R B C)) ↔
      Function.Injective p.v ∧
        Function.Surjective (p.alpha.prod (p.psi.prod (LinearMap.snd R B C))) := by
  constructor
  · intro h
    have hzero : ∀ c : C, p.v c = 0 → c = 0 := by
      intro c hc
      obtain ⟨b, hb⟩ := hz (-p.psi (0, c))
      have hpsi : p.psi (b, c) = 0 := by
        rw [psi_split_inline_KMSAnalyticHybridCoordinatesConditions, hb, neg_add_cancel]
      have hmem : (b, c) ∈ LinearMap.range (LinearMap.inl R B C) := by
        apply h.2
        change assemble p (b, c) ∈ LinearMap.range (LinearMap.inl R A (W × D))
        refine ⟨p.alpha (b, c), ?_⟩
        change (p.alpha (b, c), (0, 0)) = (p.alpha (b, c), p.psi (b, c), p.v c)
        rw [hpsi, hc]
      obtain ⟨b', hb'⟩ := hmem
      exact (congrArg (fun x : B × C => x.2) hb').symm
    refine ⟨?_, ?_⟩
    · intro c d hcd
      apply sub_eq_zero.mp
      apply hzero
      rw [map_sub, hcd, sub_self]
    · rintro ⟨a, w, c⟩
      obtain ⟨b, hb⟩ := hz (w - p.psi (0, c))
      have hpsi : p.psi (b, c) = w := by
        rw [psi_split_inline_KMSAnalyticHybridCoordinatesConditions, hb, sub_add_cancel]
      have hmem : (a - p.alpha (b, c), (0, 0)) ∈ LinearMap.range (assemble p) := by
        apply h.1
        exact ⟨a - p.alpha (b, c), rfl⟩
      obtain ⟨x, hx⟩ := hmem
      have hxa : p.alpha x = a - p.alpha (b, c) :=
        congrArg (fun y : A × (W × D) => y.1) hx
      have hxw : p.psi x = 0 :=
        congrArg (fun y : A × (W × D) => y.2.1) hx
      have hxd : p.v x.2 = 0 :=
        congrArg (fun y : A × (W × D) => y.2.2) hx
      have hxc : x.2 = 0 := hzero _ hxd
      refine ⟨x + (b, c), ?_⟩
      change (p.alpha (x + (b, c)), p.psi (x + (b, c)), (x + (b, c)).2) =
        (a, w, c)
      apply Prod.ext
      · rw [map_add, hxa, sub_add_cancel]
      · apply Prod.ext
        · change p.psi (x + (b, c)) = w
          rw [map_add, hxw, zero_add, hpsi]
        · change x.2 + c = c
          rw [hxc, zero_add]
  · rintro ⟨hv, htheta⟩
    constructor
    · rintro y ⟨a, rfl⟩
      obtain ⟨x, hx⟩ := htheta (a, 0, 0)
      change (p.alpha x, p.psi x, x.2) = (a, 0, 0) at hx
      have hxa : p.alpha x = a := congrArg (fun y : A × (W × C) => y.1) hx
      have hxw : p.psi x = 0 := congrArg (fun y : A × (W × C) => y.2.1) hx
      have hxc : x.2 = 0 := congrArg (fun y : A × (W × C) => y.2.2) hx
      refine ⟨x, ?_⟩
      change (p.alpha x, p.psi x, p.v x.2) = (a, 0, 0)
      rw [hxa, hxw, hxc, map_zero]
    · intro x hx
      change assemble p x ∈ LinearMap.range (LinearMap.inl R A (W × D)) at hx
      obtain ⟨a, ha⟩ := hx
      have hxd : p.v x.2 = 0 :=
        (congrArg (fun y : A × (W × D) => y.2.2) ha).symm
      have hxc : x.2 = 0 := hv (by simpa only [map_zero] using hxd)
      exact ⟨x.1, Prod.ext rfl hxc.symm⟩

end MaxCutGames.Inverse.KMSAnalyticHybridCoordinates

/-! The exact injection/surjection factorization of the adapted coordinates. -/

namespace MaxCutGames.Inverse.KMSAnalyticHybridCoordinates

variable {R A W D B C : Type*} [Ring R]
  [AddCommGroup A] [Module R A] [AddCommGroup W] [Module R W]
  [AddCommGroup D] [Module R D] [AddCommGroup B] [Module R B]
  [AddCommGroup C] [Module R C]

/-- The small frequency map before its last coordinate is embedded into `D`. -/
def fullCoordinates {z : B →ₗ[R] W}
    (p : Coordinates (A := A) (D := D) (C := C) z) :
    (B × C) →ₗ[R] (A × (W × C)) :=
  p.alpha.prod (p.psi.prod (LinearMap.snd R B C))

/-- The injection chosen by the last block, keeping the first two blocks fixed. -/
def embedLast (v : C →ₗ[R] D) : (A × (W × C)) →ₗ[R] (A × (W × D)) :=
  (LinearMap.id : A →ₗ[R] A).prodMap ((LinearMap.id : W →ₗ[R] W).prodMap v)

@[simp] theorem embedLast_apply (v : C →ₗ[R] D) (x : A × (W × C)) :
    embedLast v x = (x.1, x.2.1, v x.2.2) := rfl

theorem embedLast_injective (v : C →ₗ[R] D) (hv : Function.Injective v) :
    Function.Injective (embedLast (A := A) (W := W) v) := by
  intro x y h
  apply Prod.ext
  · exact congrArg (fun u : A × (W × D) => u.1) h
  · apply Prod.ext
    · exact congrArg (fun u : A × (W × D) => u.2.1) h
    · apply hv
      exact congrArg (fun u : A × (W × D) => u.2.2) h

theorem assemble_eq_embedLast_comp {z : B →ₗ[R] W}
    (p : Coordinates (A := A) (D := D) (C := C) z) :
    assemble p = (embedLast p.v).comp (fullCoordinates p) := by
  apply LinearMap.ext
  intro x
  rfl

theorem range_assemble_of_fullCoordinates_surjective {z : B →ₗ[R] W}
    (p : Coordinates (A := A) (D := D) (C := C) z)
    (hp : Function.Surjective (fullCoordinates p)) :
    (assemble p).range = (embedLast (A := A) (W := W) p.v).range := by
  rw [assemble_eq_embedLast_comp, LinearMap.range_comp,
    LinearMap.range_eq_top.mpr hp, Submodule.map_top]

theorem finrank_assemble {z : B →ₗ[R] W}
    (p : Coordinates (A := A) (D := D) (C := C) z)
    (hv : Function.Injective p.v) (hp : Function.Surjective (fullCoordinates p)) :
    Module.finrank R (assemble p).range = Module.finrank R (A × (W × C)) := by
  rw [range_assemble_of_fullCoordinates_surjective p hp]
  exact LinearMap.finrank_range_of_inj (embedLast_injective p.v hv)

theorem ker_assemble {z : B →ₗ[R] W}
    (p : Coordinates (A := A) (D := D) (C := C) z)
    (hv : Function.Injective p.v) :
    (assemble p).ker = (fullCoordinates p).ker := by
  rw [assemble_eq_embedLast_comp]
  exact LinearMap.ker_comp_of_ker_eq_bot _
    (LinearMap.ker_eq_bot.mpr (embedLast_injective p.v hv))

end MaxCutGames.Inverse.KMSAnalyticHybridCoordinates

/-! The actual hybrid compressed fiber, with no coordinate multiplicity. -/

namespace MaxCutGames.Inverse.KMSAnalyticHybridCoordinates

variable {R A W D B C : Type*} [Field R]
  [AddCommGroup A] [Module R A] [AddCommGroup W] [Module R W]
  [AddCommGroup D] [Module R D] [AddCommGroup B] [Module R B]
  [AddCommGroup C] [Module R C]

open MaxCutGames.Appendix

/-- The exact coordinate parametrization after imposing the genuine hybrid
selector. The two remaining conditions are ordinary injectivity and
surjectivity of displayed linear maps. -/
def hybridFiberEquiv (z : B →ₗ[R] W) (hz : Function.Surjective z) :
    {S : (B × C) →ₗ[R] (A × (W × D)) //
      compressBlock S = z.prod (0 : B →ₗ[R] D) ∧
        LinearIdentities.Hybrid S
          (LinearMap.range (LinearMap.inl R A (W × D)))
          (LinearMap.range (LinearMap.inl R B C))} ≃
      {p : Coordinates (A := A) (D := D) (C := C) z //
        Function.Injective p.v ∧ Function.Surjective (fullCoordinates p)} where
  toFun S := ⟨extract z ⟨S.val, S.property.1⟩, by
    apply (hybrid_assemble_iff _ hz).mp
    rw [assemble_extract]
    exact S.property.2⟩
  invFun p := ⟨assemble p.val, compressBlock_assemble p.val,
    (hybrid_assemble_iff p.val hz).mpr p.property⟩
  left_inv S := by
    apply Subtype.ext
    exact assemble_extract z ⟨S.val, S.property.1⟩
  right_inv p := by
    apply Subtype.ext
    exact extract_assemble p.val

/-- Every map in the actual fiber has the prescribed small rank. -/
theorem hybridFiber_finrank (z : B →ₗ[R] W) (hz : Function.Surjective z)
    (S : (B × C) →ₗ[R] (A × (W × D)))
    (hc : compressBlock S = z.prod (0 : B →ₗ[R] D))
    (hh : LinearIdentities.Hybrid S
      (LinearMap.range (LinearMap.inl R A (W × D)))
      (LinearMap.range (LinearMap.inl R B C))) :
    Module.finrank R S.range = Module.finrank R (A × (W × C)) := by
  let p := (hybridFiberEquiv (A := A) (D := D) (C := C) z hz) ⟨S, hc, hh⟩
  have he : assemble p.val = S := assemble_extract z ⟨S, hc⟩
  rw [← he]
  exact finrank_assemble p.val p.property.1 p.property.2

end MaxCutGames.Inverse.KMSAnalyticHybridCoordinates

/-!
# The actual small-space Fourier component

An injection from the small domain into the large domain lifts dual
frequencies by composition. Only surjective small-space frequencies are
retained. The identities below use the actual trace-character coefficients
and normalized primal expectation; no fourth-moment estimate is assumed.
-/

namespace MaxCutGames.Inverse.KMSAnalytic

noncomputable section
open scoped BigOperators Classical
open MaxCutGames.Integration.BinaryLinear (F2)
open MaxCutGames.Fourier.MatrixFourier

variable {E F I : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [AddCommGroup I] [Module F2 I]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F] [FiniteDimensional F2 I]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]
  [Fintype (I →ₗ[F2] F)] [Fintype (F →ₗ[F2] I)]

/-- The Fourier array of the small full-rank component. -/
def smallCoeff (ι : I →ₗ[F2] E) (f : (E →ₗ[F2] F) → ℝ)
    (T : F →ₗ[F2] I) : ℝ :=
  if Function.Surjective T then linearCoeff f (ι.comp T) else 0

/-- A genuine function on the small primal matrix space, synthesized in its
own orthonormal trace-character basis. -/
def smallComponent (ι : I →ₗ[F2] E) (f : (E →ₗ[F2] F) → ℝ) :
    (I →ₗ[F2] F) → ℝ := synthesis (smallCoeff ι f)

omit [FiniteDimensional F2 E] [Fintype (F →ₗ[F2] E)] in
@[simp] theorem coeff_smallComponent (ι : I →ₗ[F2] E)
    (f : (E →ₗ[F2] F) → ℝ) (T : F →ₗ[F2] I) :
    linearCoeff (smallComponent ι f) T = smallCoeff ι f T :=
  coeff_synthesis _ _

omit [FiniteDimensional F2 E] [Fintype (F →ₗ[F2] E)] in
theorem coeff_smallComponent_of_surjective (ι : I →ₗ[F2] E)
    (f : (E →ₗ[F2] F) → ℝ) (T : F →ₗ[F2] I)
    (hT : Function.Surjective T) :
    linearCoeff (smallComponent ι f) T = linearCoeff f (ι.comp T) := by
  simp only [coeff_smallComponent, smallCoeff, ite_eq_left hT]

omit [FiniteDimensional F2 E] [Fintype (F →ₗ[F2] E)] in
theorem coeff_smallComponent_of_not_surjective (ι : I →ₗ[F2] E)
    (f : (E →ₗ[F2] F) → ℝ) (T : F →ₗ[F2] I)
    (hT : ¬ Function.Surjective T) : linearCoeff (smallComponent ι f) T = 0 := by
  simp only [coeff_smallComponent, smallCoeff, ite_eq_right hT]

omit [FiniteDimensional F2 E] [Fintype (F →ₗ[F2] E)] in
/-- Exact normalization: primal expectation equals an unnormalized sum over
surjective small-space frequencies. -/
theorem smallComponent_energy (ι : I →ₗ[F2] E) (f : (E →ₗ[F2] F) → ℝ) :
    (𝔼 X, smallComponent ι f X ^ 2) =
      ∑ T ∈ Finset.univ.filter (fun T : F →ₗ[F2] I => Function.Surjective T),
        linearCoeff f (ι.comp T) ^ 2 := by
  rw [smallComponent, synthesis_energy, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro T _
  by_cases hT : Function.Surjective T <;> simp [smallCoeff, hT]

omit [FiniteDimensional F2 E] [Fintype (F →ₗ[F2] E)] in
/-- Every retained frequency has rank equal to the small domain dimension. -/
theorem rankComponent_smallComponent (ι : I →ₗ[F2] E)
    (f : (E →ₗ[F2] F) → ℝ) :
    rankComponent (Module.finrank F2 I) (smallComponent ι f) = smallComponent ι f := by
  apply eq_of_coeff_eq
  intro T
  simp only [rankComponent, coeff_component, coeff_smallComponent]
  by_cases hT : Function.Surjective T
  · have hr : Module.finrank F2 T.range = Module.finrank F2 I :=
      Submodule.eq_top_iff_finrank_eq.mp (LinearMap.range_eq_top.mpr hT)
    simp [hr]
  · simp [smallCoeff, hT]

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [FiniteDimensional F2 I] [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)] [Fintype (I →ₗ[F2] F)] [Fintype (F →ₗ[F2] I)] in
/-- Composition with an injection preserves the actual kernel. -/
theorem ker_comp_of_injective (ι : I →ₗ[F2] E) (hι : Function.Injective ι)
    (T : F →ₗ[F2] I) : (ι.comp T).ker = T.ker :=
  LinearMap.ker_comp_of_ker_eq_bot T (LinearMap.ker_eq_bot.mpr hι)

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [FiniteDimensional F2 I] [Fintype (F →ₗ[F2] E)] [Fintype (I →ₗ[F2] F)] [Fintype (F →ₗ[F2] I)] in
/-- The small Fourier array is independent of the chosen injection once the
large function's actual coefficients are proved constant on kernel classes. -/
theorem smallCoeff_eq_of_kernel_coeff_const (ι κ : I →ₗ[F2] E)
    (hι : Function.Injective ι) (hκ : Function.Injective κ)
    (f : (E →ₗ[F2] F) → ℝ)
    (hcoeff : ∀ S T : F →ₗ[F2] E,
      S.ker = T.ker → linearCoeff f S = linearCoeff f T) :
    smallCoeff ι f = smallCoeff κ f := by
  funext T
  unfold smallCoeff
  by_cases hT : Function.Surjective T
  · simp only [ite_eq_left hT]
    exact hcoeff _ _ ((ker_comp_of_injective ι hι T).trans
      (ker_comp_of_injective κ hκ T).symm)
  · simp only [ite_eq_right hT]

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [FiniteDimensional F2 I]
  [Fintype (F →ₗ[F2] E)] [Fintype (I →ₗ[F2] F)] in
/-- Equality is of the actual synthesized functions, not merely their norms. -/
theorem smallComponent_eq_of_kernel_coeff_const (ι κ : I →ₗ[F2] E)
    (hι : Function.Injective ι) (hκ : Function.Injective κ)
    (f : (E →ₗ[F2] F) → ℝ)
    (hcoeff : ∀ S T : F →ₗ[F2] E,
      S.ker = T.ker → linearCoeff f S = linearCoeff f T) :
    smallComponent ι f = smallComponent κ f :=
  congrArg synthesis (smallCoeff_eq_of_kernel_coeff_const ι κ hι hκ f hcoeff)

omit [FiniteDimensional F2 E] [Fintype (F →ₗ[F2] E)] in
/-- A small component is orthogonal to any small-space function whose full
rank coefficients vanish. -/
theorem smallComponent_orthogonal (ι : I →ₗ[F2] E)
    (f : (E →ₗ[F2] F) → ℝ) (g : (I →ₗ[F2] F) → ℝ)
    (hg : ∀ T : F →ₗ[F2] I, Function.Surjective T → linearCoeff g T = 0) :
    (𝔼 X, smallComponent ι f X * g X) = 0 := by
  rw [← linear_parseval_inner]
  apply Finset.sum_eq_zero
  intro T _
  rw [coeff_smallComponent]
  by_cases hT : Function.Surjective T
  · rw [hg T hT, mul_zero]
  · simp [smallCoeff, hT]

/-- Injective frequency lifting cannot increase the total squared norm. -/
theorem smallComponent_energy_le (ι : I →ₗ[F2] E) (hι : Function.Injective ι)
    (f : (E →ₗ[F2] F) → ℝ) :
    (𝔼 X, smallComponent ι f X ^ 2) ≤ 𝔼 X, f X ^ 2 := by
  have hinj : Function.Injective (fun T : F →ₗ[F2] I => ι.comp T) := by
    intro T U hTU
    apply LinearMap.ext
    intro x
    apply hι
    exact congrArg (fun S : F →ₗ[F2] E => S x) hTU
  rw [smallComponent_energy, ← linear_parseval]
  calc
    _ = ∑ S ∈ (Finset.univ.filter (fun T : F →ₗ[F2] I => Function.Surjective T)).image
        (fun T => ι.comp T), linearCoeff f S ^ 2 := by
      rw [Finset.sum_image]
      intro T _ U _ hTU
      exact hinj hTU
    _ ≤ ∑ S, linearCoeff f S ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun S _ _ => sq_nonneg _)

end
end MaxCutGames.Inverse.KMSAnalytic

end OAI
