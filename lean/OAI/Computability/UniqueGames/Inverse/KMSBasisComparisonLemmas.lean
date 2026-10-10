import Mathlib.Algebra.BigOperators.Expect
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Pi
import Mathlib.Logic.Equiv.Basic
import Mathlib.SetTheory.Cardinal.NatCard
import OAI.Computability.UniqueGames.Inverse.KMSAnalyticHybridEnergyImageTransportCoreLemmas
import OAI.Computability.UniqueGames.Inverse.KMSFoundationLemmas
import OAI.Computability.UniqueGames.Inverse.MatrixChartIntervalsLemmas
import OAI.Computability.UniqueGames.Inverse.MatrixChartLemmas

namespace OAI

section

/-!
# The ordered-basis lift of a Grassmann set

The ambient sample space contains every linear map, including singular maps.
The lift accepts exactly maps whose range is one of the specified
`ell`-dimensional subspaces. Thus dependence is rejected, rather than silently
conditioning the ambient uniform distribution on independence.
-/

namespace UniqueGamesTheorem.Inverse.KMSBasisComparison

noncomputable section
open scoped Classical

abbrev BasisMap (n ell : ℕ) := KMS.Ambient ell →ₗ[KMS.F2] KMS.Ambient n

instance basisMapFinite (n ell : ℕ) : Finite (BasisMap n ell) :=
  Finite.of_injective (fun X : BasisMap n ell => (X : KMS.Ambient ell → KMS.Ambient n))
    DFunLike.coe_injective

instance basisMapFintype (n ell : ℕ) : Fintype (BasisMap n ell) := Fintype.ofFinite _

/-- Membership in the lift, expressed by the actual linear-map range. -/
def InLift {n ell : ℕ} (S : Finset (KMS.Vertex n ell)) (X : BasisMap n ell) : Prop :=
  ∃ L ∈ S, LinearMap.range X = L.val

/-- The lifted finite set in the whole map space. -/
def lift {n ell : ℕ} (S : Finset (KMS.Vertex n ell)) : Finset (BasisMap n ell) :=
  Finset.univ.filter (InLift S)

@[simp] theorem mem_lift {n ell : ℕ} (S : Finset (KMS.Vertex n ell))
    (X : BasisMap n ell) : X ∈ lift S ↔ InLift S X := by
  simp [lift]

/-- Real Boolean indicator, in the orientation used by the matrix Fourier transform. -/
def liftedIndicator {n ell : ℕ} (S : Finset (KMS.Vertex n ell))
    (X : BasisMap n ell) : ℝ := if InLift S X then 1 else 0

theorem liftedIndicator_nonneg {n ell : ℕ} (S : Finset (KMS.Vertex n ell))
    (X : BasisMap n ell) : 0 ≤ liftedIndicator S X := by
  unfold liftedIndicator
  split <;> norm_num

theorem liftedIndicator_le_one {n ell : ℕ} (S : Finset (KMS.Vertex n ell))
    (X : BasisMap n ell) : liftedIndicator S X ≤ 1 := by
  unfold liftedIndicator
  split <;> norm_num

/-- A map accepted by the lift has full column rank. -/
theorem injective_of_inLift {n ell : ℕ} {S : Finset (KMS.Vertex n ell)}
    {X : BasisMap n ell} (h : InLift S X) : Function.Injective X := by
  obtain ⟨L, _, hL⟩ := h
  have hr : Module.finrank KMS.F2 (LinearMap.range X) = ell := by
    rw [hL]
    exact L.property
  have hd := X.finrank_range_add_finrank_ker
  have he : Module.finrank KMS.F2 (KMS.Ambient ell) = ell := by
    simp [KMS.Ambient]
  have hk : Module.finrank KMS.F2 (LinearMap.ker X) = 0 := by omega
  exact LinearMap.ker_eq_bot.mp (Submodule.finrank_eq_zero.mp hk)

/-- The actual Grassmann vertex represented by an injective map. -/
def rangeVertex {n ell : ℕ} (X : BasisMap n ell) (hX : Function.Injective X) :
    KMS.Vertex n ell :=
  ⟨LinearMap.range X, by
    rw [LinearMap.finrank_range_of_inj hX]
    simp [KMS.Ambient]⟩

theorem inLift_iff_rangeVertex_mem {n ell : ℕ} (S : Finset (KMS.Vertex n ell))
    (X : BasisMap n ell) (hX : Function.Injective X) :
    InLift S X ↔ rangeVertex X hX ∈ S := by
  constructor
  · rintro ⟨L, hL, hXL⟩
    have he : rangeVertex X hX = L := Subtype.ext hXL
    simpa only [he] using hL
  · intro h
    exact ⟨rangeVertex X hX, h, rfl⟩

/-- A change of the ordered domain basis leaves the range unchanged. -/
theorem inLift_comp_iff {n ell : ℕ} (S : Finset (KMS.Vertex n ell))
    (g : KMS.Ambient ell ≃ₗ[KMS.F2] KMS.Ambient ell) (X : BasisMap n ell) :
    InLift S (X.comp g.toLinearMap) ↔ InLift S X := by
  unfold InLift
  rw [LinearMap.range_comp_of_range_eq_top X g.range]

/-- The lift is basis-invariant in precisely the Fourier theorem's sense. -/
theorem liftedIndicator_basisInvariant {n ell : ℕ} (S : Finset (KMS.Vertex n ell)) :
    KMSBasisInvariant.IsBasisInvariant (liftedIndicator S) := by
  intro g X
  simp only [liftedIndicator, inLift_comp_iff]

end
end UniqueGamesTheorem.Inverse.KMSBasisComparison

end

section

/-!
# Constant ordered-basis fibers

An injective linear map with a fixed range is exactly an ordered basis of that
range. Choosing one such basis identifies this fiber with the automorphisms of
the domain. The generic finite-fiber lemma below proves uniformity, including
the complete normalization in the rational density identity.
-/

namespace UniqueGamesTheorem.Inverse.KMSBasisComparison

noncomputable section
open scoped BigOperators Classical

section UniformFibers

variable {X Y G : Type*}

/-- Trivializing equal-size fibers identifies the full sample space with a
product; the first coordinate remains the original quotient map. -/
def fiberProductEquiv (f : X → Y) (e : ∀ y, {x : X // f x = y} ≃ G) : X ≃ Y × G :=
  (Equiv.sigmaFiberEquiv f).symm.trans (Equiv.sigmaEquivProdOfEquiv e)

@[simp] theorem fiberProductEquiv_fst (f : X → Y)
    (e : ∀ y, {x : X // f x = y} ≃ G) (x : X) :
    (fiberProductEquiv f e x).1 = f x := rfl

/-- Uniform sampling pushes forward to uniform sampling whenever every fiber
is equivalent to the same nonempty finite type. This applies to real and
rational expectations alike. -/
theorem expect_eq_of_uniform_fibers [Fintype X] [Fintype Y] [Fintype G]
    [Nonempty G] {M : Type*} [AddCommMonoid M] [Module ℚ≥0 M]
    (f : X → Y) (e : ∀ y, {x : X // f x = y} ≃ G) (g : Y → M) :
    (𝔼 x, g (f x)) = 𝔼 y, g y := by
  calc
    _ = 𝔼 z : Y × G, g z.1 :=
      Fintype.expect_equiv (fiberProductEquiv f e) _ _ (fun _ => rfl)
    _ = _ := by
      simpa only [Finset.univ_product_univ, Fintype.expect_const] using
        (Finset.expect_product (Finset.univ : Finset Y) (Finset.univ : Finset G)
          (fun z : Y × G => g z.1))

/-- Exact rational finite-set density transfer; no asymptotic or probability
normalization is hidden in the fiber comparison. -/
theorem density_eq_of_uniform_fibers [Fintype X] [Fintype Y] [Fintype G]
    [Nonempty G] (f : X → Y) (e : ∀ y, {x : X // f x = y} ≃ G)
    (S : Finset Y) :
    (((Finset.univ.filter fun x => f x ∈ S).card : ℚ) / Fintype.card X) =
      (S.card : ℚ) / Fintype.card Y := by
  have h := expect_eq_of_uniform_fibers f e (fun y => if y ∈ S then (1 : ℚ) else 0)
  simpa [Finset.expect_eq_sum_div_card, Finset.sum_boole,
    Finset.filter_mem_eq_inter] using h

end UniformFibers

section LinearFibers

variable {K E F : Type*} [Field K] [AddCommGroup E] [Module K E]
  [AddCommGroup F] [Module K F]

/-- The actual fiber of injective maps over a specified range subspace. -/
def RangeFiber (L : Submodule K F) :=
  {X : E →ₗ[K] F // Function.Injective X ∧ LinearMap.range X = L}

/-- A range fiber is the set of linear equivalences onto that range. -/
def rangeFiberEquiv (L : Submodule K F) : RangeFiber (E := E) L ≃ (E ≃ₗ[K] L) where
  toFun X := LinearEquiv.ofBijective
    (X.val.codRestrict L (fun x =>
      X.property.2.le (LinearMap.mem_range_self X.val x)))
    ⟨fun _ _ h => X.property.1 (congrArg Subtype.val h), by
      intro y
      have hy : (y : F) ∈ LinearMap.range X.val := X.property.2.ge y.property
      obtain ⟨x, hx⟩ := hy
      exact ⟨x, Subtype.ext hx⟩⟩
  invFun e := ⟨L.subtype.comp e.toLinearMap,
    (Submodule.subtype_injective L).comp e.injective, by
      ext y
      constructor
      · rintro ⟨x, rfl⟩
        exact (e x).property
      · intro hy
        obtain ⟨x, hx⟩ := e.surjective ⟨y, hy⟩
        exact ⟨x, congrArg Subtype.val hx⟩⟩
  left_inv X := by
    apply Subtype.ext
    ext x
    rfl
  right_inv e := by
    ext x
    rfl

/-- After choosing one basis of a subspace, its ordered-basis fiber is exactly
the domain's automorphism group. -/
def rangeFiberEquivAut {L : Submodule K F} (e : E ≃ₗ[K] L) :
    RangeFiber (E := E) L ≃ (E ≃ₗ[K] E) :=
  (rangeFiberEquiv L).trans
    { toFun := fun a => a.trans e.symm
      invFun := fun a => a.trans e
      left_inv := by intro a; ext x; simp
      right_inv := by intro a; ext x; simp }

/-- The size of a range fiber is independent of the selected subspace. -/
theorem rangeFiber_card {L : Submodule K F} (e : E ≃ₗ[K] L) :
    Nat.card (RangeFiber (E := E) L) = Nat.card (E ≃ₗ[K] E) :=
  Nat.card_congr (rangeFiberEquivAut e)

end LinearFibers

/-- Every Grassmann vertex admits an ordered basis of the prescribed domain. -/
def vertexBasis {n ell : ℕ} (L : KMS.Vertex n ell) :
    KMS.Ambient ell ≃ₗ[KMS.F2] L.val :=
  LinearEquiv.ofFinrankEq _ _ (by simpa [KMS.Ambient] using L.property.symm)

/-- The concrete binary Grassmann range fiber has exactly as many elements as
the automorphism group of the fixed `ell`-dimensional domain. -/
theorem vertex_rangeFiber_card {n ell : ℕ} (L : KMS.Vertex n ell) :
    Nat.card (RangeFiber (E := KMS.Ambient ell) L.val) =
      Nat.card (KMS.Ambient ell ≃ₗ[KMS.F2] KMS.Ambient ell) :=
  rangeFiber_card (vertexBasis L)

/-- The sample space after explicitly conditioning on full column rank. -/
abbrev InjectiveBasisMap (n ell : ℕ) :=
  {X : BasisMap n ell // Function.Injective X}

instance injectiveBasisMapFintype (n ell : ℕ) : Fintype (InjectiveBasisMap n ell) :=
  Fintype.ofFinite _

instance basisAutomorphismFinite (ell : ℕ) :
    Finite (KMS.Ambient ell ≃ₗ[KMS.F2] KMS.Ambient ell) :=
  Finite.of_injective
    (fun e : KMS.Ambient ell ≃ₗ[KMS.F2] KMS.Ambient ell =>
      (e : KMS.Ambient ell → KMS.Ambient ell)) DFunLike.coe_injective

instance basisAutomorphismFintype (ell : ℕ) :
    Fintype (KMS.Ambient ell ≃ₗ[KMS.F2] KMS.Ambient ell) := Fintype.ofFinite _

def injectiveRange {n ell : ℕ} (X : InjectiveBasisMap n ell) : KMS.Vertex n ell :=
  rangeVertex X.val X.property

/-- The fiber of the actual range-vertex map is the injective range fiber
defined above. Both injectivity and the subspace equality are preserved. -/
def injectiveRangeFiberEquiv {n ell : ℕ} (L : KMS.Vertex n ell) :
    {X : InjectiveBasisMap n ell // injectiveRange X = L} ≃
      RangeFiber (E := KMS.Ambient ell) L.val where
  toFun X := ⟨X.val.val, X.val.property, congrArg Subtype.val X.property⟩
  invFun X := ⟨⟨X.val, X.property.1⟩, Subtype.ext X.property.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

def injectiveRangeFiberAut {n ell : ℕ} (L : KMS.Vertex n ell) :
    {X : InjectiveBasisMap n ell // injectiveRange X = L} ≃
      (KMS.Ambient ell ≃ₗ[KMS.F2] KMS.Ambient ell) :=
  (injectiveRangeFiberEquiv L).trans (rangeFiberEquivAut (vertexBasis L))

/-- Exact uniform pushforward from injective binary maps to Grassmann
vertices. The statement holds also at an empty Grassmannian. -/
theorem injectiveRange_expect {n ell : ℕ} {M : Type*}
    [AddCommMonoid M] [Module ℚ≥0 M] (g : KMS.Vertex n ell → M) :
    (𝔼 X : InjectiveBasisMap n ell, g (injectiveRange X)) = 𝔼 L, g L := by
  let : Nonempty (KMS.Ambient ell ≃ₗ[KMS.F2] KMS.Ambient ell) :=
    ⟨LinearEquiv.refl _ _⟩
  exact expect_eq_of_uniform_fibers injectiveRange injectiveRangeFiberAut g

/-- Rational density transfer with the injective-map denominator made explicit. -/
theorem injectiveRange_density {n ell : ℕ} (S : Finset (KMS.Vertex n ell)) :
    (((Finset.univ.filter fun X : InjectiveBasisMap n ell => injectiveRange X ∈ S).card : ℚ) /
      Fintype.card (InjectiveBasisMap n ell)) =
      (S.card : ℚ) / Fintype.card (KMS.Vertex n ell) := by
  let : Nonempty (KMS.Ambient ell ≃ₗ[KMS.F2] KMS.Ambient ell) :=
    ⟨LinearEquiv.refl _ _⟩
  exact density_eq_of_uniform_fibers injectiveRange injectiveRangeFiberAut S

theorem lift_nonempty_iff {n ell : ℕ} (S : Finset (KMS.Vertex n ell)) :
    (lift S).Nonempty ↔ S.Nonempty := by
  constructor
  · rintro ⟨X, hX⟩
    obtain ⟨L, hL, _⟩ := (mem_lift S X).mp hX
    exact ⟨L, hL⟩
  · rintro ⟨L, hL⟩
    let X := (rangeFiberEquiv L.val).symm (vertexBasis L)
    refine ⟨X.val, (mem_lift S X.val).mpr ?_⟩
    exact ⟨L, hL, X.property.2⟩

/-- The range quotient restricted to the lifted event itself. -/
def liftRange {n ell : ℕ} (S : Finset (KMS.Vertex n ell))
    (X : lift S) : S :=
  ⟨rangeVertex X.val (injective_of_inLift ((mem_lift S X.val).mp X.property)),
    (inLift_iff_rangeVertex_mem S X.val _).mp ((mem_lift S X.val).mp X.property)⟩

def liftRangeFiberEquiv {n ell : ℕ} (S : Finset (KMS.Vertex n ell)) (L : S) :
    {X : lift S // liftRange S X = L} ≃
      RangeFiber (E := KMS.Ambient ell) L.val.val where
  toFun X := ⟨X.val.val, injective_of_inLift ((mem_lift S X.val.val).mp X.val.property),
    congrArg (fun Z : S => Z.val.val) X.property⟩
  invFun X := ⟨⟨X.val, (mem_lift S X.val).mpr ⟨L.val, L.property, X.property.2⟩⟩,
    Subtype.ext (Subtype.ext X.property.2)⟩
  left_inv _ := rfl
  right_inv _ := rfl

def liftRangeFiberAut {n ell : ℕ} (S : Finset (KMS.Vertex n ell)) (L : S) :
    {X : lift S // liftRange S X = L} ≃
      (KMS.Ambient ell ≃ₗ[KMS.F2] KMS.Ambient ell) :=
  (liftRangeFiberEquiv S L).trans (rangeFiberEquivAut (vertexBasis L.val))

/-- Every selected Grassmann vertex contributes exactly the same number of
ordered bases to the full matrix-space lift. -/
theorem lift_card {n ell : ℕ} (S : Finset (KMS.Vertex n ell)) :
    (lift S).card = S.card *
      Fintype.card (KMS.Ambient ell ≃ₗ[KMS.F2] KMS.Ambient ell) := by
  have h := Fintype.card_congr (fiberProductEquiv (liftRange S) (liftRangeFiberAut S))
  simpa only [Fintype.card_coe, Fintype.card_prod] using h

theorem injectiveBasisMap_card (n ell : ℕ) :
    Fintype.card (InjectiveBasisMap n ell) = Fintype.card (KMS.Vertex n ell) *
      Fintype.card (KMS.Ambient ell ≃ₗ[KMS.F2] KMS.Ambient ell) := by
  have h := Fintype.card_congr
    (fiberProductEquiv (@injectiveRange n ell) injectiveRangeFiberAut)
  simpa only [Fintype.card_prod] using h

/-- The density within all maps is the Grassmann density times the full-rank
probability. In particular the full-rank factor must not be dropped when the
lift is used as a function on the ambient Fourier space. -/
theorem lift_density_factor {n ell : ℕ} (S : Finset (KMS.Vertex n ell))
    (hS : S.Nonempty) :
    ((lift S).card : ℚ) / Fintype.card (BasisMap n ell) =
      ((Fintype.card (InjectiveBasisMap n ell) : ℚ) / Fintype.card (BasisMap n ell)) *
        ((S.card : ℚ) / Fintype.card (KMS.Vertex n ell)) := by
  let : Nonempty (KMS.Vertex n ell) := ⟨hS.choose⟩
  have hV : (Fintype.card (KMS.Vertex n ell) : ℚ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  rw [lift_card, injectiveBasisMap_card]
  push_cast
  field_simp

end
end UniqueGamesTheorem.Inverse.KMSBasisComparison

end

section

/-!
The good event for an ordered-basis rank-one update is that its functional
is nonzero and its direction lies outside the starting range. Its exact
finite cardinality gives the exceptional-mass bound without conditioning
either factor of the original uniform experiment.
-/

namespace UniqueGamesTheorem.Inverse.KMSBasisComparison

noncomputable section
open scoped Classical

abbrev Functional (ell : ℕ) := KMS.Ambient ell →ₗ[KMS.F2] KMS.F2

instance functionalFinite (ell : ℕ) : Finite (Functional ell) :=
  Finite.of_injective (fun a : Functional ell => (a : KMS.Ambient ell → KMS.F2))
    DFunLike.coe_injective

instance functionalFintype (ell : ℕ) : Fintype (Functional ell) := Fintype.ofFinite _

theorem card_functional (ell : ℕ) : Fintype.card (Functional ell) = 2 ^ ell := by
  rw [Module.card_eq_pow_finrank (K := KMS.F2)]
  change Fintype.card (ZMod 2) ^ Module.finrank KMS.F2 (Module.Dual KMS.F2
    (KMS.Ambient ell)) = _
  rw [Subspace.dual_finrank_eq]
  simp [KMS.Ambient, KMS.F2]

theorem card_ambient (n : ℕ) : Fintype.card (KMS.Ambient n) = 2 ^ n := by
  simp [KMS.Ambient, KMS.F2]

/-- Actual good pairs in the unconditioned product sample space. -/
def goodParameters {n ell : ℕ} (X : BasisMap n ell) :
    Finset (Functional ell × KMS.Ambient n) :=
  (Finset.univ.filter (fun a : Functional ell => a ≠ 0)) ×ˢ
    (Finset.univ.filter (fun y : KMS.Ambient n => y ∉ X.range))

@[simp] theorem mem_goodParameters {n ell : ℕ} (X : BasisMap n ell)
    (p : Functional ell × KMS.Ambient n) :
    p ∈ goodParameters X ↔ p.1 ≠ 0 ∧ p.2 ∉ X.range := by
  simp [goodParameters]

theorem card_range {n ell : ℕ} (X : BasisMap n ell) (hX : Function.Injective X) :
    Fintype.card X.range = 2 ^ ell := by
  rw [Module.card_eq_pow_finrank (K := KMS.F2), LinearMap.finrank_range_of_inj hX]
  simp [KMS.Ambient, KMS.F2]

/-- The exact good-event count, including the zero-dimensional boundary. -/
theorem card_goodParameters {n ell : ℕ} (X : BasisMap n ell)
    (hX : Function.Injective X) :
    (goodParameters X).card = (2 ^ ell - 1) * (2 ^ n - 2 ^ ell) := by
  rw [goodParameters, Finset.card_product]
  have ha : (Finset.univ.filter (fun a : Functional ell => a ≠ 0)).card =
      2 ^ ell - 1 := by
    rw [← Fintype.card_subtype, Fintype.card_subtype_compl, card_functional]
    simp
  have hy : (Finset.univ.filter (fun y : KMS.Ambient n => y ∉ X.range)).card =
      2 ^ n - 2 ^ ell := by
    rw [← Fintype.card_subtype, Fintype.card_subtype_compl, card_ambient]
    rw [card_range X hX]
  rw [ha, hy]

/-- Exceptional mass is bounded by the sum of the two factor exceptions. -/
theorem badParameters_mass_le {n ell : ℕ} (X : BasisMap n ell)
    (hX : Function.Injective X) :
    1 - ((goodParameters X).card : ℝ) /
        Fintype.card (Functional ell × KMS.Ambient n) ≤
      ((2 : ℝ) ^ ell)⁻¹ + (2 : ℝ) ^ ell / (2 : ℝ) ^ n := by
  have hcard : 2 ^ ell ≤ 2 ^ n := by
    rw [← card_ambient ell, ← card_ambient n]
    exact Fintype.card_le_of_injective X hX
  have hone : 1 ≤ 2 ^ ell := Nat.one_le_pow ell 2 (by decide)
  rw [card_goodParameters X hX, Fintype.card_prod, card_functional, card_ambient]
  push_cast [Nat.cast_sub hone, Nat.cast_sub hcard]
  have he : (0 : ℝ) < 2 ^ ell := pow_pos (by norm_num) _
  have hn : (0 : ℝ) < 2 ^ n := pow_pos (by norm_num) _
  field_simp
  nlinarith

/-- The same estimate in the complement-cardinality form used for deleting
the bad event from a finite expectation. -/
theorem badParameters_mass_le_compl {n ell : ℕ} (X : BasisMap n ell)
    (hX : Function.Injective X) :
    (((Finset.univ \ goodParameters X).card : ℕ) : ℝ) /
        Fintype.card (Functional ell × KMS.Ambient n) ≤
      ((2 : ℝ) ^ ell)⁻¹ + (2 : ℝ) ^ ell / (2 : ℝ) ^ n := by
  have ht : (0 : ℝ) < Fintype.card (Functional ell × KMS.Ambient n) :=
    Nat.cast_pos.mpr Fintype.card_pos
  have hsub := Finset.card_le_card (Finset.subset_univ (goodParameters X))
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Nat.cast_sub hsub,
    Finset.card_univ, sub_div, div_self (ne_of_gt ht)]
  exact badParameters_mass_le X hX

end
end UniqueGamesTheorem.Inverse.KMSBasisComparison

end

section

namespace UniqueGamesTheorem.Inverse.KMSBasisComparison

noncomputable section
open scoped BigOperators Classical

variable {E F : Type*}
  [AddCommGroup E] [Module (ZMod 2) E]
  [AddCommGroup F] [Module (ZMod 2) F]
  [FiniteDimensional (ZMod 2) E] [FiniteDimensional (ZMod 2) F]

/-- The full-neighbor sampler on its exact good-event factor space. -/
def outsideNeighborSample (X : E →ₗ[ZMod 2] F) (hX : Function.Injective X)
    (p : OutsideNeighborFactors X) : MatrixChart.GrassmannNeighbors X.range :=
  rankOneUpdateNeighbor X hX p.1.val p.1.property p.2.val p.2.property

omit [FiniteDimensional (ZMod 2) F] in
@[simp] theorem outsideNeighborSample_val (X : E →ₗ[ZMod 2] F)
    (hX : Function.Injective X) (p : OutsideNeighborFactors X) :
    (outsideNeighborSample X hX p).val =
      (rankOneUpdate X p.1.val p.2.val).range := rfl

/-- Every full Grassmann neighbor has exactly the same number of original
factor pairs. The number is the size of one codimension-one kernel. -/
theorem card_outsideNeighborSample_fiber [Fintype E]
    (X : E →ₗ[ZMod 2] F) (hX : Function.Injective X)
    (W : MatrixChart.GrassmannNeighbors X.range) :
    Nat.card {p : OutsideNeighborFactors X // outsideNeighborSample X hX p = W} =
      2 ^ (Module.finrank (ZMod 2) E - 1) := by
  obtain ⟨a, y, ha, hy, hW⟩ := exists_rankOneUpdate_range_eq X hX W
  let e : {p : OutsideNeighborFactors X // outsideNeighborSample X hX p = W} ≃
      OutsideNeighborPairFiber X a y := Equiv.subtypeEquivRight (fun p => by
    constructor
    · intro h
      exact (congrArg Subtype.val h).trans hW.symm
    · intro h
      exact Subtype.ext (h.trans hW))
  rw [Nat.card_congr e]
  exact card_outsideNeighborPairFiber X hX a ha hy

/-- Uniform neighbor law for any real observable. There is no chart
restriction, hidden conditioning, or additional loss in this identity. -/
theorem expect_outsideNeighborSample [Fintype E] [Fintype F]
    [Fintype (E →ₗ[ZMod 2] ZMod 2)]
    (X : E →ₗ[ZMod 2] F) (hX : Function.Injective X)
    [Fintype (MatrixChart.GrassmannNeighbors X.range)]
    (g : MatrixChart.GrassmannNeighbors X.range → ℝ) :
    (𝔼 p : OutsideNeighborFactors X, g (outsideNeighborSample X hX p)) =
      𝔼 W : MatrixChart.GrassmannNeighbors X.range, g W := by
  let G := Fin (2 ^ (Module.finrank (ZMod 2) E - 1))
  let : Nonempty G := ⟨⟨0, by positivity⟩⟩
  let e : ∀ W : MatrixChart.GrassmannNeighbors X.range,
      {p : OutsideNeighborFactors X // outsideNeighborSample X hX p = W} ≃ G :=
    fun W => Finite.equivFinOfCardEq (card_outsideNeighborSample_fiber X hX W)
  exact expect_eq_of_uniform_fibers (outsideNeighborSample X hX) e g

end
end UniqueGamesTheorem.Inverse.KMSBasisComparison

end

end OAI
