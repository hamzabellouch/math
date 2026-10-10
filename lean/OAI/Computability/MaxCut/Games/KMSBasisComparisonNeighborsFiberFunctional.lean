import Mathlib
import OAI.Computability.MaxCut.Games.MatrixChartDegreeNeighbors

namespace OAI

/-!
Binary linear functionals are determined by their kernels. The statement
includes the zero functional; no choice of a nonzero normalization is needed.
Injective linear images retain the same uniqueness property.
-/

namespace MaxCutGames.Inverse.KMSBasisComparison

variable {E F : Type*}
  [AddCommGroup E] [Module (ZMod 2) E]
  [AddCommGroup F] [Module (ZMod 2) F]

/-- A binary functional is determined by its zero set. -/
theorem binary_functional_eq_of_ker_eq
    {a b : E →ₗ[ZMod 2] ZMod 2} (h : a.ker = b.ker) : a = b := by
  have scalar_cases : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
  apply LinearMap.ext
  intro x
  have hzero : a x = 0 ↔ b x = 0 := by
    change x ∈ a.ker ↔ x ∈ b.ker
    rw [h]
  rcases scalar_cases (a x) with ha | ha
  · exact ha.trans (hzero.mp ha).symm
  · rcases scalar_cases (b x) with hb | hb
    · exact False.elim (zero_ne_one ((hzero.mpr hb).symm.trans ha))
    · exact ha.trans hb.symm

/-- The image of a binary functional's kernel under an injective linear map
still determines that functional uniquely. -/
theorem binary_functional_eq_of_map_ker_eq
    (X : E →ₗ[ZMod 2] F) (hX : Function.Injective X)
    {a b : E →ₗ[ZMod 2] ZMod 2}
    (h : a.ker.map X = b.ker.map X) : a = b := by
  exact binary_functional_eq_of_ker_eq (Submodule.map_injective_of_injective hX h)

end MaxCutGames.Inverse.KMSBasisComparison

/-!
The complete pair fiber of the ordered-basis neighbor sampler. Equal updated
images determine the binary functional exactly. The remaining ambiguity is
the affine kernel coset, of cardinality `2 ^ (dim E - 1)`.
-/

namespace MaxCutGames.Inverse.KMSBasisComparison

noncomputable section

variable {E F : Type*} [AddCommGroup E] [Module (ZMod 2) E]
  [AddCommGroup F] [Module (ZMod 2) F]

abbrev OutsideNeighborFactors (X : E →ₗ[ZMod 2] F) :=
  {a : E →ₗ[ZMod 2] ZMod 2 // a ≠ 0} × {y : F // y ∉ X.range}

abbrev OutsideNeighborPairFiber (X : E →ₗ[ZMod 2] F)
    (a : E →ₗ[ZMod 2] ZMod 2) (y : F) :=
  {p : OutsideNeighborFactors X //
    (rankOneUpdate X p.1.val p.2.val).range = (rankOneUpdate X a y).range}

/-- The common-parent intersection recovers the binary functional uniquely. -/
theorem functional_eq_of_update_range_eq (X : E →ₗ[ZMod 2] F)
    (hX : Function.Injective X) {a b : E →ₗ[ZMod 2] ZMod 2}
    {y z : F} (hy : y ∉ X.range) (hz : z ∉ X.range)
    (h : (rankOneUpdate X a y).range = (rankOneUpdate X b z).range) :
    a = b := by
  apply binary_functional_eq_of_map_ker_eq X hX
  rw [← range_inf_rankOneUpdate X a hy, ← range_inf_rankOneUpdate X b hz, h]

def fixedToPairFiber (X : E →ₗ[ZMod 2] F)
    (a : E →ₗ[ZMod 2] ZMod 2) (ha : a ≠ 0) (y₀ : F) :
    FixedFunctionalNeighborFiber X a y₀ → OutsideNeighborPairFiber X a y₀ :=
  fun y => ⟨(⟨a, ha⟩, ⟨y.val, y.property.1⟩), y.property.2⟩

theorem fixedToPairFiber_injective (X : E →ₗ[ZMod 2] F)
    (a : E →ₗ[ZMod 2] ZMod 2) (ha : a ≠ 0) (y₀ : F) :
    Function.Injective (fixedToPairFiber X a ha y₀) := by
  intro y z h
  apply Subtype.ext
  exact congrArg (fun p => p.val.2.val) h

theorem fixedToPairFiber_surjective (X : E →ₗ[ZMod 2] F)
    (hX : Function.Injective X) (a : E →ₗ[ZMod 2] ZMod 2)
    (ha : a ≠ 0) {y₀ : F} (hy₀ : y₀ ∉ X.range) :
    Function.Surjective (fixedToPairFiber X a ha y₀) := by
  intro p
  have haeq : p.val.1.val = a :=
    functional_eq_of_update_range_eq X hX p.val.2.property hy₀ p.property
  have he : (X + a.smulRight p.val.2.val).range =
      (X + a.smulRight y₀).range := by
    simpa only [rankOneUpdate, haeq] using p.property
  refine ⟨⟨p.val.2.val, p.val.2.property, he⟩, ?_⟩
  apply Subtype.ext
  apply Prod.ext
  · exact Subtype.ext haeq.symm
  · rfl

/-- Every pair in a fixed neighbor fiber has the same functional. -/
def fixedFunctionalEquivPairFiber (X : E →ₗ[ZMod 2] F)
    (hX : Function.Injective X) (a : E →ₗ[ZMod 2] ZMod 2)
    (ha : a ≠ 0) {y₀ : F} (hy₀ : y₀ ∉ X.range) :
    FixedFunctionalNeighborFiber X a y₀ ≃ OutsideNeighborPairFiber X a y₀ :=
  Equiv.ofBijective (fixedToPairFiber X a ha y₀)
    ⟨fixedToPairFiber_injective X a ha y₀,
      fixedToPairFiber_surjective X hX a ha hy₀⟩

/-- The full rank-one neighbor-sampling fiber is the functional kernel. -/
def outsideNeighborPairFiberEquiv (X : E →ₗ[ZMod 2] F)
    (hX : Function.Injective X) (a : E →ₗ[ZMod 2] ZMod 2)
    (ha : a ≠ 0) {y₀ : F} (hy₀ : y₀ ∉ X.range) :
    a.ker ≃ OutsideNeighborPairFiber X a y₀ :=
  (fixedFunctionalNeighborFiberEquiv X hX a ha hy₀).trans
    (fixedFunctionalEquivPairFiber X hX a ha hy₀)

theorem card_outsideNeighborPairFiber [Fintype E]
    (X : E →ₗ[ZMod 2] F) (hX : Function.Injective X)
    (a : E →ₗ[ZMod 2] ZMod 2) (ha : a ≠ 0)
    {y₀ : F} (hy₀ : y₀ ∉ X.range) :
    Nat.card (OutsideNeighborPairFiber X a y₀) =
      2 ^ (Module.finrank (ZMod 2) E - 1) := by
  rw [← Nat.card_congr (fixedFunctionalEquivPairFiber X hX a ha hy₀)]
  exact card_fixedFunctionalNeighborFiber_pow X hX a ha hy₀

end

/-!
# Constant ordered-basis fibers

An injective linear map with a fixed range is exactly an ordered basis of that
range. Choosing one such basis identifies this fiber with the automorphisms of
the domain. The generic finite-fiber lemma below proves uniformity, including
the complete normalization in the rational density identity.
-/

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
end MaxCutGames.Inverse.KMSBasisComparison

namespace MaxCutGames.Inverse.KMSBasisComparison

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
end MaxCutGames.Inverse.KMSBasisComparison

/-!
Rank-one differences parametrize the actual Grassmann neighbors that remain
in the matrix chart. The equivalences retain the graph subspaces themselves,
so cardinalities and uniform sampling can be transported to the graph.
-/

namespace MaxCutGames.Inverse.MatrixChart

variable {X Y : Type*}
  [AddCommGroup X] [Module (ZMod 2) X]
  [AddCommGroup Y] [Module (ZMod 2) Y]
  [FiniteDimensional (ZMod 2) X]

/-- Coordinate matrices adjacent to a fixed graph matrix. -/
abbrev BinaryChartNeighbors (T : X →ₗ[ZMod 2] Y) :=
  {U : X →ₗ[ZMod 2] Y //
    Module.finrank (ZMod 2) (T.graph ⊓ U.graph : Submodule (ZMod 2) (X × Y)) + 1 =
      Module.finrank (ZMod 2) X}

/-- The actual adjacent subspaces that lie in the graph chart. -/
abbrev BinaryGraphChartNeighbors (T : X →ₗ[ZMod 2] Y) :=
  {L : Submodule (ZMod 2) (X × Y) //
    (∃ U : X →ₗ[ZMod 2] Y, L = U.graph) ∧
      Module.finrank (ZMod 2) (T.graph ⊓ L : Submodule (ZMod 2) (X × Y)) + 1 =
        Module.finrank (ZMod 2) X}

/-- Difference from a fixed matrix is an exact bijection between rank-one
maps and adjacent matrices. Subtraction also makes this construction valid
without invoking characteristic-two simplification. -/
def rankOneEquivChartNeighbors (T : X →ₗ[ZMod 2] Y) :
    BinaryRankOneMaps X Y ≃ BinaryChartNeighbors T where
  toFun D := ⟨T - D.val, (adjacent_iff_rank_one T (T - D.val)).mpr (by
    have he : T - (T - D.val) = D.val := by
      exact sub_sub_cancel T _
    rw [he]
    exact D.property)⟩
  invFun U := ⟨T - U.val, (adjacent_iff_rank_one T U.val).mp U.property⟩
  left_inv D := by
    apply Subtype.ext
    change T - (T - D.val) = D.val
    exact sub_sub_cancel T _
  right_inv U := by
    apply Subtype.ext
    change T - (T - U.val) = U.val
    exact sub_sub_cancel T _

def graphChartNeighbor (T : X →ₗ[ZMod 2] Y)
    (U : BinaryChartNeighbors T) : BinaryGraphChartNeighbors T :=
  ⟨U.val.graph, ⟨U.val, rfl⟩, U.property⟩

omit [FiniteDimensional (ZMod 2) X] in
theorem graphChartNeighbor_injective (T : X →ₗ[ZMod 2] Y) :
    Function.Injective (graphChartNeighbor T) := by
  intro U V h
  apply Subtype.ext
  exact graph_injective (congrArg Subtype.val h)

omit [FiniteDimensional (ZMod 2) X] in
theorem graphChartNeighbor_surjective (T : X →ₗ[ZMod 2] Y) :
    Function.Surjective (graphChartNeighbor T) := by
  intro L
  obtain ⟨U, hU⟩ := L.property.1
  have h :
      Module.finrank (ZMod 2) (T.graph ⊓ U.graph : Submodule (ZMod 2) (X × Y)) + 1 =
        Module.finrank (ZMod 2) X := by
    rw [← hU]
    exact L.property.2
  exact ⟨⟨U, h⟩, Subtype.ext hU.symm⟩

noncomputable def chartNeighborsEquivGraphNeighbors (T : X →ₗ[ZMod 2] Y) :
    BinaryChartNeighbors T ≃ BinaryGraphChartNeighbors T :=
  Equiv.ofBijective (graphChartNeighbor T)
    ⟨graphChartNeighbor_injective T, graphChartNeighbor_surjective T⟩

/-- The complete nonzero-factor sampling equivalence, ending in actual
Grassmann subspaces in the chart. -/
noncomputable def binaryFactorsEquivGraphNeighbors (T : X →ₗ[ZMod 2] Y) :
    BinaryRankOneFactors X Y ≃ BinaryGraphChartNeighbors T :=
  binaryRankOneEquiv.trans
    ((rankOneEquivChartNeighbors T).trans (chartNeighborsEquivGraphNeighbors T))

@[simp] theorem binaryFactorsEquivGraphNeighbors_apply (T : X →ₗ[ZMod 2] Y)
    (p : BinaryRankOneFactors X Y) :
    (binaryFactorsEquivGraphNeighbors T p).val =
      (T - p.1.val.smulRight p.2.val).graph := rfl

/-- In characteristic two the same parametrization is addition of the
rank-one perturbation used in the matrix test. -/
theorem binaryFactorsEquivGraphNeighbors_apply_add (T : X →ₗ[ZMod 2] Y)
    (p : BinaryRankOneFactors X Y) :
    (binaryFactorsEquivGraphNeighbors T p).val =
      (T + p.1.val.smulRight p.2.val).graph := by
  have hneg : -(p.1.val.smulRight p.2.val) = p.1.val.smulRight p.2.val := by
    have hscalar : (-1 : ZMod 2) = 1 := by decide
    calc
      -(p.1.val.smulRight p.2.val) =
          (-1 : ZMod 2) • (p.1.val.smulRight p.2.val) := (neg_one_smul _ _).symm
      _ = p.1.val.smulRight p.2.val := by rw [hscalar, one_smul]
  rw [binaryFactorsEquivGraphNeighbors_apply, sub_eq_add_neg, hneg]

/-- Every neighbor in the chart has the required Grassmann dimension. -/
theorem graphChartNeighbor_finrank (T : X →ₗ[ZMod 2] Y)
    (L : BinaryGraphChartNeighbors T) :
    Module.finrank (ZMod 2) L.val = Module.finrank (ZMod 2) X := by
  obtain ⟨U, hU⟩ := L.property.1
  rw [hU]
  exact finrank_graph U

/-- The dimension condition excludes the starting vertex itself. -/
theorem graphChartNeighbor_ne_self (T : X →ₗ[ZMod 2] Y)
    (L : BinaryGraphChartNeighbors T) : L.val ≠ T.graph := by
  intro h
  have hL := L.property.2
  rw [h, inf_idem, finrank_graph] at hL
  omega

theorem card_binaryGraphChartNeighbors [Fintype (X →ₗ[ZMod 2] ZMod 2)] [Fintype Y]
    (T : X →ₗ[ZMod 2] Y) :
    Nat.card (BinaryGraphChartNeighbors T) =
      (2 ^ Module.finrank (ZMod 2) X - 1) *
        (2 ^ Module.finrank (ZMod 2) Y - 1) := by
  rw [← Nat.card_congr
    ((rankOneEquivChartNeighbors T).trans (chartNeighborsEquivGraphNeighbors T))]
  exact card_binaryRankOneMaps_pow

theorem card_binaryGraphChartNeighbors_coordinates (ell m : ℕ)
    (T : (Fin ell → ZMod 2) →ₗ[ZMod 2] (Fin m → ZMod 2)) :
    Nat.card (BinaryGraphChartNeighbors T) = (2 ^ ell - 1) * (2 ^ m - 1) := by
  rw [← Nat.card_congr
    ((rankOneEquivChartNeighbors T).trans (chartNeighborsEquivGraphNeighbors T))]
  exact card_binaryRankOneMaps_coordinates ell m

end MaxCutGames.Inverse.MatrixChart

/-! Exact chart-to-Grassmann degree comparison over the binary field. -/

namespace MaxCutGames.Inverse.MatrixChart

open Module

variable {ell m : ℕ}

abbrev CoordinateMatrix (ell m : ℕ) :=
  (Fin ell → ZMod 2) →ₗ[ZMod 2] (Fin m → ZMod 2)

/-- Inclusion into actual full neighbors preserves the subspace. -/
def graphChartNeighborsEmbedding (T : CoordinateMatrix ell m) :
    BinaryGraphChartNeighbors T ↪ GrassmannNeighbors T.graph where
  toFun L := ⟨L.val, by
    rw [finrank_graph]
    exact ⟨graphChartNeighbor_finrank T L, L.property.2⟩⟩
  inj' := by
    intro L W h
    exact Subtype.ext (congrArg (fun N : GrassmannNeighbors T.graph => N.val) h)

theorem card_grassmann_neighbors_graph (T : CoordinateMatrix ell m) :
    Nat.card (GrassmannNeighbors T.graph) =
      (2 ^ ell - 1) * (2 ^ (m + 1) - 2) := by
  have h := card_grassmann_neighbors_binary T.graph m (by
    rw [finrank_graph, Module.finrank_prod]
    simp)
  simpa only [finrank_graph, Module.finrank_fintype_fun_eq_card,
    Fintype.card_fin] using h

/-- Exactly twice as many full neighbors as chart neighbors. This natural
number identity also covers a zero-dimensional side. -/
theorem full_degree_eq_twice_chart_degree (T : CoordinateMatrix ell m) :
    Nat.card (GrassmannNeighbors T.graph) =
      2 * Nat.card (BinaryGraphChartNeighbors T) := by
  rw [card_grassmann_neighbors_graph, card_binaryGraphChartNeighbors_coordinates]
  have hpow : 2 ^ (m + 1) - 2 = 2 * (2 ^ m - 1) := by
    rw [pow_succ, Nat.mul_sub_left_distrib]
    simp [Nat.mul_comm]
  rw [hpow]
  ac_rfl

/-- The neighbor sampling probability of remaining in the chart is one half
when both dimensions are positive. -/
theorem chart_degree_ratio (T : CoordinateMatrix ell m)
    (hell : 0 < ell) (hm : 0 < m) :
    (Nat.card (BinaryGraphChartNeighbors T) : ℚ) /
      (Nat.card (GrassmannNeighbors T.graph) : ℚ) = 1 / 2 := by
  have hpos : 0 < Nat.card (BinaryGraphChartNeighbors T) := by
    rw [card_binaryGraphChartNeighbors_coordinates]
    apply Nat.mul_pos
    · exact Nat.sub_pos_of_lt (one_lt_pow₀ (by decide : 1 < (2 : ℕ)) (by omega))
    · exact Nat.sub_pos_of_lt (one_lt_pow₀ (by decide : 1 < (2 : ℕ)) (by omega))
  rw [full_degree_eq_twice_chart_degree]
  have hne : (Nat.card (BinaryGraphChartNeighbors T) : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hpos)
  simp only [Nat.cast_mul, Nat.cast_ofNat]
  rw [mul_comm (2 : ℚ), div_mul_eq_div_div, div_self hne]

end MaxCutGames.Inverse.MatrixChart

/-! Concrete matrix coordinates for the graph chart. In particular the upper
interval equations become `M q = t`, while the lower equations become `dᵀ M = sᵀ`.
The right-hand sides are retained; none of these slices is required to be linear.
-/

namespace MaxCutGames.Inverse.MatrixChart

open Matrix

variable {K ι κ : Type*} [Field K] [Fintype ι] [Fintype κ]

abbrev matrixGraph (M : Matrix ι κ K) : Submodule K ((ι → K) × (κ → K)) :=
  M.vecMulLinear.graph

omit [Fintype κ] in
@[simp] theorem mem_matrixGraph (M : Matrix ι κ K) (x : ι → K) (y : κ → K) :
    (x, y) ∈ matrixGraph M ↔ y = M.transpose *ᵥ x := by
  rw [Matrix.mulVec_transpose]
  rfl

omit [Fintype κ] in
theorem matrixGraph_injective : Function.Injective (matrixGraph (K := K) (ι := ι) (κ := κ)) := by
  classical
  intro M N h
  have hh : M.vecMulLinear = N.vecMulLinear := graph_injective h
  exact (LinearMap.toMatrixRight' (R := K)).symm.injective hh

/-- A coordinate vector as a linear functional, for the standard dot pairing. -/
abbrev dotFunctional (x : ι → K) : (ι → K) →ₗ[K] K := dotProductBilin K K x

theorem dotFunctional_injective : Function.Injective (dotFunctional (K := K) (ι := ι)) := by
  intro x y h
  apply dotProduct_eq x y
  intro z
  exact congrArg (fun f : (ι → K) →ₗ[K] K => f z) h

/-- Transposing the chart map sends a column specification to its dot functional. -/
theorem dotFunctional_comp_vecMulLinear (M : Matrix ι κ K) (q : κ → K) :
    (dotFunctional q).comp M.vecMulLinear = dotFunctional (M *ᵥ q) := by
  apply LinearMap.ext
  intro x
  change q ⬝ᵥ (x ᵥ* M) = (M *ᵥ q) ⬝ᵥ x
  rw [← Matrix.mulVec_transpose, Matrix.dotProduct_transpose_mulVec, dotProduct_comm]

theorem column_equation_iff (M : Matrix ι κ K) (q : κ → K) (t : ι → K) :
    (dotFunctional q).comp M.vecMulLinear = dotFunctional t ↔ M *ᵥ q = t := by
  rw [dotFunctional_comp_vecMulLinear]
  exact dotFunctional_injective.eq_iff

/-- Exact concrete row-and-column slice corresponding to an interval. -/
theorem matrix_interval_iff_slice {ρ σ : Type*}
    (d : ρ → ι → K) (s : ρ → κ → K)
    (t : σ → ι → K) (q : σ → κ → K) (M : Matrix ι κ K) :
    lowerRows d s ≤ matrixGraph M ∧
        matrixGraph M ≤ upperColumns (fun j => dotFunctional (t j))
          (fun j => dotFunctional (q j)) ↔
      (∀ i, d i ᵥ* M = s i) ∧ (∀ j, M *ᵥ q j = t j) := by
  rw [interval_iff_slice]
  simp only [Matrix.vecMulLinear_apply, column_equation_iff]

omit [Fintype κ] in
/-- The graph always has the row dimension, including degenerate zero dimensions. -/
theorem finrank_matrixGraph (M : Matrix ι κ K) :
    Module.finrank K (matrixGraph M) = Fintype.card ι := by
  rw [finrank_graph]
  simp

end MaxCutGames.Inverse.MatrixChart

/-! Transport the product-coordinate chart into the actual Grassmann vertices
used by the KMS boundary. The transport is a proved ambient linear equivalence.
-/

namespace MaxCutGames.Inverse.MatrixChart

open Matrix

/-- Concatenate the two coordinate blocks of the chart ambient space. -/
def coordinateJoin (K : Type*) [Field K] (ell m : Nat) :
    ((Fin ell → K) × (Fin m → K)) ≃ₗ[K] (Fin (ell + m) → K) :=
  (LinearEquiv.sumArrowLequivProdArrow (Fin ell) (Fin m) K K).symm.trans
    (LinearEquiv.funCongrLeft K K finSumFinEquiv.symm)

/-- A matrix as an actual Grassmann vertex on `ell + m` binary coordinates. -/
def matrixVertex {ell m : Nat} (M : Matrix (Fin ell) (Fin m) (ZMod 2)) :
    KMS.Vertex (ell + m) ell :=
  ⟨(matrixGraph M).map (coordinateJoin (ZMod 2) ell m).toLinearMap, by
    rw [LinearEquiv.finrank_map_eq, finrank_matrixGraph, Fintype.card_fin]⟩

theorem matrixVertex_injective {ell m : Nat} :
    Function.Injective (matrixVertex (ell := ell) (m := m)) := by
  intro M N h
  apply matrixGraph_injective
  apply Submodule.map_injective_of_injective (coordinateJoin (ZMod 2) ell m).injective
  exact congrArg Subtype.val h

theorem finrank_matrixVertex_intersection {ell m : Nat}
    (M N : Matrix (Fin ell) (Fin m) (ZMod 2)) :
    Module.finrank (ZMod 2) ((matrixVertex M).val ⊓ (matrixVertex N).val :
      Submodule (ZMod 2) (KMS.Ambient (ell + m))) =
      Module.finrank (ZMod 2) (matrixGraph M ⊓ matrixGraph N :
        Submodule (ZMod 2) ((Fin ell → ZMod 2) × (Fin m → ZMod 2))) := by
  change Module.finrank (ZMod 2)
    ((matrixGraph M).map (coordinateJoin (ZMod 2) ell m).toLinearMap ⊓
      (matrixGraph N).map (coordinateJoin (ZMod 2) ell m).toLinearMap :
        Submodule (ZMod 2) (KMS.Ambient (ell + m))) = _
  rw [← Submodule.map_inf _ (coordinateJoin (ZMod 2) ell m).injective,
    LinearEquiv.finrank_map_eq]

/-- Exact correspondence with the KMS adjacency predicate, including its
explicit inequality requirement. -/
theorem adjacent_matrixVertex_iff {ell m : Nat}
    (M N : Matrix (Fin ell) (Fin m) (ZMod 2)) :
    KMS.Adjacent (matrixVertex M) (matrixVertex N) ↔
      Module.finrank (ZMod 2) (LinearMap.range (M.vecMulLinear - N.vecMulLinear)) = 1 := by
  have hdim : Module.finrank (ZMod 2) (Fin ell → ZMod 2) = ell := by simp
  constructor
  · intro h
    apply (adjacent_iff_rank_one M.vecMulLinear N.vecMulLinear).mp
    rw [hdim]
    rw [← finrank_matrixVertex_intersection M N]
    exact h.2
  · intro h
    refine ⟨?_, ?_⟩
    · intro heq
      have hMN : M = N := matrixVertex_injective heq
      subst N
      have hh := (adjacent_iff_rank_one M.vecMulLinear M.vecMulLinear).mpr h
      rw [inf_idem, finrank_graph] at hh
      omega
    · rw [finrank_matrixVertex_intersection]
      simpa only [hdim] using
        (adjacent_iff_rank_one M.vecMulLinear N.vecMulLinear).mpr h

noncomputable section

/-- The finite matrix chart in the Grassmann vertex type. -/
def matrixChart (ell m : Nat) : Finset (KMS.Vertex (ell + m) ell) := by
  classical
  exact Finset.univ.image (matrixVertex (ell := ell) (m := m))

@[simp] theorem mem_matrixChart {ell m : Nat} (L : KMS.Vertex (ell + m) ell) :
    L ∈ matrixChart ell m ↔
      ∃ M : Matrix (Fin ell) (Fin m) (ZMod 2), matrixVertex M = L := by
  classical
  simp [matrixChart]

theorem card_matrixChart (ell m : Nat) : (matrixChart ell m).card = 2 ^ (ell * m) := by
  classical
  rw [matrixChart, Finset.card_image_of_injective _ matrixVertex_injective,
    Finset.card_univ]
  calc
    Fintype.card (Matrix (Fin ell) (Fin m) (ZMod 2)) =
        Fintype.card (Fin ell → Fin m → ZMod 2) := Fintype.card_congr (Equiv.refl _)
    _ = 2 ^ (ell * m) := by
      rw [Fintype.card_fun, Fintype.card_fun]
      simp [ZMod.card, ← pow_mul, Nat.mul_comm]

end

end MaxCutGames.Inverse.MatrixChart

end OAI
