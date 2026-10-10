import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dual.Lemmas
import OAI.Computability.UniqueGames.Inverse.KMSAnalyticHybridCoordinatesRankLemmas
import OAI.Computability.UniqueGames.Inverse.MatrixChartLemmas

namespace OAI

section

/-! Every Grassmann interval has a chart description with exactly `dim A`
lower equations and `codim B` upper equations. This supplies the quantitative
row/column budget used when the expansion theorem selects an interval.
-/

namespace UniqueGamesTheorem.Inverse.MatrixChart

variable {K X Y : Type*} [Field K]
  [AddCommGroup X] [Module K X] [AddCommGroup Y] [Module K Y]

theorem span_basis_values {ι : Type*} (A : Submodule K (X × Y))
    (b : Module.Basis ι K A) :
    Submodule.span K (Set.range fun i => (b i).val) = A := by
  have h := congrArg (Submodule.map A.subtype) b.span_eq
  simpa only [Submodule.map_span, Submodule.map_top, Submodule.range_subtype,
    ← Set.range_comp', Submodule.coe_subtype] using h

theorem lowerRows_basis {ι : Type*} (A : Submodule K (X × Y))
    (b : Module.Basis ι K A) :
    lowerRows (fun i => (b i).val.1) (fun i => (b i).val.2) = A := by
  exact span_basis_values A b

/-- Checking an annihilator basis suffices to test membership in a subspace. -/
theorem mem_iff_annihilator_basis {ι : Type*} (B : Submodule K (X × Y))
    (b : Module.Basis ι K B.dualAnnihilator) (x : X × Y) :
    x ∈ B ↔ ∀ i, (b i).val x = 0 := by
  constructor
  · intro hx i
    exact (Submodule.mem_dualAnnihilator (b i).val).mp (b i).property x hx
  · intro h
    apply (Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff B x).mp
    intro φ hφ
    let ev : B.dualAnnihilator →ₗ[K] K :=
      (Module.Dual.eval K (X × Y) x).comp B.dualAnnihilator.subtype
    have hev : ev = 0 := b.ext (fun i => h i)
    exact congrArg (fun f : B.dualAnnihilator →ₗ[K] K => f ⟨φ, hφ⟩) hev

/-- Split a product functional into its two coordinate functionals. -/
theorem functional_coordinate_decomposition (φ : (X × Y) →ₗ[K] K) (x : X) (y : Y) :
    φ (x, y) = φ (x, 0) + φ (0, y) := by
  have h : (x, y) = (x, 0) + (0, y) := by simp
  rw [h, map_add]

theorem upperColumns_annihilator_basis {ι : Type*} (B : Submodule K (X × Y))
    (b : Module.Basis ι K B.dualAnnihilator) :
    upperColumns
      (fun i => -((b i).val.comp (LinearMap.inl K X Y)))
      (fun i => (b i).val.comp (LinearMap.inr K X Y)) = B := by
  ext x
  rw [mem_iff_annihilator_basis B b]
  simp only [upperColumns, Submodule.mem_iInf]
  change (∀ i, x ∈ LinearMap.ker
    (((b i).val.comp (LinearMap.inr K X Y)).comp (LinearMap.snd K X Y) -
      (-((b i).val.comp (LinearMap.inl K X Y))).comp (LinearMap.fst K X Y))) ↔ _
  constructor <;> intro h i
  · have hi := h i
    change (b i).val (0, x.2) - -(b i).val (x.1, 0) = 0 at hi
    rw [functional_coordinate_decomposition]
    simpa only [sub_neg_eq_add, add_comm] using hi
  · change (b i).val (0, x.2) - -(b i).val (x.1, 0) = 0
    have hi := h i
    rw [functional_coordinate_decomposition] at hi
    simpa only [sub_neg_eq_add, add_comm] using hi

/-- Coordinates for an arbitrary interval. There are exactly `dim A` rows and
`codim B` columns, so an interval order bound gives the required slice bound. -/
theorem exists_interval_coordinates [FiniteDimensional K X] [FiniteDimensional K Y]
    (A B : Submodule K (X × Y)) :
    ∃ (n_r n_c : Nat) (d : Fin n_r → X) (s : Fin n_r → Y)
      (t : Fin n_c → X →ₗ[K] K) (q : Fin n_c → Y →ₗ[K] K),
      n_r = Module.finrank K A ∧ n_c = Module.finrank K ((X × Y) ⧸ B) ∧
      ∀ T : X →ₗ[K] Y,
        (A ≤ T.graph ∧ T.graph ≤ B) ↔
          ((∀ i, T (d i) = s i) ∧ (∀ j, (q j).comp T = t j)) := by
  let a := Module.finBasis K A
  let : Module.Free K B.dualAnnihilator := Module.Free.of_divisionRing K B.dualAnnihilator
  let b := Module.finBasis K B.dualAnnihilator
  refine ⟨Module.finrank K A, Module.finrank K B.dualAnnihilator,
    (fun i => (a i).val.1), (fun i => (a i).val.2),
    (fun i => -((b i).val.comp (LinearMap.inl K X Y))),
    (fun i => (b i).val.comp (LinearMap.inr K X Y)), rfl, ?_, ?_⟩
  · exact (Subspace.quotEquivAnnihilator B).finrank_eq.symm
  · intro T
    have h := interval_iff_slice (fun i => (a i).val.1) (fun i => (a i).val.2)
      (fun i => -((b i).val.comp (LinearMap.inl K X Y)))
      (fun i => (b i).val.comp (LinearMap.inr K X Y)) T
    simpa only [lowerRows_basis A a, upperColumns_annihilator_basis B b] using h

end UniqueGamesTheorem.Inverse.MatrixChart

end

section

/-!
Exact rank-one sampling in the binary matrix chart. Nonzero pairs of a
functional and a vector represent rank-one maps uniquely over `ZMod 2`.
Thus uniform nonzero factors give uniform rank-one maps. Zero factors are
excluded explicitly; no conditioned/unconditioned sampling is identified.
-/

namespace UniqueGamesTheorem.Inverse.MatrixChart

section ArbitraryField

variable {K X Y : Type*} [Field K]
  [AddCommGroup X] [Module K X] [AddCommGroup Y] [Module K Y]

/-- Every map with one-dimensional range is a nonzero functional times a
nonzero vector. This existence statement is valid over any field. -/
theorem exists_smulRight_of_rank_one (T : X →ₗ[K] Y)
    (hT : Module.finrank K T.range = 1) :
    ∃ (a : X →ₗ[K] K) (l : Y), a ≠ 0 ∧ l ≠ 0 ∧ T = a.smulRight l := by
  classical
  obtain ⟨e⟩ := Module.nonempty_linearEquiv_of_finrank_eq_one hT
  let a : X →ₗ[K] K := e.symm.toLinearMap.comp T.rangeRestrict
  have ha : a ≠ 0 := LinearMap.surjective_iff_ne_zero.mp
    (e.symm.surjective.comp T.surjective_rangeRestrict)
  have hl : (e 1 : Y) ≠ 0 := by
    intro h
    have he : e 1 = e 0 := by
      apply Subtype.ext
      simp at h
    exact one_ne_zero (e.injective he)
  refine ⟨a, (e 1 : Y), ha, hl, ?_⟩
  apply LinearMap.ext
  intro x
  have h : a x • e 1 = T.rangeRestrict x := by
    calc
      a x • e 1 = e (a x • (1 : K)) := (e.map_smul _ _).symm
      _ = e (a x) := by rw [smul_eq_mul, mul_one]
      _ = T.rangeRestrict x := e.apply_symm_apply _
  exact (congrArg Subtype.val h).symm

/-- The exact algebraic characterization of nonzero rank-one maps. -/
theorem rank_one_iff_exists_smulRight (T : X →ₗ[K] Y) :
    Module.finrank K T.range = 1 ↔
      ∃ (a : X →ₗ[K] K) (l : Y), a ≠ 0 ∧ l ≠ 0 ∧ T = a.smulRight l := by
  constructor
  · exact exists_smulRight_of_rank_one T
  · rintro ⟨a, l, ha, hl, rfl⟩
    rw [LinearMap.range_smulRight_apply ha]
    exact finrank_span_singleton hl

end ArbitraryField

section Binary

variable {X Y : Type*}
  [AddCommGroup X] [Module (ZMod 2) X]
  [AddCommGroup Y] [Module (ZMod 2) Y]

/-- Over the two-element field there is no nontrivial rescaling ambiguity. -/
theorem binary_smulRight_unique
    {a b : X →ₗ[ZMod 2] ZMod 2} {l k : Y}
    (ha : a ≠ 0) (hl : l ≠ 0)
    (h : a.smulRight l = b.smulRight k) : a = b ∧ l = k := by
  obtain ⟨x, hx⟩ := a.surjective ha 1
  have hx' : l = b x • k := by
    simpa only [LinearMap.smulRight_apply, hx, one_smul] using
      LinearMap.congr_fun h x
  have scalar_cases : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
  have hlk : l = k := by
    rcases scalar_cases (b x) with hb | hb
    · exact False.elim (hl (by simpa only [hb, zero_smul] using hx'))
    · simpa only [hb, one_smul] using hx'
  refine ⟨?_, hlk⟩
  apply LinearMap.ext
  intro y
  apply smul_left_injective (ZMod 2) hl
  have hy := LinearMap.congr_fun h y
  simpa only [LinearMap.smulRight_apply, ← hlk] using hy

/-- Ordered nonzero factors, with functional coordinate first. -/
abbrev BinaryRankOneFactors (X Y : Type*)
    [AddCommGroup X] [Module (ZMod 2) X]
    [AddCommGroup Y] [Module (ZMod 2) Y] :=
  {a : X →ₗ[ZMod 2] ZMod 2 // a ≠ 0} × {l : Y // l ≠ 0}

/-- The actual linear maps whose range has dimension one. -/
abbrev BinaryRankOneMaps (X Y : Type*)
    [AddCommGroup X] [Module (ZMod 2) X]
    [AddCommGroup Y] [Module (ZMod 2) Y] :=
  {T : X →ₗ[ZMod 2] Y // Module.finrank (ZMod 2) T.range = 1}

def binaryRankOneMap (p : BinaryRankOneFactors X Y) : BinaryRankOneMaps X Y :=
  ⟨p.1.val.smulRight p.2.val,
    (rank_one_iff_exists_smulRight _).mpr
      ⟨p.1.val, p.2.val, p.1.property, p.2.property, rfl⟩⟩

theorem binary_smulRight_injective :
    Function.Injective (binaryRankOneMap (X := X) (Y := Y)) := by
  intro p q h
  obtain ⟨ha, hl⟩ := binary_smulRight_unique p.1.property p.2.property
    (congrArg Subtype.val h)
  exact Prod.ext (Subtype.ext ha) (Subtype.ext hl)

theorem binary_smulRight_surjective :
    Function.Surjective (binaryRankOneMap (X := X) (Y := Y)) := by
  intro T
  obtain ⟨a, l, ha, hl, h⟩ := exists_smulRight_of_rank_one T.val T.property
  exact ⟨(⟨a, ha⟩, ⟨l, hl⟩), Subtype.ext h.symm⟩

/-- Bijection justifying uniform rank-one sampling by independent uniform
nonzero factors. The inverse uses choice only to select the proved unique pair. -/
noncomputable def binaryRankOneEquiv :
    BinaryRankOneFactors X Y ≃ BinaryRankOneMaps X Y :=
  Equiv.ofBijective binaryRankOneMap
    ⟨binary_smulRight_injective, binary_smulRight_surjective⟩

@[simp] theorem binaryRankOneEquiv_apply (p : BinaryRankOneFactors X Y) :
    (binaryRankOneEquiv p).val = p.1.val.smulRight p.2.val := rfl

/-- The number of binary rank-one maps is exactly the product of the two
nonzero-factor counts, including the zero-dimensional edge cases. -/
theorem card_binaryRankOneMaps [Fintype (X →ₗ[ZMod 2] ZMod 2)] [Fintype Y] :
    Nat.card (BinaryRankOneMaps X Y) =
      (Fintype.card (X →ₗ[ZMod 2] ZMod 2) - 1) * (Fintype.card Y - 1) := by
  classical
  calc
    Nat.card (BinaryRankOneMaps X Y) = Nat.card (BinaryRankOneFactors X Y) :=
      (Nat.card_congr (binaryRankOneEquiv (X := X) (Y := Y))).symm
    _ = (Fintype.card (X →ₗ[ZMod 2] ZMod 2) - 1) * (Fintype.card Y - 1) := by
      simp only [BinaryRankOneFactors, Nat.card_eq_fintype_card, Fintype.card_prod,
        Fintype.card_subtype_compl, Fintype.card_subtype_eq]

/-- Dimensional form of the exact rank-one count. -/
theorem card_binaryRankOneMaps_pow [Fintype (X →ₗ[ZMod 2] ZMod 2)] [Fintype Y] :
    Nat.card (BinaryRankOneMaps X Y) =
      (2 ^ Module.finrank (ZMod 2) X - 1) *
        (2 ^ Module.finrank (ZMod 2) Y - 1) := by
  rw [card_binaryRankOneMaps,
    Module.card_eq_pow_finrank (K := ZMod 2) (V := X →ₗ[ZMod 2] ZMod 2),
    Module.card_eq_pow_finrank (K := ZMod 2) (V := Y)]
  simp only [ZMod.card]
  change (2 ^ Module.finrank (ZMod 2) (Module.Dual (ZMod 2) X) - 1) *
      (2 ^ Module.finrank (ZMod 2) Y - 1) = _
  rw [Subspace.dual_finrank_eq]

theorem card_binaryRankOneMaps_coordinates (ell m : ℕ) :
    Nat.card (BinaryRankOneMaps (Fin ell → ZMod 2) (Fin m → ZMod 2)) =
      (2 ^ ell - 1) * (2 ^ m - 1) := by
  classical
  let : Fintype ((Fin ell → ZMod 2) →ₗ[ZMod 2] ZMod 2) :=
    Fintype.ofInjective (fun a : (Fin ell → ZMod 2) →ₗ[ZMod 2] ZMod 2 =>
      (a : (Fin ell → ZMod 2) → ZMod 2)) DFunLike.coe_injective
  simpa using card_binaryRankOneMaps_pow
    (X := Fin ell → ZMod 2) (Y := Fin m → ZMod 2)

end Binary

end UniqueGamesTheorem.Inverse.MatrixChart

end

section

/-!
For a fixed nonzero binary functional, all updates with a prescribed image
form one affine coset of the image of its kernel. This is an exact fiber
equivalence, so it retains the multiplicities needed for uniform sampling.
-/

namespace UniqueGamesTheorem.Inverse.KMSBasisComparison

noncomputable section

variable {E F : Type*} [AddCommGroup E] [Module (ZMod 2) E]
  [AddCommGroup F] [Module (ZMod 2) F]

/-- Vectors external to the starting image which give the same updated image. -/
abbrev FixedFunctionalNeighborFiber (X : E →ₗ[ZMod 2] F)
    (a : E →ₗ[ZMod 2] ZMod 2) (y₀ : F) :=
  {y : F // y ∉ X.range ∧
    (X + a.smulRight y).range = (X + a.smulRight y₀).range}

theorem add_image_not_mem_range (X : E →ₗ[ZMod 2] F)
    {y : F} (hy : y ∉ X.range) (z : E) : y + X z ∉ X.range := by
  intro h
  exact hy (by simpa using X.range.sub_mem h (X.mem_range_self z))

/-- Kernel translations of the perturbation vector preserve its image. -/
theorem range_update_add_kernel (X : E →ₗ[ZMod 2] F)
    (a : E →ₗ[ZMod 2] ZMod 2) (y : F) (z : a.ker) :
    (X + a.smulRight (y + X z)).range = (X + a.smulRight y).range := by
  have hz : a z = 0 := z.property
  have hforward (x : E) :
      (X + a.smulRight (y + X z)) x =
        (X + a.smulRight y) (x + a x • z) := by
    simp [hz, smul_add]
    abel
  have hbackward (x : E) :
      (X + a.smulRight y) x =
        (X + a.smulRight (y + X z)) (x - a x • z) := by
    simp [hz, smul_add]
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    exact ⟨x + a x • z, (hforward x).symm⟩
  · rintro _ ⟨x, rfl⟩
    exact ⟨x - a x • z, (hbackward x).symm⟩

/-- The affine parametrization of a fixed-functional image fiber. -/
def fixedFunctionalFiberMap (X : E →ₗ[ZMod 2] F)
    (a : E →ₗ[ZMod 2] ZMod 2) {y₀ : F} (hy₀ : y₀ ∉ X.range) :
    a.ker → FixedFunctionalNeighborFiber X a y₀ :=
  fun z => ⟨y₀ + X z, add_image_not_mem_range X hy₀ z,
    range_update_add_kernel X a y₀ z⟩

theorem fixedFunctionalFiberMap_injective (X : E →ₗ[ZMod 2] F)
    (hX : Function.Injective X) (a : E →ₗ[ZMod 2] ZMod 2)
    {y₀ : F} (hy₀ : y₀ ∉ X.range) :
    Function.Injective (fixedFunctionalFiberMap X a hy₀) := by
  intro z w h
  apply Subtype.ext
  apply hX
  exact add_left_cancel (congrArg Subtype.val h)

theorem fixedFunctionalFiberMap_surjective (X : E →ₗ[ZMod 2] F)
    (a : E →ₗ[ZMod 2] ZMod 2) (ha : a ≠ 0)
    {y₀ : F} (hy₀ : y₀ ∉ X.range) :
    Function.Surjective (fixedFunctionalFiberMap X a hy₀) := by
  intro y
  obtain ⟨x, hx⟩ := a.surjective ha 1
  have hmem : X x + y.val ∈ (X + a.smulRight y₀).range := by
    exact y.property.2.le ⟨x, by simp [hx]⟩
  obtain ⟨t, ht⟩ := hmem
  have hbinary : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
  have hat : a t = 1 := by
    rcases hbinary (a t) with hat | hat
    · have he : X t = X x + y.val := by simpa [hat] using ht
      have hy : y.val = X (t - x) := by
        rw [map_sub, he]
        abel
      exact False.elim (y.property.1 ⟨t - x, hy.symm⟩)
    · exact hat
  have hz : t - x ∈ a.ker := by
    change a (t - x) = 0
    simp [hat, hx]
  refine ⟨⟨t - x, hz⟩, ?_⟩
  apply Subtype.ext
  change y₀ + X (t - x) = y.val
  have he : X t + y₀ = X x + y.val := by simpa [hat] using ht
  calc
    y₀ + X (t - x) = (X t + y₀) - X x := by rw [map_sub]; abel
    _ = y.val := by rw [he]; abel

/-- Exact constant-multiplicity fiber over an updated subspace. -/
def fixedFunctionalNeighborFiberEquiv (X : E →ₗ[ZMod 2] F)
    (hX : Function.Injective X) (a : E →ₗ[ZMod 2] ZMod 2)
    (ha : a ≠ 0) {y₀ : F} (hy₀ : y₀ ∉ X.range) :
    a.ker ≃ FixedFunctionalNeighborFiber X a y₀ :=
  Equiv.ofBijective (fixedFunctionalFiberMap X a hy₀)
    ⟨fixedFunctionalFiberMap_injective X hX a hy₀,
      fixedFunctionalFiberMap_surjective X a ha hy₀⟩

theorem card_fixedFunctionalNeighborFiber (X : E →ₗ[ZMod 2] F)
    (hX : Function.Injective X) (a : E →ₗ[ZMod 2] ZMod 2)
    (ha : a ≠ 0) {y₀ : F} (hy₀ : y₀ ∉ X.range) :
    Nat.card (FixedFunctionalNeighborFiber X a y₀) = Nat.card a.ker :=
  (Nat.card_congr (fixedFunctionalNeighborFiberEquiv X hX a ha hy₀)).symm

theorem card_fixedFunctionalNeighborFiber_pow [Fintype E]
    (X : E →ₗ[ZMod 2] F) (hX : Function.Injective X)
    (a : E →ₗ[ZMod 2] ZMod 2) (ha : a ≠ 0)
    {y₀ : F} (hy₀ : y₀ ∉ X.range) :
    Nat.card (FixedFunctionalNeighborFiber X a y₀) =
      2 ^ (Module.finrank (ZMod 2) E - 1) := by
  classical
  rw [card_fixedFunctionalNeighborFiber X hX a ha hy₀, Nat.card_eq_fintype_card,
    Module.card_eq_pow_finrank (K := ZMod 2) (V := a.ker), ZMod.card]
  congr 1
  have h := Module.Dual.finrank_ker_add_one_of_ne_zero ha
  omega

end
end UniqueGamesTheorem.Inverse.KMSBasisComparison

end

section

/-!
The complete pair fiber of the ordered-basis neighbor sampler. Equal updated
images determine the binary functional exactly. The remaining ambiguity is
the affine kernel coset, of cardinality `2 ^ (dim E - 1)`.
-/

namespace UniqueGamesTheorem.Inverse.KMSBasisComparison

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
end UniqueGamesTheorem.Inverse.KMSBasisComparison

end

section

/-!
Rank-one differences parametrize the actual Grassmann neighbors that remain
in the matrix chart. The equivalences retain the graph subspaces themselves,
so cardinalities and uniform sampling can be transported to the graph.
-/

namespace UniqueGamesTheorem.Inverse.MatrixChart

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
    have he : T - (T - D.val) = D.val := sub_sub_cancel T D.val
    rw [he]
    exact D.property)⟩
  invFun U := ⟨T - U.val, (adjacent_iff_rank_one T U.val).mp U.property⟩
  left_inv D := by
    apply Subtype.ext
    change T - (T - D.val) = D.val
    exact sub_sub_cancel T D.val
  right_inv U := by
    apply Subtype.ext
    change T - (T - U.val) = U.val
    exact sub_sub_cancel T U.val

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

end UniqueGamesTheorem.Inverse.MatrixChart

end

section

/-! Exact chart-to-Grassmann degree comparison over the binary field. -/

namespace UniqueGamesTheorem.Inverse.MatrixChart

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

end UniqueGamesTheorem.Inverse.MatrixChart

end

section

/-! Exact full-neighbor count in the KMS vertex representation. -/

namespace UniqueGamesTheorem.Inverse.MatrixChart

open Module

/-- Ambient linear equivalence transports the actual neighbor subspaces. -/
noncomputable def grassmannNeighborsMapEquiv
    {E F : Type*} [AddCommGroup E] [Module (ZMod 2) E]
    [AddCommGroup F] [Module (ZMod 2) F]
    (e : E ≃ₗ[ZMod 2] F) (L : Submodule (ZMod 2) E) :
    GrassmannNeighbors L ≃ GrassmannNeighbors (L.map e.toLinearMap) := by
  refine Equiv.subtypeEquiv (Submodule.orderIsoMapComap e).toEquiv ?_
  intro W
  change (_ ∧ _) ↔
    (finrank (ZMod 2) (W.map e.toLinearMap) =
        finrank (ZMod 2) (L.map e.toLinearMap) ∧
      finrank (ZMod 2) (L.map e.toLinearMap ⊓ W.map e.toLinearMap :
        Submodule (ZMod 2) F) + 1 =
        finrank (ZMod 2) (L.map e.toLinearMap))
  rw [← Submodule.map_inf e.toLinearMap e.injective]
  simp only [LinearEquiv.finrank_map_eq]

/-- Extrinsic submodule neighbors and the finite KMS neighbor predicate agree. -/
def kmsNeighborsEquiv {n ell : Nat} (L : KMS.Vertex n ell) :
    GrassmannNeighbors L.val ≃ {W : KMS.Vertex n ell // KMS.Adjacent L W} where
  toFun W := ⟨⟨W.val, W.property.1.trans L.property⟩, by
    refine ⟨?_, ?_⟩
    · intro h
      have hv := congrArg Subtype.val h
      have hd := W.property.2
      rw [← hv, inf_idem] at hd
      omega
    · exact W.property.2.trans L.property⟩
  invFun W := ⟨W.val.val, W.val.property.trans L.property.symm,
    W.property.2.trans L.property.symm⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem card_full_neighbors {ell m : Nat} (M : Matrix (Fin ell) (Fin m) (ZMod 2)) :
    (KMS.neighbors (matrixVertex M)).card =
      (2 ^ ell - 1) * (2 ^ (m + 1) - 2) := by
  classical
  have h : Nat.card {W : KMS.Vertex (ell + m) ell //
      KMS.Adjacent (matrixVertex M) W} =
      (2 ^ ell - 1) * (2 ^ (m + 1) - 2) := by
    rw [← Nat.card_congr (kmsNeighborsEquiv (matrixVertex M))]
    change Nat.card (GrassmannNeighbors
      ((matrixGraph M).map (coordinateJoin (ZMod 2) ell m).toLinearMap)) = _
    rw [← Nat.card_congr (grassmannNeighborsMapEquiv
      (coordinateJoin (ZMod 2) ell m) (matrixGraph M))]
    exact card_grassmann_neighbors_graph M.vecMulLinear
  simpa only [Nat.card_eq_fintype_card, KMS.neighbors, Fintype.card_subtype] using h

/-- Exactly two full Grassmann neighbors for every nonzero factor pair. -/
theorem card_full_neighbors_twice {ell m : Nat} (M : Matrix (Fin ell) (Fin m) (ZMod 2)) :
    (KMS.neighbors (matrixVertex M)).card =
      2 * ((2 ^ ell - 1) * (2 ^ m - 1)) := by
  rw [card_full_neighbors]
  have hpow : 2 ^ (m + 1) - 2 = 2 * (2 ^ m - 1) := by
    rw [pow_succ, Nat.mul_sub_left_distrib]
    simp [Nat.mul_comm]
  rw [hpow]
  ac_rfl

end UniqueGamesTheorem.Inverse.MatrixChart

end

section

/-! Extract actual vector-valued row/column data from an arbitrary interval.
The equation counts are the dimension/codimension of that interval, and no
homogeneity is imposed on the equation right-hand sides.
-/

namespace UniqueGamesTheorem.Inverse.MatrixChart

open Matrix

variable {K ι κ : Type*} [Field K] [Fintype ι] [Fintype κ]

theorem dotFunctional_surjective :
    Function.Surjective (dotFunctional (K := K) (ι := ι)) := by
  classical
  intro f
  refine ⟨fun i => f (Pi.single i 1), ?_⟩
  apply (Pi.basisFun K ι).ext
  intro i
  change (fun j => f (Pi.single j 1)) ⬝ᵥ (Pi.basisFun K ι i) =
    f (Pi.basisFun K ι i)
  simp

theorem exists_matrix_interval_slice (A B : Submodule K ((ι → K) × (κ → K))) :
    ∃ (n_r n_c : Nat) (d : Fin n_r → ι → K) (s : Fin n_r → κ → K)
      (t : Fin n_c → ι → K) (q : Fin n_c → κ → K),
      n_r = Module.finrank K A ∧
      n_c = Module.finrank K (((ι → K) × (κ → K)) ⧸ B) ∧
      ∀ M : Matrix ι κ K,
        (A ≤ matrixGraph M ∧ matrixGraph M ≤ B) ↔
          ((∀ i, d i ᵥ* M = s i) ∧ (∀ j, M *ᵥ q j = t j)) := by
  classical
  obtain ⟨nr, nc, d, s, t, q, hnr, hnc, h⟩ := exists_interval_coordinates A B
  choose tv htv using (fun j => dotFunctional_surjective (t j))
  choose qv hqv using (fun j => dotFunctional_surjective (q j))
  refine ⟨nr, nc, d, s, tv, qv, hnr, hnc, ?_⟩
  intro M
  rw [h M.vecMulLinear]
  have hj (j : Fin nc) : (q j).comp M.vecMulLinear = t j ↔ M *ᵥ qv j = tv j := by
    rw [← hqv j, ← htv j]
    exact column_equation_iff M (qv j) (tv j)
  simp only [Matrix.vecMulLinear_apply, hj]

/-- An interval order bound yields separate row and column budgets. -/
theorem exists_bounded_matrix_interval_slice
    (A B : Submodule K ((ι → K) × (κ → K))) (r : Nat)
    (horder : Module.finrank K A +
      Module.finrank K (((ι → K) × (κ → K)) ⧸ B) ≤ r) :
    ∃ (n_r n_c : Nat) (d : Fin n_r → ι → K) (s : Fin n_r → κ → K)
      (t : Fin n_c → ι → K) (q : Fin n_c → κ → K),
      n_r ≤ r ∧ n_c ≤ r ∧
      ∀ M : Matrix ι κ K,
        (A ≤ matrixGraph M ∧ matrixGraph M ≤ B) ↔
          ((∀ i, d i ᵥ* M = s i) ∧ (∀ j, M *ᵥ q j = t j)) := by
  obtain ⟨nr, nc, d, s, t, q, hnr, hnc, h⟩ := exists_matrix_interval_slice A B
  refine ⟨nr, nc, d, s, t, q, ?_, ?_, h⟩ <;> omega

end UniqueGamesTheorem.Inverse.MatrixChart

end

end OAI
