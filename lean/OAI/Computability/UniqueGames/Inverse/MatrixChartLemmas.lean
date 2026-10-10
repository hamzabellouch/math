import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Module.LinearMap.DivisionRing
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Prod
import OAI.Computability.UniqueGames.Inverse.KMSFoundationLemmas

namespace OAI

section

namespace UniqueGamesTheorem.Inverse.MatrixChart

variable {K X Y : Type*} [Field K]
  [AddCommGroup X] [Module K X] [AddCommGroup Y] [Module K Y]

/-- The first coordinate identifies the graph with its domain. -/
def graphEquiv (T : X →ₗ[K] Y) : X ≃ₗ[K] T.graph where
  toFun x := ⟨(x, T x), rfl⟩
  invFun x := x.val.1
  left_inv _ := rfl
  right_inv x := by
    apply Subtype.ext
    exact Prod.ext rfl x.property.symm
  map_add' _ _ := by
    apply Subtype.ext
    exact Prod.ext rfl (map_add T _ _)
  map_smul' _ _ := by
    apply Subtype.ext
    exact Prod.ext rfl (map_smul T _ _)

theorem graph_injective : Function.Injective (LinearMap.graph (R := K) (M := X) (M₂ := Y)) := by
  intro T U h
  apply LinearMap.ext
  intro x
  have hx : (x, T x) ∈ U.graph := h ▸ (show (x, T x) ∈ T.graph from rfl)
  exact hx

/-- Membership in the graph chart is precisely invertibility of the first
projection; this includes both existence and uniqueness of the matrix. -/
theorem exists_unique_graph_iff (L : Submodule K (X × Y)) :
    (∃! T : X →ₗ[K] Y, L = T.graph) ↔
      Function.Bijective (fun x : L => x.val.1) := by
  constructor
  · rintro ⟨T, rfl, _⟩
    exact (graphEquiv T).symm.bijective
  · intro h
    obtain ⟨T, hT⟩ := L.exists_eq_graph h
    refine ⟨T, hT, ?_⟩
    intro U hU
    exact graph_injective (hU.symm.trans hT)

/-- Common graph vectors correspond exactly to the kernel of the difference. -/
def intersectionEquiv (T U : X →ₗ[K] Y) :
    LinearMap.ker (T - U) ≃ₗ[K] (T.graph ⊓ U.graph : Submodule K (X × Y)) where
  toFun x := ⟨(x.val, T x.val), by
    refine ⟨rfl, ?_⟩
    have hx : T x.val - U x.val = 0 := x.property
    exact sub_eq_zero.mp hx⟩
  invFun x := ⟨x.val.1, by
    change T x.val.1 - U x.val.1 = 0
    exact sub_eq_zero.mpr (x.property.1.symm.trans x.property.2)⟩
  left_inv _ := rfl
  right_inv x := by
    apply Subtype.ext
    exact Prod.ext rfl x.property.1.symm
  map_add' _ _ := by
    apply Subtype.ext
    exact Prod.ext rfl (map_add T _ _)
  map_smul' _ _ := by
    apply Subtype.ext
    exact Prod.ext rfl (map_smul T _ _)

theorem finrank_graph [FiniteDimensional K X] (T : X →ₗ[K] Y) :
    Module.finrank K T.graph = Module.finrank K X :=
  (graphEquiv T).finrank_eq.symm

/-- Rank-nullity in the graph chart, without truncated natural subtraction. -/
theorem finrank_intersection_add_rank [FiniteDimensional K X] (T U : X →ₗ[K] Y) :
    Module.finrank K (T.graph ⊓ U.graph : Submodule K (X × Y)) +
      Module.finrank K (LinearMap.range (T - U)) = Module.finrank K X := by
  rw [← (intersectionEquiv T U).finrank_eq, Nat.add_comm]
  exact LinearMap.finrank_range_add_finrank_ker (T - U)

/-- Grassmann adjacency within the chart is exactly rank-one difference. -/
theorem adjacent_iff_rank_one [FiniteDimensional K X] (T U : X →ₗ[K] Y) :
    Module.finrank K (T.graph ⊓ U.graph : Submodule K (X × Y)) + 1 =
        Module.finrank K X ↔
      Module.finrank K (LinearMap.range (T - U)) = 1 := by
  have h := finrank_intersection_add_rank T U
  omega

/-- A nonzero rank-one perturbation gives an adjacent graph vertex. -/
theorem adjacent_rank_one_step [FiniteDimensional K X]
    (T : X →ₗ[K] Y) (a : X →ₗ[K] K) (l : Y) (ha : a ≠ 0) (hl : l ≠ 0) :
    Module.finrank K (T.graph ⊓ (T + a.smulRight l).graph :
      Submodule K (X × Y)) + 1 = Module.finrank K X := by
  apply (adjacent_iff_rank_one T (T + a.smulRight l)).mpr
  have heq : T - (T + a.smulRight l) = (-a).smulRight l := by
    apply LinearMap.ext
    intro x
    simp
  rw [heq, LinearMap.range_smulRight_apply (neg_ne_zero.mpr ha)]
  exact finrank_span_singleton hl

/-- The lower end of an interval is given by a spanning list of graph vectors. -/
def lowerRows {ι : Type*} (d : ι → X) (s : ι → Y) : Submodule K (X × Y) :=
  Submodule.span K (Set.range fun i => (d i, s i))

theorem lowerRows_le_graph_iff {ι : Type*} (d : ι → X) (s : ι → Y)
    (T : X →ₗ[K] Y) :
    lowerRows d s ≤ T.graph ↔ ∀ i, T (d i) = s i := by
  rw [lowerRows, Submodule.span_le]
  constructor
  · intro h i
    exact (h ⟨i, rfl⟩).symm
  · rintro h _ ⟨i, rfl⟩
    exact (h i).symm

def upperColumns {ι : Type*} (t : ι → X →ₗ[K] K) (q : ι → Y →ₗ[K] K) :
    Submodule K (X × Y) :=
  ⨅ i, LinearMap.ker ((q i).comp (LinearMap.snd K X Y) -
    (t i).comp (LinearMap.fst K X Y))

theorem graph_le_upperColumns_iff {ι : Type*}
    (t : ι → X →ₗ[K] K) (q : ι → Y →ₗ[K] K) (T : X →ₗ[K] Y) :
    T.graph ≤ upperColumns t q ↔ ∀ i, (q i).comp T = t i := by
  constructor
  · intro h i
    apply LinearMap.ext
    intro x
    have hx := h (show (x, T x) ∈ T.graph from rfl)
    have hi := ((Submodule.mem_iInf _).mp hx) i
    exact sub_eq_zero.mp hi
  · intro h x hx
    apply (Submodule.mem_iInf _).mpr
    intro i
    change q i x.2 - t i x.1 = 0
    rw [hx]
    exact sub_eq_zero.mpr (congrArg (fun f : X →ₗ[K] K => f x.1) (h i))

/-- Exact translation of a Grassmann interval into simultaneous row and
column constraints, retaining their inhomogeneous right-hand sides. -/
theorem interval_iff_slice {ι κ : Type*} (d : ι → X) (s : ι → Y)
    (t : κ → X →ₗ[K] K) (q : κ → Y →ₗ[K] K) (T : X →ₗ[K] Y) :
    lowerRows d s ≤ T.graph ∧ T.graph ≤ upperColumns t q ↔
      (∀ i, T (d i) = s i) ∧ (∀ j, (q j).comp T = t j) := by
  rw [lowerRows_le_graph_iff, graph_le_upperColumns_iff]

end UniqueGamesTheorem.Inverse.MatrixChart

end

section

/-! Concrete matrix coordinates for the graph chart. In particular the upper
interval equations become `M q = t`, while the lower equations become `dᵀ M = sᵀ`.
The right-hand sides are retained; none of these slices is required to be linear.
-/

namespace UniqueGamesTheorem.Inverse.MatrixChart

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

end UniqueGamesTheorem.Inverse.MatrixChart

end

section

/-!
Exact finite counts for the Grassmann graph comparison in Section 4.
The quotient-line parametrization is independent of any expansion theorem.
-/

namespace UniqueGamesTheorem.Inverse.MatrixChart

open Module

variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]

/-- One-dimensional vector subspaces. -/
abbrev Lines (K E : Type*) [Field K] [AddCommGroup E] [Module K E] :=
  {L : Submodule K E // finrank K L = 1}

/-- Hyperplanes, expressed without truncated dimension subtraction. -/
abbrev Hyperplanes (K E : Type*) [Field K] [AddCommGroup E] [Module K E] :=
  {H : Submodule K E // finrank K H + 1 = finrank K E}

/-- Dual annihilation bijects hyperplanes with lines in the dual space. -/
noncomputable def hyperplanesEquivDualLines [FiniteDimensional K E] :
    Hyperplanes K E ≃ Lines K (Module.Dual K E) where
  toFun H := ⟨H.val.dualAnnihilator, by
    have h := Subspace.finrank_add_finrank_dualAnnihilator_eq H.val
    have hH := H.property
    omega⟩
  invFun L := ⟨L.val.dualCoannihilator, by
    have h := Subspace.finrank_add_finrank_dualCoannihilator_eq L.val
    rw [L.property] at h
    omega⟩
  left_inv H := by
    apply Subtype.ext
    exact Subspace.dualAnnihilator_dualCoannihilator_eq
  right_inv L := by
    apply Subtype.ext
    exact Subspace.dualCoannihilator_dualAnnihilator_eq

theorem card_lines_binary [Module (ZMod 2) E] [FiniteDimensional (ZMod 2) E] :
    Nat.card (Lines (ZMod 2) E) = 2 ^ finrank (ZMod 2) E - 1 := by
  classical
  let spanMap : {v : E // v ≠ 0} → Lines (ZMod 2) E := fun v =>
    ⟨Submodule.span (ZMod 2) {v.val}, finrank_span_singleton v.property⟩
  have hinj : Function.Injective spanMap := by
    intro v w h
    have hv : v.val ∈ Submodule.span (ZMod 2) {w.val} := by
      have hs : Submodule.span (ZMod 2) {v.val} =
          Submodule.span (ZMod 2) {w.val} := congrArg Subtype.val h
      rw [← hs]
      exact Submodule.mem_span_singleton_self _
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hv
    have hcases : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
    rcases hcases c with hc0 | hc1
    · exact False.elim (v.property (by simpa [hc0] using hc.symm))
    · exact Subtype.ext (by simpa [hc1] using hc.symm)
  have hsurj : Function.Surjective spanMap := by
    intro L
    obtain ⟨v, hv0, _⟩ := (finrank_eq_one_iff').mp L.property
    have hv : (v : E) ≠ 0 := fun h => hv0 (Subtype.ext h)
    refine ⟨⟨v.val, hv⟩, Subtype.ext ?_⟩
    exact (eq_span_singleton_of_mem_of_finrank_eq_one L.property v.property hv).symm
  let e : {v : E // v ≠ 0} ≃ Lines (ZMod 2) E := Equiv.ofBijective spanMap ⟨hinj, hsurj⟩
  let coords : E ≃ₗ[ZMod 2] (Fin (finrank (ZMod 2) E) → ZMod 2) :=
    LinearEquiv.ofFinrankEq _ _ (by simp)
  let : Finite E := Finite.of_equiv _ coords.symm.toEquiv
  let : Fintype E := Fintype.ofFinite E
  rw [← Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_subtype_compl,
    Fintype.card_subtype_eq, Module.card_eq_pow_finrank (K := ZMod 2)]
  simp

theorem card_hyperplanes_binary [Module (ZMod 2) E]
    [FiniteDimensional (ZMod 2) E] :
    Nat.card (Hyperplanes (ZMod 2) E) = 2 ^ finrank (ZMod 2) E - 1 := by
  rw [Nat.card_congr (hyperplanesEquivDualLines (K := ZMod 2) (E := E)),
    card_lines_binary, Subspace.dual_finrank_eq]

/-- A dimension identity for the quotient correspondence, retaining addition. -/
theorem finrank_map_mkQ_add [FiniteDimensional K E]
    (H W : Submodule K E) (hHW : H ≤ W) :
    finrank K (W.map H.mkQ) + finrank K H = finrank K W := by
  have h := LinearMap.finrank_range_add_finrank_ker (H.mkQ.comp W.subtype)
  have hr : LinearMap.range (H.mkQ.comp W.subtype) = W.map H.mkQ := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
  have hk : LinearMap.ker (H.mkQ.comp W.subtype) = H.comap W.subtype := by
    rw [LinearMap.ker_comp, Submodule.ker_mkQ]
  rw [hr, hk, (Submodule.comapSubtypeEquivOfLe hHW).finrank_eq] at h
  exact h

/-- One-dimensional extensions of a subspace. -/
abbrev Extensions (H : Submodule K E) :=
  {W : Submodule K E // H ≤ W ∧ finrank K W = finrank K H + 1}

/-- The quotient correspondence identifies extensions with quotient lines. -/
noncomputable def extensionsEquivLines [FiniteDimensional K E]
    (H : Submodule K E) : Extensions H ≃ Lines K (E ⧸ H) where
  toFun W := ⟨W.val.map H.mkQ, by
    have h := finrank_map_mkQ_add H W.val W.property.1
    rw [W.property.2] at h
    omega⟩
  invFun L := ⟨L.val.comap H.mkQ, Submodule.le_comap_mkQ H L.val, by
    have h := finrank_map_mkQ_add H (L.val.comap H.mkQ)
      (Submodule.le_comap_mkQ H L.val)
    have heq : (L.val.comap H.mkQ).map H.mkQ = L.val :=
      Submodule.map_comap_eq_self (by simp)
    rw [heq, L.property] at h
    omega⟩
  left_inv W := by
    apply Subtype.ext
    simp [Submodule.comap_map_mkQ, sup_eq_right.mpr W.property.1]
  right_inv L := by
    apply Subtype.ext
    exact Submodule.map_comap_eq_self (by simp)

theorem card_extensions_binary [Module (ZMod 2) E]
    [FiniteDimensional (ZMod 2) E] (H : Submodule (ZMod 2) E) :
    Nat.card (Extensions H) = 2 ^ finrank (ZMod 2) (E ⧸ H) - 1 := by
  rw [Nat.card_congr (extensionsEquivLines H), card_lines_binary]

end UniqueGamesTheorem.Inverse.MatrixChart

end

section

/-!
The full Grassmann degree, by choosing the intersection hyperplane and a
different one-dimensional extension. No graph regularity is assumed.
-/

namespace UniqueGamesTheorem.Inverse.MatrixChart

open Module

variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]

abbrev HyperplanesBelow (L : Submodule K E) :=
  {H : Submodule K E // H ≤ L ∧ finrank K H + 1 = finrank K L}

abbrev GrassmannNeighbors (L : Submodule K E) :=
  {W : Submodule K E // finrank K W = finrank K L ∧
    finrank K (L ⊓ W : Submodule K E) + 1 = finrank K L}

noncomputable def hyperplanesBelowEquiv (L : Submodule K E) :
    HyperplanesBelow L ≃ Hyperplanes K L where
  toFun H := ⟨H.val.comap L.subtype, by
    rw [(Submodule.comapSubtypeEquivOfLe H.property.1).finrank_eq]
    exact H.property.2⟩
  invFun H := ⟨H.val.map L.subtype, Submodule.map_subtype_le L H.val, by
    rw [Submodule.finrank_map_subtype_eq]
    exact H.property⟩
  left_inv H := by
    apply Subtype.ext
    simp [Submodule.map_comap_subtype, inf_eq_right.mpr H.property.1]
  right_inv H := by
    apply Subtype.ext
    exact Submodule.comap_map_eq_of_injective Subtype.val_injective H.val

/-- Distinct one-dimensional extensions intersect in their common base. -/
theorem inf_eq_base_of_distinct_extensions [FiniteDimensional K E]
    (H L W : Submodule K E) (hHL : H ≤ L) (hHW : H ≤ W)
    (hL : finrank K L = finrank K H + 1)
    (hW : finrank K W = finrank K H + 1) (hWL : W ≠ L) :
    L ⊓ W = H := by
  apply le_antisymm
  · by_contra hn
    have hlt : H < L ⊓ W := lt_of_le_of_ne (le_inf hHL hHW) (by
      intro heq
      exact hn heq.ge)
    have hd := Submodule.finrank_lt_finrank_of_lt hlt
    have hi := Submodule.finrank_mono (show L ⊓ W ≤ L from inf_le_left)
    have heq : L ⊓ W = L := Submodule.eq_of_le_of_finrank_eq inf_le_left (by omega)
    have hLW : L ≤ W := by rw [← heq]; exact inf_le_right
    exact hWL (Submodule.eq_of_le_of_finrank_eq hLW (hL.trans hW.symm)).symm
  · exact le_inf hHL hHW

abbrev NeighborExtensionData (L : Submodule K E) :=
  (H : HyperplanesBelow L) × {W : Extensions H.val // W.val ≠ L}

/-- Each neighbor has a unique intersection hyperplane and extension. -/
noncomputable def neighborsEquivExtensionData [FiniteDimensional K E]
    (L : Submodule K E) : GrassmannNeighbors L ≃ NeighborExtensionData L where
  toFun W :=
    ⟨⟨L ⊓ W.val, inf_le_left, W.property.2⟩,
      ⟨⟨W.val, inf_le_right, W.property.1.trans W.property.2.symm⟩, by
        intro heq
        have h := W.property.2
        rw [heq, inf_idem] at h
        omega⟩⟩
  invFun d := ⟨d.2.val.val, by
    have hI := inf_eq_base_of_distinct_extensions d.1.val L d.2.val.val
      d.1.property.1 d.2.val.property.1 d.1.property.2.symm
      d.2.val.property.2 d.2.property
    exact ⟨d.2.val.property.2.trans d.1.property.2,
      by rw [hI]; exact d.1.property.2⟩⟩
  left_inv W := by rfl
  right_inv d := by
    rcases d with ⟨⟨H, hHL, hH⟩, ⟨⟨W, hHW, hW⟩, hWL⟩⟩
    have hI := inf_eq_base_of_distinct_extensions H L W hHL hHW hH.symm hW hWL
    cases hI
    rfl

theorem card_other_extensions_binary [Module (ZMod 2) E] [Finite E]
    [FiniteDimensional (ZMod 2) E] (L : Submodule (ZMod 2) E)
    (H : HyperplanesBelow L) :
    Nat.card {W : Extensions H.val // W.val ≠ L} =
      2 ^ finrank (ZMod 2) (E ⧸ H.val) - 2 := by
  classical
  let : Finite (Submodule (ZMod 2) E) :=
    Finite.of_injective (fun H : Submodule (ZMod 2) E => (H : Set E))
      SetLike.coe_injective
  let base : Extensions H.val := ⟨L, H.property.1, H.property.2.symm⟩
  let : Fintype (Extensions H.val) := Fintype.ofFinite _
  have heq : (fun W : Extensions H.val => W.val ≠ L) = (fun W => W ≠ base) := by
    funext W
    apply propext
    apply not_congr
    constructor
    · intro h
      exact Subtype.ext h
    · intro h
      exact congrArg Subtype.val h
  rw [heq]
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl,
    Fintype.card_subtype_eq, ← Nat.card_eq_fintype_card,
    card_extensions_binary]
  omega

theorem card_grassmann_neighbors_binary [Module (ZMod 2) E] [Finite E]
    [FiniteDimensional (ZMod 2) E] (L : Submodule (ZMod 2) E) (m : ℕ)
    (hE : finrank (ZMod 2) E = finrank (ZMod 2) L + m) :
    Nat.card (GrassmannNeighbors L) =
      (2 ^ finrank (ZMod 2) L - 1) * (2 ^ (m + 1) - 2) := by
  classical
  let : Finite (Submodule (ZMod 2) E) :=
    Finite.of_injective (fun H : Submodule (ZMod 2) E => (H : Set E))
      SetLike.coe_injective
  let : Fintype (HyperplanesBelow L) := Fintype.ofFinite _
  rw [Nat.card_congr (neighborsEquivExtensionData L), Nat.card_sigma]
  have hterm (H : HyperplanesBelow L) :
      Nat.card {W : Extensions H.val // W.val ≠ L} = 2 ^ (m + 1) - 2 := by
    rw [card_other_extensions_binary]
    have h := H.val.finrank_quotient_add_finrank
    have hH := H.property.2
    congr 2
    omega
  simp_rw [hterm]
  rw [Finset.sum_const, Finset.card_univ, smul_eq_mul,
    ← Nat.card_eq_fintype_card,
    Nat.card_congr (hyperplanesBelowEquiv L), card_hyperplanes_binary]

end UniqueGamesTheorem.Inverse.MatrixChart

end

section

/-!
The local neighbor law for the ordered-basis lift used in KMS Lemma 2.7.
The map is an arbitrary injective linear map, not a matrix graph chart.
An update in a direction outside its image stays injective, and its image
intersects the original image in exactly the transported functional kernel.
-/

namespace UniqueGamesTheorem.Inverse.KMSBasisComparison

open Module

variable {K E F : Type*} [Field K]
  [AddCommGroup E] [Module K E] [AddCommGroup F] [Module K F]

/-- The actual rank-one update of an ordered basis map. -/
def rankOneUpdate (X : E →ₗ[K] F) (a : E →ₗ[K] K) (y : F) : E →ₗ[K] F :=
  X + a.smulRight y

@[simp] theorem rankOneUpdate_apply (X : E →ₗ[K] F) (a : E →ₗ[K] K)
    (y : F) (x : E) : rankOneUpdate X a y x = X x + a x • y := rfl

/-- An outside direction returns to the original image exactly when its
coefficient vanishes. This does not require injectivity of `X`. -/
theorem rankOneUpdate_mem_range_iff (X : E →ₗ[K] F) (a : E →ₗ[K] K)
    {y : F} (hy : y ∉ LinearMap.range X) (x : E) :
    rankOneUpdate X a y x ∈ LinearMap.range X ↔ a x = 0 := by
  constructor
  · intro h
    have hs : a x • y ∈ LinearMap.range X := by
      have hh := (LinearMap.range X).sub_mem h (LinearMap.mem_range_self X x)
      simpa only [rankOneUpdate_apply, add_sub_cancel_left] using hh
    by_contra ha
    exact hy (((LinearMap.range X).smul_mem_iff ha).mp hs)
  · intro ha
    simpa only [rankOneUpdate_apply, ha, zero_smul, add_zero] using
      LinearMap.mem_range_self X x

/-- Rank-one perturbation in an outside direction preserves independence. -/
theorem injective_rankOneUpdate (X : E →ₗ[K] F) (hX : Function.Injective X)
    (a : E →ₗ[K] K) {y : F} (hy : y ∉ LinearMap.range X) :
    Function.Injective (rankOneUpdate X a y) := by
  apply (injective_iff_map_eq_zero (rankOneUpdate X a y)).mpr
  intro x hx
  have ha : a x = 0 := (rankOneUpdate_mem_range_iff X a hy x).mp
    (by rw [hx]; exact (LinearMap.range X).zero_mem)
  have hxx : X x = 0 := by simpa only [rankOneUpdate_apply, ha, zero_smul,
    add_zero] using hx
  exact hX (by simpa only [map_zero] using hxx)

/-- Exact intersection, retaining the functional rather than only its rank. -/
theorem range_inf_rankOneUpdate (X : E →ₗ[K] F) (a : E →ₗ[K] K)
    {y : F} (hy : y ∉ LinearMap.range X) :
    LinearMap.range X ⊓ LinearMap.range (rankOneUpdate X a y) =
      (LinearMap.ker a).map X := by
  ext z
  constructor
  · rintro ⟨hz, x, hx⟩
    have ha : a x = 0 := (rankOneUpdate_mem_range_iff X a hy x).mp
      (by rw [hx]; exact hz)
    refine ⟨x, ha, ?_⟩
    simpa only [rankOneUpdate_apply, ha, zero_smul, add_zero] using hx
  · rintro ⟨x, hx, rfl⟩
    refine ⟨LinearMap.mem_range_self X x, x, ?_⟩
    have ha : a x = 0 := hx
    simp only [rankOneUpdate_apply, ha, zero_smul, add_zero]

/-- In the domain coordinates, the intersection recovers the entire kernel. -/
theorem comap_range_inf_rankOneUpdate (X : E →ₗ[K] F)
    (hX : Function.Injective X) (a : E →ₗ[K] K)
    {y : F} (hy : y ∉ LinearMap.range X) :
    (LinearMap.range X ⊓ LinearMap.range (rankOneUpdate X a y)).comap X =
      LinearMap.ker a := by
  rw [range_inf_rankOneUpdate X a hy]
  exact Submodule.comap_map_eq_of_injective hX _

/-- The updated image is a genuine Grassmann neighbor, with the full
ambient neighbor predicate rather than its chart restriction. -/
noncomputable def rankOneUpdateNeighbor [FiniteDimensional K E]
    (X : E →ₗ[K] F) (hX : Function.Injective X)
    (a : E →ₗ[K] K) (ha : a ≠ 0)
    (y : F) (hy : y ∉ LinearMap.range X) :
    MatrixChart.GrassmannNeighbors (LinearMap.range X) :=
  ⟨LinearMap.range (rankOneUpdate X a y), by
    constructor
    · rw [LinearMap.finrank_range_of_inj (injective_rankOneUpdate X hX a hy),
        LinearMap.finrank_range_of_inj hX]
    · rw [range_inf_rankOneUpdate X a hy,
        ← (Submodule.equivMapOfInjective X hX (LinearMap.ker a)).finrank_eq,
        LinearMap.finrank_range_of_inj hX]
      exact Module.Dual.finrank_ker_add_one_of_ne_zero ha⟩

@[simp] theorem rankOneUpdateNeighbor_val [FiniteDimensional K E]
    (X : E →ₗ[K] F) (hX : Function.Injective X)
    (a : E →ₗ[K] K) (ha : a ≠ 0) (y : F) (hy : y ∉ LinearMap.range X) :
    (rankOneUpdateNeighbor X hX a ha y hy).val =
      LinearMap.range (rankOneUpdate X a y) := rfl

end UniqueGamesTheorem.Inverse.KMSBasisComparison

end

section

/-! Every full Grassmann neighbor is reached by an outside rank-one update.
The proof works over every field and never selects a graph chart. -/

namespace UniqueGamesTheorem.Inverse.KMSBasisComparison

open Module

variable {K E F : Type*} [Field K]
  [AddCommGroup E] [Module K E] [AddCommGroup F] [Module K F]
  [FiniteDimensional K E] [FiniteDimensional K F]

/-- A codimension-one subspace is the kernel of a nonzero functional. -/
theorem exists_functional_ker_eq (H : Submodule K E)
    (hH : finrank K H + 1 = finrank K E) :
    ∃ a : E →ₗ[K] K, a ≠ 0 ∧ LinearMap.ker a = H := by
  have hproper : H < ⊤ := lt_top_iff_ne_top.mpr (by
    intro h
    rw [h, finrank_top] at hH
    omega)
  obtain ⟨a, ha, hle⟩ := H.exists_le_ker_of_lt_top hproper
  refine ⟨a, ha, (Submodule.eq_of_le_of_finrank_eq hle ?_).symm⟩
  have hd := Module.Dual.finrank_ker_add_one_of_ne_zero ha
  omega

/-- An arbitrary Grassmann neighbor is the range of one of the actual
rank-one updates used by the ordered-basis test. -/
theorem exists_rankOneUpdate_range_eq (X : E →ₗ[K] F)
    (hX : Function.Injective X)
    (W : MatrixChart.GrassmannNeighbors (LinearMap.range X)) :
    ∃ (a : E →ₗ[K] K) (y : F), a ≠ 0 ∧ y ∉ LinearMap.range X ∧
      LinearMap.range (rankOneUpdate X a y) = W.val := by
  let H : Submodule K E := W.val.comap X
  have hmap : H.map X = LinearMap.range X ⊓ W.val := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨LinearMap.mem_range_self X x, hx⟩
    · rintro ⟨⟨x, hx⟩, hz⟩
      exact ⟨x, by change X x ∈ W.val; rw [hx]; exact hz, hx⟩
  have hH : finrank K H + 1 = finrank K E := by
    rw [(Submodule.equivMapOfInjective X hX H).finrank_eq, hmap]
    exact W.property.2.trans (LinearMap.finrank_range_of_inj hX)
  obtain ⟨a, ha, hker⟩ := exists_functional_ker_eq H hH
  obtain ⟨x₀, hx₀⟩ := LinearMap.surjective ha (1 : K)
  have hnotle : ¬ W.val ≤ LinearMap.range X := by
    intro hle
    have heq := Submodule.eq_of_le_of_finrank_eq hle W.property.1
    have hd := W.property.2
    rw [heq, inf_idem] at hd
    omega
  obtain ⟨w, hwW, hwX⟩ := SetLike.not_le_iff_exists.mp hnotle
  let y := w - X x₀
  have hy : y ∉ LinearMap.range X := by
    intro hy
    apply hwX
    have h := (LinearMap.range X).add_mem hy (LinearMap.mem_range_self X x₀)
    simpa only [y, sub_add_cancel] using h
  refine ⟨a, y, ha, hy, ?_⟩
  have hle : LinearMap.range (rankOneUpdate X a y) ≤ W.val := by
    rintro z ⟨x, rfl⟩
    have hxker : x - a x • x₀ ∈ LinearMap.ker a := by
      change a (x - a x • x₀) = 0
      simp only [map_sub, map_smul, hx₀, smul_eq_mul, mul_one, sub_self]
    have hxW : X (x - a x • x₀) ∈ W.val := by
      have hxH : x - a x • x₀ ∈ H := by rwa [← hker]
      exact hxH
    have heq : rankOneUpdate X a y x = X (x - a x • x₀) + a x • w := by
      simp only [rankOneUpdate_apply, y, map_sub, map_smul, smul_sub]
      abel
    rw [heq]
    exact W.val.add_mem hxW (W.val.smul_mem _ hwW)
  apply Submodule.eq_of_le_of_finrank_eq hle
  rw [LinearMap.finrank_range_of_inj (injective_rankOneUpdate X hX a hy),
    W.property.1, LinearMap.finrank_range_of_inj hX]

/-- Surjectivity includes all neighbors, including those outside any fixed
matrix chart. -/
theorem rankOneUpdateNeighbor_surjective (X : E →ₗ[K] F)
    (hX : Function.Injective X) :
    Function.Surjective (fun p : {a : E →ₗ[K] K // a ≠ 0} ×
      {y : F // y ∉ LinearMap.range X} =>
        rankOneUpdateNeighbor X hX p.1.val p.1.property p.2.val p.2.property) := by
  intro W
  obtain ⟨a, y, ha, hy, hW⟩ := exists_rankOneUpdate_range_eq X hX W
  exact ⟨(⟨a, ha⟩, ⟨y, hy⟩), Subtype.ext hW⟩

end UniqueGamesTheorem.Inverse.KMSBasisComparison

end

section

/-! Transport the product-coordinate chart into the actual Grassmann vertices
used by the KMS boundary. The transport is a proved ambient linear equivalence.
-/

namespace UniqueGamesTheorem.Inverse.MatrixChart

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

end UniqueGamesTheorem.Inverse.MatrixChart

end

end OAI
