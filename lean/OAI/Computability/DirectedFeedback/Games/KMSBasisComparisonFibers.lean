import Mathlib
import OAI.Computability.DirectedFeedback.Games.MatrixChartDegreeNeighbors

namespace OAI

namespace DFVSGames.Inverse.KMSBasisComparison

noncomputable section
open scoped BigOperators Classical

section UniformFibers

variable {X Y G : Type*}

def fiberProductEquiv (f : X → Y) (e : ∀ y, {x : X // f x = y} ≃ G) : X ≃ Y × G :=
  (Equiv.sigmaFiberEquiv f).symm.trans (Equiv.sigmaEquivProdOfEquiv e)

@[simp] theorem fiberProductEquiv_fst (f : X → Y)
    (e : ∀ y, {x : X // f x = y} ≃ G) (x : X) :
    (fiberProductEquiv f e x).1 = f x := rfl

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

def RangeFiber (L : Submodule K F) :=
  {X : E →ₗ[K] F // Function.Injective X ∧ LinearMap.range X = L}

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

def rangeFiberEquivAut {L : Submodule K F} (e : E ≃ₗ[K] L) :
    RangeFiber (E := E) L ≃ (E ≃ₗ[K] E) :=
  (rangeFiberEquiv L).trans
    { toFun := fun a => a.trans e.symm
      invFun := fun a => a.trans e
      left_inv := by intro a; ext x; simp
      right_inv := by intro a; ext x; simp }

theorem rangeFiber_card {L : Submodule K F} (e : E ≃ₗ[K] L) :
    Nat.card (RangeFiber (E := E) L) = Nat.card (E ≃ₗ[K] E) :=
  Nat.card_congr (rangeFiberEquivAut e)

end LinearFibers

def vertexBasis {n ell : ℕ} (L : KMS.Vertex n ell) :
    KMS.Ambient ell ≃ₗ[KMS.F2] L.val :=
  LinearEquiv.ofFinrankEq _ _ (by simpa [KMS.Ambient] using L.property.symm)

theorem vertex_rangeFiber_card {n ell : ℕ} (L : KMS.Vertex n ell) :
    Nat.card (RangeFiber (E := KMS.Ambient ell) L.val) =
      Nat.card (KMS.Ambient ell ≃ₗ[KMS.F2] KMS.Ambient ell) :=
  rangeFiber_card (vertexBasis L)

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

theorem injectiveRange_expect {n ell : ℕ} {M : Type*}
    [AddCommMonoid M] [Module ℚ≥0 M] (g : KMS.Vertex n ell → M) :
    (𝔼 X : InjectiveBasisMap n ell, g (injectiveRange X)) = 𝔼 L, g L := by
  let : Nonempty (KMS.Ambient ell ≃ₗ[KMS.F2] KMS.Ambient ell) :=
    ⟨LinearEquiv.refl _ _⟩
  exact expect_eq_of_uniform_fibers injectiveRange injectiveRangeFiberAut g

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
end DFVSGames.Inverse.KMSBasisComparison

namespace DFVSGames.Inverse.KMSBasisComparison

noncomputable section
open scoped BigOperators Classical

variable {E F : Type*}
  [AddCommGroup E] [Module (ZMod 2) E]
  [AddCommGroup F] [Module (ZMod 2) F]
  [FiniteDimensional (ZMod 2) E] [FiniteDimensional (ZMod 2) F]

def outsideNeighborSample (X : E →ₗ[ZMod 2] F) (hX : Function.Injective X)
    (p : OutsideNeighborFactors X) : MatrixChart.GrassmannNeighbors X.range :=
  rankOneUpdateNeighbor X hX p.1.val p.1.property p.2.val p.2.property

omit [FiniteDimensional (ZMod 2) F] in
@[simp] theorem outsideNeighborSample_val (X : E →ₗ[ZMod 2] F)
    (hX : Function.Injective X) (p : OutsideNeighborFactors X) :
    (outsideNeighborSample X hX p).val =
      (rankOneUpdate X p.1.val p.2.val).range := rfl

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
end DFVSGames.Inverse.KMSBasisComparison

namespace DFVSGames.Inverse.MatrixChart

variable {X Y : Type*}
  [AddCommGroup X] [Module (ZMod 2) X]
  [AddCommGroup Y] [Module (ZMod 2) Y]
  [FiniteDimensional (ZMod 2) X]

abbrev BinaryChartNeighbors (T : X →ₗ[ZMod 2] Y) :=
  {U : X →ₗ[ZMod 2] Y //
    Module.finrank (ZMod 2) (T.graph ⊓ U.graph : Submodule (ZMod 2) (X × Y)) + 1 =
      Module.finrank (ZMod 2) X}

abbrev BinaryGraphChartNeighbors (T : X →ₗ[ZMod 2] Y) :=
  {L : Submodule (ZMod 2) (X × Y) //
    (∃ U : X →ₗ[ZMod 2] Y, L = U.graph) ∧
      Module.finrank (ZMod 2) (T.graph ⊓ L : Submodule (ZMod 2) (X × Y)) + 1 =
        Module.finrank (ZMod 2) X}

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

noncomputable def binaryFactorsEquivGraphNeighbors (T : X →ₗ[ZMod 2] Y) :
    BinaryRankOneFactors X Y ≃ BinaryGraphChartNeighbors T :=
  binaryRankOneEquiv.trans
    ((rankOneEquivChartNeighbors T).trans (chartNeighborsEquivGraphNeighbors T))

@[simp] theorem binaryFactorsEquivGraphNeighbors_apply (T : X →ₗ[ZMod 2] Y)
    (p : BinaryRankOneFactors X Y) :
    (binaryFactorsEquivGraphNeighbors T p).val =
      (T - p.1.val.smulRight p.2.val).graph := rfl

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

theorem graphChartNeighbor_finrank (T : X →ₗ[ZMod 2] Y)
    (L : BinaryGraphChartNeighbors T) :
    Module.finrank (ZMod 2) L.val = Module.finrank (ZMod 2) X := by
  obtain ⟨U, hU⟩ := L.property.1
  rw [hU]
  exact finrank_graph U

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

end DFVSGames.Inverse.MatrixChart

namespace DFVSGames.Inverse.MatrixChart

open Module

variable {ell m : ℕ}

abbrev CoordinateMatrix (ell m : ℕ) :=
  (Fin ell → ZMod 2) →ₗ[ZMod 2] (Fin m → ZMod 2)

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

theorem full_degree_eq_twice_chart_degree (T : CoordinateMatrix ell m) :
    Nat.card (GrassmannNeighbors T.graph) =
      2 * Nat.card (BinaryGraphChartNeighbors T) := by
  rw [card_grassmann_neighbors_graph, card_binaryGraphChartNeighbors_coordinates]
  have hpow : 2 ^ (m + 1) - 2 = 2 * (2 ^ m - 1) := by
    rw [pow_succ, Nat.mul_sub_left_distrib]
    simp [Nat.mul_comm]
  rw [hpow]
  ac_rfl

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

end DFVSGames.Inverse.MatrixChart

namespace DFVSGames.Inverse.MatrixChart

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

abbrev dotFunctional (x : ι → K) : (ι → K) →ₗ[K] K := dotProductBilin K K x

theorem dotFunctional_injective : Function.Injective (dotFunctional (K := K) (ι := ι)) := by
  intro x y h
  apply dotProduct_eq x y
  intro z
  exact congrArg (fun f : (ι → K) →ₗ[K] K => f z) h

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

theorem finrank_matrixGraph (M : Matrix ι κ K) :
    Module.finrank K (matrixGraph M) = Fintype.card ι := by
  rw [finrank_graph]
  simp

end DFVSGames.Inverse.MatrixChart

namespace DFVSGames.Inverse.MatrixChart

open Matrix

def coordinateJoin (K : Type*) [Field K] (ell m : Nat) :
    ((Fin ell → K) × (Fin m → K)) ≃ₗ[K] (Fin (ell + m) → K) :=
  (LinearEquiv.sumArrowLequivProdArrow (Fin ell) (Fin m) K K).symm.trans
    (LinearEquiv.funCongrLeft K K finSumFinEquiv.symm)

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

end DFVSGames.Inverse.MatrixChart

namespace DFVSGames.Inverse.MatrixChart

open Module

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

theorem card_full_neighbors_twice {ell m : Nat} (M : Matrix (Fin ell) (Fin m) (ZMod 2)) :
    (KMS.neighbors (matrixVertex M)).card =
      2 * ((2 ^ ell - 1) * (2 ^ m - 1)) := by
  rw [card_full_neighbors]
  have hpow : 2 ^ (m + 1) - 2 = 2 * (2 ^ m - 1) := by
    rw [pow_succ, Nat.mul_sub_left_distrib]
    simp [Nat.mul_comm]
  rw [hpow]
  ac_rfl

end DFVSGames.Inverse.MatrixChart

namespace DFVSGames.Inverse.KMSBasisComparison

noncomputable section
open scoped BigOperators Classical

private theorem relativeDensity_eq_expect_subtype_inline_KMSBasisComparisonNeighborsRetention {Ω : Type*} [Fintype Ω]
    (S : Finset Ω) (P : Ω → Prop) :
    KMS.relativeDensity S (Finset.univ.filter P) =
      𝔼 x : {x : Ω // P x}, if x.val ∈ S then (1 : ℝ) else 0 := by
  unfold KMS.relativeDensity
  rw [Fintype.expect_eq_sum_div_card]
  rw [← Finset.sum_subtype (Finset.univ.filter P) (by simp)
    (fun x => if x ∈ S then (1 : ℝ) else 0)]
  rw [Finset.sum_boole, Fintype.card_subtype]
  have hsets : S ∩ Finset.univ.filter P =
      (Finset.univ.filter P).filter (fun x => x ∈ S) := by
    ext x
    simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and]
    exact and_comm
  rw [hsets]

theorem outsideNeighbor_retention {n ell : ℕ} (S : Finset (KMS.Vertex n ell))
    (X : BasisMap n ell) (hX : Function.Injective X) :
    (𝔼 p : OutsideNeighborFactors X,
      liftedIndicator S (rankOneUpdate X p.1.val p.2.val)) =
        KMS.relativeDensity S (KMS.neighbors (rangeVertex X hX)) := by
  let e : MatrixChart.GrassmannNeighbors X.range ≃
      {W : KMS.Vertex n ell // KMS.Adjacent (rangeVertex X hX) W} :=
    MatrixChart.kmsNeighborsEquiv (rangeVertex X hX)
  let : Fintype (MatrixChart.GrassmannNeighbors X.range) :=
    Fintype.ofEquiv {W : KMS.Vertex n ell // KMS.Adjacent (rangeVertex X hX) W} e.symm
  let g : MatrixChart.GrassmannNeighbors X.range → ℝ :=
    fun W => if (e W).val ∈ S then 1 else 0
  calc
    _ = 𝔼 p : OutsideNeighborFactors X, g (outsideNeighborSample X hX p) := by
      apply Finset.expect_congr rfl
      intro p _
      unfold liftedIndicator
      rw [inLift_iff_rangeVertex_mem S _
        (injective_rankOneUpdate X hX p.1.val p.2.property)]
      have hv : rangeVertex (rankOneUpdate X p.1.val p.2.val)
          (injective_rankOneUpdate X hX p.1.val p.2.property) =
            (e (outsideNeighborSample X hX p)).val := by
        apply Subtype.ext
        rfl
      rw [hv]
      by_cases hp : (e (outsideNeighborSample X hX p)).val ∈ S <;> simp [g, hp]
    _ = 𝔼 W : MatrixChart.GrassmannNeighbors X.range, g W :=
      expect_outsideNeighborSample X hX g
    _ = 𝔼 W : {W : KMS.Vertex n ell // KMS.Adjacent (rangeVertex X hX) W},
        if W.val ∈ S then (1 : ℝ) else 0 :=
      Fintype.expect_equiv e _ _ (fun _ => rfl)
    _ = _ := (relativeDensity_eq_expect_subtype_inline_KMSBasisComparisonNeighborsRetention S
      (KMS.Adjacent (rangeVertex X hX))).symm

end
end DFVSGames.Inverse.KMSBasisComparison

end OAI
