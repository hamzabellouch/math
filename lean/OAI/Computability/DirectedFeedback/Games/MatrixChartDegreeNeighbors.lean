import Mathlib
import OAI.Computability.DirectedFeedback.Analysis.KMSMomentScalar

namespace OAI

namespace DFVSGames.Inverse.MatrixChart

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

end DFVSGames.Inverse.MatrixChart

namespace DFVSGames.Inverse.KMSBasisComparison

open Module

variable {K E F : Type*} [Field K]
  [AddCommGroup E] [Module K E] [AddCommGroup F] [Module K F]

def rankOneUpdate (X : E →ₗ[K] F) (a : E →ₗ[K] K) (y : F) : E →ₗ[K] F :=
  X + a.smulRight y

@[simp] theorem rankOneUpdate_apply (X : E →ₗ[K] F) (a : E →ₗ[K] K)
    (y : F) (x : E) : rankOneUpdate X a y x = X x + a x • y := rfl

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

theorem comap_range_inf_rankOneUpdate (X : E →ₗ[K] F)
    (hX : Function.Injective X) (a : E →ₗ[K] K)
    {y : F} (hy : y ∉ LinearMap.range X) :
    (LinearMap.range X ⊓ LinearMap.range (rankOneUpdate X a y)).comap X =
      LinearMap.ker a := by
  rw [range_inf_rankOneUpdate X a hy]
  exact Submodule.comap_map_eq_of_injective hX _

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

end DFVSGames.Inverse.KMSBasisComparison

namespace DFVSGames.Inverse.KMSBasisComparison

open Module

variable {K E F : Type*} [Field K]
  [AddCommGroup E] [Module K E] [AddCommGroup F] [Module K F]
  [FiniteDimensional K E] [FiniteDimensional K F]

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

theorem rankOneUpdateNeighbor_surjective (X : E →ₗ[K] F)
    (hX : Function.Injective X) :
    Function.Surjective (fun p : {a : E →ₗ[K] K // a ≠ 0} ×
      {y : F // y ∉ LinearMap.range X} =>
        rankOneUpdateNeighbor X hX p.1.val p.1.property p.2.val p.2.property) := by
  intro W
  obtain ⟨a, y, ha, hy, hW⟩ := exists_rankOneUpdate_range_eq X hX W
  exact ⟨(⟨a, ha⟩, ⟨y, hy⟩), Subtype.ext hW⟩

end DFVSGames.Inverse.KMSBasisComparison

namespace DFVSGames.Inverse.MatrixChart

variable {K X Y : Type*} [Field K]
  [AddCommGroup X] [Module K X] [AddCommGroup Y] [Module K Y]

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

theorem finrank_intersection_add_rank [FiniteDimensional K X] (T U : X →ₗ[K] Y) :
    Module.finrank K (T.graph ⊓ U.graph : Submodule K (X × Y)) +
      Module.finrank K (LinearMap.range (T - U)) = Module.finrank K X := by
  rw [← (intersectionEquiv T U).finrank_eq, Nat.add_comm]
  exact LinearMap.finrank_range_add_finrank_ker (T - U)

theorem adjacent_iff_rank_one [FiniteDimensional K X] (T U : X →ₗ[K] Y) :
    Module.finrank K (T.graph ⊓ U.graph : Submodule K (X × Y)) + 1 =
        Module.finrank K X ↔
      Module.finrank K (LinearMap.range (T - U)) = 1 := by
  have h := finrank_intersection_add_rank T U
  omega

theorem adjacent_rank_one_step [FiniteDimensional K X]
    (T : X →ₗ[K] Y) (a : X →ₗ[K] K) (l : Y) (ha : a ≠ 0) (hl : l ≠ 0) :
    Module.finrank K (T.graph ⊓ (T + a.smulRight l).graph :
      Submodule K (X × Y)) + 1 = Module.finrank K X := by
  apply (adjacent_iff_rank_one T (T + a.smulRight l)).mpr
  have heq : T - (T + a.smulRight l) = (-a).smulRight l := by
    apply LinearMap.ext
    intro x
    simp []
  rw [heq, LinearMap.range_smulRight_apply (neg_ne_zero.mpr ha)]
  exact finrank_span_singleton hl

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

theorem interval_iff_slice {ι κ : Type*} (d : ι → X) (s : ι → Y)
    (t : κ → X →ₗ[K] K) (q : κ → Y →ₗ[K] K) (T : X →ₗ[K] Y) :
    lowerRows d s ≤ T.graph ∧ T.graph ≤ upperColumns t q ↔
      (∀ i, T (d i) = s i) ∧ (∀ j, (q j).comp T = t j) := by
  rw [lowerRows_le_graph_iff, graph_le_upperColumns_iff]

end DFVSGames.Inverse.MatrixChart

namespace DFVSGames.Inverse.MatrixChart

section ArbitraryField

variable {K X Y : Type*} [Field K]
  [AddCommGroup X] [Module K X] [AddCommGroup Y] [Module K Y]

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

theorem rank_one_iff_exists_smulRight (T : X →ₗ[K] Y) :
    Module.finrank K T.range = 1 ↔
      ∃ (a : X →ₗ[K] K) (l : Y), a ≠ 0 ∧ l ≠ 0 ∧ T = a.smulRight l := by
  constructor
  · exact exists_smulRight_of_rank_one T
  · rintro ⟨a, l, ha, hl, rfl⟩
    rw [LinearMap.range_smulRight_apply ha]
    exact finrank_span_singleton hl

end ArbitraryField

variable {X Y : Type*}
  [AddCommGroup X] [Module (ZMod 2) X]
  [AddCommGroup Y] [Module (ZMod 2) Y]

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

abbrev BinaryRankOneFactors (X Y : Type*)
    [AddCommGroup X] [Module (ZMod 2) X]
    [AddCommGroup Y] [Module (ZMod 2) Y] :=
  {a : X →ₗ[ZMod 2] ZMod 2 // a ≠ 0} × {l : Y // l ≠ 0}

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

noncomputable def binaryRankOneEquiv :
    BinaryRankOneFactors X Y ≃ BinaryRankOneMaps X Y :=
  Equiv.ofBijective binaryRankOneMap
    ⟨binary_smulRight_injective, binary_smulRight_surjective⟩

@[simp] theorem binaryRankOneEquiv_apply (p : BinaryRankOneFactors X Y) :
    (binaryRankOneEquiv p).val = p.1.val.smulRight p.2.val := rfl

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

end DFVSGames.Inverse.MatrixChart

namespace DFVSGames.Inverse.KMSBasisComparison

noncomputable section

variable {E F : Type*} [AddCommGroup E] [Module (ZMod 2) E]
  [AddCommGroup F] [Module (ZMod 2) F]

abbrev FixedFunctionalNeighborFiber (X : E →ₗ[ZMod 2] F)
    (a : E →ₗ[ZMod 2] ZMod 2) (y₀ : F) :=
  {y : F // y ∉ X.range ∧
    (X + a.smulRight y).range = (X + a.smulRight y₀).range}

theorem add_image_not_mem_range (X : E →ₗ[ZMod 2] F)
    {y : F} (hy : y ∉ X.range) (z : E) : y + X z ∉ X.range := by
  intro h
  exact hy (by simpa using X.range.sub_mem h (X.mem_range_self z))

theorem range_update_add_kernel (X : E →ₗ[ZMod 2] F)
    (a : E →ₗ[ZMod 2] ZMod 2) (y : F) (z : a.ker) :
    (X + a.smulRight (y + X z)).range = (X + a.smulRight y).range := by
  have hz : a z = 0 := z.property
  have hforward (x : E) :
      (X + a.smulRight (y + X z)) x =
        (X + a.smulRight y) (x + a x • z) := by
    simp [hz, smul_add] ; abel
  have hbackward (x : E) :
      (X + a.smulRight y) x =
        (X + a.smulRight (y + X z)) (x - a x • z) := by
    simp [hz, smul_add]
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    exact ⟨x + a x • z, (hforward x).symm⟩
  · rintro _ ⟨x, rfl⟩
    exact ⟨x - a x • z, (hbackward x).symm⟩

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
end DFVSGames.Inverse.KMSBasisComparison

namespace DFVSGames.Inverse.KMSBasisComparison

variable {E F : Type*}
  [AddCommGroup E] [Module (ZMod 2) E]
  [AddCommGroup F] [Module (ZMod 2) F]

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

theorem binary_functional_eq_of_map_ker_eq
    (X : E →ₗ[ZMod 2] F) (hX : Function.Injective X)
    {a b : E →ₗ[ZMod 2] ZMod 2}
    (h : a.ker.map X = b.ker.map X) : a = b := by
  exact binary_functional_eq_of_ker_eq (Submodule.map_injective_of_injective hX h)

end DFVSGames.Inverse.KMSBasisComparison

namespace DFVSGames.Inverse.KMSBasisComparison

noncomputable section

variable {E F : Type*} [AddCommGroup E] [Module (ZMod 2) E]
  [AddCommGroup F] [Module (ZMod 2) F]

abbrev OutsideNeighborFactors (X : E →ₗ[ZMod 2] F) :=
  {a : E →ₗ[ZMod 2] ZMod 2 // a ≠ 0} × {y : F // y ∉ X.range}

abbrev OutsideNeighborPairFiber (X : E →ₗ[ZMod 2] F)
    (a : E →ₗ[ZMod 2] ZMod 2) (y : F) :=
  {p : OutsideNeighborFactors X //
    (rankOneUpdate X p.1.val p.2.val).range = (rankOneUpdate X a y).range}

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

def fixedFunctionalEquivPairFiber (X : E →ₗ[ZMod 2] F)
    (hX : Function.Injective X) (a : E →ₗ[ZMod 2] ZMod 2)
    (ha : a ≠ 0) {y₀ : F} (hy₀ : y₀ ∉ X.range) :
    FixedFunctionalNeighborFiber X a y₀ ≃ OutsideNeighborPairFiber X a y₀ :=
  Equiv.ofBijective (fixedToPairFiber X a ha y₀)
    ⟨fixedToPairFiber_injective X a ha y₀,
      fixedToPairFiber_surjective X hX a ha hy₀⟩

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
end DFVSGames.Inverse.KMSBasisComparison

end OAI
