import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingDuhamelFamily
import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingBielecki

namespace OAI

/-! # Joint continuity of the actual moving-scale Picard operator

The reaction is allowed to vary with the parameter in the topology of joint
point evaluation.  Compactness of the time slab turns this into continuity
of its forcing history.  Together with the strongly continuous free family
and the uniformly bounded Duhamel operator this gives the required path
continuity without an operator-norm assertion for Schrödinger evolution.
-/

open Set

namespace DefocusingNLS

attribute [local irreducible] expandingFreeStep

noncomputable def expandingReactionSlab (T : ℝ)
    (F : C((Icc (0 : ℝ) T) × FourierL2, FourierL2))
    (u : C(Icc (0 : ℝ) T, FourierL2)) : C(Icc (0 : ℝ) T, FourierL2) :=
  ⟨fun t => F (t, u t), F.continuous.comp (continuous_id.prodMk u.continuous)⟩

theorem continuous_expandingReactionSlab
    {P : Type*} [TopologicalSpace P] (T : ℝ)
    (F : P → C((Icc (0 : ℝ) T) × FourierL2, FourierL2))
    (hF : Continuous (fun z : P × ((Icc (0 : ℝ) T) × FourierL2) => F z.1 z.2)) :
    Continuous (fun z : P × C(Icc (0 : ℝ) T, FourierL2) =>
      expandingReactionSlab T (F z.1) z.2) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact hF.comp ((continuous_fst.comp continuous_fst).prodMk
    (continuous_snd.prodMk (continuous_eval.comp
      ((continuous_snd.comp continuous_fst).prodMk continuous_snd))))

noncomputable def expandingFreeSlab (a b k L T : ℝ)
    (ha : 0 < a) (hk : 8 < k) (hL : 1 ≤ L) (u₀ : FourierL2) :
    C(Icc (0 : ℝ) T, FourierL2) :=
  ⟨fun t => expandingFreeStep a b k L t ha hk hL t.2.1 u₀, by
    let p : Icc (0 : ℝ) T → ExpandingFreeParameters :=
      fun t => (⟨L, hL⟩, ⟨t.1, t.2.1⟩)
    have hp : Continuous p :=
      continuous_const.prodMk (continuous_subtype_val.subtype_mk _)
    exact (continuous_expandingFreeFamily a b k ha hk u₀).comp hp⟩

theorem continuous_expandingFreeSlab (a b k T : ℝ) (ha : 0 < a) (hk : 8 < k) :
    Continuous (fun z : {L : ℝ // 1 ≤ L} × FourierL2 =>
      expandingFreeSlab a b k z.1.1 T ha hk z.1.2 z.2) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  let p : ({L : ℝ // 1 ≤ L} × FourierL2) × Icc (0 : ℝ) T →
      ExpandingFreeParameters × FourierL2 :=
    fun z => ((z.1.1, ⟨z.2.1, z.2.2.1⟩), z.1.2)
  have hp : Continuous p :=
    (((continuous_fst.comp continuous_fst).prodMk
      ((continuous_subtype_val.comp continuous_snd).subtype_mk _)).prodMk
        (continuous_snd.comp continuous_fst))
  exact (continuous_expandingFreeFamily_uncurry a b k ha hk).comp hp

theorem expandingPicard_eq_slab (a b k L T : ℝ)
    (ha : 0 < a) (hk : 8 < k) (hL : 1 ≤ L) (hT : 0 ≤ T)
    (F : C((Icc (0 : ℝ) T) × FourierL2, FourierL2)) (u₀ : FourierL2)
    (u : C(Icc (0 : ℝ) T, FourierL2)) :
    expandingPicard a b k L T ha hk hL hT F u₀ u =
      expandingFreeSlab a b k L T ha hk hL u₀ +
        expandingDuhamelSlab a b k L T ha hk hL hT (expandingReactionSlab T F u) := by
  apply ContinuousMap.ext
  intro t
  change expandingFreeStep a b k L t ha hk hL t.2.1 u₀ +
      expandingDuhamel a b k L ha hk hL t (expandingReactionHistory T hT F u) =
    expandingFreeStep a b k L t ha hk hL t.2.1 u₀ +
      expandingDuhamel a b k L ha hk hL t
        (expandingForcingExtension T hT (expandingReactionSlab T F u))
  rfl

theorem continuous_expandingPicard_family
    {P : Type*} [TopologicalSpace P] (a b k T : ℝ)
    (ha : 0 < a) (hk : 8 < k) (hT : 0 ≤ T)
    (L : P → {L : ℝ // 1 ≤ L}) (hL : Continuous L)
    (F : P → C((Icc (0 : ℝ) T) × FourierL2, FourierL2))
    (hF : Continuous (fun z : P × ((Icc (0 : ℝ) T) × FourierL2) => F z.1 z.2))
    (u₀ : P → FourierL2) (hu₀ : Continuous u₀) :
    Continuous (fun z : P × C(Icc (0 : ℝ) T, FourierL2) =>
      expandingPicard a b k (L z.1).1 T ha hk (L z.1).2 hT (F z.1) (u₀ z.1) z.2) := by
  simp only [expandingPicard_eq_slab]
  exact ((continuous_expandingFreeSlab a b k T ha hk).comp
    ((hL.comp continuous_fst).prodMk (hu₀.comp continuous_fst))).add
    ((continuous_expandingDuhamelSlab a b k T ha hk hT).comp
      ((hL.comp continuous_fst).prodMk (continuous_expandingReactionSlab T F hF)))

theorem continuous_expandingTimeWeight (T η : ℝ) :
    Continuous (expandingTimeWeight T η) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact (Real.continuous_exp.comp
    (continuous_const.mul (continuous_subtype_val.comp continuous_snd))).smul continuous_eval

theorem continuous_expandingBieleckiPicard_family
    {P : Type*} [TopologicalSpace P] (a b k T η : ℝ)
    (ha : 0 < a) (hk : 8 < k) (hT : 0 ≤ T)
    (L : P → {L : ℝ // 1 ≤ L}) (hL : Continuous L)
    (F : P → C((Icc (0 : ℝ) T) × FourierL2, FourierL2))
    (hF : Continuous (fun z : P × ((Icc (0 : ℝ) T) × FourierL2) => F z.1 z.2))
    (u₀ : P → FourierL2) (hu₀ : Continuous u₀) :
    Continuous (fun z : P × C(Icc (0 : ℝ) T, FourierL2) =>
      expandingBieleckiPicard a b k (L z.1).1 T η ha hk (L z.1).2 hT
        (F z.1) (u₀ z.1) z.2) :=
  (continuous_expandingTimeWeight T (-η)).comp
    ((continuous_expandingPicard_family a b k T ha hk hT L hL F hF u₀ hu₀).comp
      (continuous_fst.prodMk ((continuous_expandingTimeWeight T η).comp continuous_snd)))

end DefocusingNLS

end OAI
