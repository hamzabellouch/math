import OAI.GroupTheory.Thompson.AffinePiece
import OAI.GroupTheory.Thompson.DyadicGapChain
import OAI.GroupTheory.Thompson.OrderedChainKnots
import Mathlib.Data.List.Forall2
import Mathlib.Topology.Order.MonotoneContinuity

namespace OAI

/-!
# Actual interpolation of ordered dyadic partitions

Matched cells determine affine maps. They are glued at their common endpoints,
and the reverse matching is their inverse. Restricting the resulting real
order isomorphism gives the literal interval homeomorphism.
-/

noncomputable section

namespace ThompsonNonamenability

namespace OrderedPLInterpolation

def chainMap (b d : ℝ) : List BasicInterval → List BasicInterval → ℝ → ℝ
  | [], _, x => x + (d - b)
  | _ :: _, [], x => x + (d - b)
  | I :: L, J :: R, x =>
      if x ≤ I.right then affine I J x else chainMap b d L R x

theorem chainMap_start {a b c d : ℝ} {L R : List BasicInterval}
    (hL : GapChain a b L) (hR : GapChain c d R) (hlen : L.length = R.length) :
    chainMap b d L R a = c := by
  cases L with
  | nil =>
      have hnil : R = [] := List.length_eq_zero_iff.mp hlen.symm
      subst R
      change a = b at hL
      change c = d at hR
      simp only [chainMap, hL, hR]
      ring
  | cons I L =>
      cases R with
      | nil => simp at hlen
      | cons J R =>
          change I.left = a ∧ GapChain I.right b L at hL
          change J.left = c ∧ GapChain J.right d R at hR
          rw [← hL.1]
          simp only [chainMap, ite_eq_left I.left_lt_right.le, affine_left, hR.1]

theorem chainMap_eq_tail {b d x : ℝ} {I J : BasicInterval}
    {L R : List BasicInterval} (hL : GapChain I.right b L)
    (hR : GapChain J.right d R) (hlen : L.length = R.length)
    (hx : I.right ≤ x) :
    chainMap b d (I :: L) (J :: R) x = chainMap b d L R x := by
  by_cases h : x ≤ I.right
  · have heq : x = I.right := le_antisymm h hx
    subst x
    rw [chainMap, ite_eq_left le_rfl, affine_right, chainMap_start hL hR hlen]
  · rw [chainMap, ite_eq_right h]

theorem chainMap_end {a b c d : ℝ} {L R : List BasicInterval}
    (hL : GapChain a b L) (hR : GapChain c d R) (hlen : L.length = R.length) :
    chainMap b d L R b = d := by
  induction L generalizing a c R with
  | nil =>
      simp only [chainMap]
      ring
  | cons I L ih =>
      cases R with
      | nil => simp at hlen
      | cons J R =>
          have ht : L.length = R.length := Nat.succ.inj hlen
          rw [chainMap_eq_tail hL.2 hR.2 ht hL.2.le_endpoints]
          exact ih hL.2 hR.2 ht

theorem chainMap_strictMono {a b c d : ℝ} {L R : List BasicInterval}
    (hL : GapChain a b L) (hR : GapChain c d R) (hlen : L.length = R.length) :
    StrictMono (chainMap b d L R) := by
  induction L generalizing a c R with
  | nil =>
      intro x y hxy
      exact add_lt_add_left hxy _
  | cons I L ih =>
      cases R with
      | nil => simp at hlen
      | cons J R =>
          have ht : L.length = R.length := Nat.succ.inj hlen
          have hm := ih hL.2 hR.2 ht
          have hb := chainMap_start hL.2 hR.2 ht
          intro x y hxy
          change (if x ≤ I.right then affine I J x else chainMap b d L R x) <
            (if y ≤ I.right then affine I J y else chainMap b d L R y)
          by_cases hx : x ≤ I.right
          · rw [ite_eq_left hx]
            by_cases hy : y ≤ I.right
            · rw [ite_eq_left hy]
              exact affine_strictMono I J hxy
            · rw [ite_eq_right hy]
              calc
                affine I J x ≤ affine I J I.right :=
                  (affine_strictMono I J).monotone hx
                _ = J.right := affine_right I J
                _ = chainMap b d L R I.right := hb.symm
                _ < chainMap b d L R y := hm (lt_of_not_ge hy)
          · have hy : ¬ y ≤ I.right := fun hy => hx (hxy.le.trans hy)
            rw [ite_eq_right hx, ite_eq_right hy]
            exact hm hxy

theorem chainMap_inverse {a b c d : ℝ} {L R : List BasicInterval}
    (hL : GapChain a b L) (hR : GapChain c d R) (hlen : L.length = R.length)
    (x : ℝ) : chainMap d b R L (chainMap b d L R x) = x := by
  induction L generalizing a c R with
  | nil =>
      have hnil : R = [] := List.length_eq_zero_iff.mp hlen.symm
      subst R
      simp only [chainMap]
      ring
  | cons I L ih =>
      cases R with
      | nil => simp at hlen
      | cons J R =>
          have ht : L.length = R.length := Nat.succ.inj hlen
          by_cases hx : x ≤ I.right
          · have hy : affine I J x ≤ J.right := by
              rw [← affine_right I J]
              exact (affine_strictMono I J).monotone hx
            simp only [chainMap, ite_eq_left hx, ite_eq_left hy]
            exact affine_inverse I J x
          · have hy : ¬ chainMap b d L R x ≤ J.right := by
              have hm := chainMap_strictMono hL.2 hR.2 ht (lt_of_not_ge hx)
              rw [chainMap_start hL.2 hR.2 ht] at hm
              exact not_le_of_gt hm
            simp only [chainMap, ite_eq_right hx, ite_eq_right hy]
            exact ih hL.2 hR.2 ht

theorem chainMap_on_cells_aux {a b c d : ℝ} {L R : List BasicInterval}
    (hL : GapChain a b L) (hR : GapChain c d R) (hlen : L.length = R.length) :
    List.Forall₂ (fun I J => I ∈ L ∧ ∀ x ∈ I.carrier,
      chainMap b d L R x = affine I J x) L R := by
  induction L generalizing a c R with
  | nil =>
      have hnil : R = [] := List.length_eq_zero_iff.mp hlen.symm
      subst R
      exact List.Forall₂.nil
  | cons I L ih =>
      cases R with
      | nil => simp at hlen
      | cons J R =>
          have ht : L.length = R.length := Nat.succ.inj hlen
          apply List.Forall₂.cons
          · refine ⟨List.mem_cons_self, ?_⟩
            intro x hx
            exact ite_eq_left hx.2
          · apply (ih hL.2 hR.2 ht).imp
            intro K Q hK
            refine ⟨List.mem_cons_of_mem I hK.1, ?_⟩
            intro x hx
            rw [chainMap_eq_tail hL.2 hR.2 ht
              ((hL.2.left_le_of_mem hK.1).trans hx.1)]
            exact hK.2 x hx

theorem chainMap_on_cells {a b c d : ℝ} {L R : List BasicInterval}
    (hL : GapChain a b L) (hR : GapChain c d R) (hlen : L.length = R.length) :
    List.Forall₂ (fun I J => ∀ x ∈ I.carrier,
      chainMap b d L R x = affine I J x) L R :=
  (chainMap_on_cells_aux hL hR hlen).imp (fun _ _ h => h.2)

def chainOrderIso {L R : List BasicInterval}
    (hL : GapChain 0 1 L) (hR : GapChain 0 1 R) (hlen : L.length = R.length) :
    ℝ ≃o ℝ where
  toFun := chainMap 1 1 L R
  invFun := chainMap 1 1 R L
  left_inv := chainMap_inverse hL hR hlen
  right_inv := chainMap_inverse hR hL hlen.symm
  map_rel_iff' := (chainMap_strictMono hL hR hlen).le_iff_le

def intervalOrderIso {L R : List BasicInterval}
    (hL : GapChain 0 1 L) (hR : GapChain 0 1 R) (hlen : L.length = R.length) :
    UnitInterval ≃o UnitInterval where
  toFun x := ⟨chainMap 1 1 L R x, by
    have hm := (chainMap_strictMono hL hR hlen).monotone
    constructor
    · simpa only [chainMap_start hL hR hlen] using hm x.property.1
    · simpa only [chainMap_end hL hR hlen] using hm x.property.2⟩
  invFun x := ⟨chainMap 1 1 R L x, by
    have hm := (chainMap_strictMono hR hL hlen.symm).monotone
    constructor
    · simpa only [chainMap_start hR hL hlen.symm] using hm x.property.1
    · simpa only [chainMap_end hR hL hlen.symm] using hm x.property.2⟩
  left_inv x := Subtype.ext (chainMap_inverse hL hR hlen x)
  right_inv x := Subtype.ext (chainMap_inverse hR hL hlen.symm x)
  map_rel_iff' := (chainMap_strictMono hL hR hlen).le_iff_le

def intervalHomeomorph {L R : List BasicInterval}
    (hL : GapChain 0 1 L) (hR : GapChain 0 1 R) (hlen : L.length = R.length) :
    IntervalHomeomorph := ⟨(intervalOrderIso hL hR hlen).toHomeomorph⟩

theorem intervalHomeomorph_strictMono {L R : List BasicInterval}
    (hL : GapChain 0 1 L) (hR : GapChain 0 1 R) (hlen : L.length = R.length) :
    StrictMono (intervalHomeomorph hL hR hlen) :=
  (intervalOrderIso hL hR hlen).strictMono

def interpolationWitness {L R : List BasicInterval}
    (hL : GapChain 0 1 L) (hR : GapChain 0 1 R) (hlen : L.length = R.length) :
    DyadicPLWitness (intervalHomeomorph hL hR hlen) where
  pieceCount := L.length
  positive := hL.toSubdivision.positive
  knots := hL.toSubdivision.knots
  strictMono_knots := hL.toSubdivision.strictMono_knots
  first := hL.toSubdivision.first
  last := hL.toSubdivision.last
  dyadic := hL.toSubdivision.dyadic
  cover := hL.toSubdivision.cover
  exponent i := ((L.get i).depth : ℤ) - ((R.get (Fin.cast hlen i)).depth : ℤ)
  affine := by
    intro i x hxleft hxright
    let s := hL.toSubdivision
    have hp : ∀ y ∈ (L.get i).carrier, chainMap 1 1 L R y =
        affine (L.get i) (R.get (Fin.cast hlen i)) y :=
      (chainMap_on_cells hL hR hlen).get i.isLt (by simpa only [← hlen] using i.isLt)
    have hx : (x : ℝ) ∈ (L.get i).carrier := by
      constructor
      · rw [← s.left_eq i]
        exact hxleft
      · rw [← s.right_eq i]
        exact hxright
    have hk : (s.knots i.castSucc : ℝ) ∈ (L.get i).carrier := by
      rw [s.left_eq i]
      exact ⟨le_rfl, (L.get i).left_lt_right.le⟩
    change chainMap 1 1 L R (x : ℝ) =
      chainMap 1 1 L R (s.knots i.castSucc : ℝ) +
        (2 : ℝ) ^ (((L.get i).depth : ℤ) - ((R.get (Fin.cast hlen i)).depth : ℤ)) *
          ((x : ℝ) - (s.knots i.castSucc : ℝ))
    rw [hp _ hx, hp _ hk, s.left_eq i, affine_left]
    simp only [affine, affine_slope_zpow]

def transport {L R : List BasicInterval}
    (hL : GapChain 0 1 L) (hR : GapChain 0 1 R) (hlen : L.length = R.length) : F :=
  ⟨intervalHomeomorph hL hR hlen, intervalHomeomorph_strictMono hL hR hlen,
    ⟨interpolationWitness hL hR hlen⟩⟩

theorem transport_on_cells {L R : List BasicInterval}
    (hL : GapChain 0 1 L) (hR : GapChain 0 1 R) (hlen : L.length = R.length) :
    List.Forall₂ (CarriesAffinely (transport hL hR hlen)) L R := by
  apply (chainMap_on_cells hL hR hlen).imp
  intro I J h x
  change chainMap 1 1 L R (I.chart (x : ℝ)) = J.chart (x : ℝ)
  simpa only [BasicInterval.coe_chartPoint, affine_chart] using
    h _ (I.chartPoint_mem_carrier x)

end OrderedPLInterpolation

theorem exists_chain_transport {L R : List BasicInterval}
    (hL : GapChain 0 1 L) (hR : GapChain 0 1 R) (hlen : L.length = R.length) :
    ∃ h : F, List.Forall₂ (CarriesAffinely h) L R :=
  ⟨OrderedPLInterpolation.transport hL hR hlen,
    OrderedPLInterpolation.transport_on_cells hL hR hlen⟩

end ThompsonNonamenability

end

end OAI
