import Mathlib
import OAI.Combinatorics.KMedian.Optimization.ApproximateLPSelection

namespace OAI

section
section
namespace MetricKMedian
open Finset
namespace Instance

def indexedDistance (I : Instance) (j : Fin I.clients.card) (i : Fin I.facilities.card) : ℚ :=
  I.distance (I.clients.orderEmbOfFin rfl j) (I.facilities.orderEmbOfFin rfl i)

theorem indexedDistance_nonneg (I : Instance) : ∀ j i, 0 ≤ I.indexedDistance j i :=
  fun _ _ => I.distance_nonneg _ _

theorem indexed_integral (I : Instance) (S : Finset (Fin I.n))
    (hSF : S ⊆ I.facilities) (hS : S.Nonempty) :
    ∃ T : Finset (Fin I.facilities.card), T.Nonempty ∧ T.card=S.card ∧
      ∃ a : Fin I.clients.card → Fin I.facilities.card, (∀ j, a j ∈ T) ∧
        (∑ j, I.indexedDistance j (a j))=rationalCost I S := by
  classical
  let f := I.facilities.orderEmbOfFin rfl
  let T := S.preimage f f.injective.injOn
  have hT : T.card=S.card := by
    rw [card_preimage]
    change ({x ∈ S | x ∈ Set.range (I.facilities.orderEmbOfFin rfl)}).card=S.card
    simp only [range_orderEmbOfFin]
    congr 1
    exact filter_eq_self.mpr hSF
  have hTn : T.Nonempty := card_pos.mp (by rw [hT]; exact card_pos.mpr hS)
  have each : ∀ j : Fin I.clients.card, ∃ i : Fin I.facilities.card,
      i ∈ T ∧ I.indexedDistance j i=rationalNearest I (I.clients.orderEmbOfFin rfl j) S := by
    intro j
    obtain ⟨i,hi,hd⟩ := I.rationalNearest_attained (I.clients.orderEmbOfFin rfl j) S hS
    let b : ↥I.facilities := ⟨i,hSF hi⟩
    let ai := (I.facilities.orderIsoOfFin rfl).symm b
    have he : f ai=i := congrArg Subtype.val ((I.facilities.orderIsoOfFin rfl).apply_symm_apply b)
    refine ⟨ai,mem_preimage.mpr ?_,?_⟩
    · rwa [he]
    · change I.distance _ (f ai)=_
      rw [he,hd]
  choose a ha hd using each
  refine ⟨T,hTn,hT,a,ha,?_⟩
  calc
    _ = ∑ j : Fin I.clients.card, rationalNearest I (I.clients.orderEmbOfFin rfl j) S :=
      sum_congr rfl (fun j _ => hd j)
    _ = ∑ j : ↥I.clients, rationalNearest I j.val S :=
      (I.clients.orderIsoOfFin rfl).toEquiv.sum_comp (fun j => rationalNearest I j.val S)
    _ = _ := sum_coe_sort I.clients (fun j => rationalNearest I j S)

def computedFractional (I : Instance) (r : ℕ) (hr : 0 < r)
    (hJ : I.clients.Nonempty) : TruncatedLP.FractionalData I.facilities.card I.clients.card :=
  letI : NeZero I.facilities.card := ⟨(card_pos.mpr I.facilities_nonempty).ne'⟩
  letI : NeZero I.clients.card := ⟨(card_pos.mpr hJ).ne'⟩
  TruncatedLP.selectFractional I.indexedDistance r I.k hr I.k_pos I.indexedDistance_nonneg

theorem computedFractional_spec (I : Instance) (r : ℕ) (hr : 0 < r)
    (hJ : I.clients.Nonempty) (S : Finset (Fin I.n))
    (hSF : S ⊆ I.facilities) (hS : S.Nonempty) (hSk : S.card ≤ I.k)
    (hc : 0 < rationalCost I S) :
    let out := I.computedFractional r hr hJ
    out.Valid I.k ∧ out.value I.indexedDistance ≤ (1+3/(r:ℚ))*rationalCost I S := by
  let : NeZero I.facilities.card := ⟨(card_pos.mpr I.facilities_nonempty).ne'⟩
  let : NeZero I.clients.card := ⟨(card_pos.mpr hJ).ne'⟩
  obtain ⟨T,hT,hTc,a,ha,hac⟩ := I.indexed_integral S hSF hS
  have hh := TruncatedLP.selectFractional_spec I.indexedDistance r I.k hr I.k_pos
    I.indexedDistance_nonneg T hT (by rwa [hTc]) a ha (by rwa [hac])
  rwa [hac] at hh

end Instance
end MetricKMedian
end
end

end OAI
