import OAI.Probability.SLE.Loewner.InitialCapacityContinuity
import OAI.Probability.SLE.Loewner.InitialCapacityStrict
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Order.Hom.Set

namespace OAI

/-! The capacity of a simple attached slit is a genuine continuous clock,
with an exact continuous inverse on its full range. -/
noncomputable section
open Set Function
open scoped Topology

namespace SLEExactGauge

lemma initialCapacity_range (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t ≠ 0 → p t ∈ upperHalfPlane) :
    range (initialCapacity p hi h0 hH)=Icc 0 (initialCapacity p hi h0 hH 1) := by
  have hh := (initialCapacity_continuous p hi h0 hH).image_Icc_of_strictMono
    (initialCapacity_strictMono p hi h0 hH) (a := 0) (b := 1)
  have hIcc : Icc (0:unitInterval) 1=univ := by
    ext x
    simp only [mem_Icc,mem_univ,iff_true]
    exact ⟨bot_le,le_top⟩
  simpa only [hIcc,image_univ,initialCapacity_zero] using hh

noncomputable def initialCapacityHomeomorph (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t ≠ 0 → p t ∈ upperHalfPlane) :
    unitInterval ≃ₜ Icc 0 (initialCapacity p hi h0 hH 1) :=
  (((initialCapacity_strictMono p hi h0 hH).orderIso (initialCapacity p hi h0 hH)).trans
    (Set.orderIsoOfEq _ _ (initialCapacity_range p hi h0 hH))).toHomeomorph

@[simp] lemma initialCapacityHomeomorph_apply (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t ≠ 0 → p t ∈ upperHalfPlane)
    (t : unitInterval) :
    ((initialCapacityHomeomorph p hi h0 hH t : Icc 0 (initialCapacity p hi h0 hH 1)):ℝ)=
      initialCapacity p hi h0 hH t := rfl

@[simp] lemma initialCapacityHomeomorph_symm_capacity (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t ≠ 0 → p t ∈ upperHalfPlane)
    (c : Icc 0 (initialCapacity p hi h0 hH 1)) :
    initialCapacity p hi h0 hH ((initialCapacityHomeomorph p hi h0 hH).symm c)=(c:ℝ) := by
  have hh := congrArg (fun x : Icc 0 (initialCapacity p hi h0 hH 1) => (x:ℝ))
    ((initialCapacityHomeomorph p hi h0 hH).apply_symm_apply c)
  exact hh

end SLEExactGauge

end

end OAI
