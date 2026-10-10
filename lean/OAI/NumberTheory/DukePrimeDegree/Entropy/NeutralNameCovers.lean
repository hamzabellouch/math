import OAI.NumberTheory.DukePrimeDegree.Dynamics.CentralOrbitCover
import OAI.NumberTheory.DukePrimeDegree.Entropy.NameErrorEntropy

namespace OAI

/-! # Measurable selection of neutral orbit approximations

A finite cover by neutral displacements admits a measurable choice of
reference displacement. The same finite list works for every orbit length.
-/

noncomputable section
open MeasureTheory Set
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

local instance (n : ℕ) : MeasurableSpace (G n) := borel (G n)
local instance (n : ℕ) : BorelSpace (G n) := ⟨rfl⟩

theorem measurable_choice_fin_cover {Y : Type*} [MeasurableSpace Y]
    {N : ℕ} (S : Fin N → Set Y) (hS : ∀ i, MeasurableSet (S i))
    (hcover : ∀ y, ∃ i, y ∈ S i) :
    ∃ r : Y → Fin N, Measurable r ∧ ∀ y, y ∈ S (r y) := by
  classical
  let p (y : Y) (k : ℕ) := ∃ hk : k < N, y ∈ S ⟨k,hk⟩
  have hp (y : Y) : ∃ k, p y k := by
    obtain ⟨i,hi⟩ := hcover y
    exact ⟨i.val,i.isLt,hi⟩
  have hm : Measurable (fun y => Nat.find (hp y)) := by
    apply measurable_find hp
    intro k
    by_cases hk : k < N
    · have he : {y | p y k} = S ⟨k,hk⟩ := by
        ext y
        simp [p,hk]
      rw [he]
      exact hS ⟨k,hk⟩
    · have he : {y | p y k} = ∅ := by ext y; simp [p,hk]
      rw [he]
      exact MeasurableSet.empty
  let r (y : Y) : Fin N := ⟨Nat.find (hp y),(Nat.find_spec (hp y)).choose⟩
  refine ⟨r,?_,fun y => (Nat.find_spec (hp y)).choose_spec⟩
  apply measurable_to_countable'
  intro i
  have he : r ⁻¹' {i} = (fun y => Nat.find (hp y)) ⁻¹' {i.val} := by
    ext y
    exact Fin.ext_iff
  rw [he]
  exact hm (measurableSet_singleton _)

/-- A compact collection of neutral displacements can be encoded by one
measurable finite label, uniformly for all real times. -/
theorem compact_neutral_measurable_selector {n : ℕ}
    (ell : Fin n → ℝ) (hell : ∑ i, ell i=0)
    (K : Set (G n)) (hK : IsCompact K)
    (hcomm : ∀ g ∈ K, ∀ t : ℝ, Commute g (diagonalOneParameter ell hell t))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (N : ℕ) (g : Fin N → G n) (r : K → Fin N),
      (∀ i, g i ∈ K) ∧ Measurable r ∧
      ∀ (k : K) (x : X n) (t : ℝ),
        quotientLogDistance
          (rightAction (rightAction x k.val) (diagonalOneParameter ell hell t))
          (rightAction (rightAction x (g (r k))) (diagonalOneParameter ell hell t)) < ε := by
  classical
  let U (h : K) : Set (G n) := {g | matrixLogLength (g⁻¹*h.val) < ε}
  have hU (h : K) : IsOpen (U h) :=
    isOpen_lt ((continuous_matrixLogLength n).comp (continuous_inv.mul continuous_const))
      continuous_const
  obtain ⟨s,hs⟩ := hK.elim_finite_subcover U hU (fun g hg =>
    mem_iUnion.mpr ⟨⟨g,hg⟩,by simpa only [U,mem_ofPred_eq,inv_mul_cancel,
      matrixLogLength_one] using hε⟩)
  let e : Fin (Fintype.card s) ≃ s := (Fintype.equivFin s).symm
  let g (i : Fin (Fintype.card s)) : G n := (e i).val.val
  let S (i : Fin (Fintype.card s)) : Set K := {k | matrixLogLength (k.val⁻¹*g i) < ε}
  have hm (i : Fin (Fintype.card s)) : MeasurableSet (S i) := by
    exact (isOpen_lt ((continuous_matrixLogLength n).comp
      (continuous_subtype_val.inv.mul continuous_const)) continuous_const).measurableSet
  have hc (k : K) : ∃ i, k ∈ S i := by
    obtain ⟨h,hh,hkh⟩ := mem_iUnion₂.mp (hs k.prop)
    refine ⟨e.symm ⟨h,hh⟩,?_⟩
    simpa only [S,g,U,mem_ofPred_eq,Equiv.apply_symm_apply] using hkh
  obtain ⟨r,hr,hsel⟩ := measurable_choice_fin_cover S hm hc
  refine ⟨Fintype.card s,g,r,fun i => (e i).val.prop,hr,?_⟩
  intro k x t
  exact (quotientLogDistance_commuting_displacements x k.val (g (r k))
    (diagonalOneParameter ell hell t) (hcomm k.val k.prop t)
    (hcomm (g (r k)) (e (r k)).val.prop t)).trans_lt (hsel k)

end DukePrimeDegree

end

end OAI
