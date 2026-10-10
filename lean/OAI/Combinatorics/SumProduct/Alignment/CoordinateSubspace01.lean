import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.CompactConvex01
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

section
section
section
section
open Topology
open scoped Pointwise
open Topology Set
open MeasureTheory Set Topology
open MeasureTheory Topology Set
namespace RationalNilmanifoldMeasure
open MeasureTheory Topology Set
open scoped commutatorElement
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [SecondCountableTopology G]

 

omit [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [SecondCountableTopology G] in
lemma nilpotent_of_series (n : ℕ) (H : ℕ → Subgroup G)
    (h0 : H 0 = ⊤) (hn : H n = ⊥)
    (hc : ∀ i (g x : G), x ∈ H i → ⁅g,x⁆ ∈ H (i+1)) : Group.IsNilpotent G := by
  apply (Subgroup.nilpotent_iff_finite_descending_central_series G).mpr
  refine ⟨n,H,⟨h0,?_⟩,hn⟩
  intro x i hx g
  simpa only [commutatorElement_inv] using (H (i+1)).inv_mem (hc i g x hx)

 

theorem existsUnique_invariant (n : ℕ) (Γ : Subgroup G) (H : ℕ → Subgroup G)
    (h0 : H 0 = ⊤) (hn : H n = ⊥)
    (hc : ∀ i (g x : G), x ∈ H i → ⁅g,x⁆ ∈ H (i+1))
    (hr : ∀ i, CompactGroupProducts.HasCompactReps (H i) Γ)
    (hΓ : IsDiscrete (Γ : Set G))
    [MeasurableSpace (G ⧸ Γ)] [BorelSpace (G ⧸ Γ)] :
    ∃! μ : ProbabilityMeasure (G ⧸ Γ), SMulInvariantMeasure G (G ⧸ Γ) (μ : Measure (G ⧸ Γ)) := by
  let : Group.IsNilpotent G := nilpotent_of_series n H h0 hn hc
  let : DiscreteTopology Γ := isDiscrete_iff_discreteTopology.mp hΓ
  let : IsClosed (Γ : Set G) := Subgroup.isClosed_of_discreteTopology
  have hG : CompactGroupProducts.HasCompactReps ⊤ Γ := by simpa only [h0] using hr 0
  let : CompactSpace (G ⧸ Γ) := hG.quotient_compactSpace
  obtain ⟨μ,hμ⟩ := SolvableInvariantMeasure.exists_invariant_measure (G := G) (X := G ⧸ Γ)
  refine ⟨μ,hμ,?_⟩
  intro ν hν
  let := hμ
  let := hν
  apply ProbabilityMeasure.toMeasure_injective
  exact invariant_unique_of_series n Γ H h0 hn hc hr hΓ ν μ

end RationalNilmanifoldMeasure

end
 

 
section
noncomputable section
namespace RationalLattice
open MeasureTheory
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {n : ℕ}
variable (c : RealCoordinates G n) (Γ : Subgroup G)
variable (hΓ : ∀ g : G, g ∈ Γ ↔ ∀ i, ∃ z : ℤ, c.coord g i = z)

include hΓ in
 

theorem existsUnique_coordinateHaar [MeasurableSpace (G ⧸ Γ)] [BorelSpace (G ⧸ Γ)] :
    ∃! μ : ProbabilityMeasure (G ⧸ Γ),
      SMulInvariantMeasure G (G ⧸ Γ) (μ : Measure (G ⧸ Γ)) := by
  let : T2Space G := c.coord.symm.t2Space
  let : SecondCountableTopology G := c.coord.secondCountableTopology
  let : DiscreteTopology Γ := integerCoordinates_discrete c Γ hΓ
  exact RationalNilmanifoldMeasure.existsUnique_invariant n Γ (coordinateTail c)
    (coordinateTail_zero c) (coordinateTail_end c n le_rfl)
    (coordinateTail_commutator c) (coordinateTail_compact_reps c Γ hΓ)
    (isDiscrete_iff_discreteTopology.mpr inferInstance)

end RationalLattice
end
end
 

 
section
noncomputable section
namespace PairTail
open RationalLattice MeasureTheory
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {t d r : ℕ} (c : RealCoordinates G (t+d))
variable (K : Subgroup G) [K.Normal]
variable (hK : ∀ g : G, g ∈ K ↔ ∀ i : Fin (t+d), i.val < t → c.coord g i = 0)
variable (hr : r ≤ t+d) (N : Subgroup G) [N.Normal]
variable (hN : ∀ g : G, g ∈ N ↔ ∀ i : Fin (t+d), i.val < r → c.coord g i = 0)
variable (hcent : N ≤ Subgroup.center G)
variable [(diagonal K N).Normal]

 
def squareLattice (Γ : Subgroup G) : Subgroup (square K) :=
  (Γ.prod Γ).comap (square K).subtype
omit [TopologicalSpace G] [IsTopologicalGroup G] in
@[simp] lemma mem_squareLattice (Γ : Subgroup G) (x : square K) :
    x ∈ squareLattice K Γ ↔ x.val.1 ∈ Γ ∧ x.val.2 ∈ Γ := Iff.rfl

def reducedLattice (Γ : Subgroup G) : Subgroup (square K ⧸ diagonal K N) :=
  (squareLattice K Γ).map (QuotientGroup.mk' (diagonal K N))

variable (Γ : Subgroup G)
variable (hΓ : ∀ g : G, g ∈ Γ ↔ ∀ i, ∃ z : ℤ, c.coord g i = z)

include hΓ in
 

omit [N.Normal] in
theorem reducedLattice_iff (x : square K ⧸ diagonal K N) :
    x ∈ reducedLattice K N Γ ↔ ∀ i, ∃ z : ℤ,
      (reducedCoordinates c K hK hr N hN hcent).coord x i = z := by
  constructor
  · rintro ⟨y,hy,rfl⟩ i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · change ∃ z : ℤ, chartHomeomorph c K hK hr N hN hcent (QuotientGroup.mk y) (j.castAdd d) = z
      rw [chart_base]
      exact (hΓ y.val.1).mp hy.1 (MalcevPrefixQuotient.embed hr j)
    · change ∃ z : ℤ, chartHomeomorph c K hK hr N hN hcent (QuotientGroup.mk y) (j.natAdd r) = z
      rw [chart_tail]
      exact (hΓ (y.val.1⁻¹*y.val.2)).mp (Γ.mul_mem (Γ.inv_mem hy.1) hy.2)
        (RationalTailCoordinates.embed t j)
  · intro hx
    let X := (reducedCoordinates c K hK hr N hN hcent).coord x
    let a := MalcevPrefixQuotient.represent c (fun i : Fin r => X (i.castAdd d))
    let u := RationalTailCoordinates.rebuild c K hK (fun i : Fin d => X (i.natAdd r))
    have ha : a ∈ Γ := by
      apply (hΓ a).mpr
      intro i
      simp only [a,MalcevPrefixQuotient.represent,Homeomorph.apply_symm_apply,
        MalcevPrefixQuotient.lift]
      split_ifs with hi
      · exact hx (Fin.castAdd d ⟨i.val,hi⟩)
      · exact ⟨0,by simp⟩
    have hu : u.val ∈ Γ := by
      apply (hΓ u.val).mpr
      intro i
      simp only [u,RationalTailCoordinates.rebuild,Homeomorph.apply_symm_apply,
        RationalTailCoordinates.lift]
      split_ifs with hi
      · exact hx (Fin.natAdd r ⟨i.val-t,by have := i.isLt; omega⟩)
      · exact ⟨0,by simp⟩
    refine ⟨pair K a u,⟨ha,Γ.mul_mem ha hu⟩,?_⟩
    change (QuotientGroup.mk (pair K a u) : square K ⧸ diagonal K N) = x
    have he := chart_rebuild_base c K hK hr N hN hcent X
    simpa only [a,u,X,reducedCoordinates,Homeomorph.symm_apply_apply] using he.symm

include hΓ hK hN hr hcent in
omit [N.Normal] in
theorem reducedLattice_discrete : DiscreteTopology (reducedLattice K N Γ) :=
  integerCoordinates_discrete (reducedCoordinates c K hK hr N hN hcent)
    (reducedLattice K N Γ) (reducedLattice_iff c K hK hr N hN hcent Γ hΓ)

include hΓ hK hN hr hcent in
omit [N.Normal] in
theorem reducedHaar_existsUnique
    [MeasurableSpace ((square K ⧸ diagonal K N) ⧸ reducedLattice K N Γ)]
    [BorelSpace ((square K ⧸ diagonal K N) ⧸ reducedLattice K N Γ)] :
    ∃! μ : ProbabilityMeasure ((square K ⧸ diagonal K N) ⧸ reducedLattice K N Γ),
      SMulInvariantMeasure (square K ⧸ diagonal K N)
        ((square K ⧸ diagonal K N) ⧸ reducedLattice K N Γ) (μ : Measure _) :=
  existsUnique_coordinateHaar (reducedCoordinates c K hK hr N hN hcent)
    (reducedLattice K N Γ) (reducedLattice_iff c K hK hr N hN hcent Γ hΓ)

end PairTail
end
end
 

 
section
noncomputable section
namespace CoordinateSubspace
open RationalLattice RationalPolynomialMap
variable {G : Type*} [Group G] [TopologicalSpace G]
variable {n d : ℕ} (c : RealCoordinates G n) (e : Fin d ↪o Fin n)

def lift (x : Fin d → ℝ) (j : Fin n) : ℝ :=
  if h : j ∈ Set.range e then x h.choose else 0

@[simp] lemma lift_embed (x : Fin d → ℝ) (i : Fin d) : lift e x (e i) = x i := by
  unfold lift
  split_ifs with h
  · congr 1
    exact e.injective h.choose_spec
  · exact (h ⟨i,rfl⟩).elim

lemma lift_outside (x : Fin d → ℝ) (j : Fin n) (hj : j ∉ Set.range e) :
    lift e x j = 0 := by simp [lift,hj]

lemma lift_continuous : Continuous (lift e) := by
  apply continuous_pi
  intro j
  unfold lift
  split_ifs
  · exact continuous_apply _
  · exact continuous_const

lemma lift_polynomial (j : Fin n) : IsPolynomial (fun x => lift e x j) := by
  unfold lift
  split_ifs
  · exact coordinate _
  · exact zero

variable (H : Subgroup G)
variable (hH : ∀ g : G, g ∈ H ↔ ∀ j : Fin n, j ∉ Set.range e → c.coord g j = 0)

def coordinates (g : H) (i : Fin d) : ℝ := c.coord g.val (e i)

include hH in
lemma coord_lift (g : H) : lift e (coordinates c e H g) = c.coord g.val := by
  funext j
  by_cases hj : j ∈ Set.range e
  · obtain ⟨i,rfl⟩ := hj
    exact lift_embed e _ i
  · rw [lift_outside e _ j hj,(hH g.val).mp g.property j hj]

def rebuild (x : Fin d → ℝ) : H :=
  ⟨c.coord.symm (lift e x), (hH _).mpr (by
    intro j hj
    rw [Homeomorph.apply_symm_apply,lift_outside e x j hj])⟩

@[simp] lemma coordinates_rebuild (x : Fin d → ℝ) :
    coordinates c e H (rebuild c e H hH x) = x := by
  funext i
  simpa only [coordinates,rebuild,Homeomorph.apply_symm_apply] using lift_embed e x i

@[simp] lemma rebuild_coordinates (g : H) :
    rebuild c e H hH (coordinates c e H g) = g := by
  apply Subtype.ext
  apply c.coord.injective
  simpa only [rebuild,Homeomorph.apply_symm_apply] using coord_lift c e H hH g

def subspaceHomeomorph : H ≃ₜ (Fin d → ℝ) where
  toFun := coordinates c e H
  invFun := rebuild c e H hH
  left_inv := rebuild_coordinates c e H hH
  right_inv := coordinates_rebuild c e H hH
  continuous_toFun := continuous_pi (fun _ =>
    (continuous_apply _).comp (c.coord.continuous.comp continuous_subtype_val))
  continuous_invFun := (c.coord.symm.continuous.comp (lift_continuous e)).subtype_mk _

def lowerLift (i : Fin d) (x : Fin i.val → ℝ) (a : Fin (e i).val) : ℝ :=
  if h : ∃ j : Fin i.val, (e ⟨j.val,lt_trans j.isLt i.isLt⟩).val = a.val
  then x h.choose else 0

lemma lowerLift_polynomial (i : Fin d) (a : Fin (e i).val) :
    IsPolynomial (fun x => lowerLift e i x a) := by
  unfold lowerLift
  split_ifs
  · exact coordinate _
  · exact zero

include hH in
lemma lowerLift_coordinates (i : Fin d) (g : H) (a : Fin (e i).val) :
    lowerLift e i (fun j => coordinates c e H g ⟨j.val,lt_trans j.isLt i.isLt⟩) a =
      c.coord g.val ⟨a.val,lt_trans a.isLt (e i).isLt⟩ := by
  unfold lowerLift
  split_ifs with h
  · change c.coord g.val (e _) = _
    exact congrArg (c.coord g.val) (Fin.ext h.choose_spec)
  · symm
    apply (hH g.val).mp g.property
    rintro ⟨j,hj⟩
    have hji : j < i := e.lt_iff_lt.mp (by
      rw [hj]
      exact a.isLt)
    apply h
    exact ⟨⟨j.val,hji⟩, congrArg Fin.val hj⟩

lemma correction_exists (i : Fin d) :
    ∃ P : MvPolynomial (Fin i.val ⊕ Fin i.val) ℚ,
      ∀ v : (Fin i.val ⊕ Fin i.val) → ℝ,
        MvPolynomial.eval₂ (algebraMap ℚ ℝ)
          (Sum.elim (lowerLift e i (fun j => v (.inl j)))
            (lowerLift e i (fun j => v (.inr j)))) (c.correction (e i)) =
          MvPolynomial.eval₂ (algebraMap ℚ ℝ) v P := by
  apply RationalPolynomialMap.eval
  intro a
  cases a with
  | inl a =>
    exact RationalPolynomialMap.comp (lowerLift_polynomial e i a) (fun j => coordinate (Sum.inl j))
  | inr a =>
    exact RationalPolynomialMap.comp (lowerLift_polynomial e i a) (fun j => coordinate (Sum.inr j))

def correction (i : Fin d) : MvPolynomial (Fin i.val ⊕ Fin i.val) ℚ :=
  (correction_exists c e i).choose

include hH in
lemma mul_coord (g h : H) (i : Fin d) :
    coordinates c e H (g*h) i = coordinates c e H g i + coordinates c e H h i +
      MvPolynomial.eval₂ (algebraMap ℚ ℝ)
        (Sum.elim (fun j : Fin i.val => coordinates c e H g ⟨j.val,lt_trans j.isLt i.isLt⟩)
          (fun j : Fin i.val => coordinates c e H h ⟨j.val,lt_trans j.isLt i.isLt⟩))
        (correction c e i) := by
  unfold correction
  rw [← (correction_exists c e i).choose_spec]
  change c.coord (g.val*h.val) (e i) = _
  rw [c.mul_coord]
  congr 2
  funext a
  cases a with
  | inl a => exact (lowerLift_coordinates c e H hH i g a).symm
  | inr a => exact (lowerLift_coordinates c e H hH i h a).symm

 

def restrictedCoordinates : RealCoordinates H d where
  coord := subspaceHomeomorph c e H hH
  one_coord i := c.one_coord (e i)
  correction := correction c e
  mul_coord := mul_coord c e H hH

lemma restricted_lattice (Γ : Subgroup G)
    (hΓ : ∀ g, g ∈ Γ ↔ ∀ i, ∃ z : ℤ, c.coord g i = z) (g : H) :
    g ∈ Γ.comap H.subtype ↔ ∀ i, ∃ z : ℤ,
      (restrictedCoordinates c e H hH).coord g i = z := by
  constructor
  · intro hg i
    exact (hΓ g.val).mp hg (e i)
  · intro hg
    apply (hΓ g.val).mpr
    intro j
    by_cases hj : j ∈ Set.range e
    · obtain ⟨i,rfl⟩ := hj
      exact hg i
    · exact ⟨0,by simpa using (hH g.val).mp g.property j hj⟩

end CoordinateSubspace

end
end
end
end
end

end OAI
