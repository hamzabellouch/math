import OAI.NumberTheory.PiExponent.Cohomology.CechHigher
import OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateFiniteSections

namespace OAI

namespace PiExponent.GeometrySupport.ProjectiveTupleCharts

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open PiExponentSeshadri.Projective PiExponentSeshadri.Geometry

universe u
variable {σ : Type u} [Fintype σ]

def tupleVariables {q : ℕ} (t : Fin (q + 1) → σ) (p : Fin (q + 1)) :
    Finset {j : σ // j ≠ t p} := by
  classical
  exact Finset.univ.filter (fun j => j.val ∈ Set.range t)

@[simp] theorem mem_tupleVariables {q : ℕ} (t : Fin (q + 1) → σ)
    (p : Fin (q + 1)) (j : {j : σ // j ≠ t p}) :
    j ∈ tupleVariables t p ↔ j.val ∈ Set.range t := by
  classical
  simp [tupleVariables]

theorem tupleVariables_support {q : ℕ} (t : Fin (q + 1) → σ) (p : Fin (q + 1)) :
    ({t p} : Set σ) ∪ Subtype.val '' (tupleVariables t p : Set {j : σ // j ≠ t p}) =
      Set.range t := by
  classical
  ext j
  constructor
  · rintro (h | ⟨a, ha, rfl⟩)
    · exact h ▸ Set.mem_range_self p
    · exact (mem_tupleVariables t p a).mp ha
  · intro hj
    by_cases hp : j = t p
    · exact Or.inl hp
    · exact Or.inr ⟨⟨j, hp⟩, (mem_tupleVariables t p _).mpr hj, rfl⟩

theorem tupleVariables_support_subtuple {q r : ℕ} (t : Fin (q + 1) → σ)
    (g : Fin (r + 1) → Fin (q + 1)) (p : Fin (r + 1)) (j : Fin (q + 1)) :
    ({(t ∘ g) p} : Set σ) ∪ Subtype.val ''
        (tupleVariables (t ∘ g) p : Set {k : σ // k ≠ (t ∘ g) p}) ⊆
      ({t j} : Set σ) ∪ Subtype.val ''
        (tupleVariables t j : Set {k : σ // k ≠ t j}) := by
  rw [tupleVariables_support, tupleVariables_support]
  rintro x ⟨i, rfl⟩
  exact Set.mem_range_self (g i)

theorem tupleVariables_inf {α : Type*} [CompleteLattice α]
    (U : σ → α) {q : ℕ} (t : Fin (q + 1) → σ) (p : Fin (q + 1)) :
    U (t p) ⊓ (tupleVariables t p).inf (fun j => U j.val) = ⨅ i, U (t i) := by
  classical
  apply le_antisymm
  · apply le_iInf
    intro i
    by_cases h : t i = t p
    · rw [h]
      exact inf_le_left
    · exact inf_le_right.trans (Finset.inf_le
        ((mem_tupleVariables t p ⟨t i, h⟩).mpr (Set.mem_range_self i)))
  · apply le_inf (iInf_le _ p)
    apply Finset.le_inf
    intro j hj
    obtain ⟨i, hi⟩ := (mem_tupleVariables t p j).mp hj
    exact hi ▸ iInf_le (fun i => U (t i)) i

theorem coordinateFiniteOpen_tuple {X : Scheme} {σ : Type} [Fintype σ]
    (M : X.Modules) (s : σ → (structureSheaf X ⟶ M)) {q : ℕ}
    (t : Fin (q + 1) → σ) (p : Fin (q + 1)) :
    coordinateFiniteOpen M s (t p) (tupleVariables t p) =
      CechHigher.intersection (fun i => PiExponentSeshadri.SectionOpens.isoOpen (s i)) t := by
  change PiExponentSeshadri.SectionOpens.isoOpen (s (t p)) ⊓
    (tupleVariables t p).inf (fun j => PiExponentSeshadri.SectionOpens.isoOpen (s j.val)) = _
  exact tupleVariables_inf (fun i => PiExponentSeshadri.SectionOpens.isoOpen (s i)) t p

open PiExponentSeshadri.ModuleFlasque
open PiExponent.ProjectiveMonomialCech
attribute [local instance] MvPolynomial.gradedAlgebra

private abbrev schemeFreeOpen (X : Scheme) (U : X.Opens) : X.Modules :=
  freeOpen X.ringCatSheaf U

def freeOpenHomCongr {X : Scheme} (M : X.Modules) {U V : X.Opens} (h : U = V) :
    (schemeFreeOpen X V ⟶ M) ≃+ (schemeFreeOpen X U ⟶ M) where
  toFun b := freeOpenMap X.ringCatSheaf (eqToHom h) ≫ b
  invFun b := freeOpenMap X.ringCatSheaf (eqToHom h.symm) ≫ b
  left_inv b := by
    subst h
    simp [freeOpenMap]
    erw [Category.id_comp, Category.id_comp]
  right_inv b := by
    subst h
    simp [freeOpenMap]
    erw [Category.id_comp, Category.id_comp]
  map_add' b c := Preadditive.comp_add (C := X.Modules) _ _ _ _ b c

theorem freeOpenHomCongr_restrict {X : Scheme} (M : X.Modules)
    {U U' V V' : X.Opens} (hU : U' = U) (hV : V' = V) (h : V ≤ U)
    (b : schemeFreeOpen X U ⟶ M) :
    freeOpenHomCongr M hV (freeOpenMap X.ringCatSheaf (homOfLE h) ≫ b) =
      freeOpenMap X.ringCatSheaf (homOfLE (hV.le.trans (h.trans hU.ge))) ≫
        freeOpenHomCongr M hU b := by
  subst hU
  subst hV
  simp [freeOpenHomCongr, freeOpenMap]
  erw [Category.id_comp]

variable {X : Scheme} {K σ : Type} [CommRing K] [Fintype σ]
variable (M : X.Modules) (s : σ → (structureSheaf X ⟶ M))
variable (k : K →+* Γ(X,⊤)) (hc : (⨆ i, PiExponentSeshadri.SectionOpens.isoOpen (s i)) = ⊤)
variable (f : X ≅ Proj (PolyGrade K σ)) (hf : sectionsMorphism k s hc = f.hom)

attribute [local irreducible] coordinatePowerOverlap modulePow

include hf in
omit [Fintype σ] in

theorem coordinateOpen_isAffine (i : σ) :
    IsAffineOpen (PiExponentSeshadri.SectionOpens.isoOpen (s i)) := by
  erw [sectionOpen_eq_coordinate_preimage M k s hc f hf i]
  exact (Proj.isAffineOpen_basicOpen (PolyGrade K σ) (MvPolynomial.X i)
    (poly_X_mem i) (by decide)).preimage f.hom

def coordinateTupleCoefficient (n q : ℕ) (t : Fin (q + 1) → σ) :
    (schemeFreeOpen X
      (CechHigher.intersection (fun i => PiExponentSeshadri.SectionOpens.isoOpen (s i)) t) ⟶
        modulePow X M n) →+ Laurent σ K n :=
  (coordinatePowerOverlap M s k hc f hf n (t 0) (tupleVariables t 0)).comp
    (freeOpenHomCongr (modulePow X M n) (coordinateFiniteOpen_tuple M s t 0)).toAddMonoidHom

theorem coordinateTupleCoefficient_injective (n q : ℕ) (t : Fin (q + 1) → σ) :
    Function.Injective (coordinateTupleCoefficient M s k hc f hf n q t) :=
  (coordinatePowerOverlap_injective M s k hc f hf n (t 0) (tupleVariables t 0)).comp
    (freeOpenHomCongr (modulePow X M n) (coordinateFiniteOpen_tuple M s t 0)).injective

theorem coordinateTupleCoefficient_regular (n q : ℕ) (t : Fin (q + 1) → σ)
    (b : schemeFreeOpen X
      (CechHigher.intersection (fun i => PiExponentSeshadri.SectionOpens.isoOpen (s i)) t) ⟶
        modulePow X M n) :
    RegularOn (Set.range t) (coordinateTupleCoefficient M s k hc f hf n q t b) := by
  have h := coordinatePowerOverlap_regular M s k hc f hf n (t 0) (tupleVariables t 0)
    (freeOpenHomCongr (modulePow X M n) (coordinateFiniteOpen_tuple M s t 0) b)
  unfold coordinateTupleCoefficient
  change RegularOn (Set.range t) ((coordinatePowerOverlap M s k hc f hf n (t 0)
    (tupleVariables t 0)) ((freeOpenHomCongr (modulePow X M n) (coordinateFiniteOpen_tuple M s t 0)) b))
  simpa only [tupleVariables_support] using h

theorem coordinateTupleCoefficient_surjective_regular (n q : ℕ)
    (t : Fin (q + 1) → σ) (p : Laurent σ K n) (hp : RegularOn (Set.range t) p) :
    ∃ b, coordinateTupleCoefficient M s k hc f hf n q t b = p := by
  obtain ⟨b, hb⟩ := coordinatePowerOverlap_surjective_regular M s k hc f hf n (t 0)
    (tupleVariables t 0) p (by simpa only [tupleVariables_support] using hp)
  refine ⟨(freeOpenHomCongr (modulePow X M n)
    (coordinateFiniteOpen_tuple M s t 0)).symm b, ?_⟩
  change (coordinatePowerOverlap M s k hc f hf n (t 0) (tupleVariables t 0))
    ((freeOpenHomCongr (modulePow X M n) (coordinateFiniteOpen_tuple M s t 0))
      ((freeOpenHomCongr (modulePow X M n) (coordinateFiniteOpen_tuple M s t 0)).symm b)) = p
  rw [AddEquiv.apply_symm_apply]
  exact hb

end
end PiExponent.GeometrySupport.ProjectiveTupleCharts

end OAI
