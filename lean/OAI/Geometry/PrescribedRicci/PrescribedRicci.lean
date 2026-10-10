import Mathlib
import OAI.Geometry.PrescribedRicci.PrescribedPotential

namespace OAI

/-! Anticanonical sections and semipositive prescribed Ricci curvature. -/

noncomputable section
open Set
open scoped ContDiff

namespace Anticanonical.ComplexAtlas

variable {d : ℕ} {X : Type*} [TopologicalSpace X] (A : ComplexAtlas d X)

 

def anticanonicalSections (m : ℤ) :
    Submodule ℂ (Fin A.count → Coordinates d → ℂ) where
  carrier := {f |
    (∀ i, DifferentiableOn ℂ (f i) (A.chart i).target) ∧
    (∀ i z, z ∉ (A.chart i).target → f i z = 0) ∧
    (∀ i j x, x ∈ (A.chart i).source → x ∈ (A.chart j).source →
      f j (A.chart j x) = A.jacobian i j x ^ m * f i (A.chart i x))}
  zero_mem' := by
    refine ⟨fun _ => differentiableOn_const _, fun _ _ _ => rfl, ?_⟩
    intro i j x hi hj
    simp
  add_mem' := by
    intro f g hf hg
    refine ⟨fun i => (hf.1 i).add (hg.1 i), ?_, ?_⟩
    · intro i z hz
      change f i z + g i z = 0
      rw [hf.2.1 i z hz, hg.2.1 i z hz, add_zero]
    · intro i j x hi hj
      change f j (A.chart j x) + g j (A.chart j x) =
        A.jacobian i j x ^ m * (f i (A.chart i x) + g i (A.chart i x))
      rw [hf.2.2 i j x hi hj, hg.2.2 i j x hi hj, mul_add]
  smul_mem' := by
    intro c f hf
    refine ⟨fun i => (hf.1 i).const_smul c, ?_, ?_⟩
    · intro i z hz
      change c • f i z = 0
      rw [hf.2.1 i z hz, smul_zero]
    · intro i j x hi hj
      change c * f j (A.chart j x) = A.jacobian i j x ^ m * (c * f i (A.chart i x))
      rw [hf.2.2 i j x hi hj]
      ring

 

abbrev H0Anticanonical (m : ℤ) := ↥(A.anticanonicalSections m)

end Anticanonical.ComplexAtlas

namespace Anticanonical.ComplexAtlas

variable {d : ℕ} {X : Type*} [TopologicalSpace X]
    {A : ComplexAtlas d X} {m : ℤ}

 

theorem section_eq_zero_iff (s : A.H0Anticanonical m) :
    s = 0 ↔ ∀ i z, z ∈ (A.chart i).target → s.val i z = 0 := by
  constructor
  · intro hs
    subst hs
    intro i z hz
    rfl
  · intro hs
    apply Subtype.ext
    funext i z
    by_cases hz : z ∈ (A.chart i).target
    · exact hs i z hz
    · exact s.property.2.1 i z hz

 

theorem section_ne_zero_iff (s : A.H0Anticanonical m) :
    s ≠ 0 ↔ ∃ i z, z ∈ (A.chart i).target ∧ s.val i z ≠ 0 := by
  rw [ne_eq, section_eq_zero_iff]
  simp only [not_forall, exists_prop]

 

theorem section_ne_zero_iff_on_source (s : A.H0Anticanonical m) :
    s ≠ 0 ↔ ∃ (x : X) (i : Fin A.count),
      x ∈ (A.chart i).source ∧ s.val i (A.chart i x) ≠ 0 := by
  rw [section_ne_zero_iff]
  constructor
  · rintro ⟨i,z,hz,hs⟩
    refine ⟨(A.chart i).symm z,i,(A.chart i).mapsTo_symm hz,?_⟩
    simpa only [(A.chart i).right_inv hz] using hs
  · rintro ⟨x,i,hx,hs⟩
    exact ⟨i,A.chart i x,(A.chart i).mapsTo hx,hs⟩

 

def unitSectionOfTrivialTransitions (A : ComplexAtlas d X) (m : ℤ)
    (hJ : ∀ i j x, x ∈ (A.chart i).source → x ∈ (A.chart j).source →
      A.jacobian i j x ^ m = 1) : A.H0Anticanonical m := by
  classical
  refine ⟨fun i z => if z ∈ (A.chart i).target then 1 else 0, ?_, ?_, ?_⟩
  · intro i
    apply (differentiableOn_const (1 : ℂ)).congr
    intro z hz
    simp only [ite_eq_left hz]
  · intro i z hz
    simp only [ite_eq_right hz]
  · intro i j x hi hj
    simp only [ite_eq_left ((A.chart i).mapsTo hi), ite_eq_left ((A.chart j).mapsTo hj),
      hJ i j x hi hj, mul_one]

theorem unitSectionOfTrivialTransitions_ne_zero [Nonempty X]
    (A : ComplexAtlas d X) (m : ℤ)
    (hJ : ∀ i j x, x ∈ (A.chart i).source → x ∈ (A.chart j).source →
      A.jacobian i j x ^ m = 1) : A.unitSectionOfTrivialTransitions m hJ ≠ 0 := by
  classical
  obtain ⟨x⟩ := ‹Nonempty X›
  obtain ⟨i,hi⟩ := A.covers x
  apply (section_ne_zero_iff_on_source _).mpr
  refine ⟨x,i,hi,?_⟩
  simp only [unitSectionOfTrivialTransitions, ite_eq_left ((A.chart i).mapsTo hi), ne_eq,
    one_ne_zero, not_false_eq_true]

 

def degreeZeroSection (A : ComplexAtlas d X) : A.H0Anticanonical 0 :=
  A.unitSectionOfTrivialTransitions 0 (by intros; exact zpow_zero _)

 
@[simp] theorem jacobian_dim_zero (A : ComplexAtlas 0 X) (i j : Fin A.count) (x : X) :
    A.jacobian i j x = 1 := by
  simp [jacobian, Matrix.det_isEmpty]

 

def dimensionZeroSection (A : ComplexAtlas 0 X) (m : ℤ) : A.H0Anticanonical m :=
  A.unitSectionOfTrivialTransitions m (by intros; simp)

theorem dimensionZeroSection_ne_zero [Nonempty X] (A : ComplexAtlas 0 X) (m : ℤ) :
    A.dimensionZeroSection m ≠ 0 :=
  A.unitSectionOfTrivialTransitions_ne_zero m _

end Anticanonical.ComplexAtlas

namespace Anticanonical

 

theorem headline_dimensionZero (X : Type) [TopologicalSpace X] [Nonempty X]
    (A : ComplexAtlas 0 X) :
    ∃ m : ℤ, 0 < m ∧ ∃ s : A.H0Anticanonical m, s ≠ 0 := by
  exact ⟨1, by norm_num, A.dimensionZeroSection 1, A.dimensionZeroSection_ne_zero 1⟩

end Anticanonical

namespace Anticanonical.SourceSmooth

 

theorem prescribedRicciFromSemipositive (d : ℕ) (X : Type)
    [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    (A : ComplexAtlas d X) (P : A.ProjectiveEmbedding)
    (h : SemipositiveAnticanonicalMetric A) :
    ∃ g : KaehlerMetric A,
      (∀ i z, z ∈ (A.chart i).target →
        ∀ v : Coordinates d, g.ricciQuadratic i z v = levi (h.weight i) z v) ∧
      (∀ i z, z ∈ (A.chart i).target →
        ∀ v : Coordinates d, 0 ≤ g.ricciQuadratic i z v) := by
  obtain ⟨φ,c,hc,hp,he⟩ := prescribedPotentialViaEnergy d X A P h
  obtain ⟨g,_,hRic⟩ := prescribedRicci_of_potential P h φ hp hc he
  refine ⟨g,hRic,?_⟩
  intro i z hz v
  rw [hRic i z hz v]
  exact h.semipositive i z hz v

end Anticanonical.SourceSmooth

end

end OAI
