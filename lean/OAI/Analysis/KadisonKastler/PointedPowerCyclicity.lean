import OAI.Analysis.KadisonKastler.PointedPowerOperators
import OAI.Analysis.KadisonKastler.PointedLocalMatrix
import OAI.Analysis.KadisonKastler.PreparedPairCorrection
import Mathlib.Algebra.Group.Finsupp

namespace OAI

/-! # Cyclic and separating configuration vacua

Local cyclicity generates every finitely excited basis vector. Applying
the same argument to the commuting right actions proves separation.
-/

namespace KadisonKastler

open Generator
open scoped BigOperators

noncomputable section

def pointedPowerInsertLinear (i : ℕ) (f : PointedPowerConfiguration) :
    PointedLocalHilbert →ₗ[ℂ] PointedPowerHilbert where
  toFun x := ∑ k : Fin 4, x k • pointedPowerBasis (f.update i k)
  map_add' x y := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c x := by simp [Finset.smul_sum, smul_smul]

@[simp] theorem pointedPowerInsertLinear_single (i : ℕ)
    (f : PointedPowerConfiguration) (k : Fin 4) :
    pointedPowerInsertLinear i f (EuclideanSpace.single k 1) =
      pointedPowerBasis (f.update i k) := by
  simp [pointedPowerInsertLinear]

theorem pointedPowerInsertLinear_operator (i : ℕ) (f : PointedPowerConfiguration)
    (hf : f i = 0) (A : PointedLocalHilbert →L[ℂ] PointedLocalHilbert) :
    pointedPowerInsertLinear i f (A pointedLocalVacuum) =
      pointedPowerOperator i A (pointedPowerBasis f) := by
  rw [pointedPowerOperator_basis]
  simp only [pointedPowerInsertLinear, LinearMap.coe_mk, AddHom.coe_mk,
    finiteLocalCoefficient, hf, pointedLocalVacuum]

def pointedPowerSite
    (E : MatrixUnitSystem (Fin 2) (PointedLocalHilbert →L[ℂ] PointedLocalHilbert))
    (i : ℕ) : MatrixUnitSystem (Fin 2) (PointedPowerHilbert →L[ℂ] PointedPowerHilbert) :=
  E.map (pointedPowerOperator i)

def pointedPowerAlgebra
    (E : MatrixUnitSystem (Fin 2) (PointedLocalHilbert →L[ℂ] PointedLocalHilbert)) :
    VonNeumannAlgebra PointedPowerHilbert :=
  generatedVonNeumannAlgebra (⨆ i : ℕ, (pointedPowerSite E i).algebra)

theorem pointedPowerSite_mem
    (E : MatrixUnitSystem (Fin 2) (PointedLocalHilbert →L[ℂ] PointedLocalHilbert))
    (i : ℕ) (a b : Fin 2) : pointedPowerOperator i (E.entry a b) ∈ pointedPowerAlgebra E := by
  apply subset_generatedVonNeumannAlgebra
  exact (le_iSup (fun j : ℕ => (pointedPowerSite E j).algebra) i)
    ((pointedPowerSite E i).entry_mem a b)

theorem pointedPowerBasis_mem_orbit
    (E : MatrixUnitSystem (Fin 2) (PointedLocalHilbert →L[ℂ] PointedLocalHilbert))
    (hE : Submodule.span ℂ (Set.range (fun p : Fin 2 × Fin 2 =>
      E.entry p.1 p.2 pointedLocalVacuum)) = ⊤)
    (f : PointedPowerConfiguration) :
    pointedPowerBasis f ∈ LinearMap.range (algebraVectorMap (pointedPowerAlgebra E)
      pointedPowerVacuum) := by
  let V := LinearMap.range (algebraVectorMap (pointedPowerAlgebra E) pointedPowerVacuum)
  change pointedPowerBasis f ∈ V
  induction f using Finsupp.induction with
  | zero => exact ⟨1, by simp [algebraVectorMap, pointedPowerVacuum]⟩
  | @single_add i k f hi _hk ih =>
    have hfi : f i = 0 := Finsupp.notMem_support_iff.mp hi
    have hlocal : ∀ x : PointedLocalHilbert, pointedPowerInsertLinear i f x ∈ V := by
      have hs : Submodule.span ℂ (Set.range (fun p : Fin 2 × Fin 2 =>
          E.entry p.1 p.2 pointedLocalVacuum)) ≤ V.comap (pointedPowerInsertLinear i f) := by
        apply Submodule.span_le.mpr
        rintro _ ⟨p, rfl⟩
        change pointedPowerInsertLinear i f (E.entry p.1 p.2 pointedLocalVacuum) ∈ V
        rw [pointedPowerInsertLinear_operator i f hfi]
        obtain ⟨a, ha⟩ := ih
        refine ⟨(⟨pointedPowerOperator i (E.entry p.1 p.2),
          pointedPowerSite_mem E i p.1 p.2⟩ : Algebra (pointedPowerAlgebra E)) * a, ?_⟩
        change pointedPowerOperator i (E.entry p.1 p.2) (a.val pointedPowerVacuum) = _
        change a.val pointedPowerVacuum = pointedPowerBasis f at ha
        rw [ha]
      rw [hE] at hs
      exact fun x => hs trivial
    have h := hlocal (EuclideanSpace.single k 1)
    rw [pointedPowerInsertLinear_single] at h
    have he : Finsupp.single i k + f = f.update i k := by
      ext j
      by_cases hj : j = i
      · subst j
        simp [hfi]
      · simp [Finsupp.update_apply, hj, Finsupp.single_eq_of_ne hj]
    rwa [he]

/-- A local cyclic vector gives a cyclic vector for the countable product. -/
theorem pointedPowerAlgebra_cyclic
    (E : MatrixUnitSystem (Fin 2) (PointedLocalHilbert →L[ℂ] PointedLocalHilbert))
    (hE : Submodule.span ℂ (Set.range (fun p : Fin 2 × Fin 2 =>
      E.entry p.1 p.2 pointedLocalVacuum)) = ⊤) :
    DenseRange (algebraVectorMap (pointedPowerAlgebra E) pointedPowerVacuum) := by
  change Dense (LinearMap.range
    (algebraVectorMap (pointedPowerAlgebra E) pointedPowerVacuum) : Set PointedPowerHilbert)
  rw [Submodule.dense_iff_topologicalClosure_eq_top]
  apply top_unique
  have hspan : Submodule.span ℂ (Set.range pointedPowerBasis) ≤
      LinearMap.range (algebraVectorMap (pointedPowerAlgebra E) pointedPowerVacuum) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨f, rfl⟩
    exact pointedPowerBasis_mem_orbit E hE f
  have hd := pointedPowerHilbertBasis.dense_span
  rw [show (pointedPowerHilbertBasis : PointedPowerConfiguration → PointedPowerHilbert) =
    pointedPowerBasis from funext pointedPowerHilbertBasis_apply] at hd
  rw [← hd]
  exact Submodule.topologicalClosure_mono hspan

theorem pointedPowerAlgebra_commutant
    (E F : MatrixUnitSystem (Fin 2) (PointedLocalHilbert →L[ℂ] PointedLocalHilbert))
    (hEF : ∀ a b c d, Commute (E.entry a b) (F.entry c d)) :
    pointedPowerAlgebra F ≤ (pointedPowerAlgebra E).commutant := by
  have hentry (i j : ℕ) (a b c d : Fin 2) :
      Commute (pointedPowerOperator i (E.entry a b))
        (pointedPowerOperator j (F.entry c d)) := by
    by_cases hij : i = j
    · subst j
      change pointedPowerOperator i (E.entry a b) * pointedPowerOperator i (F.entry c d) = _
      rw [← map_mul, ← map_mul, (hEF a b c d).eq]
    · exact pointedPowerOperator_commute hij _ _
  apply generatedVonNeumannAlgebra_le_of_le
  apply iSup_le
  intro j
  apply ((pointedPowerSite F j).algebra_le_iff _).mpr
  intro c d
  apply VonNeumannAlgebra.mem_commutant_iff.mpr
  intro a ha
  let b := pointedPowerOperator j (F.entry c d)
  have hstar : star b = pointedPowerOperator j (F.entry d c) := by
    dsimp only [b]
    rw [← map_star, F.star_entry]
  let S : StarSubalgebra ℂ (PointedPowerHilbert →L[ℂ] PointedPowerHilbert) :=
    ⨆ i : ℕ, (pointedPowerSite E i).algebra
  have hs : S ≤ StarSubalgebra.centralizer ℂ {b} := by
    apply iSup_le
    intro i
    apply ((pointedPowerSite E i).algebra_le_iff _).mpr
    intro r s
    rw [StarSubalgebra.mem_centralizer_iff]
    intro z hz
    rcases Set.mem_singleton_iff.mp hz with rfl
    constructor
    · exact (hentry i j r s c d).eq.symm
    · rw [hstar]
      exact (hentry i j r s d c).eq.symm
  have hb : b ∈ Set.centralizer
      (S : Set (PointedPowerHilbert →L[ℂ] PointedPowerHilbert)) := by
    intro x hx
    exact ((StarSubalgebra.mem_centralizer_iff ℂ).mp (hs hx) b
      (Set.mem_singleton b)).1.symm
  change a ∈ (pointedPowerAlgebra E : Set (PointedPowerHilbert →L[ℂ] PointedPowerHilbert)) at ha
  rw [pointedPowerAlgebra, generatedVonNeumannAlgebra_coe] at ha
  exact (ha b hb).symm

/-- The commuting right cyclic vacuum separates the left product algebra. -/
theorem pointedPowerAlgebra_separating {ν : ℝ} (d : PointedLocalMatrixData ν) :
    Function.Injective (algebraVectorMap (pointedPowerAlgebra d.left) pointedPowerVacuum) := by
  have hc := pointedPowerAlgebra_cyclic d.right d.right_spans
  have hle := pointedPowerAlgebra_commutant d.left d.right d.commutes
  intro a b hab
  apply Subtype.ext
  apply ContinuousLinearMap.ext
  intro x
  refine hc.induction_on x (isClosed_eq a.val.continuous b.val.continuous) ?_
  intro r
  have ha := VonNeumannAlgebra.mem_commutant_iff.mp (hle r.property) a.val a.property
  have hb := VonNeumannAlgebra.mem_commutant_iff.mp (hle r.property) b.val b.property
  change a.val (r.val pointedPowerVacuum) = b.val (r.val pointedPowerVacuum)
  rw [← mul_apply_eq_comp, ← mul_apply_eq_comp, ha, hb, mul_apply_eq_comp,
    mul_apply_eq_comp]
  exact congrArg r.val hab

end

end KadisonKastler

end OAI
