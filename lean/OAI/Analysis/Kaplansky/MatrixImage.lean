import OAI.Analysis.Kaplansky.BundlePolynomials
import OAI.Analysis.Kaplansky.TestAlgebra
import OAI.Geometry.BundleTests.Retained
import OAI.Geometry.ComplexBundle.Orthonormal
import Mathlib.LinearAlgebra.LinearIndependent.Basic

namespace OAI

noncomputable section

/-! Matrix restriction, trivial input bundles, and matrix images. -/

open Bundle Topology
namespace Kaplansky
open ComplexGrassmann
variable {ι : Type*} {K : ι → ℕ} {a b : LineStage K}

def stageModelBasis (a : LineStage K) :
    Module.Basis (Fin (Fintype.card a.Slot)) ℂ a.Model :=
  ((Pi.basisFun ℂ a.Slot).map (EuclideanSpace.equiv a.Slot ℂ).symm.toLinearEquiv).reindex
    (Fintype.equivFin a.Slot)

/-- Columns of a continuous injective map from a genuinely trivial stage
are a continuous independent frame of its image. -/
def trivialMapFrame (L : ContinuousStageMap a b) (ha : ∀ s, a.label s=none)
    (y₀ : ProjectiveProduct K) (hinj : ∀ y, Function.Injective (L.map y)) :
    ContinuousIndependentStageFrame b (Fintype.card a.Slot) where
  vector y i := L.map y (show a.Fiber y from stageModelBasis a i)
  continuous_vector i := L.continuous_map.comp
    (lineStageTrivial_section a ha y₀ (stageModelBasis a i))
  independent y := (stageModelBasis a).linearIndependent.map' (L.map y)
    (LinearMap.ker_eq_bot.mpr (hinj y))

private theorem span_basis_image {J E F : Type*} [AddCommGroup E] [Module ℂ E]
    [AddCommGroup F] [Module ℂ F] (b : Module.Basis J ℂ E) (L : E →ₗ[ℂ] F) :
    Submodule.span ℂ (Set.range (fun i => L (b i))) = LinearMap.range L := by
  have hs := congrArg (fun S : Submodule ℂ E => S.map L) b.span_eq
  simpa only [Submodule.map_span, ← Set.range_comp, Submodule.map_top, Function.comp_def] using hs

theorem trivialMapFrame_span (L : ContinuousStageMap a b) (ha : ∀ s, a.label s=none)
    (y₀ : ProjectiveProduct K) (hinj : ∀ y, Function.Injective (L.map y))
    (y : ProjectiveProduct K) :
    Submodule.span ℂ (Set.range ((trivialMapFrame L ha y₀ hinj).normalize.vector y)) =
      LinearMap.range (L.map y) := by
  rw [ContinuousIndependentStageFrame.normalize_span]
  exact span_basis_image (stageModelBasis a)
    (show a.Model →ₗ[ℂ] b.Model from L.map y)

def trivialMapImageHomeomorph (L : ContinuousStageMap a b) (ha : ∀ s, a.label s=none)
    (y₀ : ProjectiveProduct K) (hinj : ∀ y, Function.Injective (L.map y)) :
    ProjectiveProduct K × EuclideanSpace ℂ (Fin (Fintype.card a.Slot)) ≃ₜ
      {z : TotalSpace b.Model b.Fiber // z.2 ∈ LinearMap.range (L.map z.proj)} := by
  let f := (trivialMapFrame L ha y₀ hinj).normalize
  exact f.imageTotalHomeomorph.trans (Homeomorph.setCongr (by
    ext z
    change z.2 ∈ Submodule.span ℂ (Set.range ((trivialMapFrame L ha y₀ hinj).normalize.vector z.proj)) ↔ _
    rw [trivialMapFrame_span L ha y₀ hinj z.proj]
    rfl))

theorem norm_lower_bound_injective {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] (L : E →ₗ[ℂ] F) {c : ℝ}
    (hc : 0<c) (hL : ∀ v, c*‖v‖ ≤ ‖L v‖) : Function.Injective L := by
  intro v w h
  have he : L (v-w)=0 := by simp [h]
  have hn := hL (v-w)
  rw [he,norm_zero] at hn
  have hz : ‖v-w‖=0 := by nlinarith [norm_nonneg (v-w)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hz)

/-- All matrix input coordinates are actual copies of E₀. -/
theorem actualInput_label_none (m n R : ℕ)
    (s : (towerInputStage (testSequenceStage m R) n).Slot) :
    (towerInputStage (testSequenceStage m R) n).label s=none := by
  revert s
  unfold towerInputStage
  rw [testSequenceStage_prefix (Nat.zero_le R)]
  intro s
  obtain ⟨col,⟨j,k⟩⟩ := s
  have hj : j=0 := Fin.eq_zero j
  subst j
  rfl

def actualInputTrivialization (m n R : ℕ) :
    TotalSpace (towerInputStage (testSequenceStage m R) n).Model
      (towerInputStage (testSequenceStage m R) n).Fiber ≃ₜ
    SmoothTestBase m R × (towerInputStage (testSequenceStage m R) n).Model :=
  lineStageTrivialTotalHomeomorph _ (actualInput_label_none m n R)
    (testBaseProjectiveHomeomorph m R (bundleTestBasePoint m R))

theorem actualInput_finrank (m n R : ℕ) (y : SmoothTestBase m R) :
    Module.finrank ℂ ((towerInputStage (testSequenceStage m R) n).Fiber y)=n*testRank m R 0 := by
  change Module.finrank ℂ (EuclideanSpace ℂ (towerInputStage (testSequenceStage m R) n).Slot)=_
  rw [finrank_euclideanSpace]
  unfold towerInputStage
  change Fintype.card (Σ _ : Fin n, (testSequenceStage m R 0).Slot)=_
  rw [Fintype.card_sigma]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul]
  congr 1
  rw [testSequenceStage_prefix (Nat.zero_le R)]
  exact testBundleSlot_card (Nat.zero_le R)

open scoped BigOperators

def actualRetainedUnitary (m R : ℕ) :
    UnitaryBundleEquiv (towerRetainedStage (testSequenceStage m R) m R).Model
      (EuclideanSpace ℂ (RetainedSlot m R))
      (towerRetainedStage (testSequenceStage m R) m R).Fiber (RetainedBundle m R) := by
  have he : (fun j : Fin (R+1) => testSequenceStage m R j.val) =
      (fun j : Fin (R+1) => testLineStage m R j.val (Nat.le_of_lt_succ j.isLt)) := by
    funext j
    exact testSequenceStage_prefix (Nat.le_of_lt_succ j.isLt)
  unfold towerRetainedStage
  rw [he]
  let e : (Σ _ : Fin m, Σ j : Fin (R+1), TestBundleSlot m R j.val) ≃ RetainedSlot m R :=
    { toFun := fun s => (s.1,s.2)
      invFun := fun s => ⟨s.1,s.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact lineSumRelabelUnitary (testProjectiveDimension m R) _ (retainedLabel m R) e
    (fun _ => rfl)

/-- The actual finite rectangular matrix map into G, constructed from all
its polynomial terms. This definition assumes no obstruction or lower bound. -/
def actualMatrixRestriction {m n R : ℕ} (hm : 0<m) {T : Type*}
    (s : Finset T) (t : T → BoundedMatrixTerm m n R) (y : SmoothTestBase m R) :
    (towerInputStage (testSequenceStage m R) n).Fiber y →ₗ[ℂ] RetainedBundle m R y :=
  ((actualRetainedUnitary m R).fiber y).toLinearMap.comp
    ((bundleMatrixPolynomial (testSequenceStep (R := R) hm) s t).map y)

theorem actualMatrixRestriction_continuous {m n R : ℕ} (hm : 0<m) {T : Type*}
    (s : Finset T) (t : T → BoundedMatrixTerm m n R) :
    Continuous (fun z : TotalSpace (towerInputStage (testSequenceStage m R) n).Model
        (towerInputStage (testSequenceStage m R) n).Fiber =>
      TotalSpace.mk' (EuclideanSpace ℂ (RetainedSlot m R)) z.proj
        (actualMatrixRestriction hm s t z.proj z.2)) :=
  (actualRetainedUnitary m R).continuous_forward.comp
    (bundleMatrixPolynomial_continuous (testSequenceStep (R := R) hm) s t)

def retainedLineStage (m R : ℕ) : LineStage (testProjectiveDimension m R) :=
  ⟨RetainedSlot m R,inferInstance,retainedLabel m R⟩

def actualMatrixStageMap {m n R : ℕ} (hm : 0<m) {T : Type*}
    (s : Finset T) (t : T → BoundedMatrixTerm m n R) :
    ContinuousStageMap (towerInputStage (testSequenceStage m R) n) (retainedLineStage m R) :=
  ⟨actualMatrixRestriction hm s t,actualMatrixRestriction_continuous hm s t⟩

theorem actualMatrixRestriction_lower_bound {m n R : ℕ} (hm : 0<m) {T : Type*}
    (s : Finset T) (t : T → BoundedMatrixTerm m n R) (y : SmoothTestBase m R) (c : ℝ)
    (h : ∀ v : MatrixTowerHilbert (testSequenceStage m R) n y,
      c*‖v‖ ≤ ‖matrixPolynomialAction (testSequenceStep (R := R) hm) s t y v‖)
    (v : (towerInputStage (testSequenceStage m R) n).Fiber y) :
    c*‖v‖ ≤ ‖actualMatrixRestriction hm s t y v‖ := by
  change c*‖v‖ ≤ ‖(actualRetainedUnitary m R).fiber y
    ((bundleMatrixPolynomial (testSequenceStep (R := R) hm) s t).map y v)‖
  rw [LinearIsometryEquiv.norm_map]
  exact bundleMatrixPolynomial_lower_bound _ s t y c h v

def actualMatrixImageHomeomorph {m n R : ℕ} (hm : 0<m) {T : Type*}
    (s : Finset T) (t : T → BoundedMatrixTerm m n R) {c : ℝ} (hc : 0<c)
    (h : ∀ y (v : MatrixTowerHilbert (testSequenceStage m R) n y),
      c*‖v‖ ≤ ‖matrixPolynomialAction (testSequenceStep (R := R) hm) s t y v‖) :
    SmoothTestBase m R × EuclideanSpace ℂ
        (Fin (Fintype.card (towerInputStage (testSequenceStage m R) n).Slot)) ≃ₜ
      {z : TotalSpace (EuclideanSpace ℂ (RetainedSlot m R)) (RetainedBundle m R) //
        z.2 ∈ LinearMap.range (actualMatrixRestriction hm s t z.proj)} :=
  trivialMapImageHomeomorph (actualMatrixStageMap hm s t) (actualInput_label_none m n R)
    (testBaseProjectiveHomeomorph m R (bundleTestBasePoint m R))
    (fun y => norm_lower_bound_injective _ hc (actualMatrixRestriction_lower_bound hm s t y c (h y)))

theorem actualMatrixImage_finrank {m n R : ℕ} (hm : 0<m) {T : Type*}
    (s : Finset T) (t : T → BoundedMatrixTerm m n R) {c : ℝ} (hc : 0<c)
    (h : ∀ y (v : MatrixTowerHilbert (testSequenceStage m R) n y),
      c*‖v‖ ≤ ‖matrixPolynomialAction (testSequenceStep (R := R) hm) s t y v‖)
    (y : SmoothTestBase m R) :
    Module.finrank ℂ (LinearMap.range (actualMatrixRestriction hm s t y))=n*testRank m R 0 := by
  have hi : Function.Injective (actualMatrixRestriction hm s t y) :=
    norm_lower_bound_injective _ hc (actualMatrixRestriction_lower_bound hm s t y c (h y))
  rw [LinearMap.finrank_range_of_inj hi]
  exact actualInput_finrank m n R y

end Kaplansky

end

end OAI
