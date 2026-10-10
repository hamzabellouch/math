import OAI.Geometry.Perimeter.Regularity.EllipticHilbert
import OAI.Geometry.Perimeter.Regularity.GradientContDiff

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff InnerProductSpace
namespace RPISingularHarnack
variable {n : ℕ}

abbrev VectorL2 (n : ℕ) := Lp (Euc n) 2 (volume : Measure (Euc n))

def SmoothLocalTest (U : Set (Euc n)) :=
  {φ : Euc n → ℝ // ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ U}

def testGradientLp {U : Set (Euc n)} (φ : SmoothLocalTest U) : VectorL2 n :=
  ((gradient_contDiff φ.property.1).continuous.memLp_of_hasCompactSupport
    (gradient_hasCompactSupport φ.property.2.1)).toLp (gradient φ.val)

theorem testGradientLp_ae {U : Set (Euc n)} (φ : SmoothLocalTest U) :
    (testGradientLp φ : Euc n → Euc n)=ᵐ[volume] gradient φ.val :=
  MemLp.coeFn_toLp _

def testGradientSpace (U : Set (Euc n)) : Submodule ℝ (VectorL2 n) :=
  (Submodule.span ℝ (Set.range (testGradientLp (U := U)))).topologicalClosure

instance testGradientSpace_complete (U : Set (Euc n)) : CompleteSpace (testGradientSpace U) :=
  (Submodule.isClosed_topologicalClosure _).completeSpace_coe

theorem testGradient_mem {U : Set (Euc n)} (φ : SmoothLocalTest U) :
    testGradientLp φ∈testGradientSpace U :=
  Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨φ,rfl⟩)

theorem inner_zero_on_closed_span {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (s : Set H) {u : H} (h : ∀ w∈s, inner ℝ u w=0) :
    ∀ w∈(Submodule.span ℝ s).topologicalClosure, inner ℝ u w=0 := by
  have hs : Submodule.span ℝ s ≤ (innerSL ℝ u).ker := by
    apply Submodule.span_le.mpr
    exact h
  exact (Submodule.span ℝ s).topologicalClosure_minimal hs (innerSL ℝ u).isClosed_ker

theorem testGradient_pairing_ext {U : Set (Euc n)} {u e : VectorL2 n}
    (h : ∀ φ : SmoothLocalTest U, inner ℝ u (testGradientLp φ)=inner ℝ e (testGradientLp φ)) :
    ∀ w∈testGradientSpace U, inner ℝ u w=inner ℝ e w := by
  have hh := inner_zero_on_closed_span (Set.range (testGradientLp (U := U))) (u := u-e)
    (by rintro _ ⟨φ,rfl⟩; rw [inner_sub_left,h φ,sub_self])
  intro w hw
  have hz := hh w hw
  simpa only [inner_sub_left,sub_eq_zero] using hz

theorem testGradient_inner {U : Set (Euc n)} (u : VectorL2 n) (φ : SmoothLocalTest U) :
    inner ℝ u (testGradientLp φ)=∫ x, inner ℝ (u x) (gradient φ.val x) := by
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [testGradientLp_ae φ] with x hx
  rw [hx]

theorem testGradient_integrable_pairing (u : VectorL2 n) {U : Set (Euc n)}
    (φ : SmoothLocalTest U) : Integrable (fun x ↦ inner ℝ (u x) (gradient φ.val x)) volume := by
  apply (MeasureTheory.L2.integrable_inner (𝕜 := ℝ) u (testGradientLp φ)).congr
  filter_upwards [testGradientLp_ae φ] with x hx
  rw [hx]

def DivFreeLpOn (u : VectorL2 n) (U : Set (Euc n)) : Prop :=
  ∀ φ : SmoothLocalTest U, (∫ x, inner ℝ (u x) (gradient φ.val x))=0

theorem orthogonal_testGradient_divFree {U : Set (Euc n)} {u : VectorL2 n}
    (hu : u∈(testGradientSpace U)ᗮ) : DivFreeLpOn u U := by
  intro φ
  rw [←testGradient_inner u φ]
  exact Submodule.inner_left_of_mem_orthogonal (testGradient_mem φ) hu

theorem weak_harmonic_gradient_comparison {U : Set (Euc n)} {u e : VectorL2 n}
    (h : ∀ φ : SmoothLocalTest U, (∫ x, inner ℝ (u x) (gradient φ.val x))=
      ∫ x, inner ℝ (e x) (gradient φ.val x)) :
    ∃ g : VectorL2 n, DivFreeLpOn g U ∧ u-g∈testGradientSpace U ∧ ‖u-g‖≤‖e‖ := by
  obtain ⟨g,hg,hug,he⟩ := harmonic_projection_exists (testGradientSpace U)
    (testGradient_pairing_ext (fun φ ↦ by simpa only [testGradient_inner] using h φ))
  exact ⟨g,orthogonal_testGradient_divFree hg,hug,he⟩

end RPISingularHarnack

end

end OAI
