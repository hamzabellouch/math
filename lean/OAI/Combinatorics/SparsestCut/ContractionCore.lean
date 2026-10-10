import OAI.Combinatorics.SparsestCut.GradientBudget

namespace OAI

universe u1

open scoped BigOperators Topology NNReal RealInnerProductSpace InnerProductSpace Matrix ContDiff ENNReal
open MeasureTheory ProbabilityTheory Set Filter Matrix

noncomputable section

namespace UniformSparsestCut.ContractionCore
open MeasureTheory Set Filter
open scoped BigOperators RealInnerProductSpace
noncomputable section
variable {m N S : ℕ} {A : Type u1} [Fintype A]
local notation "E" => EuclideanSpace ℝ (Fin (m+1))

def vertex (u : Fin S → Fin N → E) (τ : ℝ) (s : Fin S) (x : E)
    (hx : x∈RoundedCharts.cube 2) (hr : RoundedCharts.regular (u s) τ x) : RoundedCharts.Vertex u τ :=
  ⟨(s,RoundedCharts.integerLabel (u s) τ x),x,hx,hr,rfl⟩

lemma chart_mismatch (u : Fin S → Fin N → E) (hu : ∀ s i, u s i 0≠0)
    {τ lam R : ℝ} (hτ : 0<τ) (hlam : 0<lam) (hlam1 : lam<1) (hn : ∀ s i, ‖u s i‖≤2)
    (F : RoundedCharts.Vertex u τ → A → ℝ) {M : ℝ} (hM : 0≤M) (hbound : ∀ v a, |F v a|≤M)
    (hclose : ∀ s t x (hx : x∈RoundedCharts.cube 2)
      (hs : RoundedCharts.regular (u s) τ x) (ht : RoundedCharts.regular (u t) τ x),
      ∑ a, |F (vertex u τ s x hx hs) a-F (vertex u τ t x hx ht) a|≤R)
    (s t : Fin S) (x : E) (hx : ∀ j, |x j|≤1) :
    (∑ a, ‖fderiv ℝ (ConvolutionBounds.smooth (KernelGeometry.κ lam) (ConcreteCells.function u hu τ F s a) volume) x-
      fderiv ℝ (ConvolutionBounds.smooth (KernelGeometry.κ lam) (ConcreteCells.function u hu τ F t a) volume) x‖)≤
      (m+1:ℕ)*R*KernelGeometry.L lam := by
  apply GradientCalculus.gradient_mismatch (KernelGeometry.compact hlam)
    ((KernelGeometry.smooth lam).of_le (by simp)) _ _
    (fun a => ConcreteCells.function_integrable u hu τ F hM hbound s a)
    (fun a => ConcreteCells.function_integrable u hu τ F hM hbound t a) x
    (KernelGeometry.partial_integrable hlam) (KernelGeometry.partial_integral hlam)
  filter_upwards [ConcreteCells.regular_sub (u s) (hu s) τ x,
      ConcreteCells.regular_sub (u t) (hu t) τ x] with z hzs hzt
  rintro ⟨j,hj⟩
  have hmem : x-z∈RoundedCharts.cube 2 := KernelGeometry.derivative_shifted_mem hlam hlam1 x hx hj
  simp_rw [ConcreteCells.function_eq u hu hτ hn F s (x-z) hmem hzs,
    ConcreteCells.function_eq u hu hτ hn F t (x-z) hmem hzt]
  exact hclose s t (x-z) hmem hzs hzt

lemma smoothing_error (u : Fin S → Fin N → E) (hu : ∀ s i, u s i 0≠0)
    {τ lam G R : ℝ} (hτ : 0<τ) (hlam : 0<lam) (hlam1 : lam<1) (hn : ∀ s i, ‖u s i‖≤2) (hG : 0≤G)
    (F : RoundedCharts.Vertex u τ → A → ℝ) {M : ℝ} (hM : 0≤M) (hbound : ∀ v a, |F v a|≤M)
    (hmacro : ∀ s x y (hx : x∈RoundedCharts.cube 2) (hy : y∈RoundedCharts.cube 2)
      (hs : RoundedCharts.regular (u s) τ x) (ht : RoundedCharts.regular (u s) τ y),
      ∑ a, |F (vertex u τ s x hx hs) a-F (vertex u τ s y hy ht) a|≤G*‖x-y‖+R)
    (s : Fin S) (x : E) (hx : ∀ j, |x j|≤1) (hr : RoundedCharts.regular (u s) τ x) :
    (∑ a, |ConvolutionBounds.smooth (KernelGeometry.κ lam) (ConcreteCells.function u hu τ F s a) volume x-
      ConcreteCells.function u hu τ F s a x|)≤G*(lam*Real.sqrt (m+1:ℕ))+R := by
  apply ConvolutionBounds.error (KernelGeometry.compact hlam) (KernelGeometry.smooth lam).continuous
    (KernelGeometry.integrable hlam) (KernelGeometry.nonneg hlam.le) (KernelGeometry.integral_one hlam)
    _ (fun a => ConcreteCells.function_integrable u hu τ F hM hbound s a) x
  filter_upwards [ConcreteCells.regular_sub (u s) (hu s) τ x] with z hzr hz
  have hxU : x∈RoundedCharts.cube 2 := fun j => (hx j).trans_lt (by norm_num)
  have hmem : x-z∈RoundedCharts.cube 2 := KernelGeometry.shifted_mem hlam hlam1 x hx (subset_closure hz)
  simp_rw [ConcreteCells.function_eq u hu hτ hn F s (x-z) hmem hzr,
    ConcreteCells.function_eq u hu hτ hn F s x hxU hr]
  have h := hmacro s (x-z) x hmem hxU hzr hr
  have hnz : ‖x-z-x‖=‖z‖ := by rw [sub_sub_cancel_left,norm_neg]
  rw [hnz] at h
  exact h.trans (add_le_add (mul_le_mul_of_nonneg_left (KernelGeometry.norm_bound hlam hz) hG) le_rfl)

lemma gradient_bound (u : Fin S → Fin N → E) (hu : ∀ s i, u s i 0≠0)
    (hnp : ∀ s i j, i≠j → ∀ t : ℝ, u s i≠t • u s j) (hn : ∀ s i, ‖u s i‖≤2)
    {τ lam δ R J : ℝ} (hτ : 0<τ) (hlam : 0<lam) (hlam1 : lam<1) (hδ : 0≤δ) (hJ : 0≤J)
    (F : RoundedCharts.Vertex u τ → A → ℝ) {M : ℝ} (hM : 0≤M) (hbound : ∀ v a, |F v a|≤M)
    (hclose : ∀ s t x (hx : x∈RoundedCharts.cube 2)
      (hs : RoundedCharts.regular (u s) τ x) (ht : RoundedCharts.regular (u t) τ x),
      ∑ a, |F (vertex u τ s x hx hs) a-F (vertex u τ t x hx ht) a|≤R)
    (hjump : ∀ (vp vm : RoundedCharts.Vertex u τ) (i : Fin N), vp.val.1=vm.val.1 →
      vp.val.2 i=vm.val.2 i+1 → (∀ j, j≠i → vp.val.2 j=vm.val.2 j) → ∑ a, |F vp a-F vm a|≤J)
    (hsmall : ∀ s i, τ/|u s i 0| *KernelGeometry.L lam≤1)
    (hgood : ∀ D : StrongDual ℝ E, ∃ good : Finset (Fin S), (S:ℝ)/2≤good.card ∧
      ∀ s∈good, ∀ i, |D (u s i)|≤δ*‖D‖)
    (s0 : Fin S) (x : E) (hx : ∀ j, |x j|≤1) :
    (∑ a, ‖fderiv ℝ (ConvolutionBounds.smooth (KernelGeometry.κ lam) (ConcreteCells.function u hu τ F s0 a) volume) x‖)≤
      2*(δ*((N:ℝ)*(2*J/τ))+(m+1:ℕ)*R*KernelGeometry.L lam) := by
  classical
  have hex (s : Fin S) := ConcreteCells.normal_coefficients u hu hnp hn hτ hlam hlam1 F hM hJ hbound hjump hsmall s x hx
  choose β hβd hβ using hex
  let D (s : Fin S) (a : A) : StrongDual ℝ E :=
    fderiv ℝ (ConvolutionBounds.smooth (KernelGeometry.κ lam) (ConcreteCells.function u hu τ F s a) volume) x
  apply GradientCalculus.gradient_budget u β D (D s0) hδ
  · intro s a
    exact (hβd s a).fderiv
  · intro a
    simpa only [Fintype.card_fin] using hgood (D s0 a)
  · intro s
    calc
      _ ≤ ∑ _i : Fin N, 2*J/τ := Finset.sum_le_sum (fun i _ => hβ s i)
      _ = _ := by simp
  · intro s
    exact chart_mismatch u hu hτ hlam hlam1 hn F hM hbound hclose s s0 x hx
  · simpa only [Fintype.card_fin] using Nat.zero_lt_of_lt s0.isLt

end
end UniformSparsestCut.ContractionCore

end

end OAI
