import Mathlib
import OAI.Geometry.TamingCompatibility.Elliptic.LocalMatrixGarding

namespace OAI


noncomputable section
open scoped ContDiff SchwartzMap
namespace TamingCompatibility.SmoothMetric
open MetricModel LocalUnitaryFrame
variable {E D : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup D] [NormedSpace ℝ D]

lemma exists_unitaryFrame_near (g : D → Metric E) (J : D → E →L[ℝ] E)
    (hdim : Module.finrank ℝ E = 4) {U : Set D} (hU : IsOpen U)
    (hg : ContDiffOn ℝ ∞ (fun x => (g x).bilinear) U) (hJ : ContDiffOn ℝ ∞ J U)
    (hJs : ∀ x ∈ U, ∀ u, J x (J x u) = -u)
    (hgJ : ∀ x ∈ U, ∀ u v, (g x).bilinear (J x u) (J x v) = (g x).bilinear u v)
    {x : D} (hx : x ∈ U) :
    ∃ W : Set D, IsOpen W ∧ x ∈ W ∧ W ⊆ U ∧
      ∃ b : Fin 4 → D → E, (∀ i, ContDiffOn ℝ ∞ (b i) W) ∧
        (∀ y ∈ W, ∀ i j, (g y).bilinear (b i y) (b j y) = if i = j then 1 else 0) ∧
        (∀ y ∈ W, J y (b 0 y) = b 1 y ∧ J y (b 1 y) = -b 0 y ∧
          J y (b 2 y) = b 3 y ∧ J y (b 3 y) = -b 2 y) ∧
        ∃ B : Module.Basis (Fin 4) ℝ E, ∀ i, b i x = B i := by
  obtain ⟨B,hB,h0,h1,h2,h3⟩ := VolumeNormalization.exists_metric_unitary_basis (g x) (J x)
    (hJs x hx) (hgJ x hx) hdim
  have hu : (g x).bilinear (B 0) (B 0) = 1 := by simpa using hB 0 0
  have hw : (g x).bilinear (B 2) (B 2) = 1 := by simpa using hB 2 2
  have huw : (g x).bilinear (B 0) (B 2) = 0 := by simpa using hB 0 2
  have hjuw : (g x).bilinear (J x (B 0)) (B 2) = 0 := by rw [h0]; simpa using hB 1 2
  obtain ⟨W,hW,hxW,hWU,u,w,hus,hws,hux,hwx,hgram⟩ :=
    exists_smooth_frame_near (B := fun y => (g y).bilinear) x hU hx hg hJ
      (fun y _ => (g y).symm) hJs hgJ (B 0) (B 2) hu hw huw hjuw
  refine ⟨W,hW,hxW,hWU,(fun i y => frame (J y) (u y) (w y) i),?_,hgram,?_,B,?_⟩
  · intro i
    fin_cases i
    · exact hus
    · exact (hJ.mono hWU).clm_apply hus
    · exact hws
    · exact (hJ.mono hWU).clm_apply hws
  · intro y hy
    exact ⟨rfl,hJs y (hWU hy) _,rfl,hJs y (hWU hy) _⟩
  · intro i
    fin_cases i <;> simp [frame,hux,hwx,h0,h2]
end TamingCompatibility.SmoothMetric

namespace TamingCompatibility.LocalMatrixOperator
open EuclideanEnergy MetricModel MetricForms MetricHodge ExteriorForms AntiInvariantFrame
open MeasureTheory

theorem exists_unitary_local_garding {U : Set V} (hU : IsOpen U) {x₀ : V} (hx₀ : x₀ ∈ U)
    (g : V → Metric V) (J : V → V →L[ℝ] V) (F : V → MetricForms.Form V 2)
    (hg : ContDiffOn ℝ ∞ (fun x => (g x).bilinear) U) (hJ : ContDiffOn ℝ ∞ J U)
    (hJs : ∀ x ∈ U, ∀ u, J x (J x u) = -u)
    (hgJ : ∀ x ∈ U, ∀ u v, (g x).bilinear (J x u) (J x v) = (g x).bilinear u v)
    (hFs : ContDiffOn ℝ ∞ F U)
    (hF : ∀ x ∈ U, ∀ u v, F x ![u,v] = (g x).bilinear (J x u) v) :
    ∃ r K C : ℝ, 0 < r ∧ 0 < K ∧ 0 < C ∧ Metric.closedBall x₀ (2*r) ⊆ U ∧
      ∃ W : Set V, IsOpen W ∧ Metric.closedBall x₀ (2*r) ⊆ W ∧ W ⊆ U ∧
        ∃ b : Fin 4 → V → V,
          (∀ i, ContDiffOn ℝ ∞ (b i) W) ∧
          (∀ x ∈ W, ∀ i j, (g x).bilinear (b i x) (b j x) = if i = j then 1 else 0) ∧
          (∀ x ∈ W, J x (b 0 x) = b 1 x ∧ J x (b 1 x) = -b 0 x ∧
            J x (b 2 x) = b 3 x ∧ J x (b 3 x) = -b 2 x) ∧
          ∀ A B : S, tsupport A ⊆ Metric.closedBall x₀ r →
            tsupport B ⊆ Metric.closedBall x₀ r →
            (∫ x, gradientEnergy A B x) ≤ K * (∫ x,
              ‖oneVector (starThree (g x) (F x)
                (extDeriv (fun y => A y • realPart (g y) (fun i => b i y) +
                  B y • imagPart (g y) (fun i => b i y)) x))‖^2) +
                C * (∫ x, (A x)^2+(B x)^2) := by
  obtain ⟨W,hW,hxW,hWU,b,hbs,hb,hJb,B₀,hB₀⟩ :=
    SmoothMetric.exists_unitaryFrame_near g J (by simp [V]) hU hg hJ hJs hgJ hx₀
  have hψ := realPart_smooth (hg.mono hWU) hbs
  have hχ := imagPart_smooth (hg.mono hWU) hbs
  have he : (fun i => b i x₀) = B₀ := funext hB₀
  obtain ⟨h0,h1,h2,h3⟩ := hJb x₀ hxW
  have hstar := SmoothHodge.starThreeCLM_contDiffOn g J (by simp [V]) hW
    (hg.mono hWU) (hJ.mono hWU) (fun x hx => hJs x (hWU hx))
    (fun x hx => hgJ x (hWU hx)) (hFs.mono hWU)
  obtain ⟨r,K,C,hr,hK,hC,hrW,hgard⟩ := geometric_local_garding hW hxW g F
    (fun x => realPart (g x) (fun i => b i x))
    (fun x => imagPart (g x) (fun i => b i x)) hstar hψ hχ B₀
    (fun i j => by simpa only [hB₀] using hb x₀ hxW i j) (J x₀)
    (by simpa only [hB₀] using h0) (by simpa only [hB₀] using h1)
    (by simpa only [hB₀] using h2) (by simpa only [hB₀] using h3)
    (hF x₀ hx₀) (by rw [he]) (by rw [he])
  exact ⟨r,K,C,hr,hK,hC,hrW.trans hWU,W,hW,hrW,hWU,b,hbs,hb,hJb,hgard⟩
end TamingCompatibility.LocalMatrixOperator

end

end OAI
