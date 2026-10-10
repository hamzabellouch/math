import Mathlib
import OAI.Geometry.TamingCompatibility.DifferentialForms.FormEquiv
import OAI.Geometry.TamingCompatibility.Charts.UnitaryFrames

namespace OAI

noncomputable section
open scoped Manifold ContDiff
open scoped Manifold ContDiff Topology
open Filter Set
attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid
open scoped Manifold ContDiff Topology
open Bundle Filter Set
open Set
open Bundle Set Filter
open scoped Topology
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology
open scoped BigOperators
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open ContinuousAlternatingMap
namespace TamingCompatibility.SmoothMetric
open RealInnerProductSpace MetricModel MetricForms FormSmooth LocalUnitaryFrame
open scoped ContDiff BigOperators
variable {E D : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup D] [NormedSpace ℝ D]

lemma exists_unitary_vectors (g : Metric E) (J : E →L[ℝ] E)
    (hJ : ∀ u, J (J u) = -u) (hBJ : ∀ u v, g.bilinear (J u) (J v) = g.bilinear u v)
    (hdim : Module.finrank ℝ E = 4) :
    ∃ u w : E, g.bilinear u u = 1 ∧ g.bilinear w w = 1 ∧
      g.bilinear u w = 0 ∧ g.bilinear (J u) w = 0 := by
  let j := MetricModel.isometry g J hBJ
  have hj : ∀ u : MetricModel.Model g, j (j u) = -u := hJ
  obtain ⟨b,h0,h1,h2,h3⟩ := UnitaryBasis.exists_unitary_basis j hj ((finrank_model g).trans hdim)
  refine ⟨equiv g (b 0), equiv g (b 2), ?_, ?_, ?_, ?_⟩
  · exact (orthonormal_iff_ite.mp b.orthonormal 0 0).trans (ite_eq_left rfl)
  · exact (orthonormal_iff_ite.mp b.orthonormal 2 2).trans (ite_eq_left rfl)
  · exact (orthonormal_iff_ite.mp b.orthonormal 0 2).trans (ite_eq_right (by decide))
  · change ⟪j (b 0), b 2⟫ = 0
    rw [h0]
    exact (orthonormal_iff_ite.mp b.orthonormal 1 2).trans (ite_eq_right (by decide))

lemma exists_orthonormalFrame_near (g : D → Metric E) (J : D → E →L[ℝ] E)
    (hdim : Module.finrank ℝ E = 4) {U : Set D} (hU : IsOpen U)
    (hg : ContDiffOn ℝ ∞ (fun x => (g x).bilinear) U) (hJ : ContDiffOn ℝ ∞ J U)
    (hJs : ∀ x ∈ U, ∀ u, J x (J x u) = -u)
    (hgJ : ∀ x ∈ U, ∀ u v, (g x).bilinear (J x u) (J x v) = (g x).bilinear u v)
    {x : D} (hx : x ∈ U) :
    ∃ V : Set D, IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧
      ∃ b : Fin 4 → D → E, (∀ i, ContDiffOn ℝ ∞ (b i) V) ∧
        ∀ y ∈ V, ∀ i j, (g y).bilinear (b i y) (b j y) = if i = j then 1 else 0 := by
  obtain ⟨u₀,w₀,hu,hw,huw,hjuw⟩ := exists_unitary_vectors (g x) (J x) (hJs x hx) (hgJ x hx) hdim
  obtain ⟨V,hV,hxV,hVU,u,w,hus,hws,_,_,hgram⟩ :=
    exists_smooth_frame_near (B := fun y => (g y).bilinear) x hU hx hg hJ
      (fun y _ => (g y).symm) hJs hgJ u₀ w₀ hu hw huw hjuw
  refine ⟨V,hV,hxV,hVU,(fun i y => frame (J y) (u y) (w y) i),?_,hgram⟩
  intro i
  fin_cases i
  · exact hus
  · exact (hJ.mono hVU).clm_apply hus
  · exact hws
  · exact (hJ.mono hVU).clm_apply hws

lemma contDiffOn_pairing_two_frame (g : D → Metric E) (hdim : Module.finrank ℝ E = 4)
    {U : Set D} (b : Fin 4 → D → E) (hbs : ∀ i, ContDiffOn ℝ ∞ (b i) U)
    (hb : ∀ x ∈ U, ∀ i j, (g x).bilinear (b i x) (b j x) = if i = j then 1 else 0)
    {α β : D → Form E 2} (hα : ContDiffOn ℝ ∞ α U) (hβ : ContDiffOn ℝ ∞ β U) :
    ContDiffOn ℝ ∞ (fun x => pairing (g x) (α x) (β x)) U := by
  have hs : ContDiffOn ℝ ∞ (fun x => ∑ i : Fin 6,
      α x ![b (FormMetric.pairLeft i) x,b (FormMetric.pairRight i) x] *
      β x ![b (FormMetric.pairLeft i) x,b (FormMetric.pairRight i) x]) U := by
    apply ContDiffOn.sum
    intro i hi
    exact (contDiffOn_apply_two hα (hbs _) (hbs _)).mul
      (contDiffOn_apply_two hβ (hbs _) (hbs _))
  exact hs.congr (fun x hx => pairing_two_eq_sum (g x) hdim (fun i => b i x) (hb x hx) _ _)

lemma contDiffOn_pairing_three_frame (g : D → Metric E) (hdim : Module.finrank ℝ E = 4)
    {U : Set D} (b : Fin 4 → D → E) (hbs : ∀ i, ContDiffOn ℝ ∞ (b i) U)
    (hb : ∀ x ∈ U, ∀ i j, (g x).bilinear (b i x) (b j x) = if i = j then 1 else 0)
    {α β : D → Form E 3} (hα : ContDiffOn ℝ ∞ α U) (hβ : ContDiffOn ℝ ∞ β U) :
    ContDiffOn ℝ ∞ (fun x => pairing (g x) (α x) (β x)) U := by
  have hs : ContDiffOn ℝ ∞ (fun x => ∑ i : Fin 4,
      α x (fun j => b (FormMetric.tripleIndices i j) x) *
      β x (fun j => b (FormMetric.tripleIndices i j) x)) U := by
    apply ContDiffOn.sum
    intro i hi
    exact (contDiffOn_apply hα (fun j => hbs _)).mul
      (contDiffOn_apply hβ (fun j => hbs _))
  exact hs.congr (fun x hx => pairing_three_eq_sum (g x) hdim (fun i => b i x) (hb x hx) _ _)

lemma contDiffOn_pairing_two (g : D → Metric E) (J : D → E →L[ℝ] E)
    (hdim : Module.finrank ℝ E = 4) {U : Set D} (hU : IsOpen U)
    (hg : ContDiffOn ℝ ∞ (fun x => (g x).bilinear) U) (hJ : ContDiffOn ℝ ∞ J U)
    (hJs : ∀ x ∈ U, ∀ u, J x (J x u) = -u)
    (hgJ : ∀ x ∈ U, ∀ u v, (g x).bilinear (J x u) (J x v) = (g x).bilinear u v)
    {α β : D → Form E 2} (hα : ContDiffOn ℝ ∞ α U) (hβ : ContDiffOn ℝ ∞ β U) :
    ContDiffOn ℝ ∞ (fun x => pairing (g x) (α x) (β x)) U := by
  apply contDiffOn_of_locally_contDiffOn
  intro x hx
  obtain ⟨V,hV,hxV,hVU,b,hbs,hb⟩ := exists_orthonormalFrame_near g J hdim hU hg hJ hJs hgJ hx
  exact ⟨V,hV,hxV,(contDiffOn_pairing_two_frame g hdim b hbs hb
    (hα.mono hVU) (hβ.mono hVU)).mono Set.inter_subset_right⟩

lemma contDiffOn_pairing_three (g : D → Metric E) (J : D → E →L[ℝ] E)
    (hdim : Module.finrank ℝ E = 4) {U : Set D} (hU : IsOpen U)
    (hg : ContDiffOn ℝ ∞ (fun x => (g x).bilinear) U) (hJ : ContDiffOn ℝ ∞ J U)
    (hJs : ∀ x ∈ U, ∀ u, J x (J x u) = -u)
    (hgJ : ∀ x ∈ U, ∀ u v, (g x).bilinear (J x u) (J x v) = (g x).bilinear u v)
    {α β : D → Form E 3} (hα : ContDiffOn ℝ ∞ α U) (hβ : ContDiffOn ℝ ∞ β U) :
    ContDiffOn ℝ ∞ (fun x => pairing (g x) (α x) (β x)) U := by
  apply contDiffOn_of_locally_contDiffOn
  intro x hx
  obtain ⟨V,hV,hxV,hVU,b,hbs,hb⟩ := exists_orthonormalFrame_near g J hdim hU hg hJ hJs hgJ hx
  exact ⟨V,hV,hxV,(contDiffOn_pairing_three_frame g hdim b hbs hb
    (hα.mono hVU) (hβ.mono hVU)).mono Set.inter_subset_right⟩

end TamingCompatibility.SmoothMetric

namespace TamingCompatibility.SmoothHodge
open ContinuousAlternatingMap MetricForms MetricModel MetricHodge FormSmooth
open scoped ContDiff
variable {E D : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup D] [NormedSpace ℝ D]

lemma volumeSquare_contDiffOn {F : D → MetricForms.Form E 2} {U : Set D}
    (hF : ContDiffOn ℝ ∞ F U) : ContDiffOn ℝ ∞ (fun x => ExteriorForms.volumeSquare (F x)) U := by
  apply contDiffOn_of_basis (Module.finBasis ℝ E)
  intro a
  have he : (fun i => Module.finBasis ℝ E (a i)) =
      ![Module.finBasis ℝ E (a 0),Module.finBasis ℝ E (a 1),
        Module.finBasis ℝ E (a 2),Module.finBasis ℝ E (a 3)] := by
    ext i; fin_cases i <;> rfl
  simp only [he,ExteriorForms.volumeSquare_apply]
  exact ((contDiffOn_apply_two hF contDiffOn_const contDiffOn_const).mul
    (contDiffOn_apply_two hF contDiffOn_const contDiffOn_const)).sub
    ((contDiffOn_apply_two hF contDiffOn_const contDiffOn_const).mul
    (contDiffOn_apply_two hF contDiffOn_const contDiffOn_const)) |>.add
    ((contDiffOn_apply_two hF contDiffOn_const contDiffOn_const).mul
    (contDiffOn_apply_two hF contDiffOn_const contDiffOn_const))

omit [FiniteDimensional ℝ E] in
lemma curryLeft_contDiffOn {k : ℕ} {α : D → MetricForms.Form E (k+1)} {v : D → E} {U : Set D}
    (hα : ContDiffOn ℝ ∞ α U) (hv : ContDiffOn ℝ ∞ v U) :
    ContDiffOn ℝ ∞ (fun x => (α x).curryLeft (v x)) U := by
  let C : MetricForms.Form E (k+1) →L[ℝ] (E →L[ℝ] MetricForms.Form E k) := curryLeftLI.toContinuousLinearMap
  exact ((C.contDiff.comp_contDiffOn hα).clm_apply hv)

lemma comp_contDiffOn {k : ℕ} {α : D → MetricForms.Form E k} {J : D → E →L[ℝ] E} {U : Set D}
    (hα : ContDiffOn ℝ ∞ α U) (hJ : ContDiffOn ℝ ∞ J U) :
    ContDiffOn ℝ ∞ (fun x => (α x).compContinuousLinearMap (J x)) U := by
  apply contDiffOn_of_basis (Module.finBasis ℝ E)
  intro a
  change ContDiffOn ℝ ∞ (fun x => α x (fun i => J x (Module.finBasis ℝ E (a i)))) U
  exact FormSmooth.contDiffOn_apply hα (fun i => hJ.clm_apply contDiffOn_const)

variable (g : D → Metric E) (J : D → E →L[ℝ] E)
  (hdim : Module.finrank ℝ E = 4) {U : Set D} (hU : IsOpen U)
  (hg : ContDiffOn ℝ ∞ (fun x => (g x).bilinear) U) (hJ : ContDiffOn ℝ ∞ J U)
  (hJs : ∀ x ∈ U, ∀ u, J x (J x u) = -u)
  (hgJ : ∀ x ∈ U, ∀ u v, (g x).bilinear (J x u) (J x v) = (g x).bilinear u v)
  {F : D → MetricForms.Form E 2} (hF : ContDiffOn ℝ ∞ F U)

include hdim hU hg hJ hJs hgJ hF
lemma starTwo_contDiffOn {α : D → MetricForms.Form E 2} (hα : ContDiffOn ℝ ∞ α U) :
    ContDiffOn ℝ ∞ (fun x => starTwo (g x) (J x) (F x) (α x)) U := by
  exact ((SmoothMetric.contDiffOn_pairing_two g J hdim hU hg hJ hJs hgJ hα hF).smul hF).sub
    (comp_contDiffOn hα hJ)

lemma starThree_contDiffOn {α : D → MetricForms.Form E 3} (hα : ContDiffOn ℝ ∞ α U) :
    ContDiffOn ℝ ∞ (fun x => starThree (g x) (F x) (α x)) U := by
  apply contDiffOn_of_basis (Module.finBasis ℝ E)
  intro a
  have he : (fun i => Module.finBasis ℝ E (a i)) = ![Module.finBasis ℝ E (a 0)] := by
    ext i; fin_cases i; rfl
  simp only [he,starThree_apply]
  exact (SmoothMetric.contDiffOn_pairing_three g J hdim hU hg hJ hJs hgJ hα
    (curryLeft_contDiffOn (volumeSquare_contDiffOn hF) contDiffOn_const)).neg

end TamingCompatibility.SmoothHodge

end

end OAI
