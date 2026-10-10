import OAI.Geometry.Relativity.CKS.ConstraintGlobalIntegral

namespace OAI

noncomputable section
open Bundle Manifold Set Filter CKSLorentz CKSMetricGluing CKSSpatialManifold MeasureTheory
open scoped ContDiff Topology ENNReal
namespace CKSIntrinsicConstraints
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

def strictEndChart (f : M → E) (finv : E → M) {V : Set M} {T s : ℝ}
    (hs : T < s) (hV : IsOpen V)
    (hf : ContMDiffOn I 𝓘(ℝ,E) ∞ f V)
    (hi : ContMDiffOn 𝓘(ℝ,E) I ∞ finv {y | T < ‖y‖})
    (hleft : ∀ x ∈ V, finv (f x) = x)
    (hright : ∀ y, T < ‖y‖ → finv y ∈ V ∧ f (finv y) = y) :
    OpenPartialHomeomorph M E where
  toFun := f
  invFun := finv
  source := {x | x ∈ V ∧ s < ‖f x‖}
  target := {y | s < ‖y‖}
  map_source' := fun _ hx => hx.2
  map_target' := by
    intro y hy
    have h := hright y (hs.trans hy)
    exact ⟨h.1,by rw [h.2]; exact hy⟩
  left_inv' := fun _ hx => hleft _ hx.1
  right_inv' := fun y hy => (hright y (hs.trans hy)).2
  open_source := by
    exact hf.continuousOn.isOpen_inter_preimage hV (isOpen_lt continuous_const continuous_norm)
  open_target := isOpen_lt continuous_const continuous_norm
  continuousOn_toFun := hf.continuousOn.mono (fun _ hx => hx.1)
  continuousOn_invFun := hi.continuousOn.mono (fun _ hy => hs.trans hy)

variable [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M] [T2Space M]

theorem global_constraints_from_end
    (g : SmoothMetric I (M := M)) (K : InnerField I (M := M))
    (hDEC : PhysicalDEC I g.inner K)
    (f : M → E) (finv : E → M) {V : Set M} {T s : ℝ}
    (hs : T < s) (hV : IsOpen V)
    (hf : ContMDiffOn I 𝓘(ℝ,E) ∞ f V)
    (hi : ContMDiffOn 𝓘(ℝ,E) I ∞ finv {y | T < ‖y‖})
    (hleft : ∀ x ∈ V, finv (f x) = x)
    (hright : ∀ y, T < ‖y‖ → finv y ∈ V ∧ f (finv y) = y)
    (hcompact : IsCompact {x : M | x ∉ V ∨ ‖f x‖ ≤ s})
    (A B : SpatialTensor)
    (hAs : ContDiffOn ℝ ∞ A {y | T < ‖y‖})
    (hBs : ContDiffOn ℝ ∞ B {y | T < ‖y‖})
    (hA : ∀ y, T < ‖y‖ →
      (∀ v w, A y v w = A y w v) ∧ (∀ v : E, v ≠ 0 → 0 < A y v v))
    (hB : ∀ y, T < ‖y‖ → ∀ v w, B y v w = B y w v)
    (hrep : ∀ x ∈ V, g.inner x = endInner I f A x ∧ K x = endInner I f B x)
    (hCint : IntegrableOn (spatialEnergy A B) (CKSTailVolume.tailRegion s) (spatialVolume A))
    (hQint : IntegrableOn (coordinateMomentumNorm A B) (CKSTailVolume.tailRegion s) (spatialVolume A)) :
    ∃ C Q : M → ℝ, Continuous C ∧ Continuous Q ∧
      Integrable C (CKSIntrinsicVolume.riemannianVolume g.toContinuousRiemannianMetric) ∧
      Integrable Q (CKSIntrinsicVolume.riemannianVolume g.toContinuousRiemannianMetric) ∧
      (∀ x, 0 ≤ Q x ∧ Q x ≤ C x) ∧
      ∀ x (c : ConstraintChart g.inner K x), C x = c.energy ∧ Q x = c.momentumNorm := by
  let e := strictEndChart f finv hs hV hf hi hleft hright
  apply exists_integrable_constraint_densities g K hDEC e
  · convert hcompact using 1
    ext x
    simp only [e, strictEndChart, mem_compl_iff, mem_ofPred_eq, not_and, not_lt]
    tauto
  · exact hf.mono (fun _ hx => hx.1)
  · exact hAs.mono (fun _ hy => hs.trans hy)
  · exact hBs.mono (fun _ hy => hs.trans hy)
  · exact fun y hy => hA y (hs.trans hy)
  · exact fun y hy => hB y (hs.trans hy)
  · exact fun x hx => hrep x hx.1
  · exact hCint
  · exact hQint

end CKSIntrinsicConstraints

end

end OAI
