import OAI.Probability.FreeIsing.Gaussian.TreeResponse
import OAI.Probability.FreeIsing.Trees.ResponseAutomorphism

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.GaussianTreeResponseNaturality

def fieldEquiv {d : ℕ} (g : TreeAut d) (D : Finset (TreeVertex d)) :
    (D → ℝ) ≃ᵐ (D.image g.toEquiv → ℝ) :=
  MeasurableEquiv.piCongrLeft (fun _ : D.image g.toEquiv => ℝ)
    (TreeGibbsAut.vertexEquiv g D)

@[simp] theorem fieldEquiv_apply_image {d : ℕ} (g : TreeAut d)
    (D : Finset (TreeVertex d)) (y : D → ℝ) (u : D) :
    fieldEquiv g D y (TreeGibbsAut.vertexEquiv g D u) = y u := by
  simp [fieldEquiv, MeasurableEquiv.coe_piCongrLeft]

theorem measurePreserving_fieldEquiv {d : ℕ} (g : TreeAut d)
    (D : Finset (TreeVertex d)) (m : TreeVertex d → ℝ) (t : TreeVertex d → ℝ≥0) :
    MeasurePreserving (fieldEquiv g D)
      (Measure.pi (fun u : D => gaussianReal (m u) (t u)))
      (Measure.pi (fun v : D.image g.toEquiv =>
        gaussianReal (relabel g m v) (relabel g t v))) := by
  have hp := measurePreserving_piCongrLeft
    (fun v : D.image g.toEquiv => gaussianReal (relabel g m v) (relabel g t v))
    (TreeGibbsAut.vertexEquiv g D)
  simpa only [fieldEquiv, relabel, TreeGibbsAut.vertexEquiv, Equiv.coe_fn_mk,
    Equiv.symm_apply_apply] using hp

theorem relabel_updateFinset {d : ℕ} (g : TreeAut d)
    (D : Finset (TreeVertex d)) (x : TreeVertex d → ℝ) (y : D → ℝ) :
    relabel g (Function.updateFinset x D y) =
      Function.updateFinset (relabel g x) (D.image g.toEquiv) (fieldEquiv g D y) := by
  classical
  funext v
  obtain ⟨u, rfl⟩ := g.toEquiv.surjective v
  by_cases hu : u ∈ D
  · have hv : g.toEquiv u ∈ D.image g.toEquiv := Finset.mem_image.mpr ⟨u, hu, rfl⟩
    simp only [relabel, Equiv.symm_apply_apply, Function.updateFinset, dite_eq_left hu,
      dite_eq_left hv]
    exact (fieldEquiv_apply_image g D y ⟨u, hu⟩).symm
  · have hv : g.toEquiv u ∉ D.image g.toEquiv := by
      simpa only [Finset.mem_image, EmbeddingLike.apply_eq_iff_eq,
        exists_eq_right] using hu
    simp only [relabel, Equiv.symm_apply_apply, Function.updateFinset, dite_eq_right hu,
      dite_eq_right hv]

theorem response_fieldEquiv {d : ℕ} (g : TreeAut d)
    (D : Finset (TreeVertex d)) (beta : ℝ) (h x : TreeVertex d → ℝ)
    (y : D → ℝ) (u v : D) :
    TreePathResponse.response beta
      (fun a => relabel g h a +
        Function.updateFinset (relabel g x) (D.image g.toEquiv) (fieldEquiv g D y) a)
      (D.image g.toEquiv) (g.toEquiv u) (g.toEquiv v) =
    TreePathResponse.response beta
      (fun a => h a + Function.updateFinset x D y a) D u v := by
  rw [← relabel_updateFinset]
  exact TreePathResponse.response_relabel g D beta
    (fun a => h a + Function.updateFinset x D y a) u v

theorem integral_response_relabel {d : ℕ} (g : TreeAut d)
    (D : Finset (TreeVertex d)) (beta : ℝ)
    (m h x : TreeVertex d → ℝ) (t : TreeVertex d → ℝ≥0)
    (u v : D) (F : ℝ → ℝ) :
    (∫ y : D.image g.toEquiv → ℝ,
      F (TreePathResponse.response beta
        (fun a => relabel g h a + Function.updateFinset (relabel g x) (D.image g.toEquiv) y a)
        (D.image g.toEquiv) (g.toEquiv u) (g.toEquiv v))
      ∂Measure.pi (fun a : D.image g.toEquiv =>
        gaussianReal (relabel g m a) (relabel g t a))) =
    ∫ y : D → ℝ,
      F (TreePathResponse.response beta (fun a => h a + Function.updateFinset x D y a) D u v)
      ∂Measure.pi (fun a : D => gaussianReal (m a) (t a)) := by
  rw [← (measurePreserving_fieldEquiv g D m t).integral_comp']
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun y => congrArg F
    (response_fieldEquiv g D beta h x y u v)

theorem integral_gaussian_response_sq_le_distance
    {d : ℕ} {beta : ℝ} (hb : 0 ≤ beta)
    (m : TreeVertex d → ℝ) (t : TreeVertex d → ℝ≥0)
    {δ : ℝ≥0} (hδ : 0 < δ) (ht : ∀ a, δ ≤ t a)
    {D : Finset (TreeVertex d)} (hD : ConnectedFinset D)
    (h x : TreeVertex d → ℝ) (u v : D) :
    (∫ y : D → ℝ,
      TreePathResponse.response beta
        (fun a => h a + Function.updateFinset x D y a) D u v ^ 2
      ∂Measure.pi (fun a : D => gaussianReal (m a) (t a))) ≤
    (Real.tanh beta ^ 2 * GaussianTreeCovariance.gaussianContraction beta δ) ^
      reducedWordDistance u.1.1 v.1.1 := by
  obtain ⟨g, hg, hd⟩ := exists_treeAut_to_root_distance u.1
  have hzero : (g.toEquiv u).1.length = 0 := by rw [hg]; rfl
  have hmin : ∀ a ∈ D.image g.toEquiv, (g.toEquiv u).1.length ≤ a.1.length := by
    intro a _
    rw [hzero]
    exact Nat.zero_le _
  have he := GaussianTreeResponse.integral_gaussian_response_sq_le hb
    (relabel g m) (relabel g t) hδ (fun a => ht (g.toEquiv.symm a))
    (hD.image g) (TreeGibbsAut.vertexEquiv g D u).property hmin
    (relabel g h) (relabel g x) (g.toEquiv v)
    (TreeGibbsAut.vertexEquiv g D v).property
  change (∫ y : D.image g.toEquiv → ℝ,
    TreePathResponse.response beta
      (fun a => relabel g h a + Function.updateFinset (relabel g x) (D.image g.toEquiv) y a)
      (D.image g.toEquiv) (g.toEquiv u) (g.toEquiv v) ^ 2
    ∂Measure.pi (fun a : D.image g.toEquiv =>
      gaussianReal (relabel g m a) (relabel g t a))) ≤ _ at he
  rw [integral_response_relabel g D beta m h x t u v (fun z => z ^ 2)] at he
  simpa only [TreeGibbsAut.vertexEquiv, Equiv.coe_fn_mk, hzero, Nat.sub_zero, hd v] using he

end Problem367.GaussianTreeResponseNaturality

end

end OAI
