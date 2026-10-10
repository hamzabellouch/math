import OAI.Probability.FreeIsing.Estimates.CylinderAutomorphism
import OAI.Probability.FreeIsing.Trees.ConnectedHull
import OAI.Probability.FreeIsing.Trees.RootCovariance
import OAI.Probability.FreeIsing.Trees.Transitivity

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace Problem367.TreeGibbsAut

variable {d : ℕ}

def vertexEquiv (g : TreeAut d) (D : Finset (TreeVertex d)) :
    D ≃ D.image g.toEquiv where
  toFun u := ⟨g.toEquiv u, Finset.mem_image.mpr ⟨u, u.property, rfl⟩⟩
  invFun v := ⟨g.toEquiv.symm v, by
    obtain ⟨u, hu, he⟩ := Finset.mem_image.mp v.property
    rw [← he, Equiv.symm_apply_apply]
    exact hu⟩
  left_inv u := Subtype.ext (g.toEquiv.symm_apply_apply u)
  right_inv v := Subtype.ext (g.toEquiv.apply_symm_apply v)

def spinEquiv (g : TreeAut d) (D : Finset (TreeVertex d)) :
    (D → IsingSpin) ≃ (D.image g.toEquiv → IsingSpin) where
  toFun eta v := eta ((vertexEquiv g D).symm v)
  invFun xi u := xi (vertexEquiv g D u)
  left_inv eta := by funext u; simp
  right_inv xi := by funext v; simp

@[simp] theorem spinEquiv_apply_image (g : TreeAut d) (D : Finset (TreeVertex d))
    (eta : D → IsingSpin) (u : D) :
    spinEquiv g D eta (vertexEquiv g D u) = eta u := by
  simp [spinEquiv]

theorem sum_inducedEdges_image {M : Type*} [AddCommMonoid M]
    (g : TreeAut d) (D : Finset (TreeVertex d))
    (f : TreeVertex d → TreeVertex d → M) (hf : ∀ u v, f u v = f v u) :
    (∑ e ∈ inducedEdges (D.image g.toEquiv),
      f (g.toEquiv.symm e.1) (g.toEquiv.symm e.2)) =
        ∑ e ∈ inducedEdges D, f e.1 e.2 := by
  have h := CylinderAut.prod_inducedEdges_image g D
    (fun u v => Multiplicative.ofAdd (f u v))
    (fun u v => congrArg Multiplicative.ofAdd (hf u v))
  simpa using congrArg Multiplicative.toAdd h

theorem energy_relabel (g : TreeAut d) (D : Finset (TreeVertex d))
    (beta : ℝ) (h : TreeVertex d → ℝ) (eta : TreeVertex d → IsingSpin) :
    GibbsLeaf.energy beta (relabel g h) (D.image g.toEquiv) (relabel g eta) =
      GibbsLeaf.energy beta h D eta := by
  unfold GibbsLeaf.energy relabel
  rw [Finset.sum_image g.toEquiv.injective.injOn]
  simp only [Equiv.symm_apply_apply]
  rw [sum_inducedEdges_image g D
    (fun u v => spinSign (eta u) * spinSign (eta v))
    (fun u v => mul_comm _ _)]

theorem energy_spinEquiv (g : TreeAut d) (D : Finset (TreeVertex d))
    (beta : ℝ) (h : TreeVertex d → ℝ) (eta : D → IsingSpin) :
    GibbsLeaf.energy beta (relabel g h) (D.image g.toEquiv)
      (extendFiniteSpin (D.image g.toEquiv) (spinEquiv g D eta)) =
        GibbsLeaf.energy beta h D (extendFiniteSpin D eta) := by
  calc
    _ = GibbsLeaf.energy beta (relabel g h) (D.image g.toEquiv)
        (relabel g (extendFiniteSpin D eta)) := by
      apply GibbsLeaf.energy_congr_on
      intro x hx
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
      change extendFiniteSpin (D.image g.toEquiv) (spinEquiv g D eta)
          ((vertexEquiv g D ⟨u, hu⟩).val) = _
      rw [extendFiniteSpin_apply, spinEquiv_apply_image]
      simp [relabel, extendFiniteSpin, hu]
    _ = _ := energy_relabel g D beta h _

theorem expectation_equiv {A B : Type*} [Fintype A] [Fintype B]
    (e : A ≃ B) (E f : B → ℝ) :
    LeafGibbs.expectation (E ∘ e) (f ∘ e) = LeafGibbs.expectation E f := by
  unfold LeafGibbs.expectation
  simp only [Function.comp_apply]
  rw [e.sum_comp (fun b => f b * Real.exp (E b)), e.sum_comp (fun b => Real.exp (E b))]

theorem expectation_relabel (g : TreeAut d) (D : Finset (TreeVertex d))
    (beta : ℝ) (h : TreeVertex d → ℝ) (f : (D.image g.toEquiv → IsingSpin) → ℝ) :
    LeafGibbs.expectation
      (fun eta => GibbsLeaf.energy beta (relabel g h) (D.image g.toEquiv)
        (extendFiniteSpin (D.image g.toEquiv) eta)) f =
    LeafGibbs.expectation
      (fun eta => GibbsLeaf.energy beta h D (extendFiniteSpin D eta))
      (fun eta => f (spinEquiv g D eta)) := by
  rw [← expectation_equiv (spinEquiv g D)]
  congr 1
  funext eta
  exact energy_spinEquiv g D beta h eta

theorem covariance_relabel (g : TreeAut d) (D : Finset (TreeVertex d))
    (beta : ℝ) (h : TreeVertex d → ℝ) (f k : (D.image g.toEquiv → IsingSpin) → ℝ) :
    LeafGibbs.covariance
      (fun eta => GibbsLeaf.energy beta (relabel g h) (D.image g.toEquiv)
        (extendFiniteSpin (D.image g.toEquiv) eta)) f k =
    LeafGibbs.covariance
      (fun eta => GibbsLeaf.energy beta h D (extendFiniteSpin D eta))
      (fun eta => f (spinEquiv g D eta)) (fun eta => k (spinEquiv g D eta)) := by
  unfold LeafGibbs.covariance
  rw [expectation_relabel, expectation_relabel, expectation_relabel]

theorem spin_covariance_relabel (g : TreeAut d) (D : Finset (TreeVertex d))
    (beta : ℝ) (h : TreeVertex d → ℝ) (u v : D) :
    LeafGibbs.covariance
      (fun eta => GibbsLeaf.energy beta (relabel g h) (D.image g.toEquiv)
        (extendFiniteSpin (D.image g.toEquiv) eta))
      (fun eta => spinSign (eta (vertexEquiv g D u)))
      (fun eta => spinSign (eta (vertexEquiv g D v))) =
    LeafGibbs.covariance
      (fun eta => GibbsLeaf.energy beta h D (extendFiniteSpin D eta))
      (fun eta => spinSign (eta u)) (fun eta => spinSign (eta v)) := by
  rw [covariance_relabel]
  simp only [spinEquiv_apply_image]

theorem spin_expectation_relabel (g : TreeAut d) (D : Finset (TreeVertex d))
    (beta : ℝ) (h : TreeVertex d → ℝ) (u : D) :
    LeafGibbs.expectation
      (fun eta => GibbsLeaf.energy beta (relabel g h) (D.image g.toEquiv)
        (extendFiniteSpin (D.image g.toEquiv) eta))
      (fun eta => spinSign (eta (vertexEquiv g D u))) =
    LeafGibbs.expectation
      (fun eta => GibbsLeaf.energy beta h D (extendFiniteSpin D eta))
      (fun eta => spinSign (eta u)) := by
  rw [expectation_relabel]
  simp only [spinEquiv_apply_image]

theorem covariance_bounds_of_reroot {beta : ℝ} (hbeta : 0 ≤ beta)
    (D : Finset (TreeVertex d)) (hD : ConnectedFinset D)
    (h : TreeVertex d → ℝ) (u v : D) (g : TreeAut d)
    (hg : g.toEquiv u = ConnectedHull.root d) :
    0 ≤ LeafGibbs.covariance
      (fun eta => GibbsLeaf.energy beta h D (extendFiniteSpin D eta))
      (fun eta => spinSign (eta u)) (fun eta => spinSign (eta v)) ∧
    LeafGibbs.covariance
      (fun eta => GibbsLeaf.energy beta h D (extendFiniteSpin D eta))
      (fun eta => spinSign (eta u)) (fun eta => spinSign (eta v)) ≤
        Real.tanh beta ^ (g.toEquiv v).1.length := by
  have hzero : (g.toEquiv u).1.length = 0 := by rw [hg]; rfl
  have hb := tree_gibbs_root_covariance_bounds hbeta (hD.image g)
    (vertexEquiv g D u).property
    (fun x hx => by change (g.toEquiv u).1.length ≤ x.1.length; rw [hzero]; exact Nat.zero_le _)
    (relabel g h) (g.toEquiv v) (vertexEquiv g D v).property
  change 0 ≤ LeafGibbs.covariance
      (fun eta => GibbsLeaf.energy beta (relabel g h) (D.image g.toEquiv)
        (extendFiniteSpin (D.image g.toEquiv) eta))
      (fun eta => spinSign (eta (vertexEquiv g D u)))
      (fun eta => spinSign (eta (vertexEquiv g D v))) ∧
    LeafGibbs.covariance
      (fun eta => GibbsLeaf.energy beta (relabel g h) (D.image g.toEquiv)
        (extendFiniteSpin (D.image g.toEquiv) eta))
      (fun eta => spinSign (eta (vertexEquiv g D u)))
      (fun eta => spinSign (eta (vertexEquiv g D v))) ≤
        Real.tanh beta ^ ((g.toEquiv v).1.length - (g.toEquiv u).1.length) at hb
  simpa only [spin_covariance_relabel, hzero, Nat.sub_zero] using hb

end Problem367.TreeGibbsAut

end

end OAI
