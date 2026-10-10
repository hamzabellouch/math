import OAI.Probability.FreeIsing.Energy.FiniteLeafCovariance
import OAI.Probability.FreeIsing.Gibbs.Leaf

namespace OAI

noncomputable section

namespace Problem367

private theorem leaf_expectation_equiv {A B : Type*} [Fintype A] [Fintype B]
    (e : A ≃ B) (E f : B → ℝ) :
    LeafGibbs.expectation (E ∘ e) (f ∘ e) = LeafGibbs.expectation E f := by
  unfold LeafGibbs.expectation
  simp only [Function.comp_apply]
  rw [e.sum_comp (fun b => f b * Real.exp (E b)), e.sum_comp (fun b => Real.exp (E b))]

private theorem leaf_covariance_equiv {A B : Type*} [Fintype A] [Fintype B]
    (e : A ≃ B) (E f g : B → ℝ) :
    LeafGibbs.covariance (E ∘ e) (f ∘ e) (g ∘ e) = LeafGibbs.covariance E f g := by
  unfold LeafGibbs.covariance
  rw [leaf_expectation_equiv, leaf_expectation_equiv]
  congr 1
  exact leaf_expectation_equiv e E (fun b => f b * g b)

theorem tree_gibbs_leaf_energy_split
    {d : ℕ} {D : Finset (TreeVertex d)} {v p : TreeVertex d}
    (beta : ℝ) (h : TreeVertex d → ℝ) (hv : v ∈ D) (hpne : p ≠ v)
    (hedges : inducedEdges D = insert (p, v) (inducedEdges (D.erase v))) :
    (fun eta => GibbsLeaf.energy beta h D (extendFiniteSpin D eta)) ∘
      (finiteSpinEraseEquiv hv).symm =
    LeafGibbs.energy
      (fun eta => GibbsLeaf.energy beta h (D.erase v) (extendFiniteSpin (D.erase v) eta))
      (fun eta => extendFiniteSpin (D.erase v) eta p) beta (h v) := by
  funext z
  rcases z with ⟨eta, s⟩
  simp only [Function.comp_apply, extendFiniteSpin_eraseEquiv_symm,
    GibbsLeaf.energy_update_eq_erase_add beta h hv hpne hedges, LeafGibbs.energy]
  ring

theorem tree_gibbs_covariance_leaf
    {d : ℕ} {D : Finset (TreeVertex d)} {v p : TreeVertex d}
    (beta : ℝ) (h : TreeVertex d → ℝ) (hv : v ∈ D) (hp : p ∈ D.erase v)
    (hedges : inducedEdges D = insert (p, v) (inducedEdges (D.erase v)))
    (f : (D.erase v → IsingSpin) → ℝ) :
    LeafGibbs.covariance
      (fun eta => GibbsLeaf.energy beta h D (extendFiniteSpin D eta))
      (fun eta => f ((finiteSpinEraseEquiv hv eta).1))
      (fun eta => spinSign (eta ⟨v, hv⟩)) =
    (Real.tanh beta * responseAttenuation (Real.tanh beta) (h v)) *
      LeafGibbs.covariance
        (fun eta => GibbsLeaf.energy beta h D (extendFiniteSpin D eta))
        (fun eta => f ((finiteSpinEraseEquiv hv eta).1))
        (fun eta => spinSign (eta ⟨p, (Finset.mem_erase.mp hp).2⟩)) := by
  classical
  let : Nonempty (D.erase v → IsingSpin) := ⟨fun _ => .neg⟩
  let e := (finiteSpinEraseEquiv hv).symm
  let E : (D → IsingSpin) → ℝ :=
    fun eta => GibbsLeaf.energy beta h D (extendFiniteSpin D eta)
  let F : (D → IsingSpin) → ℝ := fun eta => f ((finiteSpinEraseEquiv hv eta).1)
  let L : (D → IsingSpin) → ℝ := fun eta => spinSign (eta ⟨v, hv⟩)
  let P : (D → IsingSpin) → ℝ :=
    fun eta => spinSign (eta ⟨p, (Finset.mem_erase.mp hp).2⟩)
  change LeafGibbs.covariance E F L = _ * LeafGibbs.covariance E F P
  rw [← leaf_covariance_equiv e E F L, ← leaf_covariance_equiv e E F P]
  have he : E ∘ e = LeafGibbs.energy
      (fun eta => GibbsLeaf.energy beta h (D.erase v) (extendFiniteSpin (D.erase v) eta))
      (fun eta => extendFiniteSpin (D.erase v) eta p) beta (h v) :=
    tree_gibbs_leaf_energy_split beta h hv (Finset.mem_erase.mp hp).1 hedges
  have hf : F ∘ e = fun z => f z.1 := by
    funext z
    simp [F, e]
  have hl : L ∘ e = fun z => spinSign z.2 := by
    funext z
    simp [L, e, finiteSpinEraseEquiv]
  have hp' : P ∘ e = fun z => spinSign (extendFiniteSpin (D.erase v) z.1 p) := by
    funext z
    simp [P, e, finiteSpinEraseEquiv, extendFiniteSpin,
      (Finset.mem_erase.mp hp).1, hp]
  rw [he, hf, hl, hp']
  exact LeafGibbs.covariance_leaf_eq_mul_parent _ f _ beta (h v)

theorem tree_gibbs_covariance_maximal_leaf
    {d : ℕ} {D : Finset (TreeVertex d)} {v p : TreeVertex d}
    (beta : ℝ) (h : TreeVertex d → ℝ) (hv : v ∈ D) (hp : p ∈ D)
    (hpv : treeAdj p v) (hplen : p.1.length < v.1.length)
    (hmax : ∀ x ∈ D, x.1.length ≤ v.1.length)
    (f : (D.erase v → IsingSpin) → ℝ) :
    LeafGibbs.covariance
      (fun eta => GibbsLeaf.energy beta h D (extendFiniteSpin D eta))
      (fun eta => f ((finiteSpinEraseEquiv hv eta).1))
      (fun eta => spinSign (eta ⟨v, hv⟩)) =
    (Real.tanh beta * responseAttenuation (Real.tanh beta) (h v)) *
      LeafGibbs.covariance
        (fun eta => GibbsLeaf.energy beta h D (extendFiniteSpin D eta))
        (fun eta => f ((finiteSpinEraseEquiv hv eta).1))
        (fun eta => spinSign (eta ⟨p, hp⟩)) := by
  have hpne : p ≠ v := by
    intro heq
    subst p
    exact lt_irrefl _ hplen
  exact tree_gibbs_covariance_leaf beta h hv (Finset.mem_erase.mpr ⟨hpne, hp⟩)
    (inducedEdges_eq_insert_erase_of_max_length hv hp hpv hplen hmax) f

end Problem367

end

end OAI
