import OAI.Probability.FreeIsing.Estimates.CylinderBasics
import OAI.Probability.FreeIsing.Trees.GibbsMarginal
import OAI.Probability.FreeIsing.Trees.LeafCovariance

namespace OAI

noncomputable section

namespace Problem367

theorem tree_gibbs_root_covariance_bounds
    {d : ℕ} {beta : ℝ} (hbeta : 0 ≤ beta)
    {E : Finset (TreeVertex d)} {r : TreeVertex d}
    (hE : ConnectedFinset E) (hr : r ∈ E)
    (hmin : ∀ x ∈ E, r.1.length ≤ x.1.length)
    (h : TreeVertex d → ℝ) (v : TreeVertex d) (hv : v ∈ E) :
    0 ≤ LeafGibbs.covariance
      (fun eta => GibbsLeaf.energy beta h E (extendFiniteSpin E eta))
      (fun eta => spinSign (eta ⟨r, hr⟩)) (fun eta => spinSign (eta ⟨v, hv⟩)) ∧
    LeafGibbs.covariance
      (fun eta => GibbsLeaf.energy beta h E (extendFiniteSpin E eta))
      (fun eta => spinSign (eta ⟨r, hr⟩)) (fun eta => spinSign (eta ⟨v, hv⟩)) ≤
        Real.tanh beta ^ (v.1.length - r.1.length) := by
  classical
  have ht : 0 ≤ Real.tanh beta := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_nonneg (Real.sinh_nonneg_iff.mpr hbeta) (Real.cosh_pos beta).le
  revert hE hr hmin h v
  refine Finset.strongInductionOn E ?_
  intro E ih hE hr hmin h v hv
  let : Nonempty (E → IsingSpin) := ⟨fun _ => .neg⟩
  by_cases hvr : v = r
  · subst v
    simpa only [LeafGibbs.covariance, spinSign_mul_self, LeafGibbs.expectation_const,
      Nat.sub_self, pow_zero, pow_two] using
      LeafGibbs.spin_variance_bounds
        (fun eta => GibbsLeaf.energy beta h E (extendFiniteSpin E eta))
        (fun eta => eta ⟨r, hr⟩)
  have hsub : ({r} : Finset (TreeVertex d)) ⊆ E := Finset.singleton_subset_iff.mpr hr
  have hne : ({r} : Finset (TreeVertex d)) ≠ E := by
    intro heq
    exact hvr (Finset.mem_singleton.mp (heq.symm ▸ hv))
  obtain ⟨w, p, hwE, hwr, hpE, hpw, hEr, hsubr, hedges⟩ :=
    (connectedFinset_singleton r).exists_prunable_vertex_of_shared_min
      hE hsub (Finset.mem_singleton_self r) hmin hne
  have hrEr : r ∈ E.erase w := hsubr (Finset.mem_singleton_self r)
  have hpEr : p ∈ E.erase w := Finset.mem_erase.mpr ⟨hpw, hpE⟩
  have hErE : E.erase w ⊆ E := Finset.erase_subset _ _
  let h' := Function.update h p (h p + cavityMessage (Real.tanh beta) (h w))
  have hmin' : ∀ x ∈ E.erase w, r.1.length ≤ x.1.length :=
    fun x hx => hmin x (hErE hx)
  by_cases hvw : v = w
  · subst v
    have hrec := ih (E.erase w) (Finset.erase_ssubset hwE) hEr hrEr hmin' h' p hpEr
    have hcov := tree_gibbs_covariance_leaf beta h hwE hpEr hedges
      (fun eta => spinSign (eta ⟨r, hrEr⟩))
    have hmarg := tree_gibbs_covariance_erase beta h hwE hpEr hedges
      (fun eta => spinSign (eta ⟨r, hrEr⟩))
      (fun eta => spinSign (eta ⟨p, hpEr⟩))
    change LeafGibbs.covariance _ (fun eta : E → IsingSpin => spinSign (eta ⟨r, hr⟩))
        (fun eta => spinSign (eta ⟨w, hv⟩)) =
        (Real.tanh beta * responseAttenuation (Real.tanh beta) (h w)) *
          LeafGibbs.covariance _ (fun eta : E → IsingSpin => spinSign (eta ⟨r, hr⟩))
            (fun eta => spinSign (eta ⟨p, hpE⟩)) at hcov
    change LeafGibbs.covariance _ (fun eta : E → IsingSpin => spinSign (eta ⟨r, hr⟩))
        (fun eta => spinSign (eta ⟨p, hpE⟩)) = _ at hmarg
    rw [hcov, hmarg]
    have ha := responseAttenuation_pos (Real.tanh_sq_lt_one beta).le (h w)
    have ha1 := responseAttenuation_le_one (Real.tanh_sq_lt_one beta).le (h w)
    have hslope : 0 ≤ Real.tanh beta * responseAttenuation (Real.tanh beta) (h w) :=
      mul_nonneg ht ha.le
    have hedge : (p, w) ∈ inducedEdges E := by rw [hedges]; exact Finset.mem_insert_self _ _
    have hdata := Finset.mem_filter.mp hedge
    have hadj : treeAdj p w := hdata.2.1
    have hlower : p.1.length < w.1.length := hdata.2.2
    have hlen := treeAdj_length hadj
    have hdist : w.1.length - r.1.length = (p.1.length - r.1.length) + 1 := by
      have := hmin p hpE
      omega
    constructor
    · exact mul_nonneg hslope hrec.1
    · rw [hdist, pow_succ]
      calc
        _ ≤ (Real.tanh beta * responseAttenuation (Real.tanh beta) (h w)) *
            Real.tanh beta ^ (p.1.length - r.1.length) :=
          mul_le_mul_of_nonneg_left hrec.2 hslope
        _ ≤ Real.tanh beta * Real.tanh beta ^ (p.1.length - r.1.length) :=
          mul_le_mul_of_nonneg_right (mul_le_of_le_one_right ht ha1) (pow_nonneg ht _)
        _ = _ := mul_comm _ _
  · have hvEr : v ∈ E.erase w := Finset.mem_erase.mpr ⟨hvw, hv⟩
    have hrec := ih (E.erase w) (Finset.erase_ssubset hwE) hEr hrEr hmin' h' v hvEr
    have hmarg := tree_gibbs_covariance_erase beta h hwE hpEr hedges
      (fun eta => spinSign (eta ⟨r, hrEr⟩))
      (fun eta => spinSign (eta ⟨v, hvEr⟩))
    change LeafGibbs.covariance _ (fun eta : E → IsingSpin => spinSign (eta ⟨r, hr⟩))
        (fun eta => spinSign (eta ⟨v, hv⟩)) = _ at hmarg
    rw [hmarg]
    exact hrec

end Problem367

end

end OAI
