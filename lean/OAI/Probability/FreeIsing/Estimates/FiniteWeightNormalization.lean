import OAI.Probability.FreeIsing.Estimates.FiniteMarginals
import OAI.Probability.FreeIsing.Estimates.LeafWeights

namespace OAI

noncomputable section

namespace Problem367

def finiteSpinEraseEquiv {d : ℕ} {D : Finset (TreeVertex d)} {v : TreeVertex d}
    (hv : v ∈ D) : (D → IsingSpin) ≃ ((D.erase v → IsingSpin) × IsingSpin) := by
  classical
  exact
    { toFun := fun f => ⟨(fun x => f ⟨x.1, (Finset.mem_erase.mp x.2).2⟩), f ⟨v, hv⟩⟩
      invFun := fun f x => if h : x.1 = v then f.2 else
        f.1 ⟨x.1, Finset.mem_erase.mpr ⟨h, x.2⟩⟩
      left_inv := by
        intro f
        funext x
        dsimp
        split_ifs with h
        · congr 1
          exact Subtype.ext h.symm
        · rfl
      right_inv := by
        intro f
        apply Prod.ext
        · funext x
          simp [(Finset.mem_erase.mp x.2).1]
        · simp }

theorem extendFiniteSpin_eraseEquiv_symm
    {d : ℕ} {D : Finset (TreeVertex d)} {v : TreeVertex d} (hv : v ∈ D)
    (eta : D.erase v → IsingSpin) (s : IsingSpin) :
    extendFiniteSpin D ((finiteSpinEraseEquiv hv).symm (eta, s)) =
      Function.update (extendFiniteSpin (D.erase v) eta) v s := by
  classical
  funext x
  by_cases hxv : x = v
  · subst x
    simp [extendFiniteSpin, finiteSpinEraseEquiv, hv]
  · by_cases hx : x ∈ D
    · simp [extendFiniteSpin, finiteSpinEraseEquiv, hxv, hx]
    · simp [extendFiniteSpin, hxv, hx]

theorem sum_freeCylinderWeight_erase_of_max_length
    {d : ℕ} {D : Finset (TreeVertex d)} {v p : TreeVertex d} {theta : ℝ}
    (hlo : -1 ≤ theta) (hhi : theta ≤ 1)
    (hv : v ∈ D) (hp : p ∈ D) (hpv : treeAdj p v)
    (hplen : p.1.length < v.1.length)
    (hmax : ∀ x ∈ D, x.1.length ≤ v.1.length) :
    (∑ eta : D → IsingSpin, freeCylinderWeight theta D (extendFiniteSpin D eta)) =
      ∑ eta : D.erase v → IsingSpin,
        freeCylinderWeight theta (D.erase v) (extendFiniteSpin (D.erase v) eta) := by
  classical
  calc
    _ = ∑ z : (D.erase v → IsingSpin) × IsingSpin,
        freeCylinderWeight theta D
          (extendFiniteSpin D ((finiteSpinEraseEquiv hv).symm z)) :=
      ((finiteSpinEraseEquiv hv).symm.sum_comp
        (fun eta => freeCylinderWeight theta D (extendFiniteSpin D eta))).symm
    _ = _ := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro eta _
      simp only [extendFiniteSpin_eraseEquiv_symm]
      exact freeCylinderWeight_sum_update_leaf hlo hhi hv hp hpv hplen hmax _

theorem sum_freeCylinderWeight_singleton {d : ℕ} (v : TreeVertex d) (theta : ℝ) :
    (∑ eta : ({v} : Finset (TreeVertex d)) → IsingSpin,
      freeCylinderWeight theta {v} (extendFiniteSpin {v} eta)) = 1 := by
  classical
  have hE : inducedEdges ({v} : Finset (TreeVertex d)) = ∅ := by
    ext e
    simp only [inducedEdges, Finset.product_eq_sprod, Finset.mem_filter,
      Finset.mem_product, Finset.mem_singleton, Finset.notMem_empty, iff_false]
    rintro ⟨⟨hx, hy⟩, _, hlen⟩
    rw [hx, hy] at hlen
    exact lt_irrefl _ hlen
  have hc : Fintype.card IsingSpin = 2 := by decide
  simp [freeCylinderWeight, hE, hc]
  exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num)

theorem sum_freeCylinderWeight_eq_one
    {d : ℕ} {theta : ℝ} (hlo : -1 ≤ theta) (hhi : theta ≤ 1)
    (D : Finset (TreeVertex d)) (hD : ConnectedFinset D) :
    (∑ eta : D → IsingSpin, freeCylinderWeight theta D (extendFiniteSpin D eta)) = 1 := by
  classical
  revert hD
  refine Finset.strongInductionOn D ?_
  intro D ih hD
  obtain ⟨v, hv, hmax⟩ := Finset.exists_max_image D (fun x => x.1.length) hD.1
  by_cases hn : (D.erase v).Nonempty
  · obtain ⟨q, hq⟩ := hn
    obtain h | ⟨p, hvp, _⟩ := (hD.2 v hv q (Finset.mem_erase.mp hq).2).cases_head
    · exact False.elim ((Finset.mem_erase.mp hq).1 h.symm)
    · have hpv : treeAdj p v := hvp.2.2.elim Or.inr Or.inl
      have hplen : p.1.length < v.1.length := by
        rcases hvp.2.2 with ⟨c, hc⟩ | ⟨c, hc⟩
        · have hlen := congrArg List.length hc
          have hbound := hmax p hvp.2.1
          simp only [List.length_append, List.length_singleton] at hlen
          omega
        · have hlen := congrArg List.length hc
          simp only [List.length_append, List.length_singleton] at hlen
          omega
      rw [sum_freeCylinderWeight_erase_of_max_length hlo hhi hv hvp.2.1 hpv hplen hmax]
      exact ih (D.erase v) (Finset.erase_ssubset hv)
        (connectedFinset_erase_of_max_length hD hv ⟨q, hq⟩ hmax)
  · have he : D.erase v = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    have hsingle : D = {v} := ((Finset.erase_eq_empty_iff D v).mp he).resolve_left hD.1.ne_empty
    subst D
    exact sum_freeCylinderWeight_singleton v theta

def finiteFreeIsingPMF
    {d : ℕ} {theta : ℝ} (hlo : -1 ≤ theta) (hhi : theta ≤ 1)
    (D : Finset (TreeVertex d)) (hD : ConnectedFinset D) : PMF (D → IsingSpin) :=
  PMF.ofFintype (fun eta => freeCylinderWeight theta D (extendFiniteSpin D eta))
    (sum_freeCylinderWeight_eq_one hlo hhi D hD)

@[simp]
theorem finiteFreeIsingPMF_apply
    {d : ℕ} {theta : ℝ} (hlo : -1 ≤ theta) (hhi : theta ≤ 1)
    (D : Finset (TreeVertex d)) (hD : ConnectedFinset D) (eta : D → IsingSpin) :
    finiteFreeIsingPMF hlo hhi D hD eta =
      freeCylinderWeight theta D (extendFiniteSpin D eta) := rfl

theorem finiteFreeIsingPMF_map_erase_of_edges
    {d : ℕ} {D : Finset (TreeVertex d)} {v p : TreeVertex d} {theta : ℝ}
    (hlo : -1 ≤ theta) (hhi : theta ≤ 1) (hD : ConnectedFinset D)
    (hv : v ∈ D) (hpne : p ≠ v) (hE : ConnectedFinset (D.erase v))
    (hedges : inducedEdges D = insert (p, v) (inducedEdges (D.erase v))) :
    (finiteFreeIsingPMF hlo hhi D hD).map
      (fun eta x => eta ⟨x.1, (Finset.mem_erase.mp x.2).2⟩) =
    finiteFreeIsingPMF hlo hhi (D.erase v) hE := by
  classical
  apply PMF.ext
  intro eta
  rw [PMF.map_apply, tsum_fintype]
  simp only [finiteFreeIsingPMF_apply]
  have hr (z : (D.erase v → IsingSpin) × IsingSpin) :
      (fun x : D.erase v => (finiteSpinEraseEquiv hv).symm z
        ⟨x.1, (Finset.mem_erase.mp x.2).2⟩) = z.1 :=
    congrArg Prod.fst ((finiteSpinEraseEquiv hv).apply_symm_apply z)
  calc
    _ = ∑ z : (D.erase v → IsingSpin) × IsingSpin,
        if eta = z.1 then freeCylinderWeight theta D
          (extendFiniteSpin D ((finiteSpinEraseEquiv hv).symm z)) else 0 := by
      symm
      refine Fintype.sum_equiv (finiteSpinEraseEquiv hv).symm _ _ ?_
      intro z
      simp only [hr]
    _ = ∑ s : IsingSpin, freeCylinderWeight theta D
        (Function.update (extendFiniteSpin (D.erase v) eta) v s) := by
      rw [Fintype.sum_prod_type, Finset.sum_comm]
      simp only [extendFiniteSpin_eraseEquiv_symm]
      simp
    _ = _ := freeCylinderWeight_sum_update_of_edges hlo hhi hpne hedges _

theorem finiteFreeIsingPMF_map_erase
    {d : ℕ} {D : Finset (TreeVertex d)} {v p : TreeVertex d} {theta : ℝ}
    (hlo : -1 ≤ theta) (hhi : theta ≤ 1) (hD : ConnectedFinset D)
    (hv : v ∈ D) (hp : p ∈ D) (hpv : treeAdj p v)
    (hplen : p.1.length < v.1.length) (hn : (D.erase v).Nonempty)
    (hmax : ∀ x ∈ D, x.1.length ≤ v.1.length) :
    (finiteFreeIsingPMF hlo hhi D hD).map
      (fun eta x => eta ⟨x.1, (Finset.mem_erase.mp x.2).2⟩) =
    finiteFreeIsingPMF hlo hhi (D.erase v)
      (connectedFinset_erase_of_max_length hD hv hn hmax) := by
  apply finiteFreeIsingPMF_map_erase_of_edges (p := p) hlo hhi hD hv
  · intro h
    subst p
    exact lt_irrefl _ hplen
  · exact inducedEdges_eq_insert_erase_of_max_length hv hp hpv hplen hmax

theorem HasFreeIsingLaw.restrict_eq_finiteFreeIsingPMF
    {d : ℕ} {theta : ℝ} {mu : MeasureTheory.Measure (TreeVertex d → IsingSpin)}
    (hmu : HasFreeIsingLaw theta mu) (hlo : -1 ≤ theta) (hhi : theta ≤ 1)
    (D : Finset (TreeVertex d)) (hD : ConnectedFinset D) :
    mu.map D.restrict = (finiteFreeIsingPMF hlo hhi D hD).toMeasure := by
  apply MeasureTheory.Measure.ext_of_singleton
  intro eta
  rw [hmu.restrict_atom D hD eta, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton eta)]
  rfl

end Problem367

end

end OAI
