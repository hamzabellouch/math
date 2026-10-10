import OAI.Probability.FreeIsing.Posterior.BranchObservationRegression
import OAI.Probability.FreeIsing.Trees.PathSideReroot

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367.PathSideBranches

def noisyRegionArray {d : ℕ} {A : Type*} (S : Set (TreeVertex d))
    (z : (TreeVertex d → IsingSpin) × (TreeVertex d → A)) :
    (S → IsingSpin) × (S → A) :=
  (S.domRestrict z.1, S.domRestrict z.2)

theorem measurable_noisyRegionArray {d : ℕ} {A : Type*} [MeasurableSpace A]
    (S : Set (TreeVertex d)) : Measurable (noisyRegionArray (A := A) S) := by
  exact (S.measurable_restrict.comp measurable_fst).prodMk
    (S.measurable_restrict.comp measurable_snd)

def decodeCone {d : ℕ} {A : Type*} (g : TreeAut d) (r : TreeVertex d) (c : Fin d)
    (hgeo : ∀ u : TreeVertex d, u ∈ cone r ↔ [c] <+: (g.toEquiv u).1)
    (p : (RootedBroadcast.BranchVertex c → IsingSpin) ×
      (RootedBroadcast.BranchVertex c → A)) :
    (cone r → IsingSpin) × (cone r → A) :=
  ((fun u => p.1 ⟨g.toEquiv u.1, (hgeo u.1).mp u.2⟩),
    fun u => p.2 ⟨g.toEquiv u.1, (hgeo u.1).mp u.2⟩)

theorem measurable_decodeCone {d : ℕ} {A : Type*} [MeasurableSpace A]
    (g : TreeAut d) (r : TreeVertex d) (c : Fin d)
    (hgeo : ∀ u : TreeVertex d, u ∈ cone r ↔ [c] <+: (g.toEquiv u).1) :
    Measurable (decodeCone (A := A) g r c hgeo) := by
  unfold decodeCone
  fun_prop

theorem decodeCone_relabel {d : ℕ} {A : Type*}
    (g : TreeAut d) (r : TreeVertex d) (c : Fin d)
    (hgeo : ∀ u : TreeVertex d, u ∈ cone r ↔ [c] <+: (g.toEquiv u).1)
    (z : (TreeVertex d → IsingSpin) × (TreeVertex d → A)) :
    decodeCone g r c hgeo (noisyBranchArray c
      (Prod.map (relabel g) (relabel g) z)) = noisyRegionArray (cone r) z := by
  apply Prod.ext <;> funext u <;>
    simp [decodeCone, noisyBranchArray, noisyRegionArray, relabel]

def decodeConeComplement {d : ℕ} {A : Type*}
    (g : TreeAut d) (r : TreeVertex d) (c : Fin d)
    (hgeo : ∀ u : TreeVertex d, u ∈ cone r ↔ [c] <+: (g.toEquiv u).1)
    (p : NoisyRootOtherData A c) :
    ({u : TreeVertex d // u ∉ cone r} → IsingSpin) ×
      ({u : TreeVertex d // u ∉ cone r} → A) :=
  ((fun u => (noisyRootOtherDecode c p
      ⟨g.toEquiv u.1, fun h => u.2 ((hgeo u.1).mpr h)⟩).1),
    fun u => (noisyRootOtherDecode c p
      ⟨g.toEquiv u.1, fun h => u.2 ((hgeo u.1).mpr h)⟩).2)

theorem measurable_decodeConeComplement {d : ℕ} {A : Type*} [MeasurableSpace A]
    (g : TreeAut d) (r : TreeVertex d) (c : Fin d)
    (hgeo : ∀ u : TreeVertex d, u ∈ cone r ↔ [c] <+: (g.toEquiv u).1) :
    Measurable (decodeConeComplement (A := A) g r c hgeo) := by
  exact (Measurable.of_eval (fun vertex : {u : TreeVertex d // u ∉ cone r} =>
    (measurable_noisyRootOtherDecode c
      ⟨g.toEquiv vertex.1, fun hmem => vertex.2 ((hgeo vertex.1).mpr hmem)⟩).fst)).prodMk
    (Measurable.of_eval (fun vertex : {u : TreeVertex d // u ∉ cone r} =>
      (measurable_noisyRootOtherDecode c
        ⟨g.toEquiv vertex.1, fun hmem => vertex.2 ((hgeo vertex.1).mpr hmem)⟩).snd))

theorem decodeConeComplement_relabel {d : ℕ} {A : Type*}
    (g : TreeAut d) (r : TreeVertex d) (c : Fin d)
    (hgeo : ∀ u : TreeVertex d, u ∈ cone r ↔ [c] <+: (g.toEquiv u).1)
    (z : (TreeVertex d → IsingSpin) × (TreeVertex d → A)) :
    decodeConeComplement g r c hgeo (noisyRootOtherArray c
      (Prod.map (relabel g) (relabel g) z)) = noisyRegionArray (cone r)ᶜ z := by
  apply Prod.ext
  · funext u
    change (noisyRootOtherDecode c _ _).1 = _
    rw [noisyRootOtherDecode_array]
    simp [Prod.map, relabel, noisyRegionArray]
  · funext u
    change (noisyRootOtherDecode c _ _).2 = _
    rw [noisyRootOtherDecode_array]
    simp [Prod.map, relabel, noisyRegionArray]

end Problem367.PathSideBranches

namespace Problem367

open PathSideBranches

theorem HasFreeIsingLaw.condIndepFun_noisy_cone_complement
    {d : ℕ} {theta : ℝ} {A : Type*}
    [MeasurableSpace A] [StandardBorelSpace A]
    {μ : Measure (TreeVertex d → IsingSpin)} [IsFiniteMeasure μ]
    (hμ : HasFreeIsingLaw theta μ)
    (h0 : -1 ≤ theta) (h1 : theta ≤ 1)
    (ν : Measure A) [IsProbabilityMeasure ν]
    (r : TreeVertex d) (hr : r.1 ≠ []) :
    CondIndepFun
      ((inferInstance : MeasurableSpace IsingSpin).comap
        (fun z : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
          z.1 (parentVertex r)))
      ((measurable_pi_apply (parentVertex r)).comp measurable_fst).comap_le
      (noisyRegionArray (cone r)ᶜ) (noisyRegionArray (cone r))
      (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))) := by
  obtain ⟨g, c, hp, hc, hgeo⟩ := exists_reroot_cone r hr
  have hroot : g.toEquiv.symm (RootedBroadcast.root d) = parentVertex r := by
    apply g.toEquiv.injective
    rw [Equiv.apply_symm_apply, hp]
    rfl
  have h := (hμ.condIndepFun_relabel_noisy_root_others_branch h0 h1 ν g c).comp
    (measurable_decodeConeComplement g r c hgeo) (measurable_decodeCone g r c hgeo)
  classical
  simp only [hroot, Function.comp_def, decodeConeComplement_relabel,
    decodeCone_relabel] at h
  exact h

theorem HasFreeIsingLaw.condIndepFun_noisy_sideCone_complement
    {d : ℕ} {theta : ℝ} {A : Type*}
    [MeasurableSpace A] [StandardBorelSpace A]
    {μ : Measure (TreeVertex d → IsingSpin)} [IsFiniteMeasure μ]
    (hμ : HasFreeIsingLaw theta μ) (h0 : -1 ≤ theta) (h1 : theta ≤ 1)
    (ν : Measure A) [IsProbabilityMeasure ν]
    (hd : 3 ≤ d) (v : TreeVertex d) (i : Fin v.1.length) :
    CondIndepFun
      (isingSpinMeasurable.comap
        (fun z : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
          z.1 (ConnectedHull.takeVertex v (i.1 + 1))))
      ((measurable_pi_apply (ConnectedHull.takeVertex v (i.1 + 1))).comp
        measurable_fst).comap_le
      (noisyRegionArray (cone (sideVertex hd v i))ᶜ)
      (noisyRegionArray (cone (sideVertex hd v i)))
      (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))) := by
  have hr : (sideVertex hd v i).1 ≠ [] := by
    intro h
    have hl := sideVertex_length hd v i
    rw [h] at hl
    simp at hl
  have h := hμ.condIndepFun_noisy_cone_complement h0 h1 ν (sideVertex hd v i) hr
  simpa only [parent_sideVertex] using h

end Problem367

end

end OAI
