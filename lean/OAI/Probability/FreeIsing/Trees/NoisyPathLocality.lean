import OAI.Probability.FreeIsing.Trees.NoisyConeSeparation
import OAI.Probability.FreeIsing.Trees.PathSideLocality

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367.PathSideBranches

@[implicit_reducible] def noisyRegionSigma {d : ℕ} {A : Type*}
    [MeasurableSpace A] (S : Set (TreeVertex d)) :
    MeasurableSpace ((TreeVertex d → IsingSpin) × (TreeVertex d → A)) :=
  MeasurableSpace.comap (noisyRegionArray (A := A) S) inferInstance

def restrictNoisyRegion {d : ℕ} {A : Type*} {S T : Set (TreeVertex d)}
    (hST : S ⊆ T) (p : (T → IsingSpin) × (T → A)) :
    (S → IsingSpin) × (S → A) :=
  ((fun u => p.1 ⟨u.1, hST u.2⟩), fun u => p.2 ⟨u.1, hST u.2⟩)

theorem measurable_restrictNoisyRegion {d : ℕ} {A : Type*} [MeasurableSpace A]
    {S T : Set (TreeVertex d)} (hST : S ⊆ T) :
    Measurable (restrictNoisyRegion (A := A) hST) := by
  unfold restrictNoisyRegion
  fun_prop

@[simp] theorem restrictNoisyRegion_array {d : ℕ} {A : Type*}
    {S T : Set (TreeVertex d)} (hST : S ⊆ T)
    (z : (TreeVertex d → IsingSpin) × (TreeVertex d → A)) :
    restrictNoisyRegion hST (noisyRegionArray T z) = noisyRegionArray S z := rfl

theorem measurable_noisyRegionArray_of_subset {d : ℕ} {A : Type*}
    [MeasurableSpace A] {S T : Set (TreeVertex d)} (hST : S ⊆ T) :
    Measurable[noisyRegionSigma (A := A) T] (noisyRegionArray (A := A) S) := by
  exact (measurable_restrictNoisyRegion hST).comp
    (comap_measurable (noisyRegionArray (A := A) T))

theorem noisyRegionSigma_mono {d : ℕ} {A : Type*} [MeasurableSpace A]
    {S T : Set (TreeVertex d)} (hST : S ⊆ T) :
    noisyRegionSigma (A := A) S ≤ noisyRegionSigma (A := A) T :=
  (measurable_noisyRegionArray_of_subset (A := A) hST).comap_le

theorem noisyRegionSigma_le {d : ℕ} {A : Type*} [MeasurableSpace A]
    (S : Set (TreeVertex d)) :
    noisyRegionSigma (A := A) S ≤
      (inferInstance : MeasurableSpace ((TreeVertex d → IsingSpin) × (TreeVertex d → A))) :=
  (measurable_noisyRegionArray S).comap_le

theorem measurable_later_noisy_forward_observable {d : ℕ} {A C : Type*}
    [MeasurableSpace A] [MeasurableSpace C] (hd : 3 ≤ d) (v : TreeVertex d)
    {i j : Fin v.1.length} (hij : i < j)
    (F : (cone (ConnectedHull.takeVertex v (j.1 + 1)) → IsingSpin) ×
      (cone (ConnectedHull.takeVertex v (j.1 + 1)) → A) → C)
    (hF : Measurable F) :
    Measurable[noisyRegionSigma (A := A) (cone (sideVertex hd v i))ᶜ]
      (F ∘ noisyRegionArray (cone (ConnectedHull.takeVertex v (j.1 + 1)))) :=
  hF.comp (measurable_noisyRegionArray_of_subset
    (later_forward_subset_side_complement hd v hij))

theorem measurable_later_noisy_forward_product {d : ℕ} {A : Type*}
    [MeasurableSpace A] (hd : 3 ≤ d) (v : TreeVertex d) (i : Fin v.1.length)
    (s : Finset (Fin v.1.length))
    (F : ∀ j : Fin v.1.length,
      (cone (ConnectedHull.takeVertex v (j.1 + 1)) → IsingSpin) ×
        (cone (ConnectedHull.takeVertex v (j.1 + 1)) → A) → ℝ)
    (hF : ∀ j ∈ s, Measurable (F j)) (hs : ∀ j ∈ s, i < j) :
    Measurable[noisyRegionSigma (A := A) (cone (sideVertex hd v i))ᶜ]
      (fun z : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
        ∏ j ∈ s, F j (noisyRegionArray (cone (ConnectedHull.takeVertex v (j.1 + 1))) z)) := by
  let : MeasurableSpace ((TreeVertex d → IsingSpin) × (TreeVertex d → A)) :=
    noisyRegionSigma (A := A) (cone (sideVertex hd v i))ᶜ
  exact s.measurable_fun_prod (fun j hj =>
    measurable_later_noisy_forward_observable hd v (hs j hj) (F j) (hF j hj))

theorem measurable_path_spin_outside_sideCone {d : ℕ} {A : Type*}
    [MeasurableSpace A] (hd : 3 ≤ d) (v : TreeVertex d)
    (i : Fin v.1.length) (k : ℕ) :
    Measurable[noisyRegionSigma (A := A) (cone (sideVertex hd v i))ᶜ]
      (fun z : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
        z.1 (ConnectedHull.takeVertex v k)) := by
  exact ((measurable_pi_apply
    (⟨ConnectedHull.takeVertex v k, path_vertex_not_mem_sideCone hd v i k⟩ :
      {u : TreeVertex d // u ∉ cone (sideVertex hd v i)})).comp measurable_fst).comp
        (comap_measurable (noisyRegionArray (A := A) (cone (sideVertex hd v i))ᶜ))

end Problem367.PathSideBranches

namespace Problem367

open PathSideBranches

theorem HasFreeIsingLaw.condIndepFun_noisy_cone_observables
    {d : ℕ} {theta : ℝ} {A B C : Type*}
    [MeasurableSpace A] [StandardBorelSpace A]
    [MeasurableSpace B] [StandardBorelSpace B] [Nonempty B]
    [MeasurableSpace C] [StandardBorelSpace C] [Nonempty C]
    {μ : Measure (TreeVertex d → IsingSpin)} [IsFiniteMeasure μ]
    (hμ : HasFreeIsingLaw theta μ) (h0 : -1 ≤ theta) (h1 : theta ≤ 1)
    (ν : Measure A) [IsProbabilityMeasure ν]
    (r : TreeVertex d) (hr : r.1 ≠ [])
    (X : (TreeVertex d → IsingSpin) × (TreeVertex d → A) → B)
    (Q : (TreeVertex d → IsingSpin) × (TreeVertex d → A) → C)
    (hX : Measurable[noisyRegionSigma (A := A) (cone r)ᶜ] X)
    (hQ : Measurable[noisyRegionSigma (A := A) (cone r)] Q) :
    CondIndepFun
      (isingSpinMeasurable.comap
        (fun z : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
          z.1 (parentVertex r)))
      ((measurable_pi_apply (parentVertex r)).comp measurable_fst).comap_le X Q
      (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))) := by
  obtain ⟨F, hF, rfl⟩ := hX.exists_eq_measurable_comp
  obtain ⟨G, hG, rfl⟩ := hQ.exists_eq_measurable_comp
  exact (hμ.condIndepFun_noisy_cone_complement h0 h1 ν r hr).comp hF hG

theorem HasFreeIsingLaw.condIndepFun_noisy_sideCone_observables
    {d : ℕ} {theta : ℝ} {A B C : Type*}
    [MeasurableSpace A] [StandardBorelSpace A]
    [MeasurableSpace B] [StandardBorelSpace B] [Nonempty B]
    [MeasurableSpace C] [StandardBorelSpace C] [Nonempty C]
    {μ : Measure (TreeVertex d → IsingSpin)} [IsFiniteMeasure μ]
    (hμ : HasFreeIsingLaw theta μ) (h0 : -1 ≤ theta) (h1 : theta ≤ 1)
    (ν : Measure A) [IsProbabilityMeasure ν]
    (hd : 3 ≤ d) (v : TreeVertex d) (i : Fin v.1.length)
    (X : (TreeVertex d → IsingSpin) × (TreeVertex d → A) → B)
    (Q : (TreeVertex d → IsingSpin) × (TreeVertex d → A) → C)
    (hX : Measurable[noisyRegionSigma (A := A) (cone (sideVertex hd v i))ᶜ] X)
    (hQ : Measurable[noisyRegionSigma (A := A) (cone (sideVertex hd v i))] Q) :
    CondIndepFun
      (isingSpinMeasurable.comap
        (fun z : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
          z.1 (ConnectedHull.takeVertex v (i.1 + 1))))
      ((measurable_pi_apply (ConnectedHull.takeVertex v (i.1 + 1))).comp
        measurable_fst).comap_le X Q
      (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))) := by
  obtain ⟨F, hF, rfl⟩ := hX.exists_eq_measurable_comp
  obtain ⟨G, hG, rfl⟩ := hQ.exists_eq_measurable_comp
  exact (hμ.condIndepFun_noisy_sideCone_complement h0 h1 ν hd v i).comp hF hG

end Problem367

end

end OAI
