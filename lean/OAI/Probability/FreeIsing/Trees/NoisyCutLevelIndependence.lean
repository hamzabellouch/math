import OAI.Probability.FreeIsing.Conditioning.DiscreteConditioning
import OAI.Probability.FreeIsing.Estimates.DependentInfinitePiPair
import OAI.Probability.FreeIsing.Spins.Moments
import OAI.Probability.FreeIsing.Trees.CutLevelBranchIndependence

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367.RootedBroadcast

local instance noisyCutLevelMeasurableSingletonIsingSpin :
    MeasurableSingletonClass IsingSpin := ⟨fun _ => trivial⟩
local instance noisyCutLevelIsProbabilityLabelMeasure (d : ℕ) :
    IsProbabilityMeasure (labelMeasure d) := by
  unfold labelMeasure
  infer_instance

theorem map_cutSpins_cutLabels_noises {d : ℕ} {A : Type*}
    [MeasurableSpace A] (theta : ℝ) (n : ℕ)
    (ν : TreeVertex d → Measure A) [∀ v, IsProbabilityMeasure (ν v)] :
    ((labelMeasure d).prod (Measure.infinitePi ν)).map
      (fun z : (TreeVertex d → ℝ) × (TreeVertex d → A) =>
        (cutSpins theta n z.1, fun c : TreeShell d n =>
          (cutLabels z.1 c, fun v : DescendantVertex c.1 => z.2 v.1))) =
      ((labelMeasure d).map (cutSpins theta n)).prod
        (Measure.infinitePi (fun c : TreeShell d n =>
          (Measure.infinitePi (fun _ : StrictDescendantVertex c.1 => uniform01)).prod
            (Measure.infinitePi (fun v : DescendantVertex c.1 => ν v.1)))) := by
  let S := TreeShell d n → IsingSpin
  let R := (c : TreeShell d n) → StrictDescendantVertex c.1 → ℝ
  let N := (c : TreeShell d n) → DescendantVertex c.1 → A
  let rho := (labelMeasure d).map (cutSpins theta n)
  let muR := Measure.infinitePi (fun c : TreeShell d n =>
    Measure.infinitePi (fun _ : StrictDescendantVertex c.1 => uniform01))
  let muN := Measure.infinitePi (fun c : TreeShell d n =>
    Measure.infinitePi (fun v : DescendantVertex c.1 => ν v.1))
  let muP := Measure.infinitePi (fun c : TreeShell d n =>
    (Measure.infinitePi (fun _ : StrictDescendantVertex c.1 => uniform01)).prod
      (Measure.infinitePi (fun v : DescendantVertex c.1 => ν v.1)))
  let f : (TreeVertex d → ℝ) → S × R := fun U => (cutSpins theta n U, cutLabels U)
  let g : (TreeVertex d → A) → N := fun W _ v => W v.1
  let p : R × N → ((c : TreeShell d n) →
      (StrictDescendantVertex c.1 → ℝ) × (DescendantVertex c.1 → A)) :=
    fun z c => (z.1 c, z.2 c)
  have hf : MeasurePreserving f (labelMeasure d) (rho.prod muR) :=
    ⟨(measurable_cutSpins d theta n).prodMk (measurable_cutLabels d n),
      map_cutSpins_cutLabels d theta n⟩
  have hg : MeasurePreserving g (Measure.infinitePi ν) muN := by
    refine ⟨by fun_prop, ?_⟩
    exact infinitePi_map_disjoint_family ν
      (fun c : TreeShell d n => {v : TreeVertex d | c.1.1 <+: v.1})
      cutLevel_descendants_disjoint
  have hp : MeasurePreserving p (muR.prod muN) muP :=
    ⟨by fun_prop, infinitePi_map_pair_dependent_arrays
      (fun c : TreeShell d n => Measure.infinitePi
        (fun _ : StrictDescendantVertex c.1 => uniform01))
      (fun c : TreeShell d n => Measure.infinitePi
        (fun v : DescendantVertex c.1 => ν v.1))⟩
  have h := ((MeasurePreserving.id rho).prod hp).comp
    ((measurePreserving_prodAssoc rho muR muN).comp (hf.prod hg))
  exact h.map_eq

theorem iCondIndepFun_noisy_factor_cutLevel {d : ℕ} {A : Type*}
    [MeasurableSpace A] [StandardBorelSpace A]
    (theta : ℝ) (n : ℕ) (ν : TreeVertex d → Measure A)
    [∀ v, IsProbabilityMeasure (ν v)] :
    iCondIndepFun
      ((inferInstance : MeasurableSpace (TreeShell d n → IsingSpin)).comap
        (fun z : (TreeVertex d → ℝ) × (TreeVertex d → A) => cutSpins theta n z.1))
      ((measurable_cutSpins d theta n).comp measurable_fst).comap_le
      (fun (c : TreeShell d n) (z : (TreeVertex d → ℝ) × (TreeVertex d → A)) =>
        ((fun v : DescendantVertex c.1 => factor theta z.1 v.1),
          fun v : DescendantVertex c.1 => z.2 v.1))
      ((labelMeasure d).prod (Measure.infinitePi ν)) := by
  let S := TreeShell d n → IsingSpin
  let R := (c : TreeShell d n) →
    (StrictDescendantVertex c.1 → ℝ) × (DescendantVertex c.1 → A)
  let rho := (labelMeasure d).map (cutSpins theta n)
  let muP := Measure.infinitePi (fun c : TreeShell d n =>
    (Measure.infinitePi (fun _ : StrictDescendantVertex c.1 => uniform01)).prod
      (Measure.infinitePi (fun v : DescendantVertex c.1 => ν v.1)))
  let e : (TreeVertex d → ℝ) × (TreeVertex d → A) → S × R :=
    fun z => (cutSpins theta n z.1,
      fun c => (cutLabels z.1 c, fun v => z.2 v.1))
  have he : MeasurePreserving e ((labelMeasure d).prod (Measure.infinitePi ν))
      (rho.prod muP) :=
    ⟨((measurable_cutSpins d theta n).comp measurable_fst).prodMk
      (by unfold cutLabels; fun_prop),
      map_cutSpins_cutLabels_noises theta n ν⟩
  let F := fun (c : TreeShell d n)
      (p : S × ((StrictDescendantVertex c.1 → ℝ) × (DescendantVertex c.1 → A))) =>
    (coneFactor theta c.1 (p.1 c, p.2.1), p.2.2)
  have hF : ∀ c, Measurable (F c) := by
    intro c
    exact ((measurable_coneFactor theta c.1).comp
      (((measurable_pi_apply c).comp measurable_fst).prodMk
        (measurable_fst.comp measurable_snd))).prodMk
      (measurable_snd.comp measurable_snd)
  have hbase := iCondIndepFun_latent_infinitePi rho
    (fun c : TreeShell d n =>
      (Measure.infinitePi (fun _ : StrictDescendantVertex c.1 => uniform01)).prod
        (Measure.infinitePi (fun v : DescendantVertex c.1 => ν v.1))) F hF
  have hpull := iCondIndepFun_comp_measurePreserving
    ((labelMeasure d).prod (Measure.infinitePi ν)) (rho.prod muP) e he
    ((inferInstance : MeasurableSpace S).comap Prod.fst) measurable_fst.comap_le
    (fun c => show Measurable (fun p : S × R => F c (p.1, p.2 c)) from
      (hF c).comp (measurable_fst.prodMk
        ((measurable_pi_apply c).comp measurable_snd))) hbase
  have hfun : (fun c => (fun p : S × R => F c (p.1, p.2 c)) ∘ e) =
      (fun (c : TreeShell d n) (z : (TreeVertex d → ℝ) × (TreeVertex d → A)) =>
        ((fun v : DescendantVertex c.1 => factor theta z.1 v.1),
          fun v : DescendantVertex c.1 => z.2 v.1)) := by
    funext c z
    apply Prod.ext
    · exact (factor_cone_representation theta c.1 z.1).symm
    · rfl
  rw [hfun] at hpull
  simpa only [MeasurableSpace.comap_comp, Function.comp_def, e] using hpull

end Problem367.RootedBroadcast

namespace Problem367

local instance noisyCutLevelFreeIsingMeasurableSingletonIsingSpin :
    MeasurableSingletonClass IsingSpin := ⟨fun _ => trivial⟩

theorem freeIsingMeasure_iCondIndepFun_noisy_cutLevel {d : ℕ} {A : Type*}
    [MeasurableSpace A] [StandardBorelSpace A]
    (theta : ℝ) (n : ℕ) (ν : TreeVertex d → Measure A)
    [∀ v, IsProbabilityMeasure (ν v)] :
    iCondIndepFun
      ((inferInstance : MeasurableSpace (TreeShell d n → IsingSpin)).comap
        (fun z : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
          fun c : TreeShell d n => z.1 c.1))
      (by fun_prop : Measurable
        (fun z : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
          fun c : TreeShell d n => z.1 c.1)).comap_le
      (fun (c : TreeShell d n) (z : (TreeVertex d → IsingSpin) × (TreeVertex d → A)) =>
        ((fun v : RootedBroadcast.DescendantVertex c.1 => z.1 v.1),
          fun v : RootedBroadcast.DescendantVertex c.1 => z.2 v.1))
      ((freeIsingMeasure d theta).prod (Measure.infinitePi ν)) := by
  let : IsProbabilityMeasure (labelMeasure d) := by
    unfold labelMeasure
    infer_instance
  have hf : MeasurePreserving (RootedBroadcast.factor theta)
      (labelMeasure d) (freeIsingMeasure d theta) :=
    ⟨RootedBroadcast.measurable_factor d theta, rfl⟩
  have he := hf.prod (MeasurePreserving.id (Measure.infinitePi ν))
  apply iCondIndepFun_of_comp_measurePreserving
    ((labelMeasure d).prod (Measure.infinitePi ν))
    ((freeIsingMeasure d theta).prod (Measure.infinitePi ν))
    (Prod.map (RootedBroadcast.factor theta) id) he
    ((inferInstance : MeasurableSpace (TreeShell d n → IsingSpin)).comap
      (fun z : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
        fun c : TreeShell d n => z.1 c.1))
    (by fun_prop : Measurable
      (fun z : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
        fun c : TreeShell d n => z.1 c.1)).comap_le
    (fun _ => by fun_prop)
  simp only [MeasurableSpace.comap_comp, Function.comp_def, Prod.map_fst, Prod.map_snd,
    id_eq]
  exact RootedBroadcast.iCondIndepFun_noisy_factor_cutLevel theta n ν

theorem HasFreeIsingLaw.iCondIndepFun_noisy_cutLevel {d : ℕ} {theta : ℝ}
    {A : Type*} [MeasurableSpace A] [StandardBorelSpace A]
    {μ : Measure (TreeVertex d → IsingSpin)} [IsFiniteMeasure μ]
    (hμ : HasFreeIsingLaw theta μ) (h0 : -1 ≤ theta) (h1 : theta ≤ 1)
    (n : ℕ) (ν : TreeVertex d → Measure A) [∀ v, IsProbabilityMeasure (ν v)] :
    iCondIndepFun
      ((inferInstance : MeasurableSpace (TreeShell d n → IsingSpin)).comap
        (fun z : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
          fun c : TreeShell d n => z.1 c.1))
      (by fun_prop : Measurable
        (fun z : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
          fun c : TreeShell d n => z.1 c.1)).comap_le
      (fun (c : TreeShell d n) (z : (TreeVertex d → IsingSpin) × (TreeVertex d → A)) =>
        ((fun v : RootedBroadcast.DescendantVertex c.1 => z.1 v.1),
          fun v : RootedBroadcast.DescendantVertex c.1 => z.2 v.1))
      (μ.prod (Measure.infinitePi ν)) := by
  have heq := hμ.eq_freeIsingMeasure h0 h1
  subst μ
  exact freeIsingMeasure_iCondIndepFun_noisy_cutLevel theta n ν

theorem HasFreeIsingLaw.iCondIndepFun_cutLevel_observables {d : ℕ} {theta : ℝ}
    {A : Type*} [MeasurableSpace A] [StandardBorelSpace A]
    {μ : Measure (TreeVertex d → IsingSpin)} [IsFiniteMeasure μ]
    (hμ : HasFreeIsingLaw theta μ) (h0 : -1 ≤ theta) (h1 : theta ≤ 1)
    (n : ℕ) (ν : TreeVertex d → Measure A) [∀ v, IsProbabilityMeasure (ν v)]
    {B : TreeShell d n → Type*} [∀ c, MeasurableSpace (B c)]
    (F : ∀ c : TreeShell d n, (RootedBroadcast.DescendantVertex c.1 → IsingSpin) ×
      (RootedBroadcast.DescendantVertex c.1 → A) → B c)
    (hF : ∀ c, Measurable (F c)) :
    iCondIndepFun
      ((inferInstance : MeasurableSpace (TreeShell d n → IsingSpin)).comap
        (fun z : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
          fun c : TreeShell d n => z.1 c.1))
      (by fun_prop : Measurable
        (fun z : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
          fun c : TreeShell d n => z.1 c.1)).comap_le
      (fun (c : TreeShell d n) (z : (TreeVertex d → IsingSpin) × (TreeVertex d → A)) =>
        F c ((fun v => z.1 v.1), fun v => z.2 v.1))
      (μ.prod (Measure.infinitePi ν)) :=
  (hμ.iCondIndepFun_noisy_cutLevel h0 h1 n ν).comp F hF

theorem HasFreeIsingLaw.iIndepFun_cutLevel_observables_cond {d : ℕ} {theta : ℝ}
    {A : Type*} [MeasurableSpace A] [StandardBorelSpace A]
    {μ : Measure (TreeVertex d → IsingSpin)} [IsFiniteMeasure μ]
    (hμ : HasFreeIsingLaw theta μ) (h0 : -1 ≤ theta) (h1 : theta ≤ 1)
    (n : ℕ) (ν : TreeVertex d → Measure A) [∀ v, IsProbabilityMeasure (ν v)]
    {B : TreeShell d n → Type*} [∀ c, MeasurableSpace (B c)]
    (F : ∀ c : TreeShell d n, (RootedBroadcast.DescendantVertex c.1 → IsingSpin) ×
      (RootedBroadcast.DescendantVertex c.1 → A) → B c)
    (hF : ∀ c, Measurable (F c)) (s : TreeShell d n → IsingSpin)
    (hs : (μ.prod (Measure.infinitePi ν))
      {z | (fun c : TreeShell d n => z.1 c.1) = s} ≠ 0) :
    iIndepFun
      (fun (c : TreeShell d n) (z : (TreeVertex d → IsingSpin) × (TreeVertex d → A)) =>
        F c ((fun v => z.1 v.1), fun v => z.2 v.1))
      (μ.prod (Measure.infinitePi ν))[|{z | (fun c : TreeShell d n => z.1 c.1) = s}] := by
  exact iIndepFun_cond_fiber_of_iCondIndepFun
    (by fun_prop) (fun c => (hF c).comp (by fun_prop))
    (hμ.iCondIndepFun_cutLevel_observables h0 h1 n ν F hF) s hs

end Problem367

end

end OAI
