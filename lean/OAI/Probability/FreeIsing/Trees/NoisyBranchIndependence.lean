import OAI.Probability.FreeIsing.Estimates.InfinitePiPair
import OAI.Probability.FreeIsing.Spins.Moments
import OAI.Probability.FreeIsing.Trees.FreeIsingBranchFamily

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367
namespace RootedBroadcast

theorem map_root_branch_family_of_sampler {d : ℕ} {A S : Type*}
    [MeasurableSpace A] [MeasurableSpace S]
    (ν : TreeVertex d → Measure A) [∀ v, IsProbabilityMeasure (ν v)]
    (f : A → S) (hf : Measurable f) :
    (Measure.infinitePi ν).map (fun U => (f (U (root d)),
      fun c : Fin d => fun v : BranchVertex c => U v.val)) =
      ((ν (root d)).map f).prod (Measure.infinitePi (fun c : Fin d =>
        Measure.infinitePi (fun v : BranchVertex c => ν v.val))) := by
  let F : (NonrootVertex d → A) → (∀ c : Fin d, BranchVertex c → A) :=
    fun Y c v => Y (branchEmbedding c v)
  have hF : Measurable F := by fun_prop
  have hind := (LabelDecomposition.indepFun_coordinate_rest ν (root d)).comp hf hF
  have hB : Measurable (fun U : TreeVertex d → A => f (U (root d))) :=
    hf.comp (measurable_pi_apply (root d))
  have hY : Measurable (fun U : TreeVertex d → A =>
      fun c : Fin d => fun v : BranchVertex c => U v.val) := by fun_prop
  have hroot : (Measure.infinitePi ν).map (fun U => f (U (root d))) =
      (ν (root d)).map f := by
    change (Measure.infinitePi ν).map (f ∘ (fun U => U (root d))) = _
    rw [← Measure.map_map hf (measurable_pi_apply (root d)), Measure.infinitePi_map_eval]
  change IndepFun (fun U : TreeVertex d → A => f (U (root d)))
    (fun U => fun c : Fin d => fun v : BranchVertex c => U v.val)
    (Measure.infinitePi ν) at hind
  rw [hind.map_prod_eq_prod_map_map hB.aemeasurable hY.aemeasurable, hroot]
  congr 1
  exact infinitePi_map_disjoint_family ν
    (fun c : Fin d => {v : TreeVertex d | [c] <+: v.val})
    (fun _ _ hce => branch_disjoint hce)

theorem iCondIndepFun_root_branch_observables {d : ℕ} {A S : Type*}
    [MeasurableSpace A] [mS : MeasurableSpace S]
    [StandardBorelSpace A] [StandardBorelSpace S]
    {B : Fin d → Type*} [∀ c, MeasurableSpace (B c)]
    (ν : TreeVertex d → Measure A) [∀ v, IsProbabilityMeasure (ν v)]
    (f : A → S) (hf : Measurable f)
    (F : ∀ c, S × (BranchVertex c → A) → B c) (hF : ∀ c, Measurable (F c)) :
    iCondIndepFun
      (mS.comap (fun U : TreeVertex d → A => f (U (root d))))
      (hf.comp (measurable_pi_apply (root d))).comap_le
      (fun c U => F c (f (U (root d)), fun v => U v.val))
      (Measure.infinitePi ν) := by
  let e : (TreeVertex d → A) → S × (∀ c : Fin d, BranchVertex c → A) :=
    fun U => (f (U (root d)), fun c v => U v.val)
  let ρ := ((ν (root d)).map f).prod (Measure.infinitePi (fun c : Fin d =>
    Measure.infinitePi (fun v : BranchVertex c => ν v.val)))
  have he : MeasurePreserving e (Measure.infinitePi ν) ρ :=
    ⟨(hf.comp (measurable_pi_apply (root d))).prodMk (by fun_prop),
      map_root_branch_family_of_sampler ν f hf⟩
  have hbase := iCondIndepFun_latent_infinitePi ((ν (root d)).map f)
    (fun c : Fin d => Measure.infinitePi (fun v : BranchVertex c => ν v.val)) F hF
  have hpull := iCondIndepFun_comp_measurePreserving (Measure.infinitePi ν) ρ e he
    (mS.comap Prod.fst) measurable_fst.comap_le
    (fun c => show Measurable (fun z : S × (∀ c : Fin d, BranchVertex c → A) =>
      F c (z.1, z.2 c)) from by fun_prop) hbase
  simpa only [MeasurableSpace.comap_comp, Function.comp_def, e] using hpull

theorem map_noisyBroadcast {d : ℕ} {A : Type*} [MeasurableSpace A]
    (theta : ℝ) (ν : TreeVertex d → Measure A)
    [∀ v, IsProbabilityMeasure (ν v)] :
    (Measure.infinitePi (fun v => uniform01.prod (ν v))).map
      (fun U : TreeVertex d → ℝ × A =>
        (factor theta (fun v => (U v).1), fun v => (U v).2)) =
      (freeIsingMeasure d theta).prod (Measure.infinitePi ν) := by
  calc
    _ = ((Measure.infinitePi (fun v => uniform01.prod (ν v))).map
        (fun U : TreeVertex d → ℝ × A =>
          ((fun v => (U v).1), fun v => (U v).2))).map
        (Prod.map (factor theta) id) := by
      rw [Measure.map_map ((measurable_factor d theta).prodMap measurable_id) (by fun_prop)]
      rfl
    _ = _ := by
      rw [infinitePi_map_split_pairs, ← Measure.map_prod_map _ _
        (measurable_factor d theta) measurable_id, Measure.map_id]
      rfl

local instance : MeasurableSingletonClass IsingSpin := ⟨fun _ => trivial⟩

theorem iCondIndepFun_noisy_factor_branches {d : ℕ} {A : Type*}
    [MeasurableSpace A] [StandardBorelSpace A]
    (theta : ℝ) (ν : TreeVertex d → Measure A)
    [∀ v, IsProbabilityMeasure (ν v)] :
    iCondIndepFun
      ((inferInstance : MeasurableSpace IsingSpin).comap
        (fun U : TreeVertex d → ℝ × A => fairSpin (U (root d)).1))
      ((measurable_fairSpin.comp measurable_fst).comp
        (measurable_pi_apply (root d))).comap_le
      (fun c U => ((fun v : BranchVertex c => factor theta (fun w => (U w).1) v.val),
        fun v : BranchVertex c => (U v.val).2))
      (Measure.infinitePi (fun v => uniform01.prod (ν v))) := by
  let F : ∀ c : Fin d, IsingSpin × (BranchVertex c → ℝ × A) →
      (BranchVertex c → IsingSpin) × (BranchVertex c → A) :=
    fun c p => (branchFactor theta c (p.1, fun v => (p.2 v).1),
      fun v => (p.2 v).2)
  have hF : ∀ c, Measurable (F c) := by
    intro c
    exact ((measurable_branchFactor theta c).comp
      (measurable_fst.prodMk (by fun_prop))).prodMk (by fun_prop)
  have h := iCondIndepFun_root_branch_observables
    (fun v => uniform01.prod (ν v)) (fun p : ℝ × A => fairSpin p.1)
    (measurable_fairSpin.comp measurable_fst) F hF
  have heq : (fun (c : Fin d) (U : TreeVertex d → ℝ × A) => F c (fairSpin (U (root d)).1, fun v => U v.val)) =
      (fun c U => ((fun v : BranchVertex c => factor theta (fun w => (U w).1) v.val),
        fun v : BranchVertex c => (U v.val).2)) := by
    funext c U
    apply Prod.ext
    · exact (factor_branch_representation theta c (fun w => (U w).1)).symm
    · rfl
  rw [heq] at h
  exact h

end RootedBroadcast

local instance : MeasurableSingletonClass IsingSpin := ⟨fun _ => trivial⟩

theorem freeIsingMeasure_iCondIndepFun_noisy_branches {d : ℕ} {A : Type*}
    [MeasurableSpace A] [StandardBorelSpace A]
    (theta : ℝ) (ν : TreeVertex d → Measure A)
    [∀ v, IsProbabilityMeasure (ν v)] :
    iCondIndepFun
      ((inferInstance : MeasurableSpace IsingSpin).comap
        (fun z : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
          z.1 (RootedBroadcast.root d)))
      ((measurable_pi_apply (RootedBroadcast.root d)).comp measurable_fst).comap_le
      (fun c z => ((fun v : RootedBroadcast.BranchVertex c => z.1 v.val),
        fun v : RootedBroadcast.BranchVertex c => z.2 v.val))
      ((freeIsingMeasure d theta).prod (Measure.infinitePi ν)) := by
  let e : (TreeVertex d → ℝ × A) →
      (TreeVertex d → IsingSpin) × (TreeVertex d → A) :=
    fun U => (RootedBroadcast.factor theta (fun v => (U v).1), fun v => (U v).2)
  have he : MeasurePreserving e (Measure.infinitePi (fun v => uniform01.prod (ν v)))
      ((freeIsingMeasure d theta).prod (Measure.infinitePi ν)) :=
    ⟨((RootedBroadcast.measurable_factor d theta).comp (by fun_prop)).prodMk
      (by fun_prop), RootedBroadcast.map_noisyBroadcast theta ν⟩
  apply iCondIndepFun_of_comp_measurePreserving
    (Measure.infinitePi (fun v => uniform01.prod (ν v)))
    ((freeIsingMeasure d theta).prod (Measure.infinitePi ν)) e he
    ((inferInstance : MeasurableSpace IsingSpin).comap
      (fun z : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
        z.1 (RootedBroadcast.root d)))
    ((measurable_pi_apply (RootedBroadcast.root d)).comp measurable_fst).comap_le
    (fun c => show Measurable (fun z : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
      ((fun v : RootedBroadcast.BranchVertex c => z.1 v.val),
        fun v : RootedBroadcast.BranchVertex c => z.2 v.val)) from by fun_prop)
  have hroot : (fun U : TreeVertex d → ℝ × A =>
      RootedBroadcast.factor theta (fun v => (U v).1) (RootedBroadcast.root d)) =
      (fun U => fairSpin (U (RootedBroadcast.root d)).1) := by
    funext U
    simp [RootedBroadcast.factor, RootedBroadcast.root,
      RootedBroadcast.ofNoise_root, RootedBroadcast.inputNoise]
  simpa only [MeasurableSpace.comap_comp, Function.comp_def, e, hroot] using
    RootedBroadcast.iCondIndepFun_noisy_factor_branches theta ν

theorem HasFreeIsingLaw.iCondIndepFun_noisy_branches {d : ℕ} {theta : ℝ}
    {A : Type*} [MeasurableSpace A] [StandardBorelSpace A]
    {μ : Measure (TreeVertex d → IsingSpin)} [IsFiniteMeasure μ]
    (hμ : HasFreeIsingLaw theta μ) (h0 : -1 ≤ theta) (h1 : theta ≤ 1)
    (ν : TreeVertex d → Measure A) [∀ v, IsProbabilityMeasure (ν v)] :
    iCondIndepFun
      ((inferInstance : MeasurableSpace IsingSpin).comap
        (fun z : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
          z.1 (RootedBroadcast.root d)))
      ((measurable_pi_apply (RootedBroadcast.root d)).comp measurable_fst).comap_le
      (fun c z => ((fun v : RootedBroadcast.BranchVertex c => z.1 v.val),
        fun v : RootedBroadcast.BranchVertex c => z.2 v.val))
      (μ.prod (Measure.infinitePi ν)) := by
  have heq := hμ.eq_freeIsingMeasure h0 h1
  subst μ
  exact freeIsingMeasure_iCondIndepFun_noisy_branches theta ν

theorem HasFreeIsingLaw.iCondIndepFun_branch_observables {d : ℕ} {theta : ℝ}
    {A : Type*} [MeasurableSpace A] [StandardBorelSpace A]
    {B : Fin d → Type*} [∀ c, MeasurableSpace (B c)]
    {μ : Measure (TreeVertex d → IsingSpin)} [IsFiniteMeasure μ]
    (hμ : HasFreeIsingLaw theta μ) (h0 : -1 ≤ theta) (h1 : theta ≤ 1)
    (ν : TreeVertex d → Measure A) [∀ v, IsProbabilityMeasure (ν v)]
    (F : ∀ c : Fin d, (RootedBroadcast.BranchVertex c → IsingSpin) ×
      (RootedBroadcast.BranchVertex c → A) → B c)
    (hF : ∀ c, Measurable (F c)) :
    iCondIndepFun
      ((inferInstance : MeasurableSpace IsingSpin).comap
        (fun z : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
          z.1 (RootedBroadcast.root d)))
      ((measurable_pi_apply (RootedBroadcast.root d)).comp measurable_fst).comap_le
      (fun c z => F c ((fun v => z.1 v.val), fun v => z.2 v.val))
      (μ.prod (Measure.infinitePi ν)) :=
  (hμ.iCondIndepFun_noisy_branches h0 h1 ν).comp F hF

theorem HasFreeIsingLaw.iCondIndepFun_planted_branch_observations
    {d : ℕ} {theta : ℝ} {A T : Type*}
    [MeasurableSpace A] [StandardBorelSpace A]
    {μ : Measure (TreeVertex d → IsingSpin)} [IsFiniteMeasure μ]
    (hμ : HasFreeIsingLaw theta μ) (h0 : -1 ≤ theta) (h1 : theta ≤ 1)
    (ν : TreeVertex d → Measure A) [∀ v, IsProbabilityMeasure (ν v)]
    (a : T → ℝ) (B : TreeVertex d → T → A → ℝ)
    (hB : ∀ v t, Measurable (B v t)) :
    iCondIndepFun
      ((inferInstance : MeasurableSpace IsingSpin).comap
        (fun z : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
          z.1 (RootedBroadcast.root d)))
      ((measurable_pi_apply (RootedBroadcast.root d)).comp measurable_fst).comap_le
      (fun c z => fun v : RootedBroadcast.BranchVertex c => fun t : T =>
        a t * (z.1 v.val).toReal + B v.val t (z.2 v.val))
      (μ.prod (Measure.infinitePi ν)) := by
  apply hμ.iCondIndepFun_branch_observables h0 h1 ν
    (fun c p => fun v : RootedBroadcast.BranchVertex c => fun t : T =>
      a t * (p.1 v).toReal + B v.val t (p.2 v))
  intro c
  apply Measurable.of_eval
  intro v
  apply Measurable.of_eval
  intro t
  exact ((measurable_spinToReal.comp ((measurable_pi_apply v).comp measurable_fst)).const_mul
    (a t)).add ((hB v.val t).comp ((measurable_pi_apply v).comp measurable_snd))

end Problem367

end

end OAI
