import OAI.Probability.DirectionalWalk.Model

namespace OAI

open MeasureTheory ProbabilityTheory Filter Preorder
open scoped ENNReal BigOperators Topology

namespace DirectionalZeroOne

noncomputable def walkInitialLaw {d : ℕ} (μ : Measure (Environment d)) (x : Site d) :
    Measure (State d) := μ.map (fun ω => (ω, x))

instance {d : ℕ} (μ : Measure (Environment d)) [IsProbabilityMeasure μ] (x : Site d) :
    IsProbabilityMeasure (walkInitialLaw μ x) := by
  apply probabilityMeasure_map
  exact (measurable_id.prodMk measurable_const).aemeasurable

noncomputable def walkStateLaw {d : ℕ} (μ : Measure (Environment d)) [IsProbabilityMeasure μ]
    (x : Site d) : Measure (ℕ → State d) :=
  Kernel.trajMeasure (X := fun _ => State d) (walkInitialLaw μ x) (historyKernel d)

instance {d : ℕ} (μ : Measure (Environment d)) [IsProbabilityMeasure μ] (x : Site d) :
    IsProbabilityMeasure (walkStateLaw μ x) := by
  unfold walkStateLaw
  infer_instance

lemma lintegral_transition {d : ℕ} (s : State d) (f : State d → ℝ≥0∞)
    (hf : Measurable f) :
    (∫⁻ t, f t ∂transition d s) =
      ∑ e, ENNReal.ofReal ((s.1 s.2).val e) * f (s.1, s.2 + stepVector e) := by
  change (∫⁻ t, f t ∂∑ e : Step d,
    ENNReal.ofReal ((s.1 s.2).val e) • Measure.dirac (s.1, s.2 + stepVector e)) = _
  rw [lintegral_finsetSum_measure]
  simp only [lintegral_smul_measure, lintegral_dirac' _ hf, smul_eq_mul]

lemma walkStateLaw_initial_history {d : ℕ} (μ : Measure (Environment d)) [IsProbabilityMeasure μ]
    (x : Site d) :
    (walkStateLaw μ x).map (Preorder.frestrictLe 0) =
      (walkInitialLaw μ x).map (MeasurableEquiv.piUnique (fun _ : Finset.Iic 0 => State d)).symm := by
  rw [walkStateLaw, Kernel.trajMeasure, Measure.map_comp _ _ (measurable_frestrictLe _),
    Kernel.traj_map_frestrictLe, Kernel.partialTraj_self, Measure.id_comp]

lemma walkStateLaw_initial {d : ℕ} (μ : Measure (Environment d)) [IsProbabilityMeasure μ]
    (x : Site d) : (walkStateLaw μ x).map (fun z => z 0) = walkInitialLaw μ x := by
  let e := MeasurableEquiv.piUnique (fun _ : Finset.Iic 0 => State d)
  have h : (fun z : ℕ → State d => z 0) = e ∘ Preorder.frestrictLe 0 := by
    funext z
    rfl
  rw [h, ← Measure.map_map e.measurable (measurable_frestrictLe 0), walkStateLaw_initial_history]
  exact e.symm.map_symm_map

lemma walkStateLaw_one_step {d : ℕ} (μ : Measure (Environment d)) [IsProbabilityMeasure μ]
    (x : Site d) (n : ℕ)
    (f : ((i : Finset.Iic n) → State d) × State d → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ z, f (Preorder.frestrictLe n z, z (n + 1)) ∂walkStateLaw μ x) =
      ∫⁻ z, ∫⁻ t, f (Preorder.frestrictLe n z, t) ∂transition d (z n) ∂walkStateLaw μ x := by
  have hm : Measurable (fun z : ℕ → State d => (Preorder.frestrictLe n z, z (n+1))) :=
    (measurable_frestrictLe n).prodMk (measurable_pi_apply _)
  rw [← lintegral_map hf hm]
  unfold walkStateLaw
  rw [← Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure,
    Measure.lintegral_compProd hf]
  rw [lintegral_map]
  · rfl
  · exact hf.lintegral_kernel_prod_right'
  · exact measurable_frestrictLe n

noncomputable def entryWeight {d : ℕ} (ω : Environment d) (x y : Site d) : ℝ≥0∞ :=
  ∑ e : Step d, if x + stepVector e = y then ENNReal.ofReal ((ω x).val e) else 0

lemma measurable_entryWeight {d : ℕ} (x y : Site d) :
    Measurable (fun ω : Environment d => entryWeight ω x y) := by
  apply Finset.measurable_sum
  intro e he
  split_ifs
  · exact ((measurable_pi_apply e).comp
      (measurable_subtype_coe.comp (measurable_pi_apply x))).ennreal_ofReal
  · exact measurable_const

def prefixMatches {d : ℕ} (n : ℕ) (γ : ℕ → Site d) (z : ℕ → State d) : Prop :=
  ∀ i ≤ n, (z i).2 = γ i

noncomputable def prefixObservable {d : ℕ} (n : ℕ) (γ : ℕ → Site d)
    (f : Environment d → ℝ≥0∞) (z : ℕ → State d) : ℝ≥0∞ := by
  classical
  exact if prefixMatches n γ z then f (z n).1 else 0

lemma measurableSet_prefixMatches {d : ℕ} (n : ℕ) (γ : ℕ → Site d) :
    MeasurableSet {z : ℕ → State d | prefixMatches n γ z} := by
  simp only [prefixMatches, Set.ofPred_forall]
  exact MeasurableSet.iInter (fun i => MeasurableSet.iInter (fun _ =>
    measurableSet_eq_fun (measurable_snd.comp (measurable_pi_apply i)) measurable_const))

lemma measurable_prefixObservable {d : ℕ} (n : ℕ) (γ : ℕ → Site d)
    (f : Environment d → ℝ≥0∞) (hf : Measurable f) :
    Measurable (prefixObservable n γ f) := by
  exact (hf.comp (measurable_fst.comp (measurable_pi_apply n))).ite
    (measurableSet_prefixMatches n γ) measurable_const

lemma prefixMatches_succ {d : ℕ} (n : ℕ) (γ : ℕ → Site d) (z : ℕ → State d) :
    prefixMatches (n+1) γ z ↔ prefixMatches n γ z ∧ (z (n+1)).2 = γ (n+1) := by
  constructor
  · intro h
    exact ⟨fun i hi => h i (by omega), h _ le_rfl⟩
  · rintro ⟨h, hn⟩ i hi
    by_cases hin : i ≤ n
    · exact h i hin
    · have hie : i = n+1 := by omega
      simpa only [hie] using hn

noncomputable def pathWeight {d : ℕ} (n : ℕ) (γ : ℕ → Site d)
    (ω : Environment d) : ℝ≥0∞ :=
  ∏ i ∈ Finset.range n, entryWeight ω (γ i) (γ (i+1))

lemma measurable_pathWeight {d : ℕ} (n : ℕ) (γ : ℕ → Site d) :
    Measurable (pathWeight n γ) := by
  exact Finset.measurable_prod _ (fun i _ => measurable_entryWeight (γ i) (γ (i+1)))

lemma pathWeight_succ {d : ℕ} (n : ℕ) (γ : ℕ → Site d) (ω : Environment d) :
    pathWeight (n+1) γ ω = pathWeight n γ ω * entryWeight ω (γ n) (γ (n+1)) :=
  Finset.prod_range_succ _ n

lemma history_matches_iff {d : ℕ} (n : ℕ) (γ : ℕ → Site d) (z : ℕ → State d) :
    (∀ i : Finset.Iic n, (frestrictLe n z i).2 = γ i) ↔ prefixMatches n γ z := by
  constructor
  · intro h i hi
    exact h ⟨i, Finset.mem_Iic.mpr hi⟩
  · intro h i
    exact h i (Finset.mem_Iic.mp i.property)

lemma prefix_lintegral_succ {d : ℕ} (μ : Measure (Environment d)) [IsProbabilityMeasure μ]
    (x : Site d) (n : ℕ) (γ : ℕ → Site d) (f : Environment d → ℝ≥0∞)
    (hf : Measurable f) :
    (∫⁻ z, prefixObservable (n+1) γ f z ∂walkStateLaw μ x) =
      ∫⁻ z, prefixObservable n γ (fun ω => entryWeight ω (γ n) (γ (n+1)) * f ω) z
        ∂walkStateLaw μ x := by
  classical
  let F : ((i : Finset.Iic n) → State d) × State d → ℝ≥0∞ := fun q =>
    if (∀ i, (q.1 i).2 = γ i) then
      if q.2.2 = γ (n+1) then f q.2.1 else 0
    else 0
  have hm : MeasurableSet {q : ((i : Finset.Iic n) → State d) × State d |
      ∀ i, (q.1 i).2 = γ i} := by
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter (fun i => measurableSet_eq_fun
      (measurable_snd.comp ((measurable_pi_apply i).comp measurable_fst)) measurable_const)
  have hn : MeasurableSet {q : ((i : Finset.Iic n) → State d) × State d |
      q.2.2 = γ (n+1)} :=
    measurableSet_eq_fun (measurable_snd.comp measurable_snd) measurable_const
  have hF : Measurable F :=
    Measurable.ite hm (Measurable.ite hn
      (hf.comp (measurable_fst.comp measurable_snd)) measurable_const) measurable_const
  have hFeq (z : ℕ → State d) :
      F (frestrictLe n z, z (n+1)) = prefixObservable (n+1) γ f z := by
    simp only [F, history_matches_iff, prefixObservable, prefixMatches_succ]
    split_ifs <;> simp_all
  calc
    (∫⁻ z, prefixObservable (n+1) γ f z ∂walkStateLaw μ x) =
        ∫⁻ z, F (frestrictLe n z, z (n+1)) ∂walkStateLaw μ x :=
      lintegral_congr (fun z => (hFeq z).symm)
    _ = ∫⁻ z, ∫⁻ t, F (frestrictLe n z, t) ∂transition d (z n) ∂walkStateLaw μ x :=
      walkStateLaw_one_step μ x n F hF
    _ = _ := by
      apply lintegral_congr
      intro z
      rw [lintegral_transition (z n) (fun t => F (frestrictLe n z, t))
        (hF.comp (measurable_const.prodMk measurable_id))]
      by_cases hz : prefixMatches n γ z
      · have hzn := hz n le_rfl
        simp only [F, history_matches_iff, hz, ite_true, prefixObservable]
        rw [hzn, entryWeight, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro e he
        split_ifs <;> simp_all
      · simp only [F, history_matches_iff, hz, ite_false, prefixObservable, mul_zero,
          Finset.sum_const_zero]

lemma prefix_lintegral_zero {d : ℕ} (μ : Measure (Environment d)) [IsProbabilityMeasure μ]
    (x : Site d) (γ : ℕ → Site d) (f : Environment d → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ z, prefixObservable 0 γ f z ∂walkStateLaw μ x) =
      if x = γ 0 then ∫⁻ ω, f ω ∂μ else 0 := by
  classical
  let g : State d → ℝ≥0∞ := fun s => if s.2 = γ 0 then f s.1 else 0
  have hg : Measurable g := Measurable.ite
    (measurableSet_eq_fun measurable_snd measurable_const) (hf.comp measurable_fst) measurable_const
  have heq : prefixObservable 0 γ f = fun z => g (z 0) := by
    funext z
    simp [prefixObservable, prefixMatches, g]
  rw [heq, ← lintegral_map hg (measurable_pi_apply 0), walkStateLaw_initial,
    walkInitialLaw, lintegral_map (g := fun ω : Environment d => (ω, x)) hg
      (measurable_id.prodMk measurable_const)]
  by_cases hx : x = γ 0 <;> simp [g, hx]

lemma prefix_lintegral {d : ℕ} (μ : Measure (Environment d)) [IsProbabilityMeasure μ]
    (x : Site d) (n : ℕ) (γ : ℕ → Site d) (f : Environment d → ℝ≥0∞)
    (hf : Measurable f) :
    (∫⁻ z, prefixObservable n γ f z ∂walkStateLaw μ x) =
      if x = γ 0 then ∫⁻ ω, pathWeight n γ ω * f ω ∂μ else 0 := by
  induction n generalizing f with
  | zero => simpa [pathWeight] using prefix_lintegral_zero μ x γ f hf
  | succ n ih =>
    rw [prefix_lintegral_succ μ x n γ f hf,
      ih (fun ω => entryWeight ω (γ n) (γ (n+1)) * f ω)
        ((measurable_entryWeight (γ n) (γ (n+1))).mul hf)]
    simp only [pathWeight_succ, mul_assoc]

noncomputable def stateLaw {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (x : Site d) : Measure (ℕ → State d) := walkStateLaw (environmentLaw μ) x

lemma annealed_eq_map_stateLaw {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (x : Site d) : annealed μ x = (stateLaw μ x).map (fun z n => (z n).2) := rfl

noncomputable def walkLaw {d : ℕ} (μ : Measure (Environment d)) [IsProbabilityMeasure μ]
    (x : Site d) : Measure (Path d) := (walkStateLaw μ x).map (fun z n => (z n).2)

instance {d : ℕ} (μ : Measure (Environment d)) [IsProbabilityMeasure μ] (x : Site d) :
    IsProbabilityMeasure (walkLaw μ x) := by
  apply probabilityMeasure_map
  exact (Measurable.of_eval (fun n => measurable_snd.comp (measurable_pi_apply n))).aemeasurable

def pathCylinder {d : ℕ} (n : ℕ) (γ : ℕ → Site d) : Set (Path d) :=
  {X | ∀ i ≤ n, X i = γ i}

lemma measurableSet_pathCylinder {d : ℕ} (n : ℕ) (γ : ℕ → Site d) :
    MeasurableSet (pathCylinder n γ) := by
  simp only [pathCylinder, Set.ofPred_forall]
  exact MeasurableSet.iInter (fun i => MeasurableSet.iInter (fun _ =>
    measurableSet_eq_fun (measurable_pi_apply i) measurable_const))

lemma walkLaw_cylinder {d : ℕ} (μ : Measure (Environment d)) [IsProbabilityMeasure μ]
    (x : Site d) (n : ℕ) (γ : ℕ → Site d) :
    walkLaw μ x (pathCylinder n γ) =
      if x = γ 0 then ∫⁻ ω, pathWeight n γ ω ∂μ else 0 := by
  classical
  have hp := prefix_lintegral μ x n γ (fun _ => 1) measurable_const
  have hobs : prefixObservable n γ (fun _ => 1) =
      {z : ℕ → State d | prefixMatches n γ z}.indicator (fun _ => 1) := by
    funext z
    simp [prefixObservable, Set.indicator]
  rw [hobs] at hp
  change (∫⁻ z, {z' : ℕ → State d | prefixMatches n γ z'}.indicator 1 z
    ∂walkStateLaw μ x) = _ at hp
  rw [lintegral_indicator_one (measurableSet_prefixMatches n γ)] at hp
  rw [walkLaw, Measure.map_apply (f := fun z : ℕ → State d => fun n => (z n).2)
    (Measurable.of_eval (fun n => measurable_snd.comp (measurable_pi_apply n)))
    (measurableSet_pathCylinder n γ)]
  simpa only [pathCylinder, prefixMatches, Set.preimage_ofPred_eq, mul_one] using hp

lemma annealed_cylinder {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (x : Site d) (n : ℕ) (γ : ℕ → Site d) :
    annealed μ x (pathCylinder n γ) =
      if x = γ 0 then ∫⁻ ω, pathWeight n γ ω ∂environmentLaw μ else 0 :=
  walkLaw_cylinder (environmentLaw μ) x n γ

lemma stepVector_injective {d : ℕ} : Function.Injective (@stepVector d) := by
  rintro ⟨i, b⟩ ⟨j, c⟩ h
  have hij : i = j := by
    by_contra hn
    have hh := congr_fun h i
    cases b <;> simp [stepVector, hn] at hh
  subst j
  have hh := congr_fun h i
  cases b <;> cases c <;> simp_all [stepVector]

lemma entryWeight_step {d : ℕ} (ω : Environment d) (x : Site d) (e : Step d) :
    entryWeight ω x (x + stepVector e) = ENNReal.ofReal ((ω x).val e) := by
  simp [entryWeight, stepVector_injective.eq_iff]

noncomputable def quenchedKernel (d : ℕ) : Kernel (State d) (Path d) :=
  ((Kernel.traj (X := fun _ => State d) (historyKernel d) 0).comap
    (MeasurableEquiv.piUnique (fun _ : Finset.Iic 0 => State d)).symm
    (MeasurableEquiv.measurable _)).map (fun z n => (z n).2)

instance (d : ℕ) : IsMarkovKernel (quenchedKernel d) := by
  unfold quenchedKernel
  apply Kernel.IsMarkovKernel.map
  exact Measurable.of_eval (fun n => measurable_snd.comp (measurable_pi_apply n))

lemma walkLaw_apply {d : ℕ} (μ : Measure (Environment d)) [IsProbabilityMeasure μ]
    (x : Site d) {s : Set (Path d)} (hs : MeasurableSet s) :
    walkLaw μ x s = ∫⁻ ω, quenchedKernel d (ω,x) s ∂μ := by
  let ψ : (ℕ → State d) → Path d := fun z n => (z n).2
  have hψ : Measurable ψ :=
    Measurable.of_eval (fun n => measurable_snd.comp (measurable_pi_apply n))
  let e := MeasurableEquiv.piUnique (fun _ : Finset.Iic 0 => State d)
  change ((Kernel.trajMeasure (X := fun _ => State d) (walkInitialLaw μ x) (historyKernel d)).map ψ) s = _
  rw [Kernel.trajMeasure, Measure.map_comp _ _ hψ,
    Measure.bind_apply hs (Kernel.measurable _).aemeasurable]
  rw [lintegral_map (Kernel.measurable_coe _ hs) e.symm.measurable]
  rw [walkInitialLaw, lintegral_map
    (f := fun a : State d => ((Kernel.traj (historyKernel d) 0).map ψ) (e.symm a) s)
    (g := fun ω : Environment d => (ω,x))
    ((Kernel.measurable_coe _ hs).comp e.symm.measurable)
    (measurable_id.prodMk measurable_const)]
  apply lintegral_congr
  intro ω
  change (((Kernel.traj (historyKernel d) 0).map ψ) (e.symm (ω,x))) s =
    (((Kernel.traj (historyKernel d) 0).comap e.symm e.symm.measurable).map ψ) (ω,x) s
  rw [Kernel.map_apply _ hψ, Kernel.map_apply _ hψ, Kernel.comap_apply]

lemma walkLaw_dirac {d : ℕ} (ω : Environment d) (x : Site d) :
    walkLaw (Measure.dirac ω) x = quenchedKernel d (ω,x) := by
  ext s hs
  rw [walkLaw_apply _ _ hs, lintegral_dirac' _]
  exact (Kernel.measurable_coe _ hs).comp (measurable_id.prodMk measurable_const)

lemma annealed_apply {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (x : Site d) {s : Set (Path d)} (hs : MeasurableSet s) :
    annealed μ x s = ∫⁻ ω, quenchedKernel d (ω,x) s ∂environmentLaw μ :=
  walkLaw_apply (environmentLaw μ) x hs

lemma quenchedKernel_cylinder {d : ℕ} (ω : Environment d) (x : Site d)
    (n : ℕ) (γ : ℕ → Site d) :
    quenchedKernel d (ω,x) (pathCylinder n γ) =
      if x = γ 0 then pathWeight n γ ω else 0 := by
  rw [← walkLaw_dirac, walkLaw_cylinder, lintegral_dirac' _ (measurable_pathWeight n γ)]

lemma measure_eq_of_prefix {A : Type*} [MeasurableSpace A]
    (μ ν : Measure (ℕ → A)) [IsFiniteMeasure μ]
    (h : ∀ n, μ.map (frestrictLe n) = ν.map (frestrictLe n)) : μ = ν := by
  let P : ∀ I : Finset ℕ, Measure (I → A) := fun I => μ.map I.restrict
  have hP : IsProjectiveMeasureFamily (α := fun _ : ℕ => A) P := by
    intro I J hJI
    dsimp [P]
    have h1 : Measurable (Finset.restrict₂ (π := fun _ : ℕ => A) hJI) :=
      Measurable.of_eval (fun i => measurable_pi_apply (⟨i, hJI i.property⟩ : I))
    have h2 : Measurable (I.restrict : (ℕ → A) → (I → A)) :=
      Measurable.of_eval (fun i => measurable_pi_apply (i : ℕ))
    rw [Measure.map_map h1 h2]
    rfl
  have hμ : IsProjectiveLimit (α := fun _ : ℕ => A) μ P := fun I => rfl
  have hν : IsProjectiveLimit (α := fun _ : ℕ => A) ν P := (isProjectiveLimit_nat_iff hP ν).2 (fun n => (h n).symm)
  exact hμ.unique hν

lemma pathMeasure_ext {d : ℕ} (μ ν : Measure (Path d)) [IsFiniteMeasure μ]
    (h : ∀ n γ, μ (pathCylinder n γ) = ν (pathCylinder n γ)) : μ = ν := by
  classical
  apply measure_eq_of_prefix
  intro n
  apply Measure.ext_of_singleton
  intro a
  let γ : ℕ → Site d := fun i => if hi : i ∈ Finset.Iic n then a ⟨i,hi⟩ else 0
  have heq : (frestrictLe n : Path d → (Finset.Iic n → Site d)) ⁻¹' {a} = pathCylinder n γ := by
    ext X
    simp only [Set.mem_preimage, Set.mem_singleton_iff, pathCylinder, Set.mem_ofPred_eq]
    constructor
    · intro hh i hi
      have hh' := congr_fun hh ⟨i, Finset.mem_Iic.mpr hi⟩
      simpa [γ, hi, frestrictLe] using hh'
    · intro hh
      funext i
      have hi := Finset.mem_Iic.mp i.property
      simpa [γ, hi, frestrictLe] using hh i hi
  rw [Measure.map_apply (measurable_frestrictLe n) (measurableSet_singleton a),
    Measure.map_apply (measurable_frestrictLe n) (measurableSet_singleton a), heq]
  exact h n γ

end DirectionalZeroOne

end OAI
