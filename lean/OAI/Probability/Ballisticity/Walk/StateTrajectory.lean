import Mathlib
import OAI.Probability.Ballisticity.Model

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology

namespace DirectionalTransience

instance environmentLaw_probability {d : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] : IsProbabilityMeasure (environmentLaw ν) := by
  unfold environmentLaw
  infer_instance

instance initialLaw_probability {d : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] : IsProbabilityMeasure (initialLaw ν) := by
  unfold initialLaw
  infer_instance

instance annealedLaw_probability {d : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] : IsProbabilityMeasure (annealedLaw ν) := by
  unfold annealedLaw
  infer_instance

lemma environment_site_law {d : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (x : Lattice d) :
    (environmentLaw ν).map (fun ω => ω x) = ν := by
  exact (measurePreserving_eval_infinitePi (fun _ : Lattice d => ν) x).map_eq

lemma environment_uniform_elliptic {d : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (hue : UniformElliptic ν) :
    ∃ κ : ℝ≥0, 0 < κ ∧ ∀ᵐ ω ∂environmentLaw ν, ∀ x e, κ ≤ (ω x).1 e := by
  obtain ⟨κ, hκ, hrows⟩ := hue
  refine ⟨κ, hκ, ae_all_iff.mpr fun x => ?_⟩
  exact (measurePreserving_eval_infinitePi (fun _ : Lattice d => ν) x).quasiMeasurePreserving.ae hrows

lemma row_entry_le_one {d : ℕ} (p : Row d) (e : Direction d) : p.1 e ≤ 1 := by
  calc
    p.1 e ≤ ∑ i, p.1 i := Finset.single_le_sum (fun _ _ => zero_le) (Finset.mem_univ e)
    _ = 1 := p.2

lemma hasVelocity_unique {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    {v w : Vector d} (hv : HasVelocity ν v) (hw : HasVelocity ν w) : v = w := by
  obtain ⟨X, hXv, hXw⟩ := (hv.and hw).exists
  exact tendsto_nhds_unique hXv hXw

noncomputable def stateTrajectory {d : ℕ} : Kernel (State d) (ℕ → State d) :=
  (Kernel.traj (historyTransition (d := d)) 0).comap
    (fun z _ => z) (Measurable.of_eval fun _ => measurable_id)

instance stateTrajectory_markov {d : ℕ} : IsMarkovKernel (stateTrajectory (d := d)) := by
  unfold stateTrajectory
  infer_instance

noncomputable def quenchedKernel {d : ℕ} : Kernel (State d) (Path d) :=
  stateTrajectory.map (fun z n => (z n).2)

instance quenchedKernel_markov {d : ℕ} : IsMarkovKernel (quenchedKernel (d := d)) := by
  apply Kernel.IsMarkovKernel.map
  exact Measurable.of_eval fun n => measurable_snd.comp (measurable_pi_apply n)

lemma stateTrajectory_eq {d : ℕ} (μ : Measure (State d)) :
    stateTrajectory ∘ₘ μ = Kernel.trajMeasure μ (historyTransition (d := d)) := by
  unfold Kernel.trajMeasure stateTrajectory
  rw [← Kernel.comp_deterministic_eq_comap, ← Measure.comp_assoc,
    Measure.deterministic_comp_eq_map]
  rfl

lemma annealed_eq_quenched_mixture {d : ℕ} (ν : Measure (Row d)) :
    annealedLaw ν = quenchedKernel ∘ₘ initialLaw ν := by
  unfold annealedLaw quenchedKernel
  rw [← stateTrajectory_eq, Measure.map_comp]
  exact Measurable.of_eval fun n => measurable_snd.comp (measurable_pi_apply n)

lemma annealed_apply {d : ℕ} (ν : Measure (Row d)) {A : Set (Path d)}
    (hA : MeasurableSet A) :
    annealedLaw ν A = ∫⁻ ω, quenchedKernel (ω, (0 : Lattice d)) A ∂environmentLaw ν := by
  rw [annealed_eq_quenched_mixture, Measure.bind_apply hA (Kernel.aemeasurable _),
    initialLaw, lintegral_map]
  · exact Kernel.measurable_coe _ hA
  · exact measurable_id.prodMk measurable_const

lemma environment_translation {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (z : Lattice d) :
    (environmentLaw ν).map (fun ω x => ω (z + x)) = environmentLaw ν := by
  apply Measure.map_infinitePi_infinitePi_of_inj
  exact add_right_injective z

lemma stateTrajectory_initial {d : ℕ} (z : State d) :
    (stateTrajectory z).map (fun X => X 0) = Measure.dirac z := by
  rw [stateTrajectory, Kernel.comap_apply]
  have h := Kernel.traj_map_frestrictLe_apply (X := fun _ => State d)
    (κ := historyTransition (d := d))
    0 0 (fun _ => z)
  rw [Kernel.partialTraj_self, Kernel.id_apply] at h
  have hm : Measurable (fun X : (i : Finset.Iic 0) → State d =>
      X ⟨0, Finset.mem_Iic.mpr le_rfl⟩) := measurable_pi_apply _
  have := congrArg (fun μ => μ.map
    (fun X : (i : Finset.Iic 0) → State d => X ⟨0, Finset.mem_Iic.mpr le_rfl⟩)) h
  rw [Measure.map_map hm (Preorder.measurable_frestrictLe 0), Measure.map_dirac' hm] at this
  exact this

lemma quenched_initial {d : ℕ} (z : State d) :
    (quenchedKernel z).map (fun X => X 0) = Measure.dirac z.2 := by
  have hm : Measurable (fun z : ℕ → State d => fun n => (z n).2) := by fun_prop
  rw [quenchedKernel, Kernel.map_apply _ hm, Measure.map_map (measurable_pi_apply 0) hm]
  have h := congrArg (fun μ => μ.map Prod.snd) (stateTrajectory_initial z)
  rw [Measure.map_map measurable_snd (measurable_pi_apply 0),
    Measure.map_dirac' measurable_snd] at h
  exact h

lemma quenched_initial_ae {d : ℕ} (z : State d) :
    ∀ᵐ X ∂quenchedKernel z, X 0 = z.2 := by
  have h : ∀ᵐ x ∂(quenchedKernel z).map (fun X => X 0), x = z.2 := by
    rw [quenched_initial]
    exact ae_dirac_iff (measurableSet_singleton _ ) |>.mpr rfl
  exact (ae_map_iff (measurable_pi_apply 0).aemeasurable
    (measurableSet_singleton _)).mp h

instance state_measurableEq {d : ℕ} : MeasurableEq (State d) where
  measurableSet_diagonal := by
    change MeasurableSet {zz : State d × State d | zz.1 = zz.2}
    simp only [Prod.ext_iff, Set.ofPred_and]
    exact (measurableSet_eq_fun (measurable_fst.comp measurable_fst)
      (measurable_fst.comp measurable_snd)).inter
      (measurableSet_eq_fun (measurable_snd.comp measurable_fst)
        (measurable_snd.comp measurable_snd))

instance state_measurableSingleton {d : ℕ} : MeasurableSingletonClass (State d) := by
  infer_instance

def AdmissibleStep {d : ℕ} (z z' : State d) : Prop :=
  ∃ e : Direction d, z' = (z.1, z.2 + step e)

lemma measurableSet_admissibleStep {d : ℕ} :
    MeasurableSet {zz : State d × State d | AdmissibleStep zz.1 zz.2} := by
  simp only [AdmissibleStep, Prod.ext_iff, Set.ofPred_exists, Set.ofPred_and]
  apply MeasurableSet.iUnion
  intro e
  exact (measurableSet_eq_fun (measurable_fst.comp measurable_snd)
    (measurable_fst.comp measurable_fst)).inter
    (measurableSet_eq_fun (measurable_snd.comp measurable_snd)
      ((measurable_snd.comp measurable_fst).add_const (step e)))

lemma transition_admissible {d : ℕ} (z : State d) :
    ∀ᵐ z' ∂transition z, AdmissibleStep z z' := by
  change ∀ᵐ z' ∂∑ e : Direction d,
    ((z.1 z.2).1 e : ℝ≥0∞) • Measure.dirac (z.1, z.2 + step e), AdmissibleStep z z'
  apply ae_finsetSum_measure_iff.mpr
  intro e _
  apply Measure.ae_smul_measure
  apply (ae_dirac_iff _).mpr
  · exact ⟨e, rfl⟩
  · exact measurableSet_admissibleStep.preimage (measurable_const.prodMk measurable_id)

lemma stateTrajectory_admissible {d : ℕ} (z : State d) :
    ∀ᵐ X ∂stateTrajectory z, ∀ n, AdmissibleStep (X n) (X (n + 1)) := by
  rw [stateTrajectory, Kernel.comap_apply]
  apply ae_all_iff.mpr
  intro n
  let p := fun zz : ((i : Finset.Iic n) → State d) × State d =>
    AdmissibleStep (zz.1 ⟨n, Finset.mem_Iic.mpr le_rfl⟩) zz.2
  have hm : Measurable (fun zz : ((i : Finset.Iic n) → State d) × State d =>
      (zz.1 ⟨n, Finset.mem_Iic.mpr le_rfl⟩, zz.2)) := by fun_prop
  have hp : MeasurableSet {zz | p zz} :=
    measurableSet_admissibleStep.preimage hm
  have h : ∀ᵐ zz ∂(Kernel.partialTraj (X := fun _ => State d) (historyTransition (d := d)) 0 n (fun _ => z))
      ⊗ₘ historyTransition (d := d) n, p zz := by
    apply Measure.ae_compProd_of_ae_ae hp
    exact ae_of_all _ fun x => transition_admissible _
  rw [Kernel.partialTraj_compProd_eq_map_traj (Nat.zero_le n)] at h
  exact (ae_map_iff (by fun_prop) hp).mp h

lemma stateTrajectory_environment {d : ℕ} (z : State d) :
    ∀ᵐ X ∂stateTrajectory z, ∀ n, (X n).1 = z.1 := by
  have h0 : ∀ᵐ X ∂stateTrajectory z, X 0 = z := by
    have h : ∀ᵐ y ∂(stateTrajectory z).map (fun X => X 0), y = z := by
      rw [stateTrajectory_initial]
      exact (ae_dirac_iff (measurableSet_singleton _)).mpr rfl
    exact (ae_map_iff (measurable_pi_apply 0).aemeasurable
      (measurableSet_singleton _)).mp h
  filter_upwards [h0, stateTrajectory_admissible z] with X hX hstep n
  induction n with
  | zero => rw [hX]
  | succ n ih =>
    obtain ⟨e, he⟩ := hstep n
    rw [he]
    exact ih

lemma quenched_nearest_neighbor {d : ℕ} (z : State d) :
    ∀ᵐ X ∂quenchedKernel z, ∀ n, ∃ e : Direction d, X (n + 1) = X n + step e := by
  have hm : Measurable (fun z : ℕ → State d => fun n => (z n).2) := by fun_prop
  rw [quenchedKernel, Kernel.map_apply _ hm]
  apply (ae_map_iff hm.aemeasurable _).mpr
  · filter_upwards [stateTrajectory_admissible z] with X hX n
    obtain ⟨e, he⟩ := hX n
    exact ⟨e, congrArg Prod.snd he⟩
  · simp only [Set.ofPred_forall, Set.ofPred_exists]
    apply MeasurableSet.iInter
    intro n
    apply MeasurableSet.iUnion
    intro e
    exact measurableSet_eq_fun (measurable_pi_apply _) ((measurable_pi_apply _).add_const _)

lemma step_injective {d : ℕ} : Function.Injective (step (d := d)) := by
  rintro ⟨i, b⟩ ⟨j, c⟩ he
  have hij : i = j := by
    by_contra hne
    have hi := congrFun he i
    cases b <;> simp [step, hne] at hi
  subst j
  have hi := congrFun he i
  cases b <;> cases c <;> simp_all [step]

lemma transition_singleton_step {d : ℕ} (z : State d) (e : Direction d) :
    transition z {(z.1, z.2 + step e)} = ((z.1 z.2).1 e : ℝ≥0∞) := by
  change (∑ f : Direction d,
    ((z.1 z.2).1 f : ℝ≥0∞) • Measure.dirac (z.1, z.2 + step f))
      {(z.1, z.2 + step e)} = _
  simp only [Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single e]
  · simp
  · intro f _ hne
    have hh : (z.1, z.2 + step f) ∉ ({(z.1, z.2 + step e)} : Set (State d)) := by
      intro he
      apply hne
      exact step_injective (add_left_cancel (congrArg Prod.snd (Set.mem_singleton_iff.mp he)))
    simp [Measure.dirac_apply' _ (measurableSet_singleton _), hh]
  · simp

def stateCylinder {d : ℕ} (f : ℕ → State d) (n : ℕ) : Set (ℕ → State d) :=
  {X | ∀ i ≤ n, X i = f i}

lemma measurableSet_stateCylinder {d : ℕ} (f : ℕ → State d) (n : ℕ) :
    MeasurableSet (stateCylinder f n) := by
  simp only [stateCylinder, Set.ofPred_forall]
  exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun _ =>
    measurableSet_eq_fun (measurable_pi_apply i : Measurable (fun X : ℕ → State d => X i))
      measurable_const

lemma stateCylinder_eq_preimage {d : ℕ} (f : ℕ → State d) (n : ℕ) :
    stateCylinder f n = (fun X : ℕ → State d => Preorder.frestrictLe n X) ⁻¹' {fun i : Finset.Iic n => f i} := by
  ext X
  simp only [stateCylinder, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_singleton_iff]
  constructor
  · intro h
    funext i
    exact h i (Finset.mem_Iic.mp i.2)
  · intro h i hi
    exact congrFun h ⟨i, Finset.mem_Iic.mpr hi⟩

lemma stateTrajectory_cylinder_succ {d : ℕ} (z : State d) (f : ℕ → State d) (n : ℕ) :
    stateTrajectory z (stateCylinder f (n + 1)) =
      transition (f n) {f (n + 1)} * stateTrajectory z (stateCylinder f n) := by
  rw [stateTrajectory, Kernel.comap_apply]
  have h := Kernel.partialTraj_compProd_eq_map_traj (X := fun _ => State d)
    (κ := historyTransition (d := d)) (x₀ := fun _ => z) (Nat.zero_le n)
  have hm : Measurable (fun X : ℕ → State d => (Preorder.frestrictLe n X, X (n + 1))) := by
    fun_prop
  have he : (fun X : ℕ → State d => (Preorder.frestrictLe n X, X (n + 1))) ⁻¹'
      ({fun i : Finset.Iic n => f i} ×ˢ {f (n + 1)}) = stateCylinder f (n + 1) := by
    ext X
    simp only [Set.mem_preimage, Set.mem_prod, Set.mem_singleton_iff,
      stateCylinder, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨h₁, h₂⟩ i hi
      obtain hi | rfl := Nat.lt_or_eq_of_le hi
      · exact congrFun h₁ ⟨i, Finset.mem_Iic.mpr (by omega)⟩
      · exact h₂
    · intro hX
      exact ⟨funext fun i => hX i (by have := Finset.mem_Iic.mp i.2; omega), hX _ le_rfl⟩
  have hs := congrArg (fun μ : Measure (((i : Finset.Iic n) → State d) × State d) =>
    μ ({fun i : Finset.Iic n => f i} ×ˢ {f (n + 1)})) h
  rw [Measure.compProd_apply_prod (measurableSet_singleton _) (measurableSet_singleton _),
    lintegral_singleton, Measure.map_apply hm
      ((measurableSet_singleton _).prod (measurableSet_singleton _)), he] at hs
  rw [← hs]
  congr 1
  rw [stateCylinder_eq_preimage, ← Measure.map_apply (Preorder.measurable_frestrictLe n)
    (measurableSet_singleton _), Kernel.traj_map_frestrictLe_apply]

lemma stateTrajectory_cylinder {d : ℕ} (z : State d) (f : ℕ → State d)
    (hf : f 0 = z) (n : ℕ) :
    stateTrajectory z (stateCylinder f n) =
      ∏ i ∈ Finset.range n, transition (f i) {f (i + 1)} := by
  induction n with
  | zero =>
    have he : stateCylinder f 0 = (fun X : ℕ → State d => X 0) ⁻¹' {z} := by
      ext X
      simp [stateCylinder, hf]
    rw [he, ← Measure.map_apply (measurable_pi_apply 0) (measurableSet_singleton _),
      stateTrajectory_initial]
    simp
  | succ n ih =>
    rw [stateTrajectory_cylinder_succ, ih, Finset.prod_range_succ, mul_comm]

abbrev rowSigma {d : ℕ} (S : Set (Lattice d)) : MeasurableSpace (Environment d) :=
  ⨆ x ∈ S, MeasurableSpace.comap (fun ω : Environment d => ω x) inferInstance

lemma rowSigma_le {d : ℕ} (S : Set (Lattice d)) : rowSigma S ≤ (inferInstance : MeasurableSpace (Environment d)) := by
  exact iSup_le fun x => iSup_le fun _ => (measurable_pi_apply x).comap_le

lemma measurable_row_on {d : ℕ} {S : Set (Lattice d)} {x : Lattice d} (hx : x ∈ S) :
    @Measurable _ _ (rowSigma S) _ (fun ω : Environment d => ω x) := by
  apply Measurable.of_comap_le
  exact le_iSup_of_le x (le_iSup_of_le hx le_rfl)

lemma environment_indep_rows {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    {S T : Set (Lattice d)} (hST : Disjoint S T) :
    Indep (rowSigma S) (rowSigma T) (environmentLaw ν) := by
  exact indep_iSup_of_disjoint (fun x => (measurable_pi_apply x).comap_le)
    (iIndepFun_infinitePi (P := fun _ : Lattice d => ν)
      (X := fun _ p => p) (fun _ => measurable_id)).iIndep hST

lemma rowSigma_mono {d : ℕ} {S T : Set (Lattice d)} (hST : S ⊆ T) :
    rowSigma S ≤ rowSigma T :=
  iSup₂_le fun x hx => le_iSup_of_le x (le_iSup_of_le (hST hx) le_rfl)

lemma environment_tail_zero_one {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    {E : Set (Environment d)}
    (hE : ∀ S ∈ (cofinite : Filter (Lattice d)), MeasurableSet[rowSigma S] E) :
    environmentLaw ν E = 0 ∨ environmentLaw ν E = 1 := by
  let s : Lattice d → MeasurableSpace (Environment d) := fun x =>
    MeasurableSpace.comap (fun ω : Environment d => ω x) inferInstance
  have hind : iIndep s (environmentLaw ν) :=
    (iIndepFun_infinitePi (P := fun _ : Lattice d => ν)
      (X := fun _ p => p) (fun _ => measurable_id)).iIndep
  have ht : MeasurableSet[limsup s cofinite] E := by
    rw [limsup_eq_iInf_iSup]
    apply MeasurableSpace.measurableSet_iInf.mpr
    intro S
    apply MeasurableSpace.measurableSet_iInf.mpr
    exact hE S
  apply measure_zero_or_one_of_measurableSet_limsup
    (s := s) (p := Set.Finite) (ns := fun F : Finset (Lattice d) => (F : Set (Lattice d)))
    (fun x => (measurable_pi_apply x).comap_le) hind
    (fun S hS => by simpa only [mem_cofinite, compl_compl] using hS) _
    (fun F => F.finite_toSet) (fun x => ⟨{x}, by simp⟩) ht
  intro F G
  exact ⟨F ∪ G, Finset.coe_subset.mpr Finset.subset_union_left,
    Finset.coe_subset.mpr Finset.subset_union_right⟩

end DirectionalTransience
end
end

end OAI
