import OAI.Probability.ProjectionMoments.BorelRules

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open MeasureTheory ProbabilityTheory Set Filter unitInterval
open scoped ENNReal NNReal RealInnerProductSpace
namespace NoiselessRegression

lemma finite_kernel_borel_version {X J : Type*} [MeasurableSpace X]
    [Fintype J] [Nonempty J] [MeasurableSpace J] [MeasurableSingletonClass J]
    (μ : Measure X) (P : X → Measure J) (hP : ∀ x, IsProbabilityMeasure (P x))
    (hm : ∀ j, AEMeasurable (fun x => P x {j}) μ) :
    ∃ κ : Kernel X J, IsMarkovKernel κ ∧ (fun x => κ x) =ᵐ[μ] P := by
  classical
  let v : X → Measure J := fun x => ∑ j, ((hm j).mk _ x) • Measure.dirac j
  have hv : Measurable v := by
    apply Finset.measurable_sum
    intro j _
    exact (hm j).measurable_mk.smul_measure (Measure.dirac j)
  have he : v =ᵐ[μ] P := by
    have hh : ∀ᵐ x ∂μ, ∀ j, (hm j).mk _ x = P x {j} := by
      simp only [ae_all_iff]
      intro j
      exact (hm j).ae_eq_mk.symm
    filter_upwards [hh] with x hx
    simp only [v,hx,← Measure.sum_fintype,Measure.sum_smul_dirac]
  let κ : Kernel X J := ⟨fun x => if v x Set.univ = 1 then v x else Measure.dirac (Classical.choice ‹Nonempty J›),
    hv.ite (measurableSet_eq_fun ((Measure.measurable_coe MeasurableSet.univ).comp hv) measurable_const)
      measurable_const⟩
  refine ⟨κ,⟨fun x => ⟨?_⟩⟩,?_⟩
  · dsimp [κ]
    split_ifs with h
    · exact h
    · simp
  · filter_upwards [he] with x hx
    have hx1 : v x Set.univ = 1 := by rw [hx]; exact (hP x).measure_univ
    dsimp only [κ,Kernel.coe_mk]
    rw [ite_eq_left hx1,hx]

namespace FiniteKernelLearner
variable {d M T : ℕ}

structure BorelRules (K : FiniteKernelLearner d M T) : Prop where
  transition : ∀ t j, Measurable (K.transition t j)

lemma exists_borel_version (K : FiniteKernelLearner d M T) (hK : K.CompletedRules) :
    ∃ K' : FiniteKernelLearner d M T, K'.BorelRules ∧ K'.initial = K.initial ∧
      K'.output = K.output ∧ ∀ t j, K'.transition t j =ᵐ[observationReference d] K.transition t j := by
  classical
  choose κ hκ he using fun t j => finite_kernel_borel_version (observationReference d)
    (K.transition t j) (K.transition_probability t j) (hK.transition t j)
  let K' : FiniteKernelLearner d M T := ⟨K.initial,K.initial_probability,
    fun t j obs => κ t j obs,fun t j obs => (hκ t j).isProbabilityMeasure obs,
    K.output,K.output_probability⟩
  exact ⟨K',⟨fun t j => (κ t j).measurable⟩,rfl,rfl,he⟩

end FiniteKernelLearner

variable {J O : Type*} [Fintype J] [MeasurableSpace J] [MeasurableSingletonClass J]
  [MeasurableSpace O]

def coinRun (F : ℕ → J → O → I → J) :
    (n : ℕ) → J → (Fin n → O) → (Fin n → I) → J
  | 0, j, _, _ => j
  | n+1, j, obs, u => F (n+1) (coinRun F n j (Fin.init obs) (Fin.init u)) (obs (Fin.last n)) (u (Fin.last n))

omit [MeasurableSpace O] in
lemma measurable_coinRun [MeasurableSpace O] {F : ℕ → J → O → I → J}
    (hF : ∀ t j obs, Measurable (F t j obs)) (n : ℕ) (j : J) (obs : Fin n → O) :
    Measurable (coinRun F n j obs) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    change Measurable (fun u : Fin (n+1) → I => F (n+1) (coinRun F n j (Fin.init obs) (Fin.init u)) (obs (Fin.last n)) (u (Fin.last n)))
    have hi : Measurable (fun u : Fin (n+1) → I => Fin.init u) := by
      change Measurable (fun u : Fin (n+1) → I => fun i : Fin n => u i.castSucc)
      fun_prop
    have hg : Measurable (fun u : Fin (n+1) → I => coinRun F n j (Fin.init obs) (Fin.init u)) :=
      (ih (Fin.init obs)).comp hi
    exact measurable_select (h := fun a (u : Fin (n+1) → I) => F (n+1) a (obs (Fin.last n)) (u (Fin.last n)))
      (fun a => (hF (n+1) a (obs (Fin.last n))).comp (measurable_pi_apply _)) hg

lemma lintegral_coinRun {F : ℕ → J → O → I → J} {P : ℕ → J → O → Measure J}
    (hF : ∀ t j obs, Measurable (F t j obs))
    (hP : ∀ t j obs, volume.map (F t j obs) = P t j obs)
    (n : ℕ) (j : J) (obs : Fin n → O) (f : J → ℝ≥0∞) :
    (∫⁻ u, f (coinRun F n j obs u) ∂Measure.pi (fun _ => (volume : Measure I))) =
      ∫⁻ a, f a ∂kernelRun P n j obs := by
  induction n generalizing f with
  | zero => simp [coinRun,kernelRun]
  | succ n ih =>
    rw [lintegral_pi_snoc volume (fun u => f (coinRun F (n+1) j obs u))
      ((measurable_of_finite f).comp (measurable_coinRun hF (n+1) j obs))]
    simp only [coinRun,Fin.init_snoc,Fin.snoc_last]
    have hh (a : J) : (∫⁻ u, f (F (n+1) a (obs (Fin.last n)) u) ∂volume) =
        ∫⁻ b, f b ∂P (n+1) a (obs (Fin.last n)) := by
      rw [←hP]
      exact (lintegral_map (measurable_of_finite f) (hF _ _ _)).symm
    simp_rw [hh]
    rw [ih (Fin.init obs) (fun a => ∫⁻ b, f b ∂P (n+1) a (obs (Fin.last n)))]
    exact (Measure.lintegral_bind (measurable_of_finite _).aemeasurable
      (measurable_of_finite f).aemeasurable).symm

lemma coinRun_law {F : ℕ → J → O → I → J} {P : ℕ → J → O → Measure J}
    (hF : ∀ t j obs, Measurable (F t j obs))
    (hP : ∀ t j obs, volume.map (F t j obs) = P t j obs)
    (n : ℕ) (j : J) (obs : Fin n → O) :
    (Measure.pi (fun _ => (volume : Measure I))).map (coinRun F n j obs) = kernelRun P n j obs := by
  apply Measure.ext
  intro s hs
  have hh := lintegral_coinRun hF hP n j obs (s.indicator (fun _ => (1 : ℝ≥0∞)))
  rw [← lintegral_map (by fun_prop) (measurable_coinRun hF n j obs)] at hh
  simpa only [lintegral_indicator_const hs,one_mul] using hh

omit [Fintype J] [MeasurableSpace J] [MeasurableSingletonClass J] [MeasurableSpace O] in
lemma kernelRun_congr [Fintype J] [MeasurableSpace J] [MeasurableSingletonClass J]
    [MeasurableSpace O] {P P' : ℕ → J → O → Measure J} (n : ℕ) (j : J) (obs : Fin n → O)
    (h : ∀ t a i, P t a (obs i) = P' t a (obs i)) :
    kernelRun P n j obs = kernelRun P' n j obs := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [kernelRun]
    rw [ih (Fin.init obs) (fun t a i => h t a i.castSucc)]
    congr 1
    funext a
    exact h _ _ _

end NoiselessRegression

end

end OAI
