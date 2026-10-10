import OAI.NumberTheory.Jacobsthal.Estimates.PairTraceBridge

namespace OAI

namespace Erdos970

section

namespace Erdos970Dependency.MarkedVisits
open Set MeasureTheory ProbabilityTheory Function Preorder
open scoped ProbabilityTheory ENNReal
open NumberTheoryLean.FinitePathMeasures NumberTheoryLean.PairedCostProcess
open NumberTheoryLean.PairedCostGrouping

noncomputable def pathPairEval (h : ∀ _ : Finset.Iic (2:ℕ), CostState) : CostState × CostState :=
  (h ⟨1,by decide⟩,h ⟨2,by decide⟩)

lemma pathPairEval_measurable : Measurable pathPairEval :=
  (measurable_pi_apply (⟨1,by decide⟩ : Finset.Iic (2:ℕ))).prodMk
    (measurable_pi_apply (⟨2,by decide⟩ : Finset.Iic (2:ℕ)))

theorem finitePath_two_trace (z : CostState) :
    ((finitePathKernel 2) (fun _ => z)).map pathPairEval = fullPairTraceKernel z := by
  apply Measure.ext_of_lintegral
  intro F hF
  let G : (ℕ → CostState) → ℝ≥0∞ := fun x => F (x 1,x 2)
  have hG : Measurable G := hF.comp ((measurable_pi_apply 1).prodMk (measurable_pi_apply 2))
  have he : (∫⁻ h, F (pathPairEval h) ∂finitePathKernel 2 (fun _ => z)) =
      Kernel.lmarginalPartialTraj historyKernel 0 2 G (fun _ => z) := by
    unfold Kernel.lmarginalPartialTraj finitePathKernel
    apply lintegral_congr
    intro h
    simp [G,pathPairEval,Function.updateFinset]
  rw [lintegral_map hF pathPairEval_measurable,he]
  have hc := congrFun (Kernel.lmarginalPartialTraj_self (κ := historyKernel)
    (show (0:ℕ) ≤ 1 by decide) (show (1:ℕ) ≤ 2 by decide) hG) (fun _ => z)
  rw [← hc,Kernel.lmarginalPartialTraj_succ 0
    (Kernel.measurable_lmarginalPartialTraj 1 2 hG)]
  have hi (t : CostState) : Kernel.lmarginalPartialTraj historyKernel 1 2 G
      (Function.update (fun _ => z) 1 t) = ∫⁻ u, F (t,u) ∂costKernel t := by
    rw [Kernel.lmarginalPartialTraj_succ 1 hG]
    simp [G,historyKernel,Kernel.comap_apply,frestrictLe,Function.update]
  simp_rw [hi]
  rw [fullPairTraceKernel,Kernel.lintegral_compProd _ _ _ hF]
  rfl

theorem sourcePair_canonical_history (z : OddCost) :
    (pairWitnessKernel z).map (pairTraceOfWitness z) =
      ((finitePathKernel 2) (fun _ => embedOdd z)).map pathPairEval := by
  rw [pairWitness_joint_full_trace,finitePath_two_trace]

end Erdos970Dependency.MarkedVisits

end

section

namespace Erdos970Dependency.MarkedVisits
open Set MeasureTheory ProbabilityTheory Function Preorder
open scoped ProbabilityTheory ENNReal
open NumberTheoryLean.FinitePathMeasures NumberTheoryLean.PairedCostProcess
open NumberTheoryLean.PairedCostGrouping

noncomputable def nextPairEval (n : ℕ) (h : ∀ _ : Finset.Iic (n+2), CostState) : CostState × CostState :=
  (h ⟨n+1,by simp⟩,h ⟨n+2,by simp⟩)

lemma nextPairEval_measurable (n : ℕ) : Measurable (nextPairEval n) :=
  (measurable_pi_apply (⟨n+1,by simp⟩ : Finset.Iic (n+2))).prodMk
    (measurable_pi_apply (⟨n+2,by simp⟩ : Finset.Iic (n+2)))

lemma conditional_pair_trace_extension (n : ℕ) (x0 : ℕ → CostState) :
    ((Kernel.partialTraj (X := fun _ => CostState) historyKernel n (n+2)) (frestrictLe n x0)).map (nextPairEval n) =
      fullPairTraceKernel (x0 n) := by
  apply Measure.ext_of_lintegral
  intro F hF
  let G : (ℕ → CostState) → ℝ≥0∞ := fun x => F (x (n+1),x (n+2))
  have hG : Measurable G := hF.comp ((measurable_pi_apply (n+1)).prodMk (measurable_pi_apply (n+2)))
  have he : (∫⁻ h, F (nextPairEval n h) ∂Kernel.partialTraj (X := fun _ => CostState) historyKernel n (n+2) (frestrictLe n x0)) =
      Kernel.lmarginalPartialTraj historyKernel n (n+2) G x0 := by
    unfold Kernel.lmarginalPartialTraj
    apply lintegral_congr
    intro h
    simp [G,nextPairEval,Function.updateFinset]
  rw [lintegral_map hF (nextPairEval_measurable n),he]
  have hc := congrFun (Kernel.lmarginalPartialTraj_self (κ := historyKernel)
    (show n ≤ n+1 by omega) (show n+1 ≤ n+2 by omega) hG) x0
  rw [← hc,Kernel.lmarginalPartialTraj_succ n
    (Kernel.measurable_lmarginalPartialTraj (n+1) (n+2) hG)]
  have hi (t : CostState) : Kernel.lmarginalPartialTraj historyKernel (n+1) (n+2) G
      (Function.update x0 (n+1) t) = ∫⁻ u, F (t,u) ∂costKernel t := by
    rw [Kernel.lmarginalPartialTraj_succ (n+1) hG]
    simp [G,historyKernel,Kernel.comap_apply,frestrictLe,Function.update]
  simp_rw [hi]
  rw [fullPairTraceKernel,Kernel.lintegral_compProd _ _ _ hF]
  rfl

theorem conditional_pair_trace (n : ℕ) (h : ∀ _ : Finset.Iic n, CostState) :
    ((Kernel.partialTraj (X := fun _ => CostState) historyKernel n (n+2)) h).map (nextPairEval n) =
      fullPairTraceKernel (h ⟨n,by simp⟩) := by
  let x0 : ℕ → CostState := fun i => if hi : i ≤ n then h ⟨i,Finset.mem_Iic.mpr hi⟩ else h ⟨n,by simp⟩
  have he : frestrictLe n x0 = h := by
    funext i
    simp only [frestrictLe_apply,x0,dite_eq_left (Finset.mem_Iic.mp i.2)]
  have hn : x0 n = h ⟨n,by simp⟩ := by simp [x0]
  simpa only [he,hn] using conditional_pair_trace_extension n x0

theorem sourcePair_after_history (n : ℕ) (h : ∀ _ : Finset.Iic n, CostState)
    (z : OddCost) (hz : h ⟨n,by simp⟩ = embedOdd z) :
    ((Kernel.partialTraj (X := fun _ => CostState) historyKernel n (n+2)) h).map (nextPairEval n) =
      (pairWitnessKernel z).map (pairTraceOfWitness z) := by
  rw [conditional_pair_trace,hz,pairWitness_joint_full_trace]

end Erdos970Dependency.MarkedVisits

end

section

namespace Erdos970Dependency.MarkedVisits
open Filter Set MeasureTheory ProbabilityTheory Function Preorder
open scoped ProbabilityTheory ENNReal
open NumberTheoryLean.FinitePathMeasures

lemma restriction_comp_of_retained_prefix {α β γ : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (K : Kernel α β) (L : Kernel β γ) {r : γ → β} (hr : Measurable r)
    (hPast : ∀ y, ∀ᵐ z ∂L y, r z=y) {B : Set β} {C : Set γ}
    (hB : MeasurableSet B) (hC : MeasurableSet C) :
    (L ∘ₖ K).restrict ((hr hB).inter hC) = (L.restrict hC) ∘ₖ (K.restrict hB) := by
  ext x S hS
  rw [Kernel.restrict_apply' _ _ _ hS,Kernel.comp_apply' _ _ _ (hS.inter ((hr hB).inter hC)),
    Kernel.comp_apply' _ _ _ hS,Kernel.restrict_apply]
  simp_rw [Kernel.restrict_apply' _ _ _ hS]
  rw [← lintegral_indicator hB]
  apply lintegral_congr
  intro y
  by_cases hy : y ∈ B
  · rw [indicator_of_mem hy]
    apply measure_congr
    filter_upwards [hPast y] with z hz
    apply propext
    change (z ∈ S ∧ (r z ∈ B ∧ z ∈ C)) ↔ (z ∈ S ∧ z ∈ C)
    simp only [hz,hy,true_and]
  · rw [indicator_of_notMem hy]
    calc
      _ = L y ∅ := by
        apply measure_congr
        filter_upwards [hPast y] with z hz
        apply propext
        change (z ∈ S ∧ (r z ∈ B ∧ z ∈ C)) ↔ False
        simp only [hz,hy,false_and,and_false]
      _ = 0 := measure_empty

abbrev RawHistory (n : ℕ) := ∀ _ : Finset.Iic n, CostState

def rawPrefix {a b : ℕ} (hab : a ≤ b) : RawHistory b → RawHistory a :=
  frestrictLe₂ (π := fun _ => CostState) hab

lemma rawPrefix_measurable {a b : ℕ} (hab : a ≤ b) : Measurable (rawPrefix hab) :=
  measurable_frestrictLe₂ (X := fun _ => CostState) hab

noncomputable def rawExtension (a b : ℕ) : Kernel (RawHistory a) (RawHistory b) :=
  Kernel.partialTraj (X := fun _ => CostState) historyKernel a b

instance rawExtension_isMarkovKernel (a b : ℕ) : IsMarkovKernel (rawExtension a b) := by
  unfold rawExtension
  infer_instance

local instance : MeasurableSingletonClass State := by
  constructor
  intro x
  cases x with
  | inl e =>
    simpa only [image_singleton] using ((measurableSet_singleton e).inl_image :
      MeasurableSet (Sum.inl '' {e} : Set State))
  | inr o =>
    simpa only [image_singleton] using ((measurableSet_singleton o).inr_image :
      MeasurableSet (Sum.inr '' {o} : Set State))

lemma rawExtension_retains_prefix {b c : ℕ} (hbc : b ≤ c) (h : RawHistory b) :
    ∀ᵐ z ∂rawExtension b c h, rawPrefix hbc z = h := by
  have he : (rawExtension b c h).map (rawPrefix hbc) = Measure.dirac h := by
    rw [rawExtension,rawPrefix,Kernel.partialTraj_map_frestrictLe₂_apply (X := fun _ => CostState) (κ := historyKernel) h hbc,Kernel.partialTraj_self,Kernel.id_apply]
  have hd : ∀ᵐ y ∂(rawExtension b c h).map (rawPrefix hbc), y=h := by
    rw [he]
    exact ae_eq_dirac' measurable_id
  exact (ae_map_iff (rawPrefix_measurable hbc).aemeasurable (measurableSet_singleton h)).mp hd

theorem rawExtension_restrict_comp {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c)
    {B : Set (RawHistory b)} {C : Set (RawHistory c)}
    (hB : MeasurableSet B) (hC : MeasurableSet C) :
    (rawExtension a c).restrict (((rawPrefix_measurable hbc) hB).inter hC) =
      ((rawExtension b c).restrict hC) ∘ₖ ((rawExtension a b).restrict hB) := by
  rw [← restriction_comp_of_retained_prefix _ _ (rawPrefix_measurable hbc)
    (rawExtension_retains_prefix hbc) hB hC]
  have he : rawExtension b c ∘ₖ rawExtension a b = rawExtension a c :=
    Kernel.partialTraj_comp_partialTraj hab hbc
  rw [he]

end Erdos970Dependency.MarkedVisits

end

end Erdos970

end OAI
