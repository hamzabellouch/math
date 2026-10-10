import OAI.Probability.DilutedSpin.CavityInsertionAlgebra
import OAI.Probability.DilutedSpin.PerturbedEnergyMean
import OAI.Probability.DilutedSpin.RandomInsertion

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory _root_.OAI.MeasureTheory Filter
open scoped BigOperators Topology

namespace FiniteLaw
lemma spinLog_reindex {ι κ : Type} [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (F : (ι → Spin) → ℝ) (x : κ → ℝ) :
    spinLog (fun s : κ → Spin => F (fun i => s (e i))) x = spinLog F (fun i => x (e i)) := by
  classical
  rw [spinLog_eq,spinLog_eq]
  apply congrArg Real.log
  apply Fintype.sum_equiv (Equiv.arrowCongr e.symm (Equiv.refl Spin))
  intro s
  change (∏ j : κ,q (x j) (s j))*Real.exp (F (fun i => s (e i))) =
    (∏ i : ι,q (x (e i)) (s (e i)))*Real.exp (F (fun i => s (e i)))
  rw [e.prod_comp (fun j => q (x j) (s j))]
end FiniteLaw

namespace UniversalDictionary
open ConcreteReservoir

noncomputable def reservoirInsertionOn {ι : Type} [Fintype ι] {p : ℕ}
    (M : Model p) (C H : ℝ) (N L : ℕ) (u : Spec L×ℕ → ℝ) (F : (ι → Spin) → ℝ) : ℝ :=
  reservoirInsertion M C H N L u (Fintype.card ι)
    (fun s => F (fun i => s (Fintype.equivFin ι i)))

lemma reservoirInsertionOn_bound {ι : Type} [Fintype ι] {p : ℕ}
    (M : Model p) (C H : ℝ) (N L : ℕ) (u : Spec L×ℕ → ℝ) (F : (ι → Spin) → ℝ)
    {D : ℝ} (hF : ∀ s,|F s|≤D) : |reservoirInsertionOn M C H N L u F|≤D :=
  reservoirInsertion_bound M C H N L u (Fintype.card ι) _ (fun _ => hF _)

lemma trialLog_spinLog_reindex {ι κ : Type} [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (r : ℕ) (ζ : Hierarchy (r+1)) (m : Fin r → ℝ) (F : (ι → Spin) → ℝ) :
    trialLog r ζ m (FiniteLaw.spinLog (fun s : κ → Spin => F (fun i => s (e i)))) =
      trialLog r ζ m (FiniteLaw.spinLog F) := by
  have he : FiniteLaw.spinLog (fun s : κ → Spin => F (fun i => s (e i))) =
      (fun x : κ → ℝ => FiniteLaw.spinLog F (fun i => x (e i))) :=
    funext (FiniteLaw.spinLog_reindex e F)
  rw [he]
  exact trialLog_reindex e r (FiniteLaw.spinLog F) m ζ

lemma randomInsertionOn_comparison_tendsto {ι X : Type} [Fintype ι] [MeasurableSpace X]
    {p : ℕ} (M : Model p) (hα : 0<M.alpha) (C H : ℝ)
    (Ns : ℕ → ℕ → ℕ) (hNs : ∀ L,Tendsto (Ns L) atTop atTop)
    (us : (L : ℕ) → ℕ → Spec L×ℕ → ℝ)
    (hcontrol : ∀ L,FullShapeControl M C H L (Ns L) (us L))
    (μ : Measure X) [IsProbabilityMeasure μ] (F : X → (ι → Spin) → ℝ)
    (hFm : Measurable F) {D : ℝ} (hD : 0≤D) (hF : ∀ x s,|F x s|≤D) :
    Tendsto (fun L => limsup (fun n =>
      |(∫ x,reservoirInsertionOn M C H (Ns L n+1) L (us L n) (F x) ∂μ)-
        (∫ x,trialLog L (reservoirTrialLaw M C H (Ns L n+1) L (us L n))
          (fun i => gridExponents L i.castSucc) (FiniteLaw.spinLog (F x)) ∂μ)|) atTop) atTop (𝓝 0) := by
  have h := randomInsertion_comparison_tendsto M hα C H Ns hNs us hcontrol (Fintype.card ι) μ
    (fun x s => F x (fun i => s (Fintype.equivFin ι i)))
    (Measurable.of_eval (fun _ => (measurable_pi_apply _).comp hFm)) hD (fun x _ => hF x _)
  simpa only [reservoirInsertionOn,trialLog_spinLog_reindex] using h

end UniversalDictionary
end DilutedSpinGlass

end

section
namespace DilutedSpinGlass.PhysicalRoot
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory HeterogeneousMarks KernelTower
open scoped BigOperators NNReal
variable {Y I : Type} [MeasurableSpace Y] [Countable I] [MeasurableSpace I]
    [MeasurableSingletonClass I] {A : I → Type} [∀ i,Fintype (A i)] {N L : ℕ}

omit [MeasurableSpace Y] [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I] in
lemma energyRoot_bound (Q : (i : I) → Fin (L+1) → FiniteLaw (A i))
    (m : Fin (L+1) → ℝ) (hm : ∀ i,0 < m i) (field : Y → ℝ)
    (factor : (i : I) → FinitePath (Fin N → Spin) (L+1) → FinitePath (A i) (L+1) → ℝ)
    {H D : ℝ} (hh : ∀ y,|field y|≤H) (hf : ∀ i y a,|Real.log (factor i y a)|≤D)
    (h : RootPath Y N) (a : Sigma (RootPath I)) (E : (Fin N → Spin) → ℝ) :
    |energyRoot Q m field factor h a E|≤‖E‖+H*N+D*a.1 := by
  apply root_uniform_bound _ Q m hm _ _ factor _ hf
  intro y
  apply (abs_add_le _ _).trans
  apply add_le_add
  · simpa only [Real.norm_eq_abs] using norm_le_pi_norm E (terminalState L y)
  · apply (Finset.abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ i : Fin N,H := Finset.sum_le_sum (fun i _ => by
        rw [abs_mul,abs_spin,mul_one]; exact hh _)
      _ = H*N := by simp [mul_comm]

lemma measurable_energyRoot (Q : (i : I) → Fin (L+1) → FiniteLaw (A i))
    (m : Fin (L+1) → ℝ) (field : Y → ℝ) (hh : Measurable field)
    (factor : (i : I) → FinitePath (Fin N → Spin) (L+1) → FinitePath (A i) (L+1) → ℝ) :
    Measurable (fun z : ((RootPath Y N) × ((Fin N → Spin) → ℝ)) × Sigma (RootPath I) =>
      energyRoot Q m field factor z.1.1 z.2 z.1.2) := by
  apply measurable_prodSigma (f := fun (z : (RootPath Y N) × ((Fin N → Spin) → ℝ)) n a => energyRoot Q m field factor z.1 ⟨n,a⟩ z.2)
  intro k
  apply measurable_from_prod_countable_left
  intro a
  apply measurable_root _ Q m _ (rootArray k a) (fun _ => factor) _ (fun _ _ _ => measurable_const)
  intro y
  exact ((measurable_pi_apply _).comp measurable_snd).add
    (Finset.measurable_sum _ (fun i _ => (hh.comp ((measurable_rootArray N i).comp measurable_fst)).mul_const _))

noncomputable def averagedEnergyRoot (ξ : Measure Y) (ν : Measure I) (s : ℝ≥0)
    (Q : (i : I) → Fin (L+1) → FiniteLaw (A i)) (m : Fin (L+1) → ℝ) (field : Y → ℝ)
    (factor : (i : I) → FinitePath (Fin N → Spin) (L+1) → FinitePath (A i) (L+1) → ℝ)
    (E : (Fin N → Spin) → ℝ) : ℝ :=
  ∫ h,∫ a,energyRoot Q m field factor h a E ∂compoundRootLaw ν s ∂rootLaw N (fun _ => ξ)

omit [MeasurableSpace Y] in
lemma integrable_energyRoot_marks (ν : Measure I) [IsProbabilityMeasure ν] (s : ℝ≥0)
    (Q : (i : I) → Fin (L+1) → FiniteLaw (A i)) (m : Fin (L+1) → ℝ) (hm : ∀ i,0 < m i)
    (field : Y → ℝ) (factor : (i : I) → FinitePath (Fin N → Spin) (L+1) → FinitePath (A i) (L+1) → ℝ)
    {H D : ℝ} (hh : ∀ y,|field y|≤H) (hf : ∀ i y a,|Real.log (factor i y a)|≤D)
    (h : RootPath Y N) (E : (Fin N → Spin) → ℝ) :
    Integrable (fun a => energyRoot Q m field factor h a E) (compoundRootLaw ν s) := by
  have hc : Integrable (fun a : Sigma (RootPath I) => (a.1:ℝ)) (compoundRootLaw ν s) :=
    familyPoisson_count_integrable (fun n => rootLaw n (fun _ => ν)) s
  have hmeas : Measurable (fun a : Sigma (RootPath I) => energyRoot Q m field factor h a E) :=
    measurable_sigmaUncurry (f := fun n a => energyRoot Q m field factor h ⟨n,a⟩ E) (fun n => measurable_of_countable _)
  apply ((integrable_const (‖E‖+H*N)).add (hc.const_mul D)).mono' hmeas.aestronglyMeasurable
  exact ae_of_all _ (fun a => by simpa only [Real.norm_eq_abs,Pi.add_apply] using energyRoot_bound Q m hm field factor hh hf h a E)

omit [MeasurableSpace Y] in
lemma energyRoot_marks_bound (ν : Measure I) [IsProbabilityMeasure ν] (s : ℝ≥0)
    (Q : (i : I) → Fin (L+1) → FiniteLaw (A i)) (m : Fin (L+1) → ℝ) (hm : ∀ i,0 < m i)
    (field : Y → ℝ) (factor : (i : I) → FinitePath (Fin N → Spin) (L+1) → FinitePath (A i) (L+1) → ℝ)
    {H D : ℝ} (hh : ∀ y,|field y|≤H) (hf : ∀ i y a,|Real.log (factor i y a)|≤D)
    (h : RootPath Y N) (E : (Fin N → Spin) → ℝ) :
    |∫ a,energyRoot Q m field factor h a E ∂compoundRootLaw ν s|≤‖E‖+H*N+D*s := by
  apply (abs_integral_le_integral_abs).trans
  apply (integral_mono (integrable_energyRoot_marks ν s Q m hm field factor hh hf h E).abs
    ((integrable_const (‖E‖+H*N)).add ((familyPoisson_count_integrable (fun n => rootLaw n (fun _ => ν)) s).const_mul D))
    (fun a => energyRoot_bound Q m hm field factor hh hf h a E)).trans_eq
  simp only [Pi.add_apply]
  change (∫ a : Sigma (RootPath I), (‖E‖+H*N)+D*a.1 ∂familyLaw (poissonMeasure s) (fun n => rootLaw n (fun _ => ν))) = _
  rw [integral_add (integrable_const _) ((familyPoisson_count_integrable (fun n => rootLaw n (fun _ => ν)) s).const_mul D),
    integral_const_mul,familyPoisson_count_mean]
  simp

lemma averagedEnergyRoot_lipschitz (ξ : Measure Y) [IsProbabilityMeasure ξ]
    (ν : Measure I) [IsProbabilityMeasure ν] (s : ℝ≥0)
    (Q : (i : I) → Fin (L+1) → FiniteLaw (A i)) (m : Fin (L+1) → ℝ) (hm : ∀ i,0 < m i)
    (field : Y → ℝ) (hhm : Measurable field)
    (factor : (i : I) → FinitePath (Fin N → Spin) (L+1) → FinitePath (A i) (L+1) → ℝ)
    {H D : ℝ} (hh : ∀ y,|field y|≤H) (hf : ∀ i y a,|Real.log (factor i y a)|≤D) :
    LipschitzWith 1 (averagedEnergyRoot ξ ν s Q m field factor) := by
  have hmi E : Measurable (fun h : RootPath Y N => ∫ a,energyRoot Q m field factor h a E ∂compoundRootLaw ν s) := by
    exact ((measurable_energyRoot Q m field hhm factor).comp
      ((measurable_fst.prodMk measurable_const).prodMk measurable_snd)).stronglyMeasurable.integral_prod_right'.measurable
  have hi E : Integrable (fun h : RootPath Y N => ∫ a,energyRoot Q m field factor h a E ∂compoundRootLaw ν s) (rootLaw N (fun _ => ξ)) :=
    bounded_memLp (hmi E) (fun h => energyRoot_marks_bound ν s Q m hm field factor hh hf h E) 1 |>.integrable le_rfl
  apply LipschitzWith.of_dist_le_mul
  intro E F
  simp only [NNReal.coe_one,one_mul,dist_eq_norm,Real.norm_eq_abs,averagedEnergyRoot]
  rw [← integral_sub (hi E) (hi F)]
  apply abs_integral_le_bound
  intro h
  rw [← integral_sub (integrable_energyRoot_marks ν s Q m hm field factor hh hf h E)
    (integrable_energyRoot_marks ν s Q m hm field factor hh hf h F)]
  apply abs_integral_le_bound
  intro a
  simpa only [dist_eq_norm,Real.norm_eq_abs,NNReal.coe_one,one_mul] using
    (energyRoot_lipschitz Q m hm field factor h a).dist_le_mul E F

end DilutedSpinGlass.PhysicalRoot

end

end OAI
