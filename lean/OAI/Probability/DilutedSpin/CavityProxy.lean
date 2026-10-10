import OAI.Probability.DilutedSpin.CavityInsertionAlgebra
import OAI.Probability.DilutedSpin.CavityTrialIdentity
import OAI.Probability.DilutedSpin.FunctionalContinuity
import OAI.Probability.DilutedSpin.InsertionPoissonAlgebra
import OAI.Probability.DilutedSpin.MixedPatterns
import OAI.Probability.DilutedSpin.TowerPadding
import OAI.Probability.DilutedSpin.UpperRootInsertion

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal BigOperators

namespace UniversalDictionary
open ConcreteReservoir

noncomputable def cavityProxy {p : ℕ} (M : Model p) (C H : ℝ)
    (N L : ℕ) (u : Spec L×ℕ → ℝ) : ℝ := Real.log 2+
  insertionPoisson M C H N L u
    (fun k => (Measure.pi (fun _ : Fin k => M.disorder.toMeasure)).prod M.field.toMeasure)
    (fun _ z => cavitySiteEnergy z.1 z.2) (M.alpha*p)-
  insertionPoisson M C H N L u
    (fun k => Measure.pi (fun _ : Fin k => M.disorder.toMeasure))
    (fun _ θ => cavityBondEnergy θ) (M.alpha*(p-1:ℕ))

lemma cavitySiteEnergy_ae_bound {p k : ℕ} (M : Model p) {C H : ℝ}
    (hθ : ∀ᵐ z ∂M.disorder.toMeasure,‖z.1‖≤C)
    (hh : ∀ᵐ h ∂M.field.toMeasure,|h|≤H) :
    ∀ᵐ z ∂(Measure.pi (fun _ : Fin k => M.disorder.toMeasure)).prod M.field.toMeasure,
      ∀ s,|cavitySiteEnergy z.1 z.2 s|≤H+C*k := by
  have ht : ∀ᵐ θ ∂Measure.pi (fun _ : Fin k => M.disorder.toMeasure),∀ j,‖(θ j).1‖≤C :=
    Filter.eventually_all.mpr (fun j => (Measure.tendsto_eval_ae_ae (μ := fun _ : Fin k => M.disorder.toMeasure) (i := j)).eventually hθ)
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae ht,Measure.quasiMeasurePreserving_snd.ae hh] with z hz hh
  intro s
  apply (cavitySiteEnergy_bound z.1 z.2 s).trans
  have hs := Finset.sum_le_sum (fun j (_ : j∈(Finset.univ : Finset (Fin k))) => hz j)
  simpa [mul_comm] using add_le_add hh hs

lemma cavityBondEnergy_ae_bound {p k : ℕ} (M : Model p) {C : ℝ}
    (hθ : ∀ᵐ z ∂M.disorder.toMeasure,‖z.1‖≤C) :
    ∀ᵐ θ ∂Measure.pi (fun _ : Fin k => M.disorder.toMeasure),
      ∀ s,|cavityBondEnergy θ s|≤0+C*k := by
  have ht : ∀ᵐ θ ∂Measure.pi (fun _ : Fin k => M.disorder.toMeasure),∀ j,‖(θ j).1‖≤C :=
    Filter.eventually_all.mpr (fun j => (Measure.tendsto_eval_ae_ae (μ := fun _ : Fin k => M.disorder.toMeasure) (i := j)).eventually hθ)
  filter_upwards [ht] with θ hθ
  intro s
  apply (cavityBondEnergy_bound θ s).trans
  simpa [mul_comm] using Finset.sum_le_sum (fun j (_ : j∈(Finset.univ : Finset (Fin k))) => hθ j)

lemma cavityProxy_comparison_tendsto {p : ℕ} (M : Model p) (hα : 0<M.alpha)
    {C H : ℝ} (hC : 0≤C) (hH : 0≤H)
    (hθ : ∀ᵐ z ∂M.disorder.toMeasure,‖z.1‖≤C)
    (hh : ∀ᵐ h ∂M.field.toMeasure,|h|≤H)
    (hθi : Integrable (fun z : InteractionSample p => ‖z.1‖) M.disorder.toMeasure)
    (hhi : Integrable (fun h : ℝ => |h|) M.field.toMeasure)
    (Ns : ℕ → ℕ → ℕ) (hNs : ∀ L,Tendsto (Ns L) atTop atTop)
    (us : (L : ℕ) → ℕ → Spec L×ℕ → ℝ)
    (hcontrol : ∀ L,FullShapeControl M C H L (Ns L) (us L)) :
    Tendsto (fun L => limsup (fun n =>
      |cavityProxy M C H (Ns L n+1) L (us L n)-
        functional M L (reservoirTrialLaw M C H (Ns L n+1) L (us L n))
          (fun i => gridExponents L i.castSucc)|) atTop) atTop (𝓝 0) := by
  let μs := fun k => (Measure.pi (fun _ : Fin k => M.disorder.toMeasure)).prod M.field.toMeasure
  let μb := fun k => Measure.pi (fun _ : Fin k => M.disorder.toMeasure)
  let Fs := fun (k : ℕ) (z : (Fin k → InteractionSample p)×ℝ) => cavitySiteEnergy z.1 z.2
  let Fb := fun (k : ℕ) (θ : Fin k → InteractionSample p) => cavityBondEnergy θ
  let es := fun L n => ∫ k,|(∫ x,reservoirInsertionOn M C H (Ns L n+1) L (us L n) (Fs k x) ∂μs k)-
    (∫ x,trialLog L (reservoirTrialLaw M C H (Ns L n+1) L (us L n))
      (fun i => gridExponents L i.castSucc) (FiniteLaw.spinLog (Fs k x)) ∂μs k)| ∂poissonMeasure (M.alpha*p)
  let eb := fun L n => ∫ k,|(∫ x,reservoirInsertionOn M C H (Ns L n+1) L (us L n) (Fb k x) ∂μb k)-
    (∫ x,trialLog L (reservoirTrialLaw M C H (Ns L n+1) L (us L n))
      (fun i => gridExponents L i.castSucc) (FiniteLaw.spinLog (Fb k x)) ∂μb k)| ∂poissonMeasure (M.alpha*(p-1:ℕ))
  let (k : ℕ) : OpensMeasurableSpace (Fin k → InteractionSample p) := Pi.opensMeasurableSpace
  have hFs k : Measurable (Fs k) := continuous_cavitySiteEnergy.measurable
  have hFb k : Measurable (Fb k) := continuous_cavityBondEnergy.measurable
  have hsb k := cavitySiteEnergy_ae_bound (k := k) M hθ hh
  have hbb k := cavityBondEnergy_ae_bound (k := k) M hθ
  have hs := poissonInsertionOn_comparison_tendsto_ae M hα C H Ns hNs us hcontrol μs Fs hFs hH hC hsb (M.alpha*p)
  have hb := poissonInsertionOn_comparison_tendsto_ae M hα C H Ns hNs us hcontrol μb Fb hFb (le_refl 0) hC hbb (M.alpha*(p-1:ℕ))
  have hsbound L n : es L n≤2*H+2*C*(M.alpha*p) := by
    apply (le_abs_self _).trans
    apply poisson_average_bound
    intro k
    rw [abs_abs]
    have h1 := abs_integral_le_bound_ae (μs k) ((hsb k).mono (fun x hx => reservoirInsertionOn_bound M C H (Ns L n+1) L (us L n) (Fs k x) hx))
    have h2 := abs_integral_le_bound_ae (μs k) ((hsb k).mono (fun x hx => (trialLog_continuous_bound L _ (FiniteLaw.spinLog_continuous (Fs k x)) (FiniteLaw.spinLog_bound (Fs k x) hx) _ (fun i => gridExponents_pos L i.castSucc)).2 (reservoirTrialLaw M C H (Ns L n+1) L (us L n))))
    exact (abs_sub _ _).trans (by linarith)
  have hbbound L n : eb L n≤0+2*C*(M.alpha*(p-1:ℕ)) := by
    apply (le_abs_self _).trans
    apply poisson_average_bound
    intro k
    rw [abs_abs]
    have h1 := abs_integral_le_bound_ae (μb k) ((hbb k).mono (fun x hx => reservoirInsertionOn_bound M C H (Ns L n+1) L (us L n) (Fb k x) hx))
    have h2 := abs_integral_le_bound_ae (μb k) ((hbb k).mono (fun x hx => (trialLog_continuous_bound L _ (FiniteLaw.spinLog_continuous (Fb k x)) (FiniteLaw.spinLog_bound (Fb k x) hx) _ (fun i => gridExponents_pos L i.castSucc)).2 (reservoirTrialLaw M C H (Ns L n+1) L (us L n))))
    exact (abs_sub _ _).trans (by linarith)
  apply double_limit_two _ es eb (fun _ _ => abs_nonneg _) (fun _ _ => integral_nonneg (fun _ => abs_nonneg _))
    (fun _ _ => integral_nonneg (fun _ => abs_nonneg _)) hsbound hbbound ?_ hs hb
  intro L n
  rw [functional_cavity_trial M hθi hhi _ _ (fun i => gridExponents_pos L i.castSucc)]
  have hs' := insertionPoisson_comparison_bound M C H (Ns L n+1) L (us L n) μs Fs hsb (M.alpha*p)
  have hb' := insertionPoisson_comparison_bound M C H (Ns L n+1) L (us L n) μb Fb hbb (M.alpha*(p-1:ℕ))
  have hh := (abs_sub (insertionPoisson M C H (Ns L n+1) L (us L n) μs Fs (M.alpha*p)-trialPoisson L (reservoirTrialLaw M C H (Ns L n+1) L (us L n)) μs Fs (M.alpha*p))
    (insertionPoisson M C H (Ns L n+1) L (us L n) μb Fb (M.alpha*(p-1:ℕ))-trialPoisson L (reservoirTrialLaw M C H (Ns L n+1) L (us L n)) μb Fb (M.alpha*(p-1:ℕ)))).trans (add_le_add hs' hb')
  have hlin (a b c d x : ℝ) : |(x+a-b)-(x+c-d)|=|(a-c)-(b-d)| := by congr 1; ring
  simpa only [cavityProxy,trialPoisson,Fs,Fb,μs,μb,es,eb,hlin] using hh

end UniversalDictionary
end DilutedSpinGlass

end

section
namespace DilutedSpinGlass
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Filter
open scoped NNReal BigOperators

noncomputable def functionalEnvelope {p : ℕ} (M : Model p) : ℝ :=
  fieldMoment M+((M.alpha:ℝ)*p+(M.alpha:ℝ)*(p-1:ℕ))*interactionMoment M

lemma functional_envelope {p r : ℕ} (M : Model p)
    (hθ : Integrable (fun z : InteractionSample p => ‖z.1‖) M.disorder.toMeasure)
    (hh : Integrable (fun h : ℝ => |h|) M.field.toMeasure)
    (ζ : Hierarchy (r+1)) (m : Fin r → ℝ) (hm : ∀ i,0 < m i) :
    |functional M r ζ m-Real.log 2|≤functionalEnvelope M := by
  have hs := poisson_average_bound (M.alpha*p) (trialSiteDisorder M m ζ)
    (B := fieldMoment M) (D := interactionMoment M)
    (fun k => (trialSiteDisorder_bound M m hm hθ hh ζ k).trans_eq (by
      simp only [fieldMoment,interactionMoment]; ring))
  have he : |∫ θ : InteractionSample p,trialLog r ζ m (fun x => Real.log (edge θ.1 x)) ∂M.disorder.toMeasure| ≤ interactionMoment M := by
    simpa only [Real.norm_eq_abs,interactionMoment] using
      norm_integral_le_of_norm_le (f := fun θ : InteractionSample p => trialLog r ζ m (fun x => Real.log (edge θ.1 x))) hθ (ae_of_all _ (fun θ => by
        simpa only [Real.norm_eq_abs] using trial_edge_bound r m hm ζ θ.1))
  have he' := mul_le_mul_of_nonneg_left he
    (show 0≤(M.alpha:ℝ)*(p-1:ℕ) by positivity)
  rw [← abs_of_nonneg (show 0≤(M.alpha:ℝ)*(p-1:ℕ) by positivity),← abs_mul] at he'
  rw [abs_of_nonneg (show 0≤(M.alpha:ℝ)*(p-1:ℕ) by positivity)] at he'
  have hx := (abs_sub (∫ k,trialSiteDisorder M m ζ k ∂poissonMeasure (M.alpha*p))
    ((M.alpha:ℝ)*(p-1:ℕ)*(∫ θ : InteractionSample p,trialLog r ζ m (fun x => Real.log (edge θ.1 x)) ∂M.disorder.toMeasure))).trans (add_le_add hs he')
  have hid : functional M r ζ m-Real.log 2 =
      (∫ k,trialSiteDisorder M m ζ k ∂poissonMeasure (M.alpha*p))-
      (M.alpha:ℝ)*(p-1:ℕ)*(∫ θ : InteractionSample p,trialLog r ζ m (fun x => Real.log (edge θ.1 x)) ∂M.disorder.toMeasure) := by
    simp only [functional,trialSiteDisorder,trialSiteField]
    ring
  rw [hid]
  apply hx.trans_eq
  simp only [functionalEnvelope,NNReal.coe_mul,NNReal.coe_natCast]
  ring

lemma variationalValue_le_functional_integrable {p : ℕ} (M : Model p)
    (hθ : Integrable (fun z : InteractionSample p => ‖z.1‖) M.disorder.toMeasure)
    (hh : Integrable (fun h : ℝ => |h|) M.field.toMeasure)
    (r : ℕ) (ζ : Hierarchy (r+1)) (m : Fin r → ℝ) (hm : Exponents m) :
    variationalValue M≤functional M r ζ m := by
  have hl r ζ m (hm : Exponents m) : Real.log 2-functionalEnvelope M≤functional M r ζ m := by
    have hh := (abs_le.mp (functional_envelope M hθ hh ζ m (fun i => (hm.2 i).1))).1
    linarith
  have hphi r : Real.log 2-functionalEnvelope M≤phi M r := by
    obtain ⟨m,hm⟩ := exponents_nonempty r
    apply le_csInf
    · exact ⟨functional M r (zeroHierarchy (r+1)) m,zeroHierarchy (r+1),m,hm,rfl⟩
    · rintro v ⟨ζ,m,hm,rfl⟩
      exact hl r ζ m hm
  apply (ciInf_le (show BddBelow (Set.range (phi M)) from ⟨_,by rintro v ⟨t,rfl⟩; exact hphi t⟩) r).trans
  apply csInf_le
  · exact ⟨_,by rintro v ⟨ζ,m,hm,rfl⟩; exact hl r ζ m hm⟩
  · exact ⟨ζ,m,hm,rfl⟩

end DilutedSpinGlass

end

section
namespace DilutedSpinGlass
open _root_.MeasureTheory _root_.OAI.MeasureTheory
open scoped BigOperators
namespace FiniteLaw
lemma pi_point {ι : Type} [Fintype ι] [DecidableEq ι] {α : ι → Type}
    [∀ i,Fintype (α i)] (a : (i : ι) → α i) :
    pi (fun i => point (a i))=point a := by
  classical
  apply ext
  intro b
  by_cases h : a=b
  · subst b; simp [pi,point]
  · obtain ⟨i,hi⟩ := Function.ne_iff.mp h
    simp only [pi,point,ite_eq_right (Ne.symm h)]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right (Ne.symm hi))
end FiniteLaw

lemma mixedEnergy_true {p : ℕ} (z : InteractionSample p)
    (s : Fin p → Spin) (x : Fin p → ℝ) :
    mixedEnergy z (fun _ => true) s x=z.1 s := by
  unfold mixedEnergy mixedSpinLaw
  simp only [↓reduceIte,FiniteLaw.pi_point,FiniteLaw.logMean,FiniteLaw.expMoment,
    FiniteLaw.expect_point,one_mul,div_one,Real.log_exp]

lemma mixedEnergy_false {p : ℕ} (z : InteractionSample p)
    (s : Fin p → Spin) (x : Fin p → ℝ) :
    mixedEnergy z (fun _ => false) s x=Real.log (edge z.1 x) := by
  unfold mixedEnergy mixedSpinLaw
  simp only [Bool.false_eq_true,↓reduceIte,FiniteLaw.logMean,FiniteLaw.expMoment,one_mul,div_one,
    FiniteLaw.expect,FiniteLaw.pi,qLaw]
  congr 1
  unfold edge
  exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)

namespace PrescribedTree
variable {Ω Λ R : Type} [Fintype Ω] [Fintype Λ] [Fintype R]
    {n p N : ℕ} [NeZero N]

noncomputable def edgeRoot (Q : FiniteLaw R) (U : R → KernelTower Λ n)
    (x : R → FinitePath Λ n → ℝ) (m : Fin n → ℝ) (z : InteractionSample p) : ℝ :=
  (FiniteLaw.pi (fun _ : Fin p => Q)).expect (fun r =>
    KernelTower.backwardLog n (KernelTower.piTower n (fun j : Fin p => U (r j))) m
      (fun y => Real.log (edge z.1 (fun j => x (r j)
        (KernelTower.pathMap (fun a : Fin p → Λ => a j) n y)))))

lemma mixedRootIncrement_true (T : KernelTower Ω n)
    (Q : FiniteLaw R) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Fin N → Spin) (x : R → FinitePath Λ n → ℝ)
    (m : Fin (n+1) → ℝ) (f : FinitePath Ω n → ℝ) (z : InteractionSample p) :
    mixedRootIncrement T Q U V x m f z (fun _ => true)=
      (FiniteLaw.pi (fun _ : Fin p => (FiniteLaw.uniform : FiniteLaw (Fin N)))).expect (fun i =>
        KernelTower.backwardLog n T (fun j => m j.succ) (fun y => f y+z.1 (fun j => V y (i j)))-
          KernelTower.backwardLog n T (fun j => m j.succ) f) := by
  unfold mixedRootIncrement mixedTreeEnergy
  simp only [mixedEnergy_true]
  apply FiniteLaw.expect_congr
  intro i
  have he (r : Fin p → R) := KernelTower.backwardLog_prod_fst n T
    (KernelTower.piTower n (fun j : Fin p => U (r j))) (fun j => m j.succ)
    (fun y => f y+z.1 (fun j => V y (i j)))
  simp only [he,FiniteLaw.expect_const]

lemma mixedRootIncrement_false (T : KernelTower Ω n)
    (Q : FiniteLaw R) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Fin N → Spin) (x : R → FinitePath Λ n → ℝ)
    (m : Fin (n+1) → ℝ) (f : FinitePath Ω n → ℝ) (z : InteractionSample p) :
    mixedRootIncrement T Q U V x m f z (fun _ => false)=edgeRoot Q U x (fun j => m j.succ) z := by
  unfold mixedRootIncrement mixedTreeEnergy edgeRoot
  simp only [mixedEnergy_false]
  have he (r : Fin p → R) := KernelTower.backwardLog_prod_add n T
    (KernelTower.piTower n (fun j : Fin p => U (r j))) (fun j => m j.succ) f
    (fun y => Real.log (edge z.1 (fun j => x (r j)
      (KernelTower.pathMap (fun a : Fin p → Λ => a j) n y))))
  simp only [he,add_sub_cancel_left,FiniteLaw.expect_const]

/-- The upper local producer with an actual extensive energy in its old tree;
the compensator is independent of that tree and is precisely an edge root. -/
lemma integral_real_cavity_bound (M : Model p) (hM : Admissible M)
    (T : KernelTower Ω n) (Q : FiniteLaw R) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Fin N → Spin) (x : R → FinitePath Λ n → ℝ)
    (m : Fin (n+1) → ℝ) (hm : Monotone m) (hpos : ∀ j,0 ≤ m j)
    (hstrict : ∀ j : Fin n,0 < m j.succ) (hroot : m 0=0) (hend : m (Fin.last n)=1)
    (f : FinitePath Ω n → ℝ) (j : Fin p) :
    (∫ z,(FiniteLaw.pi (fun _ : Fin p => (FiniteLaw.uniform : FiniteLaw (Fin N)))).expect (fun i =>
        KernelTower.backwardLog n T (fun j => m j.succ) (fun y => f y+z.1 (fun j => V y (i j)))-
          KernelTower.backwardLog n T (fun j => m j.succ) f) ∂M.disorder.toMeasure)+
      ((p-1:ℕ):ℝ)*(∫ z,edgeRoot Q U x (fun j => m j.succ) z ∂M.disorder.toMeasure) ≤
      (p:ℝ)*(∫ z,mixedRootIncrement T Q U V x m f z (fun l => decide (l=j)) ∂M.disorder.toMeasure) := by
  have hh := integral_mixedRoot_combination_nonpos M hM T Q U V x m hm hpos hstrict hroot hend f j
  rw [show (fun z => mixedRootIncrement T Q U V x m f z (fun _ => true)) = _ from
    funext (mixedRootIncrement_true T Q U V x m f),
    show (fun z => mixedRootIncrement T Q U V x m f z (fun _ => false)) = _ from
    funext (mixedRootIncrement_false T Q U V x m f)] at hh
  linarith
end PrescribedTree
end DilutedSpinGlass

end

end OAI
