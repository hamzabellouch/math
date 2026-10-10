import OAI.Probability.DilutedSpin.CavityInsertionAlgebra
import OAI.Probability.DilutedSpin.FunctionalContinuity
import OAI.Probability.DilutedSpin.PhysicalInsertionIdentity
import OAI.Probability.DilutedSpin.SpinMarginal

namespace OAI

section
namespace DilutedSpinGlass.HeterogeneousMarks
open KernelTower
open scoped BigOperators
variable {I : Type} {A : I → Type} [∀ i,Fintype (A i)] {N k p l L : ℕ}

lemma terminalRoot_cavity_marginal
    (Q : (i : I) → Fin (L+1) → FiniteLaw (A i)) (m : Fin (L+1) → ℝ)
    (hm : m (Fin.last L)=1) (E : (Fin N → Spin) → ℝ)
    (roots : Fin l → I) (ψ : (i : I) → (Fin N → Spin) → FinitePath (A i) (L+1) → ℝ)
    (θ : Fin k → InteractionSample p) (h : ℝ) (j : Fin k × Fin (p-1) → Fin N) :
    terminalRoot (fun _ : Fin (N+1) => false) FiniteLaw.uniform Q m
      (fun σ => E (fun i => σ i.succ)+h*spin (σ 0)+
        ∑ a,(θ a).1 (appendSpin (fun b => σ (j (a,b)).succ) (σ 0))) roots
      (fun i σ z => ψ i (fun v => σ v.succ) z) =
    terminalRoot (fun _ : Fin N => false) FiniteLaw.uniform Q m
      (fun σ => E σ+cavitySiteEnergy θ h (fun a => σ (j a))) roots ψ := by
  have he : (fun σ : Fin (N+1) → Spin => E (fun i => σ i.succ)+h*spin (σ 0)+
      ∑ a,(θ a).1 (appendSpin (fun b => σ (j (a,b)).succ) (σ 0))) =
      (fun σ => E (fun i => σ i.succ)+(h*spin (σ 0)+
      ∑ a,(θ a).1 (appendSpin (fun b => σ (j (a,b)).succ) (σ 0)))) := by
    funext σ; ring
  rw [he,terminalRoot_spin_marginal Q m hm]
  congr 1
  funext σ
  congr 1
  simp only [Fin.cons_succ,Fin.cons_zero]
  simp only [FiniteLaw.logMean,FiniteLaw.expMoment,one_mul,div_one,FiniteLaw.uniform_expect,
    Fintype.card_bool,Nat.cast_ofNat,cavitySiteEnergy]

lemma terminalRoot_cavity_increment
    (Q : (i : I) → Fin (L+1) → FiniteLaw (A i)) (m : Fin (L+1) → ℝ)
    (hm : m (Fin.last L)=1) (E : (Fin N → Spin) → ℝ)
    (roots : Fin l → I) (ψ : (i : I) → (Fin N → Spin) → FinitePath (A i) (L+1) → ℝ)
    (θ : Fin k → InteractionSample p) (h : ℝ) (j : Fin k × Fin (p-1) → Fin N) :
    terminalRoot (fun _ : Fin (N+1) => false) FiniteLaw.uniform Q m
      (fun σ => E (fun i => σ i.succ)+h*spin (σ 0)+
        ∑ a,(θ a).1 (appendSpin (fun b => σ (j (a,b)).succ) (σ 0))) roots
      (fun i σ z => ψ i (fun v => σ v.succ) z) -
    terminalRoot (fun _ : Fin N => false) FiniteLaw.uniform Q m E roots ψ =
    backwardLog (L+1)
      (tilt (L+1) (tower roots (L+1) (terminalTower (fun _ : Fin N => false) FiniteLaw.uniform L) Q) m
        (logWeight (fun y => E (terminalState L y)) roots
          (fun i y z => ψ i (terminalState L y) z))) m
      (fun y => cavitySiteEnergy θ h (fun a => terminalState L (physical roots (L+1) y) (j a))) := by
  rw [terminalRoot_cavity_marginal Q m hm]
  exact root_energy_insertion (terminalTower (fun _ : Fin N => false) FiniteLaw.uniform L)
    Q m (fun y => E (terminalState L y))
    (fun y => cavitySiteEnergy θ h (fun a => terminalState L y (j a))) roots
    (fun i y z => ψ i (terminalState L y) z)

end DilutedSpinGlass.HeterogeneousMarks

end

section
namespace DilutedSpinGlass
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

noncomputable def cavityBondEnergy {p k : ℕ} (θ : Fin k → InteractionSample p)
    (s : Fin k × Fin p → Spin) : ℝ := ∑ j,(θ j).1 (fun i => s (j,i))

lemma cavityBondEnergy_bound {p k : ℕ} (θ : Fin k → InteractionSample p)
    (s : Fin k × Fin p → Spin) : |cavityBondEnergy θ s|≤∑ j,‖(θ j).1‖ :=
  (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun j _ => by
    simpa only [Real.norm_eq_abs] using norm_le_pi_norm (θ j).1 (fun i => s (j,i))))

lemma continuous_cavityBondEnergy {p k : ℕ} :
    Continuous (cavityBondEnergy : (Fin k → InteractionSample p) → (Fin k × Fin p → Spin) → ℝ) := by
  apply continuous_pi
  intro s
  exact continuous_finsetSum _ (fun j _ =>
    (continuous_apply (fun i => s (j,i))).comp (continuous_fst.comp (continuous_apply j)))

lemma continuous_cavitySiteEnergy {p k : ℕ} :
    Continuous (fun z : (Fin k → InteractionSample p) × ℝ => cavitySiteEnergy z.1 z.2) := by
  apply continuous_pi
  intro s
  apply Continuous.log
  · apply Continuous.div_const
    apply continuous_finsetSum
    intro ε _
    apply Real.continuous_exp.comp
    exact (continuous_snd.mul_const (spin ε)).add (continuous_finsetSum _ (fun j _ =>
      (continuous_apply (appendSpin (fun l => s (j,l)) ε)).comp
        (continuous_fst.comp ((continuous_apply j).comp continuous_fst))))
  · intro z
    exact ne_of_gt (div_pos (Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty) (by norm_num))

lemma trialLog_cavityBondEnergy {p k r : ℕ} (ζ : Hierarchy (r+1))
    (m : Fin r → ℝ) (hm : ∀ i,0 < m i) (θ : Fin k → InteractionSample p) :
    trialLog r ζ m (FiniteLaw.spinLog (cavityBondEnergy θ)) =
      ∑ j,trialLog r ζ m (fun x => Real.log (edge (θ j).1 x)) := by
  have he : FiniteLaw.spinLog (cavityBondEnergy θ) =
      fun x : Fin k × Fin p → ℝ => ∑ j,Real.log (edge (θ j).1 (fun i => x (j,i))) := by
    funext x
    change FiniteLaw.spinLog (fun s : Fin k × Fin p → Spin => ∑ j,(θ j).1 (fun i => s (j,i))) x = _
    rw [FiniteLaw.spinLog_blocks]
    simp only [FiniteLaw.spinLog_edge]
  rw [he]
  exact trialLog_blocks r k _ (fun j => continuous_log_edge (θ j).1)
    (fun j => ‖(θ j).1‖) (fun j => log_edge_bound (θ j).1) m hm ζ

lemma integral_trial_cavityBondEnergy {p k r : ℕ} (M : Model p)
    (hθ : Integrable (fun z : InteractionSample p => ‖z.1‖) M.disorder.toMeasure)
    (ζ : Hierarchy (r+1)) (m : Fin r → ℝ) (hm : ∀ i,0 < m i) :
    (∫ θ : Fin k → InteractionSample p,trialLog r ζ m (FiniteLaw.spinLog (cavityBondEnergy θ))
      ∂Measure.pi (fun _ : Fin k => M.disorder.toMeasure)) =
      k*(∫ θ : InteractionSample p,trialLog r ζ m (fun x => Real.log (edge θ.1 x)) ∂M.disorder.toMeasure) := by
  have hi : Integrable (fun θ : InteractionSample p => trialLog r ζ m (fun x => Real.log (edge θ.1 x))) M.disorder.toMeasure := by
    apply hθ.mono' (((trial_edge_lipschitz r m hm ζ).continuous.comp continuous_fst).aestronglyMeasurable)
    exact ae_of_all _ (fun θ => by simpa only [Real.norm_eq_abs,Function.comp_apply] using trial_edge_bound r m hm ζ θ.1)
  simp_rw [trialLog_cavityBondEnergy ζ m hm]
  rw [integral_finsetSum _ (fun j _ => integrable_comp_eval (μ := fun _ : Fin k => M.disorder.toMeasure) hi)]
  simp only [integral_comp_eval (μ := fun _ : Fin k => M.disorder.toMeasure) hi.aestronglyMeasurable,
    Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]

lemma integral_trial_cavitySiteEnergy {p k r : ℕ} (M : Model p)
    (hθ : Integrable (fun z : InteractionSample p => ‖z.1‖) M.disorder.toMeasure)
    (hh : Integrable (fun h : ℝ => |h|) M.field.toMeasure)
    (ζ : Hierarchy (r+1)) (m : Fin r → ℝ) (hm : ∀ i,0 < m i) :
    (∫ z : (Fin k → InteractionSample p) × ℝ,
      trialLog r ζ m (FiniteLaw.spinLog (cavitySiteEnergy z.1 z.2))
      ∂(Measure.pi (fun _ : Fin k => M.disorder.toMeasure)).prod M.field.toMeasure) =
      trialSiteDisorder M m ζ k := by
  let : OpensMeasurableSpace (Fin k → InteractionSample p) := Pi.opensMeasurableSpace
  simp_rw [show ∀ θ h, FiniteLaw.spinLog (cavitySiteEnergy (p := p) (k := k) θ h)=siteLog θ h from
    fun θ h => funext (spinLog_cavitySiteEnergy θ h)]
  apply integral_prod
  apply ((hh.comp_snd _).add ((interaction_sum_integrable M hθ k).comp_fst _)).mono'
    (trial_site_lipschitz r m hm ζ).continuous.aestronglyMeasurable
  exact ae_of_all _ (fun z => by simpa only [Real.norm_eq_abs,Pi.add_apply,Function.comp_apply] using trial_site_bound r m hm ζ z.1 z.2)

lemma functional_cavity_trial {p r : ℕ} (M : Model p)
    (hθ : Integrable (fun z : InteractionSample p => ‖z.1‖) M.disorder.toMeasure)
    (hh : Integrable (fun h : ℝ => |h|) M.field.toMeasure)
    (ζ : Hierarchy (r+1)) (m : Fin r → ℝ) (hm : ∀ i,0 < m i) :
    functional M r ζ m = Real.log 2+
      (∫ k, ∫ z : (Fin k → InteractionSample p) × ℝ,
        trialLog r ζ m (FiniteLaw.spinLog (cavitySiteEnergy z.1 z.2))
        ∂(Measure.pi (fun _ : Fin k => M.disorder.toMeasure)).prod M.field.toMeasure
        ∂poissonMeasure (M.alpha*p))-
      (∫ k, ∫ θ : Fin k → InteractionSample p,
        trialLog r ζ m (FiniteLaw.spinLog (cavityBondEnergy θ))
        ∂Measure.pi (fun _ : Fin k => M.disorder.toMeasure)
        ∂poissonMeasure (M.alpha*(p-1:ℕ))) := by
  simp_rw [integral_trial_cavitySiteEnergy M hθ hh ζ m hm,
    integral_trial_cavityBondEnergy M hθ ζ m hm,integral_mul_const,poisson_mean]
  unfold functional trialSiteDisorder trialSiteField
  simp only [NNReal.coe_mul,NNReal.coe_natCast]

end DilutedSpinGlass

end

end OAI
