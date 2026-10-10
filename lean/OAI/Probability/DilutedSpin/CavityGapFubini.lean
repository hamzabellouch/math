import OAI.Probability.DilutedSpin.CavityInsertionFunctional
import OAI.Probability.DilutedSpin.CavityPoissonEndpoint
import OAI.Probability.DilutedSpin.ExtendedExponents
import OAI.Probability.DilutedSpin.PhysicalCavityRate
import OAI.Probability.DilutedSpin.TerminalPiRoot

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators
variable {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y] {N p : ℕ} [NeZero N]

lemma cavityPoisson_gap_fubini
    (μ : Measure X) [IsProbabilityMeasure μ] (ξ : Measure Y) [IsProbabilityMeasure ξ]
    (ρ : Measure ((Fin N → Spin) → ℝ)) [IsProbabilityMeasure ρ]
    (theta : X → InteractionSample p) (field : Y → ℝ)
    (hθm : ∀ σ,Measurable (fun x => (theta x).1 σ)) (hhm : Measurable field)
    {F : ((Fin N → Spin) → ℝ) → ℝ} (hF : LipschitzWith 1 F)
    {H C : ℝ} (hH : 0≤H) (hC : 0≤C) (hθ : ∀ x,‖(theta x).1‖≤C)
    (hh : ∀ y,|field y|≤H) (r : ℝ≥0) :
    (∫ k,∫ z : Fin k → X,∫ E,cavityArrayValue ξ theta field F E z-F E ∂ρ
        ∂Measure.pi (fun _ : Fin k => μ) ∂poissonMeasure r)=
      ∫ E,cavityPoissonValue μ ξ theta field F r E-F E ∂ρ := by
  let g := fun (k : ℕ) (E : (Fin N → Spin) → ℝ) (z : Fin k → X) =>
    cavityArrayValue ξ theta field F E z-F E
  have hgm k : Measurable (fun w : ((Fin N → Spin) → ℝ)×(Fin k → X) => g k w.1 w.2) :=
    (measurable_cavityArrayValue_joint ξ theta field hθm hhm hF.continuous).sub
      (hF.continuous.measurable.comp measurable_fst)
  have hgb k E z : |g k E z|≤H+C*k :=
    cavityArrayValue_gap_bound ξ theta field hhm hF hH hC hθ hh z E
  have hgi k : Integrable (fun w : ((Fin N → Spin) → ℝ)×(Fin k → X) => g k w.1 w.2)
      (ρ.prod (Measure.pi (fun _ : Fin k => μ))) :=
    Integrable.of_bound (hgm k).aestronglyMeasurable (H+C*k)
      (ae_of_all _ (fun w => by simpa only [Real.norm_eq_abs] using hgb k w.1 w.2))
  have hs k : (∫ z : Fin k → X,∫ E,g k E z ∂ρ ∂Measure.pi (fun _ : Fin k => μ))=
      ∫ E,∫ z : Fin k → X,g k E z ∂Measure.pi (fun _ : Fin k => μ) ∂ρ :=
    (integral_integral_swap (hgi k)).symm
  let f := fun (k : ℕ) (E : (Fin N → Spin) → ℝ) =>
    ∫ z : Fin k → X,g k E z ∂Measure.pi (fun _ : Fin k => μ)
  have hfm : Measurable (fun w : ((Fin N → Spin) → ℝ)×ℕ => f w.2 w.1) := by
    apply measurable_from_prod_countable_left
    intro k
    exact (hgm k).stronglyMeasurable.integral_prod_right' (ν := Measure.pi (fun _ : Fin k => μ)) |>.measurable
  have hfb k E : |f k E|≤H+C*k := abs_integral_le_bound (fun z => hgb k E z)
  have hfi : Integrable (fun w : ((Fin N → Spin) → ℝ)×ℕ => f w.2 w.1)
      (ρ.prod (poissonMeasure r)) := by
    apply (((integrable_const H).add ((poisson_integrable_count r).const_mul C)).comp_snd ρ).mono'
      hfm.aestronglyMeasurable
    exact ae_of_all _ (fun w => by simpa only [Real.norm_eq_abs,Pi.add_apply,Function.comp_apply] using hfb w.2 w.1)
  change (∫ k,∫ z : Fin k → X,∫ E,g k E z ∂ρ ∂Measure.pi (fun _ : Fin k => μ) ∂poissonMeasure r)=_
  simp_rw [hs]
  rw [show (∫ k,∫ E,f k E ∂ρ ∂poissonMeasure r)=∫ E,∫ k,f k E ∂poissonMeasure r ∂ρ from
    (integral_integral_swap hfi).symm]
  apply integral_congr_ae
  filter_upwards [] with E
  have hge k : Integrable (g k E) (Measure.pi (fun _ : Fin k => μ)) :=
    Integrable.of_bound (((hgm k).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable)
      (H+C*k) (ae_of_all _ (fun z => by simpa only [Real.norm_eq_abs] using hgb k E z))
  have ha k : Integrable (cavityArrayValue ξ theta field F E : (Fin k → X) → ℝ)
      (Measure.pi (fun _ : Fin k => μ)) := by
    exact ((hge k).add (integrable_const (F E))).congr (ae_of_all _ (fun z => by simp [g]))
  have he k : f k E=(∫ z : Fin k → X,cavityArrayValue ξ theta field F E z
      ∂Measure.pi (fun _ : Fin k => μ))-F E := by
    dsimp only [f,g]
    rw [integral_sub (ha k) (integrable_const _)]; simp
  have hfie : Integrable (fun k => f k E) (poissonMeasure r) := poisson_average_integrable r _ (fun k => hfb k E)
  have hca : Integrable (fun k => ∫ z : Fin k → X,cavityArrayValue ξ theta field F E z
      ∂Measure.pi (fun _ : Fin k => μ)) (poissonMeasure r) := by
    exact (hfie.add (integrable_const (F E))).congr (ae_of_all _ (fun k => by simp [he k]))
  simp_rw [he]
  rw [integral_sub hca (integrable_const _)]; simp [cavityPoissonValue]

end DilutedSpinGlass

end

section
namespace DilutedSpinGlass.PrescribedTree
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory KernelTower
open scoped BigOperators NNReal
variable {Λ R : Type} [Fintype Λ] [Fintype R]
    [MeasurableSpace R] [MeasurableSingletonClass R] {N q : ℕ} [NeZero N]

lemma finiteTrial_upper_fixedField (M : Model (q+1)) (hM : Admissible M)
    (a : Λ) (r : ℕ) (Q : FiniteLaw R) (U : R → KernelTower Λ r)
    (x : R → FinitePath Λ r → ℝ) (m : Fin r → ℝ) (hm : Exponents m) (h : Fin N → ℝ) :
    (∫ k,∫ z : Fin k → InteractionSample (q+1),
      (FiniteLaw.uniform : FiniteLaw (Fin k → Fin (q+1) → Fin N)).expect
        (fun i => logPartition z h i-(N:ℝ)*Real.log 2)
      ∂Measure.pi (fun _ : Fin k => M.disorder.toMeasure) ∂poissonMeasure (M.alpha*N))+
      (M.alpha:ℝ)*N*q*(∫ z,trialLog r (finiteTrialLaw r Q U x) m
        (fun y => Real.log (edge z.1 y)) ∂M.disorder.toMeasure) ≤
      ∑ s : Fin N,∫ k,∫ z : Fin k → InteractionSample (q+1),
        trialLog r (finiteTrialLaw r Q U x) m (siteLog z (h s))
        ∂Measure.pi (fun _ : Fin k => M.disorder.toMeasure) ∂poissonMeasure (M.alpha*(q+1)) := by
  let m' : Fin (r+1) → ℝ := Fin.snoc m 1
  let m₀ : Fin (r+2) → ℝ := Fin.cons 0 m'
  have hpos : ∀ d,0 < m' d := snoc_exponents_pos hm
  have hend : m' (Fin.last r)=1 := Fin.snoc_last _ _
  have hend₀ : m₀ (Fin.last (r+1))=1 := by
    change Fin.cons (α := fun _ => ℝ) 0 m' (Fin.last r).succ=1
    simpa only [Fin.cons_succ] using hend
  let T : Fin N → KernelTower Spin (r+1) := fun _ => terminalTower false FiniteLaw.uniform r
  let V : Fin N → FinitePath Spin (r+1) → Spin := fun _ => terminalState r
  let f : Fin N → FinitePath Spin (r+1) → ℝ := fun s y => h s*spin (terminalState r y)
  let Up : R → KernelTower Λ (r+1) := fun b => pad a r (U b)
  let xp : R → FinitePath Λ (r+1) → ℝ := fun b y => x b (pathPrefix r y)
  have hx := upperPoissonCount_bound_firstMoment M hM (KernelTower.pi (r+1) T) Q Up
    (fun y s => V s (FinitePath.proj (r+1) y s)) xp m₀
    (cons_snoc_exponents_mono hm) (cons_snoc_exponents_nonneg hm)
    (fun d => hpos d) rfl hend₀ (Fin.last q)
    (fun y => ∑ s,f s (FinitePath.proj (r+1) y s)) (M.alpha*(q+1)*N)
  have hr : (M.alpha*(q+1)*N:ℝ≥0)/(q+1)=M.alpha*N := by
    have hp : (q+1:ℝ≥0)≠0 := by positivity
    field_simp
  have hs : (M.alpha*(q+1)*N:ℝ≥0)/N=M.alpha*(q+1) := by
    have hN : (N:ℝ≥0)≠0 := by exact_mod_cast NeZero.ne N
    exact mul_div_cancel_right₀ _ hN
  simp only [m₀,Fin.cons_succ,Nat.cast_add,Nat.cast_one] at hx
  change (∫ k,upperCountMean M (KernelTower.pi (r+1) T) Q Up
      (fun y s => V s (FinitePath.proj (r+1) y s)) xp m' (Fin.last q)
      (fun y => ∑ s,f s (FinitePath.proj (r+1) y s)) k 0 ∂poissonMeasure ((M.alpha*(q+1)*N)/(q+1)))+
      ((M.alpha*(q+1)*N:ℝ≥0):ℝ)*(((q+1-1:ℕ):ℝ)/(q+1))*
        (∫ z,edgeRoot Q Up xp m' z ∂M.disorder.toMeasure) ≤ _ at hx
  rw [hr,upperPoisson_cavity_separable M hM Q T Up V xp m' hpos (Fin.last q) f,hs] at hx
  dsimp only [T,V,f,Up,xp] at hx
  simp_rw [upperCountMean_real_terminal M hM Q r _ _ m' hpos hend,
    activeCountMean_site q M hM a r Q U x m' hpos hend,
    edgeRoot_pad r a Q U x m' (by rw [hend]; norm_num)] at hx
  have he : (fun d : Fin r => m' d.castSucc)=m := by funext d; exact Fin.snoc_castSucc _ _ d
  rw [he] at hx
  have hc : ((M.alpha*(q+1)*N:ℝ≥0):ℝ)*(((q+1-1:ℕ):ℝ)/(q+1))=(M.alpha:ℝ)*N*q := by
    simp only [Nat.add_sub_cancel,NNReal.coe_mul,NNReal.coe_add,NNReal.coe_natCast,NNReal.coe_one]
    have hp : (q:ℝ)+1≠0 := by positivity
    field_simp
  rwa [hc] at hx

end DilutedSpinGlass.PrescribedTree

end

end OAI
