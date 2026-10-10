import OAI.Probability.DilutedSpin.CavityOldNewMean
import OAI.Probability.DilutedSpin.FullRootIncrement
import OAI.Probability.DilutedSpin.PerturbedEnergyMean
import OAI.Probability.DilutedSpin.PhysicalCavityPoisson
import OAI.Probability.DilutedSpin.RootMapLaw
import OAI.Probability.DilutedSpin.TerminalMeanField
import OAI.Probability.DilutedSpin.UpperPoissonBound

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory PhysicalRoot SizeCoupling
open scoped NNReal BigOperators
variable {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y] {N q : ℕ} [NeZero N]

lemma cavity_old_average_error
    (μ : Measure X) [IsProbabilityMeasure μ] (ξ : Measure Y) [IsProbabilityMeasure ξ]
    (ρ : Measure ((Fin N → Spin) → ℝ)) [IsProbabilityMeasure ρ] (hρ : Integrable id ρ)
    (θ : X → InteractionSample (q+1)) (field : Y → ℝ)
    (hθm : ∀ σ,Measurable (fun x => (θ x).1 σ)) (hhm : Measurable field)
    {C H B δ : ℝ} (hC : 0≤C) (hH : 0≤H)
    (hθ : ∀ x,‖(θ x).1‖≤C) (hh : ∀ y,|field y|≤H)
    {F : ((Fin N → Spin) → ℝ) → ℝ} (hF : Continuous F) (hFb : ∀ E,|F E|≤‖E‖+B)
    {G : ((Fin (N+1) → Spin) → ℝ) → ℝ} (hG : Continuous G) (r : ℝ≥0)
    (he : ∀ E,|(∫ v,G (liftOldEnergy E+v) ∂compoundPoisson r
        (Measure.map (newPotential (N := N) θ) (μ.prod (finiteUniform (Fin q → Fin N)))))-
      cavityPoissonValue μ ξ θ field F r E|≤δ) :
    |(∫ E,∫ v,G (liftOldEnergy E+v) ∂compoundPoisson r
        (Measure.map (newPotential (N := N) θ) (μ.prod (finiteUniform (Fin q → Fin N)))) ∂ρ)-
      (∫ E,cavityPoissonValue μ ξ θ field F r E ∂ρ)|≤δ := by
  let : IsProbabilityMeasure (Measure.map (newPotential (N := N) θ)
      (μ.prod (finiteUniform (Fin q → Fin N)))) := inferInstance
  have hgb (E : (Fin N → Spin) → ℝ) :
      |cavityPoissonValue μ ξ θ field F r E|≤‖E‖+(H+C*r+B) := by
    simpa only [add_assoc] using cavityPoissonValue_bound μ ξ θ field hH hC hθ hh hFb r E
  have hgi : Integrable (cavityPoissonValue μ ξ θ field F r) ρ :=
    (hρ.norm.add (integrable_const (H+C*r+B))).mono'
      (measurable_cavityPoissonValue μ ξ θ field hθm hhm hF r).aestronglyMeasurable
      (ae_of_all _ (fun E => by simpa only [Real.norm_eq_abs,Pi.add_apply,id_eq] using hgb E))
  have hfm : AEStronglyMeasurable (fun E => ∫ v,G (liftOldEnergy E+v)
      ∂compoundPoisson r (Measure.map (newPotential (N := N) θ)
        (μ.prod (finiteUniform (Fin q → Fin N))))) ρ := by
    have hc : Continuous (fun z : ((Fin N → Spin) → ℝ)×((Fin (N+1) → Spin) → ℝ) =>
        G (liftOldEnergy z.1+z.2)) := hG.comp
      (((liftOldEnergy (N := N)).continuous.comp continuous_fst).add continuous_snd)
    exact hc.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable
  have h := integrate_error ρ hfm hgi (integrable_const δ) (ae_of_all _ he)
  simpa only [integral_const,probReal_univ,one_smul] using h.2

end DilutedSpinGlass

end

section
namespace DilutedSpinGlass
open _root_.MeasureTheory _root_.OAI.MeasureTheory KernelTower
open scoped BigOperators ENNReal

lemma FiniteLaw.uniform_asProbability {J : Type} [Fintype J] [Nonempty J]
    [MeasurableSpace J] [MeasurableSingletonClass J] :
    ((FiniteLaw.uniform : FiniteLaw J).asProbability id).toMeasure=finiteUniform J := by
  apply Measure.ext_of_singleton
  intro j
  rw [FiniteLaw.asProbability_id_singleton]
  change ENNReal.ofReal ((Fintype.card J : ℝ)⁻¹)=(PMF.uniformOfFintype J).toMeasure {j}
  rw [PMF.toMeasure_apply_singleton,PMF.uniformOfFintype_apply,
    ENNReal.ofReal_inv_of_pos (by exact_mod_cast (Fintype.card_pos : 0 < Fintype.card J))]
  · simp
  · exact measurableSet_singleton j


lemma integral_root_prod_finite_ae {X J : Type} [MeasurableSpace X]
    [Fintype J] [Nonempty J] [MeasurableSpace J] [MeasurableSingletonClass J]
    (μ : Measure X) [IsProbabilityMeasure μ] (n : ℕ)
    (F : (Fin n → X) × (Fin n → J) → ℝ) (hF : Measurable F)
    {B : ℝ} (hb : ∀ᵐ z ∂Measure.pi (fun _ : Fin n => μ),∀ j,|F (z,j)|≤B) :
    (∫ z : RootPath (X×J) n,F ((fun i => (rootArray n z i).1),(fun i => (rootArray n z i).2))
      ∂rootLaw n (fun _ => μ.prod (finiteUniform J))) =
      ∫ x : Fin n → X,(FiniteLaw.uniform : FiniteLaw (Fin n → J)).expect (fun j => F (x,j))
        ∂Measure.pi (fun _ : Fin n => μ) := by
  rw [integral_root_prod μ (finiteUniform J) n F
    (Integrable.of_bound hF.aestronglyMeasurable B (by
      filter_upwards [Measure.quasiMeasurePreserving_fst.ae hb] with z hz
      simpa only [Real.norm_eq_abs] using hz z.2))]
  simp only [finiteUniform_pi]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [integral_finiteUniform,FiniteLaw.expect_uniform]
  simp only [smul_eq_mul,div_eq_mul_inv,mul_comm]

namespace PrescribedTree
variable {Ω Λ R : Type} [Fintype Ω] [Fintype Λ] [Fintype R]
    [MeasurableSpace R] [MeasurableSingletonClass R] {n p N : ℕ} [NeZero N]

omit [MeasurableSingletonClass R] in
lemma upperDatum_real_projection (M : Model p) (Q : FiniteLaw R) :
    MeasurePreserving (fun a : UpperDatum p N R => (a.1,a.2.1))
      (upperDatumLaw M Q) (M.disorder.toMeasure.prod (finiteUniform (Fin p → Fin N))) := by
  unfold upperDatumLaw
  rw [FiniteLaw.pi_uniform,FiniteLaw.uniform_asProbability]
  exact (MeasurePreserving.id _).prod measurePreserving_fst

omit [MeasurableSingletonClass R] in
lemma upperCountMean_real (M : Model p) (T : KernelTower Ω n) (Q : FiniteLaw R)
    (U : R → KernelTower Λ n) (V : FinitePath Ω n → Fin N → Spin)
    (x : R → FinitePath Λ n → ℝ) (m : Fin n → ℝ) (hm : ∀ d,0 < m d)
    (j : Fin p) (f : FinitePath Ω n → ℝ) (k : ℕ)
    {C : ℝ} (hC : ∀ᵐ a ∂M.disorder.toMeasure,‖a.1‖≤C) :
    upperCountMean M T Q U V x m j f k 0 =
      ∫ z : Fin k → InteractionSample p,
       (FiniteLaw.uniform : FiniteLaw (Fin k → Fin p → Fin N)).expect
        (fun i => backwardLog n T m (fun y => f y+∑ a,(z a).1 (fun b => V y (i a b))))
          ∂Measure.pi (fun _ : Fin k => M.disorder.toMeasure) := by
  let F : RootPath (InteractionSample p × (Fin p → Fin N)) k → ℝ := fun z =>
    backwardLog n T m (fun y => f y+∑ a,(rootArray k z a).1.1 (fun b => V y ((rootArray k z a).2 b)))
  have hFm : Measurable F := by
    apply measurable_backwardLog
    intro y
    apply measurable_const.add
    apply Finset.measurable_sum
    intro a _
    exact (measurable_pi_apply (V y)).comp ((PhysicalRoot.measurable_indexedPotential (fun x : InteractionSample p => x)
      (fun σ => (measurable_pi_apply σ).comp measurable_fst)).comp (measurable_rootArray k a))
  have he : upperCountMean M T Q U V x m j f k 0 =
      ∫ z,F (rootMap (fun a : UpperDatum p N R => (a.1,a.2.1)) k z)
        ∂rootLaw k (fun _ => upperDatumLaw M Q) := by
    let : IsProbabilityMeasure (rootLaw 0 (fun _ : Fin 0 => upperDatumLaw (N := N) M Q)) := Measure.dirac.isProbabilityMeasure
    unfold upperCountMean
    apply integral_congr_ae
    filter_upwards [] with z
    simp only [datumRoot,cavityRoot,cavityTower,cavityEnergy,realCountEnergy,
      rootArray_rootMap,F]
    simp only [integral_const,Measure.real,measure_univ,ENNReal.toReal_one,one_smul]
    rfl
  rw [he,integral_rootMap (upperDatum_real_projection M Q) k F hFm]
  apply integral_root_prod_finite_ae M.disorder.toMeasure k
    (fun z : (Fin k → InteractionSample p) × (Fin k → Fin p → Fin N) => backwardLog n T m (fun y => f y+∑ a,(z.1 a).1 (fun b => V y (z.2 a b))))
  · apply measurable_from_prod_countable_left
    intro i
    apply measurable_backwardLog
    intro y
    change Measurable (fun z : Fin k → InteractionSample p => f y+∑ a,(z a).1 (fun b => V y (i a b)))
    exact measurable_const.add (Finset.measurable_sum _ (fun a _ =>
      (measurable_pi_apply _).comp (measurable_fst.comp (measurable_pi_apply a))))
  · have ha : ∀ᵐ z ∂Measure.pi (fun _ : Fin k => M.disorder.toMeasure),∀ a,‖(z a).1‖≤C :=
      Filter.eventually_all.mpr (fun a => (Measure.tendsto_eval_ae_ae (μ := fun _ : Fin k => M.disorder.toMeasure) (i := a)).eventually hC)
    filter_upwards [ha] with z hz
    intro i
    apply backwardLog_bound n T m hm
    intro y
    apply (abs_add_le _ _).trans
    apply add_le_add (norm_le_pi_norm f y)
    calc
      _ ≤ ∑ a,|(z a).1 (fun b => V y (i a b))| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _a : Fin k,C := Finset.sum_le_sum (fun a _ => (norm_le_pi_norm (z a).1 _).trans (hz a))
      _ = C*k := by simp [mul_comm]

end PrescribedTree
end DilutedSpinGlass

end

section
namespace DilutedSpinGlass.KernelTower
variable {Ω : Type} [Fintype Ω]
lemma pi_pad {ι : Type} [Fintype ι] [DecidableEq ι]
    (a : Ω) (n : ℕ) (T : ι → KernelTower Ω n) :
    pi (n+1) (fun i => pad a n (T i))=pad (fun _ : ι => a) n (pi n T) := by
  simp_rw [←piTower_eq_pi]
  exact piTower_pad a n T
omit [Fintype Ω] in
lemma pathMap_snd {Λ : Type} (n : ℕ) (y : FinitePath (Ω×Λ) n) :
    pathMap Prod.snd n y=pathSnd n y := by
  induction n with
  | zero => rfl
  | succ n ih => exact Prod.ext rfl (ih y.2)
end DilutedSpinGlass.KernelTower

namespace DilutedSpinGlass.PrescribedTree
open KernelTower
open scoped BigOperators
variable {Λ R : Type} [Fintype Λ] [Fintype R]
omit [Fintype R] in
lemma activeRoot_site (a : Λ) (r : ℕ) (U : R → KernelTower Λ r)
    (x : R → FinitePath Λ r → ℝ) (m : Fin (r+1) → ℝ) (hend : m (Fin.last r)=1)
    (q k : ℕ) (b : RootPath (Fin (q+1) → R) k) (z : RootPath (InteractionSample (q+1)) k) (h : ℝ) :
    backwardLog (r+1)
      (cavityTower (terminalTower false (FiniteLaw.uniform : FiniteLaw Spin) r)
        (fun b => pad a r (U b)) k b) m
      (activeEnergy (terminalState r) (fun b y => x b (pathPrefix r y)) (Fin.last q) k b z
        (fun y => h*spin (terminalState r y))) =
      backwardLog r (piTower r (fun c : Fin k×Fin q => U (rootArray k b c.1 c.2.castSucc)))
        (fun d => m d.castSucc) (fun y => siteLog (rootArray k z) h
          (fun c => x (rootArray k b c.1 c.2.castSucc)
            (pathMap (fun w : Fin k×Fin q → Λ => w c) r y))) := by
  rw [activeRoot_flat]
  simp_rw [piTower_pad a r]
  rw [pi_pad (fun _ : Fin (q+1) => a) r]
  let F := fun (s : Spin) (y : FinitePath (Fin k → Fin (q+1) → Λ) r) =>
    h*spin s+∑ i,message (rootArray k z i).1
      (fun j => x (rootArray k b i j.castSucc)
        (pathMap (fun w : Fin k → Fin (q+1) → Λ => w i j.castSucc) r y)) s
  have he : (fun y : FinitePath (Spin × (Fin k → Fin (q+1) → Λ)) (r+1) =>
      h*spin (terminalState r (pathFst (r+1) y))+
        ∑ i,mixedEnergy (rootArray k z i) (fun j => decide (j=Fin.last q))
          (fun _ => terminalState r (pathFst (r+1) y))
          (fun j => x (rootArray k b i j) (pathPrefix r
            (pathMap (fun w : Spin × (Fin k → Fin (q+1) → Λ) => w.2 i j) (r+1) y)))) =
      fun y => F (terminalState r (pathFst (r+1) y)) (pathPrefix r (pathSnd (r+1) y)) := by
    funext y
    simp only [mixedEnergy_last,F]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    funext j
    congr 1
    rw [pathMap_pathPrefix]
    rw [←pathMap_snd,←pathMap_comp]
    rfl
  rw [he,backwardLog_terminal_pad,hend]
  have hs (y : FinitePath (Fin k → Fin (q+1) → Λ) r) :
      (FiniteLaw.uniform : FiniteLaw Spin).logMean 1 (fun s => F s y)=
      siteLog (rootArray k z) h (fun c : Fin k×Fin q => x (rootArray k b c.1 c.2.castSucc)
        (pathMap (fun w : Fin k → Fin (q+1) → Λ => w c.1 c.2.castSucc) r y)) := by
    simp only [FiniteLaw.logMean,FiniteLaw.expMoment,one_mul,div_one,FiniteLaw.expect,
      FiniteLaw.uniform,Fintype.card_bool,Nat.cast_ofNat,inv_mul_eq_div,
      siteLog,F,Finset.sum_div]
  simp only [hs]
  rw [←backwardLog_of_projects r (pi_rect_castSucc_projects r k q (fun i j => U (rootArray k b i j)))]
  congr 1
  funext y
  congr 1
  funext c
  congr 1
  rw [←pathMap_comp]
  rfl

end DilutedSpinGlass.PrescribedTree

end

end OAI
