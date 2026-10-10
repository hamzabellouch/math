import OAI.Probability.DilutedSpin.CavitySeparable
import OAI.Probability.DilutedSpin.CompoundSample
import OAI.Probability.DilutedSpin.EnergyInsertionMean
import OAI.Probability.DilutedSpin.InsertionPoissonAlgebra
import OAI.Probability.DilutedSpin.OneNewLaw
import OAI.Probability.DilutedSpin.PhysicalNewSpin

namespace OAI

section
namespace DilutedSpinGlass.PhysicalRoot
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory HeterogeneousMarks KernelTower
open scoped NNReal BigOperators
variable {X Y I : Type} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace I] [Countable I] [MeasurableSingletonClass I]
    {A : I → Type} [∀ i,Fintype (A i)] {N L : ℕ}

lemma measurable_reorder_increment {α β γ : Type} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] [Add γ] [MeasurableAdd₂ γ]
    (F : (α × γ) × β → ℝ) (hF : Measurable F) (J : γ) :
    Measurable (fun z : (α × β) × γ => F ((z.1.1,z.2+J),z.1.2)-F ((z.1.1,z.2),z.1.2)) := by
  exact (hF.comp ((measurable_fst.fst.prodMk (measurable_snd.add_const J)).prodMk measurable_fst.snd)).sub
    (hF.comp ((measurable_fst.fst.prodMk measurable_snd).prodMk measurable_fst.snd))

lemma measurable_energyRoot_increment
    (Q : (i : I) → Fin (L+1) → FiniteLaw (A i)) (m : Fin (L+1) → ℝ)
    (field : Y → ℝ) (hfield : Measurable field)
    (factor : (i : I) → FinitePath (Fin N → Spin) (L+1) → FinitePath (A i) (L+1) → ℝ)
    (J : (Fin N → Spin) → ℝ) :
    Measurable (fun z : (RootPath Y N × Sigma (RootPath I)) × ((Fin N → Spin) → ℝ) =>
      energyRoot Q m field factor z.1.1 z.1.2 (z.2+J)-energyRoot Q m field factor z.1.1 z.1.2 z.2) :=
  measurable_reorder_increment
    (fun z : (RootPath Y N × ((Fin N → Spin) → ℝ)) × Sigma (RootPath I) =>
      energyRoot Q m field factor z.1.1 z.2 z.1.2)
    (measurable_energyRoot Q m field hfield factor) J

lemma fullRoot_energy_increment
    (ξ : Measure Y) [IsProbabilityMeasure ξ] (μ : Measure X) [IsProbabilityMeasure μ]
    (ν : Measure I) [IsProbabilityMeasure ν] (r s : ℝ≥0)
    (V : X → (Fin N → Spin) → ℝ) (hV : Measurable V)
    (Q : (i : I) → Fin (L+1) → FiniteLaw (A i)) (m : Fin (L+1) → ℝ)
    (hm : ∀ d,0 < m d) (field : Y → ℝ) (hfield : Measurable field)
    (factor : (i : I) → FinitePath (Fin N → Spin) (L+1) → FinitePath (A i) (L+1) → ℝ)
    {H D : ℝ} (hh : ∀ y,|field y|≤H) (hf : ∀ i y a,|Real.log (factor i y a)|≤D)
    (J : (Fin N → Spin) → ℝ) :
    (∫ z : FullRootState Y X I N,
      energyRoot Q m field factor z.1 z.2.2 ((∑ i,V (rootArray z.2.1.1 z.2.1.2 i))+J)-
        energyRoot Q m field factor z.1 z.2.2 (∑ i,V (rootArray z.2.1.1 z.2.1.2 i))
       ∂fullRootLaw (fun _ => ξ) μ ν r s) =
      ∫ E,averagedEnergyRoot ξ ν s Q m field factor (E+J)-
        averagedEnergyRoot ξ ν s Q m field factor E ∂compoundPoisson r (Measure.map V μ) := by
  let κ := compoundPoisson r (Measure.map V μ)
  let : IsProbabilityMeasure (Measure.map V μ) := inferInstance
  let G := fun z : (RootPath Y N × Sigma (RootPath I)) × ((Fin N → Spin) → ℝ) =>
    energyRoot Q m field factor z.1.1 z.1.2 (z.2+J)-energyRoot Q m field factor z.1.1 z.1.2 z.2
  have hmG : Measurable G := measurable_energyRoot_increment Q m field hfield factor J
  have hbG (z) : |G z|≤‖J‖ := energyRoot_increment_bound Q m hm field factor z.1.1 z.1.2 z.2 J
  have hiG : Integrable G (((rootLaw N (fun _ => ξ)).prod (compoundRootLaw ν s)).prod κ) :=
    Integrable.of_bound hmG.aestronglyMeasurable _ (ae_of_all _ (fun z => by simpa only [Real.norm_eq_abs] using hbG z))
  let F := fun (h : RootPath Y N) (k : ℕ) (x : RootPath X k) (n : ℕ) (a : RootPath I n) =>
    G ((h,⟨n,a⟩),∑ i,V (rootArray k x i))
  have hFm k n : Measurable (fun z : (RootPath Y N × RootPath X k) × RootPath I n => F z.1.1 k z.1.2 n z.2) := by
    apply hmG.comp
    apply Measurable.prodMk
    · exact measurable_fst.fst.prodMk ((measurable_sigmaMk (i := n)).comp measurable_snd)
    · exact Finset.measurable_sum _ (fun i _ => hV.comp ((measurable_rootArray k i).comp measurable_fst.snd))
  have he : (∫ z,packRoot F z ∂fullRootLaw (fun _ => ξ) μ ν r s)=
      ∫ h,∫ a,∫ E,G ((h,a),E) ∂κ ∂compoundRootLaw ν s ∂rootLaw N (fun _ => ξ) := by
    rw [integral_fullRootLaw_reordered (fun _ => ξ) μ ν r s hFm
      (B := ‖J‖) (C := 0) (D := 0) (fun h k x n a => by simpa only [zero_mul,add_zero] using hbG ((h,⟨n,a⟩),∑ i,V (rootArray k x i)))]
    apply integral_congr_ae
    filter_upwards [] with h
    apply integral_congr_ae
    filter_upwards [] with a
    dsimp only [F,κ]
    rw [← map_compoundRoot_energy μ V hV r]
    have hma : Measurable (fun E : (Fin N → Spin) → ℝ => G ((h,a),E)) :=
      hmG.comp (measurable_const.prodMk measurable_id)
    rw [integral_map (measurable_compound_sample V hV).aemeasurable hma.aestronglyMeasurable]
  change (∫ z,packRoot F z ∂fullRootLaw (fun _ => ξ) μ ν r s)=_
  rw [he,← integral_prod _ hiG.integral_prod_left,integral_integral_swap hiG]
  apply integral_congr_ae
  filter_upwards [hiG.prod_left_ae] with E hE
  rw [integral_prod _ hE,← averagedEnergyRoot_increment ξ ν s Q m hm field hfield factor hh hf E J]

end DilutedSpinGlass.PhysicalRoot

end

section
namespace DilutedSpinGlass
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
variable {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y]
    {N p k : ℕ} [NeZero N]

lemma measurable_cavityArrayValue_joint (ξ : Measure Y) [SFinite ξ]
    (theta : X → InteractionSample p) (field : Y → ℝ)
    (hθ : ∀ σ,Measurable (fun x => (theta x).1 σ)) (hh : Measurable field)
    {F : ((Fin N → Spin) → ℝ) → ℝ} (hF : Continuous F) :
    Measurable (fun z : ((Fin N → Spin) → ℝ)×(Fin k → X) =>
      cavityArrayValue ξ theta field F z.1 z.2) := by
  apply FiniteLaw.measurable_expect
  intro j
  apply StronglyMeasurable.measurable
  apply StronglyMeasurable.integral_prod_right' (f := fun z : (((Fin N → Spin) → ℝ)×(Fin k → X))×Y =>
    F (cavityArrayEnergy theta field z.1.1 j (z.1.2,z.2)))
  apply Measurable.stronglyMeasurable
  apply hF.measurable.comp
  apply Measurable.of_eval
  intro σ
  change Measurable (fun z : (((Fin N → Spin) → ℝ)×(Fin k → X))×Y =>
    z.1.1 σ+cavitySiteEnergy (fun a => theta (z.1.2 a)) (field z.2) (fun a => σ (j a.1 a.2)))
  apply ((measurable_pi_apply σ).comp (measurable_fst.comp measurable_fst)).add
  unfold cavitySiteEnergy
  apply Measurable.log
  apply Measurable.div_const
  apply Finset.measurable_sum
  intro ε _
  apply Measurable.exp
  apply ((hh.comp measurable_snd).mul_const _).add
  exact Finset.measurable_sum _ (fun a _ => (hθ _).comp
    ((measurable_pi_apply a).comp (measurable_snd.comp measurable_fst)))

noncomputable def cavityPoissonValue (μ : Measure X) (ξ : Measure Y)
    (theta : X → InteractionSample p) (field : Y → ℝ)
    (F : ((Fin N → Spin) → ℝ) → ℝ) (r : ℝ≥0) (E : (Fin N → Spin) → ℝ) : ℝ :=
  ∫ k,∫ z : Fin k → X,cavityArrayValue ξ theta field F E z
    ∂Measure.pi (fun _ : Fin k => μ) ∂poissonMeasure r

lemma measurable_cavityPoissonValue (μ : Measure X) [IsProbabilityMeasure μ]
    (ξ : Measure Y) [SFinite ξ]
    (theta : X → InteractionSample p) (field : Y → ℝ)
    (hθ : ∀ σ,Measurable (fun x => (theta x).1 σ)) (hh : Measurable field)
    {F : ((Fin N → Spin) → ℝ) → ℝ} (hF : Continuous F) (r : ℝ≥0) :
    Measurable (cavityPoissonValue μ ξ theta field F r) := by
  unfold cavityPoissonValue
  apply StronglyMeasurable.measurable
  apply StronglyMeasurable.integral_prod_right' (f := fun z : ((Fin N → Spin) → ℝ)×ℕ =>
    ∫ x : Fin z.2 → X,cavityArrayValue ξ theta field F z.1 x ∂Measure.pi (fun _ : Fin z.2 => μ))
  apply Measurable.stronglyMeasurable
  apply measurable_from_prod_countable_left
  intro k
  exact (measurable_cavityArrayValue_joint (k := k) ξ theta field hθ hh hF).stronglyMeasurable.integral_prod_right' (ν := Measure.pi (fun _ : Fin k => μ)) |>.measurable

lemma cavityPoissonValue_bound (μ : Measure X) [IsProbabilityMeasure μ]
    (ξ : Measure Y) [IsProbabilityMeasure ξ]
    (theta : X → InteractionSample p) (field : Y → ℝ)
    {H C B : ℝ} (hH : 0≤H) (hC : 0≤C)
    (hθ : ∀ x,‖(theta x).1‖≤C) (hh : ∀ y,|field y|≤H)
    {F : ((Fin N → Spin) → ℝ) → ℝ} (hF : ∀ E,|F E|≤‖E‖+B)
    (r : ℝ≥0) (E : (Fin N → Spin) → ℝ) :
    |cavityPoissonValue μ ξ theta field F r E|≤‖E‖+H+C*r+B := by
  have hb (k : ℕ) : |∫ z : Fin k → X,cavityArrayValue ξ theta field F E z
      ∂Measure.pi (fun _ : Fin k => μ)|≤‖E‖+H+C*k+B :=
    abs_integral_le_bound (fun z => cavityArrayValue_bound ξ theta field hH hC hθ hh hF E z)
  have h := poisson_average_bound r (fun k : ℕ => ∫ z : Fin k → X,
    cavityArrayValue ξ theta field F E z ∂Measure.pi (fun _ : Fin k => μ))
    (B := ‖E‖+H+B) (D := C) (fun k => (hb k).trans_eq (by ring))
  exact h.trans_eq (by ring)

end DilutedSpinGlass

end

section
namespace DilutedSpinGlass
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory PhysicalRoot HeterogeneousMarks
open scoped NNReal BigOperators
variable {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y] {N q : ℕ} [NeZero N]

lemma cavity_poisson_bridge
    (μ : Measure X) [IsProbabilityMeasure μ] (ξ : Measure Y) [IsProbabilityMeasure ξ]
    (theta : X → InteractionSample (q+1)) (field : Y → ℝ)
    (hθm : ∀ σ,Measurable (fun x => (theta x).1 σ)) (hhm : Measurable field)
    {H C B δ : ℝ} (hH : 0≤H) (hC : 0≤C)
    (hθ : ∀ x,‖(theta x).1‖≤C) (hh : ∀ y,|field y|≤H)
    {F : ((Fin N → Spin) → ℝ) → ℝ} {G : ((Fin (N+1) → Spin) → ℝ) → ℝ}
    (hF : Continuous F) (hFb : ∀ v,|F v|≤‖v‖+B) (hG : LipschitzWith 1 G)
    (E : (Fin N → Spin) → ℝ) (r : ℝ≥0)
    (he : ∀ k (z : Fin k → X) (j : Fin k → Fin q → Fin N),
      |G (fun σ => E (fun i => σ i.succ)+∑ a,(theta (z a)).1
        (appendSpin (fun b => σ (j a b).succ) (σ 0)))-
        ∫ h,F (cavityArrayEnergy theta field E j (z,h)) ∂ξ|≤δ) :
    |(∫ v,G (fun σ => E (fun i => σ i.succ)+v σ)
        ∂compoundPoisson r (Measure.map (newPotential (N := N) theta)
          (μ.prod (finiteUniform (Fin q → Fin N)))))-
      (∫ k,∫ z : Fin k → X,cavityArrayValue ξ theta field F E z
        ∂Measure.pi (fun _ : Fin k => μ) ∂poissonMeasure r)|≤δ := by
  have hGs : LipschitzWith 1 (fun v : (Fin (N+1) → Spin) → ℝ => G (fun σ => E (fun i => σ i.succ)+v σ)) := by
    simpa only [mul_one,Function.comp_def,Pi.add_def] using
      hG.comp (isometry_add_left (fun σ : Fin (N+1) → Spin => E (fun i => σ i.succ))).lipschitzWith
  have hVb (z : X×(Fin q → Fin N)) : ‖newPotential theta z‖≤C :=
    (pi_norm_le_iff_of_nonneg hC).mpr (fun σ => (norm_le_pi_norm (theta z.1).1 _).trans (hθ z.1))
  rw [integral_compound_finite_sample μ (newPotential theta)
    (measurable_newPotential theta hθm) hVb r hGs]
  let f (k : ℕ) (z : Fin k → X) :=
    (FiniteLaw.uniform : FiniteLaw (Fin k → Fin q → Fin N)).expect
      (fun j => G (fun σ => E (fun i => σ i.succ)+∑ a,newPotential theta (z a,j a) σ))
  let g (k : ℕ) (z : Fin k → X) := cavityArrayValue ξ theta field F E z
  have hgm k : Measurable (g k) := measurable_cavityArrayValue ξ theta field hθm hhm hF E
  have hgb k z : |g k z|≤‖E‖+H+C*k+B := cavityArrayValue_bound ξ theta field hH hC hθ hh hFb E z
  have hgi k : Integrable (g k) (Measure.pi (fun _ : Fin k => μ)) :=
    Integrable.of_bound (hgm k).aestronglyMeasurable _ (ae_of_all _ (fun z => by simpa only [Real.norm_eq_abs] using hgb k z))
  have hfm k : Measurable (f k) := by
    apply FiniteLaw.measurable_expect
    intro j
    apply hG.continuous.measurable.comp
    apply Measurable.of_eval
    intro σ
    change Measurable (fun z : Fin k → X => E (fun i => σ i.succ)+∑ a,(theta (z a)).1 (appendSpin (fun b => σ (j a b).succ) (σ 0)))
    exact measurable_const.add (Finset.measurable_sum _ (fun a _ => (hθm _).comp (measurable_pi_apply a)))
  have he' k z : |f k z-g k z|≤δ := by
    apply FiniteLaw.abs_expect_sub_le
    intro j
    exact he k z j
  have hb k : |(∫ z,f k z ∂Measure.pi (fun _ : Fin k => μ))-
      ∫ z,g k z ∂Measure.pi (fun _ : Fin k => μ)|≤δ := by
    have h := integrate_error (Measure.pi (fun _ : Fin k => μ))
      (hfm k).aestronglyMeasurable (hgi k) (integrable_const δ) (ae_of_all _ (he' k))
    simpa using h.2
  have hgI : Integrable (fun k => ∫ z,g k z ∂Measure.pi (fun _ : Fin k => μ)) (poissonMeasure r) := by
    apply poisson_integrable_linear r (A := ‖E‖+H+B) (B := C)
    intro k
    calc
      _ ≤ ‖E‖+H+C*k+B := abs_integral_le_bound (hgb k)
      _ = _ := by ring
  have h := integrate_error (poissonMeasure r) (measurable_of_countable _).aestronglyMeasurable
    hgI (integrable_const δ) (ae_of_all _ hb)
  simpa only [Pi.add_apply,Finset.sum_apply,Real.norm_eq_abs,integral_const,
    Measure.real,measure_univ,ENNReal.toReal_one,one_smul,f,g] using h.2

end DilutedSpinGlass

end

section
namespace DilutedSpinGlass.KernelTower
variable {Ω Λ : Type} [Fintype Ω] [Fintype Λ]
lemma Projects.prod_fst (n : ℕ) (T : KernelTower Ω n) (U : KernelTower Λ n) :
    Projects Prod.fst n (KernelTower.prod n T U) T := by
  induction n with
  | zero => trivial
  | succ n ih =>
    refine ⟨?_,fun a => ih (T.2 a.1) (U.2 a.2)⟩
    intro f
    change (T.1.bind (fun _ => U.1)).expect (fun z => f z.1)=T.1.expect f
    simp only [FiniteLaw.expect_bind,FiniteLaw.expect_const]

omit [Fintype Ω] [Fintype Λ] in
lemma pathMap_fst (n : ℕ) (y : FinitePath (Ω×Λ) n) :
    pathMap Prod.fst n y=pathFst n y := by
  induction n with
  | zero => rfl
  | succ n ih => exact Prod.ext rfl (ih y.2)
end DilutedSpinGlass.KernelTower

namespace DilutedSpinGlass.PrescribedTree
open KernelTower
variable {Ω Λ R : Type} [Fintype Ω] [Fintype Λ] [Fintype R] {n p : ℕ}

def selectCavity : (l : ℕ) → (b : RootPath Bool l) → CavityState Ω Λ p l →
    CavityState Ω Λ p (selectedCount l b)
  | 0,_,z => z
  | l+1,(true,b),z => (selectCavity l b z.1,z.2)
  | l+1,(false,b),z => selectCavity l b z.1

omit [Fintype R] in
lemma selectCavity_projects (T : KernelTower Ω n) (U : R → KernelTower Λ n)
    (l : ℕ) (b : RootPath Bool l) (r : RootPath (Fin p → R) l) :
    Projects (selectCavity (Ω := Ω) (Λ := Λ) (p := p) l b) n
      (cavityTower T U l r) (cavityTower T U (selectedCount l b) (selectRoot l b r)) := by
  induction l with
  | zero => exact Projects.refl n T
  | succ l ih =>
    rcases b with ⟨v,b⟩
    cases v
    · change Projects (fun z : CavityState Ω Λ p l × (Fin p → Λ) => selectCavity l b z.1) n
        (KernelTower.prod n (cavityTower T U l r.2) (piTower n (fun j => U (r.1 j))))
        (cavityTower T U (selectedCount l b) (selectRoot l b r.2))
      exact Projects.comp n (Projects.prod_fst n (cavityTower T U l r.2) (piTower n (fun j => U (r.1 j)))) (ih b r.2)
    · change Projects (fun z : CavityState Ω Λ p l × (Fin p → Λ) => (selectCavity l b z.1,id z.2)) n
        (KernelTower.prod n (cavityTower T U l r.2) (piTower n (fun j => U (r.1 j))))
        (KernelTower.prod n (cavityTower T U (selectedCount l b) (selectRoot l b r.2)) (piTower n (fun j => U (r.1 j))))
      exact Projects.prod n (ih b r.2) (Projects.refl n (piTower n (fun j => U (r.1 j))))

omit [Fintype Ω] [Fintype Λ] in
lemma cavityProject_select (l : ℕ) (b : RootPath Bool l) (a : CavityState Ω Λ p l) :
    cavityProject (selectedCount l b) (selectCavity l b a)=cavityProject l a := by
  induction l with
  | zero => rfl
  | succ l ih =>
    rcases b with ⟨v,b⟩
    cases v <;> simpa only [selectCavity,selectedCount,Bool.false_eq_true,↓reduceDIte,↓reduceIte,cavityProject] using ih b a.1

omit [Fintype Ω] [Fintype Λ] in
lemma cavityProject_pathSelect (l : ℕ) (b : RootPath Bool l) (y : FinitePath (CavityState Ω Λ p l) n) :
    pathMap (cavityProject (selectedCount l b)) n (pathMap (selectCavity l b) n y)=
      pathMap (cavityProject l) n y := by
  induction n with
  | zero => rfl
  | succ n ih => exact Prod.ext (cavityProject_select l b y.1) (ih y.2)

end DilutedSpinGlass.PrescribedTree

end

end OAI
