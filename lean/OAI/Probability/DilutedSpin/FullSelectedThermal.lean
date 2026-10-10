import OAI.Probability.DilutedSpin.ActualNegligible
import OAI.Probability.DilutedSpin.FullSelectedRegularity
import OAI.Probability.DilutedSpin.SelectorPolarization
import OAI.Probability.DilutedSpin.ShapeEmbedding

namespace OAI

section
section
namespace DilutedSpinGlass.KernelTower
variable {Ω : Type} [Fintype Ω]

theorem thermalDefect_bound {L n : ℕ} (T : KernelTower Ω L) (m : Fin L → ℝ)
    (base : FinitePath Ω L → ℝ) (D E : Fin n → FinitePath Ω L → ℝ)
    (hD : ∀ q y, |D q y| ≤ 1) (hE : ∀ q y, |E q y| ≤ 1)
    {t u : ℝ} (ht : |t| ≤ 1/4) (hu : |u| ≤ 1/4) :
    thermalDefect T m base D E t u ≤ 4*n := by
  let P := law L (tilt L T m (perturbLog base D E t u))
  have hs := perturbScore_bound D E hD hE ht hu
  have he := P.abs_expect_le hs
  have hh := P.expect_mono (fun y =>
    (abs_sub (perturbScore D E t u y) (P.expect (perturbScore D E t u))).trans
      ((add_le_add (hs y) he).trans_eq (show 2*(n:ℝ)+2*n=4*n by ring)))
  simpa only [thermalDefect, P,FiniteLaw.expect_const] using hh

end DilutedSpinGlass.KernelTower

namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
variable {Ω I X Y : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)]
    [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    [MeasurableSpace X] [MeasurableSpace Y] {L M : ℕ}

noncomputable def fullSelectedThermal
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin L → ℝ)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω L → ℝ)
    (sel : I → Bool) (fixed D E : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (t : ℝ) (z : FullRootState Y X I M) (u : ℝ) : ℝ :=
  KernelTower.thermalDefect (tower (rootArray z.2.2.1 z.2.2.2) L T Q) m
    (otherLog (base z.1 z.2.1.1 z.2.1.2) (rootArray z.2.2.1 z.2.2.2) sel fixed)
    (selectedCoefficient (rootArray z.2.2.1 z.2.2.2) sel D)
    (selectedCoefficient (rootArray z.2.2.1 z.2.2.2) sel E) t u

variable (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin L → ℝ)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω L → ℝ)
    (sel : I → Bool) (fixed D E : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (t : ℝ)

theorem measurable_fullSelectedThermal
    (hb : ∀ k y, Measurable (fun z : RootPath Y M × RootPath X k => base z.1 k z.2 y)) :
    Measurable (fun z : FullRootState Y X I M × ℝ => fullSelectedThermal T Q m base sel fixed D E t z.1 z.2) := by
  apply measurable_packRoot_param (F := fun h k x n y u =>
    KernelTower.thermalDefect (tower (rootArray n y) L T Q) m
      (otherLog (base h k x) (rootArray n y) sel fixed)
      (selectedCoefficient (rootArray n y) sel D)
      (selectedCoefficient (rootArray n y) sel E) t u)
  intro k n
  have hh : Measurable (fun z : ((RootPath Y M × RootPath X k) × ℝ) × RootPath I n =>
      KernelTower.thermalDefect (tower (rootArray n z.2) L T Q) m
        (otherLog (base z.1.1.1 k z.1.1.2) (rootArray n z.2) sel fixed)
        (selectedCoefficient (rootArray n z.2) sel D)
        (selectedCoefficient (rootArray n z.2) sel E) t z.1.2) := by
    apply measurable_from_prod_countable_left
    intro roots
    exact KernelTower.measurable_thermalDefect (tower (rootArray n roots) L T Q) m
      (base := fun z : (RootPath Y M × RootPath X k) × ℝ =>
        otherLog (base z.1.1 k z.1.2) (rootArray n roots) sel fixed)
      (D := fun _ : (RootPath Y M × RootPath X k) × ℝ => selectedCoefficient (rootArray n roots) sel D)
      (E := fun _ : (RootPath Y M × RootPath X k) × ℝ => selectedCoefficient (rootArray n roots) sel E)
      (t := fun _ : (RootPath Y M × RootPath X k) × ℝ => t) (u := fun z => z.2)
      (fun y => ((hb k (physical (rootArray n roots) L y)).comp measurable_fst).add measurable_const)
      (fun _ _ => measurable_const) (fun _ _ => measurable_const) measurable_const measurable_snd
  exact hh.comp ((measurable_fst.fst.prodMk measurable_snd).prodMk measurable_fst.snd)

omit [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I] [MeasurableSpace X] [MeasurableSpace Y] in
theorem fullSelectedThermal_nonneg (z : FullRootState Y X I M) (u : ℝ) :
    0 ≤ fullSelectedThermal T Q m base sel fixed D E t z u :=
  KernelTower.thermalDefect_nonneg _ _ _ _ _ _ _

omit [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I] [MeasurableSpace X] [MeasurableSpace Y] in
theorem fullSelectedThermal_bound
    (hD : ∀ i x y, |D i x y| ≤ 1) (hE : ∀ i x y, |E i x y| ≤ 1)
    (ht : |t| ≤ 1/4) {u : ℝ} (hu : |u| ≤ 1/4) (z : FullRootState Y X I M) :
    fullSelectedThermal T Q m base sel fixed D E t z u ≤ 4*(z.2.2.1:ℝ) :=
  KernelTower.thermalDefect_bound _ _ _ _ _
    (selectedCoefficient_bound _ sel D hD) (selectedCoefficient_bound _ sel E hE) ht hu

omit [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I] [MeasurableSpace X] [MeasurableSpace Y] in
theorem fullSelectedThermal_integral_sq
    (hD : ∀ i x y, |D i x y| ≤ 1) (hE : ∀ i x y, |E i x y| ≤ 1)
    (ht : |t| ≤ 1/4) {a b c : ℝ} (hab : a < b) (hc : 0 < c)
    (hm : ∀ j, c ≤ m j) (hI : Icc a b ⊆ Icc (-(1:ℝ)/4) (1/4)) (z : FullRootState Y X I M) :
    (∫ u in a..b, fullSelectedThermal T Q m base sel fixed D E t z u)^2 ≤
      (b-a)*(4+4*(b-a))/c*(z.2.2.1:ℝ) := by
  have hh := KernelTower.perturb_thermal_absolute
    (tower (rootArray z.2.2.1 z.2.2.2) L T Q) m
    (otherLog (base z.1 z.2.1.1 z.2.1.2) (rootArray z.2.2.1 z.2.2.2) sel fixed)
    (selectedCoefficient (rootArray z.2.2.1 z.2.2.2) sel D)
    (selectedCoefficient (rootArray z.2.2.1 z.2.2.2) sel E)
    (selectedCoefficient_bound _ sel D hD) (selectedCoefficient_bound _ sel E hE) ht hab hc hm hI
  unfold fullSelectedThermal
  convert hh using 1; ring

end DilutedSpinGlass.HeterogeneousMarks

namespace DilutedSpinGlass
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
variable {X I Y : Type} [MeasurableSpace X] [MeasurableSpace I] [MeasurableSpace Y] {M : ℕ}

/-- Jensen under the genuine entire disorder law, using its actual Poisson count. -/
theorem fullRoot_average_sq
    (ξ : Fin M → Measure Y) [∀ j, IsProbabilityMeasure (ξ j)]
    (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure I) [IsProbabilityMeasure ν] (r s : ℝ≥0)
    {F : FullRootState Y X I M → ℝ} (hF : Measurable F) {K : ℝ}
    (hb : ∀ z, (F z)^2 ≤ K*(z.2.2.1:ℝ)) :
    (∫ z, F z ∂fullRootLaw ξ μ ν r s)^2 ≤ K*s := by
  have hi := ((fullRoot_count_memLp ξ μ ν r s).integrable (by norm_num)).const_mul K
  have hsq : Integrable (fun z => (F z)^2) (fullRootLaw ξ μ ν r s) :=
    hi.mono' (hF.pow_const 2).aestronglyMeasurable (ae_of_all _ (fun z => by
      simpa only [Real.norm_eq_abs,abs_sq] using hb z))
  have hLp := (memLp_two_iff_integrable_sq hF.aestronglyMeasurable).mpr hsq
  have hv := variance_nonneg F (fullRootLaw ξ μ ν r s)
  rw [variance_eq_sub hLp] at hv
  have hh := integral_mono hsq hi hb
  rw [integral_const_mul,fullRoot_count_mean] at hh
  simp only [Pi.pow_apply] at hv
  linarith

end DilutedSpinGlass
end

end

section
section
namespace DilutedSpinGlass.SizeCoupling
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory HeterogeneousMarks
open scoped BigOperators NNReal

variable {Z X Y I : Type} [MeasurableSpace Z] [MeasurableSpace X] [MeasurableSpace Y]
  [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
  {A : I → Type} [∀ i, Fintype (A i)]

lemma measurable_integral_family (μ : Measure X) [SFinite μ] (f : Z → X → ℝ)
    (hf : Measurable (fun z : Z × X => f z.1 z.2)) :
    Measurable (fun z => ∫ x, f z x ∂μ) :=
  hf.stronglyMeasurable.integral_prod_right'.measurable

lemma measurable_spinMean_family {N p k l r : ℕ} [NeZero N] {B : Fin l → Type}
    [∀ i, Fintype (B i)]
    (Q : (i : Fin l) → Fin (r+1) → FiniteLaw (B i)) (m : Fin (r+1) → ℝ)
    (theta : Z → Fin k → InteractionSample p) (h : Z → Fin N → ℝ)
    (ψ : Z → (i : Fin l) → Spin → FinitePath (B i) (r+1) → ℝ)
    (hθ : ∀ j σ, Measurable (fun z => (theta z j).1 σ))
    (hh : ∀ i, Measurable (fun z => h z i))
    (hψ : ∀ i σ a, Measurable (fun z => ψ z i σ a)) :
    Measurable (fun z => spinMean Q m (theta z) (h z) (ψ z)) := by
  unfold spinMean
  apply FiniteLaw.measurable_expect
  intro indices
  apply FiniteLaw.measurable_expect
  intro sites
  apply measurable_root
  · intro x
    exact (Finset.measurable_sum _ (fun j _ => hθ j _)).add
      (Finset.measurable_sum _ (fun i _ => (hh i).mul_const _))
  · intro i x a
    exact hψ i _ a

/-- Quenched averaging preserves measurability in the entire parameter vector,
not merely in a single selected coordinate. -/
lemma measurable_countedMean_family (μ : Measure X) [IsProbabilityMeasure μ]
    (ξ : Measure Y) [IsProbabilityMeasure ξ] (ν : Measure I) [IsProbabilityMeasure ν]
    {p r N : ℕ} [NeZero N] (theta : X → InteractionSample p) (field : Y → ℝ)
    (hθ : ∀ σ, Measurable (fun x => (theta x).1 σ)) (hh : Measurable field)
    (Q : (i : I) → Fin (r+1) → FiniteLaw (A i)) (m : Fin (r+1) → ℝ)
    (ψ : Z → (i : I) → Spin → FinitePath (A i) (r+1) → ℝ)
    (hψ : ∀ i σ a, Measurable (fun z => ψ z i σ a)) (k l : ℕ) :
    Measurable (fun z => countedMean (N := N) μ ξ ν theta field Q m (ψ z) k l) := by
  let F (a : RootPath I l) (z : (Z × RootPath X k) × RootPath Y N) : ℝ :=
    spinMean (fun j => Q (rootArray l a j)) m (fun j => theta (rootArray k z.1.2 j))
      (fun i => field (rootArray N z.2 i)) (fun j => ψ z.1.1 (rootArray l a j))
  have hF (a : RootPath I l) : Measurable (F a) := by
    apply measurable_spinMean_family
    · intro j σ
      exact (hθ σ).comp ((measurable_rootArray k j).comp (measurable_snd.comp measurable_fst))
    · intro i
      exact hh.comp ((measurable_rootArray N i).comp measurable_snd)
    · intro i σ b
      exact (hψ _ σ b).comp (measurable_fst.comp measurable_fst)
  let G (a : RootPath I l) (z : Z × RootPath X k) := ∫ h, F a (z,h) ∂rootLaw N (fun _ => ξ)
  have hG (a : RootPath I l) : Measurable (G a) :=
    (hF a).stronglyMeasurable.integral_prod_right'.measurable
  let H (a : RootPath I l) (z : Z) := ∫ x, G a (z,x) ∂rootLaw k (fun _ => μ)
  have hH (a : RootPath I l) : Measurable (H a) :=
    (hG a).stronglyMeasurable.integral_prod_right'.measurable
  have hJ : Measurable (fun z : Z × RootPath I l => H z.2 z.1) :=
    measurable_from_prod_countable_left hH
  exact hJ.stronglyMeasurable.integral_prod_right'.measurable

lemma measurable_perturbedMean_family (μ : Measure X) [IsProbabilityMeasure μ]
    (ξ : Measure Y) [IsProbabilityMeasure ξ] (ν : Measure I) [IsProbabilityMeasure ν]
    {p r N : ℕ} [NeZero N] (theta : X → InteractionSample p) (field : Y → ℝ)
    (hθ : ∀ σ, Measurable (fun x => (theta x).1 σ)) (hh : Measurable field)
    (Q : (i : I) → Fin (r+1) → FiniteLaw (A i)) (m : Fin (r+1) → ℝ)
    (ψ : Z → (i : I) → Spin → FinitePath (A i) (r+1) → ℝ)
    (hψ : ∀ i σ a, Measurable (fun z => ψ z i σ a)) (u v : ℝ≥0) :
    Measurable (fun z => perturbedMean (N := N) μ ξ ν theta field Q m (ψ z) u v) := by
  apply measurable_const.add
  unfold twoPoissonMean
  apply measurable_integral_family
  apply measurable_from_prod_countable_left
  intro k
  apply measurable_integral_family
  apply measurable_from_prod_countable_left
  intro l
  exact measurable_countedMean_family μ ξ ν theta field hθ hh Q m ψ hψ k l

 
theorem parameter_average_negligible (π : Measure Z) [IsProbabilityMeasure π]
    (ν : Measure I) [IsProbabilityMeasure ν] {p r N : ℕ} [NeZero N] (M : Model p)
    (hθ : Integrable (fun z : InteractionSample p => ‖z.1‖) M.disorder.toMeasure)
    (hh : Integrable (fun h : ℝ => |h|) M.field.toMeasure)
    (Q : (i : I) → Fin (r+1) → FiniteLaw (A i)) (m : Fin (r+1) → ℝ)
    (hm : ∀ j, 0 < m j) (hend : m (Fin.last r) = 1)
    (ψ : Z → (i : I) → Spin → FinitePath (A i) (r+1) → ℝ)
    (hψm : ∀ i σ a, Measurable (fun z => ψ z i σ a))
    {D : ℝ} (hψ : ∀ z i σ a, |Real.log (ψ z i σ a)| ≤ D) (s : ℝ≥0) :
    Integrable (fun z => perturbedMean (N := N) M.disorder.toMeasure M.field.toMeasure ν
      id id Q m (ψ z) (M.alpha*N) s) π ∧
    |(∫ z, perturbedMean (N := N) M.disorder.toMeasure M.field.toMeasure ν
      id id Q m (ψ z) (M.alpha*N) s ∂π)-N*pressure M N| ≤ D*s := by
  have hc := integrate_close π (measurable_perturbedMean_family M.disorder.toMeasure
    M.field.toMeasure ν id id (fun σ => by fun_prop) measurable_id Q m ψ hψm (M.alpha*N) s)
    (integrable_const (N*pressure M N))
    (fun z => actual_perturbedMean_close ν M hθ hh Q m hm hend (ψ z) (hψ z) s)
  simpa only [integral_const,probReal_univ,smul_eq_mul,one_mul] using hc

end DilutedSpinGlass.SizeCoupling
end

end

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
variable {Ω R : Type} [Fintype Ω] [Fintype R] [DecidableEq R] {n k : ℕ}

lemma constrainedHistory_singleton (hk : 0 < k) (T : KernelTower Ω n)
    (m : Fin (n+1) → ℝ) (hm : ∀ j : Fin n, m j.succ ≠ 0)
    (hroot : m 0 = 0) (hend : m (Fin.last n) = 1)
    (a b : R → Option (Fin k)) (d : R → Fin n)
    (spinColor : Option (Fin k) → FinitePath Ω n → ℝ)
    (S : PrescribedTree n) (anchor : S.Leaf) :
    constrainedHistory T m a b d spinColor S anchor (fun _ => 1) =
      constrainedHistory T m a b d spinColor (single n) (firstLeaf (single n)) (fun _ => 1) := by
  let T' := KernelTower.prod n T (markPrior n (fun _ => FiniteLaw.pi (fun _ : R => MarkSelector.rademacher)))
  let D := fun c (y : FinitePath (Ω×(R→Bool)) n) => spinColor c (KernelTower.pathFst n y) *
    MarkSelector.pathColor a b d c (KernelTower.pathSnd n y)
  have hS := constrainedHistory_polarization hk T m hm hroot hend a b d spinColor S anchor (fun _ => 1)
  have h0 := constrainedHistory_polarization hk T m hm hroot hend a b d spinColor (single n) (firstLeaf _) (fun _ => 1)
  dsimp only at hS h0
  simp only [one_mul] at hS h0
  refine hS.trans (Eq.trans ?_ h0.symm)
  apply congrArg (fun t : ℝ => ((k:ℝ)^k/2^k)*t)
  apply Finset.sum_congr rfl
  intro ε _
  apply congrArg (fun t : ℝ => (∏ j, Polarization.sign (ε j))*t)
  exact anchorCoefficient_leaf S T' m hm hroot hend anchor
    (Polarization.averageDirection ε (fun j => D (some j))) (D none) k

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
