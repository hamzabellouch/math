import OAI.Probability.DilutedSpin.JointRootParam
import OAI.Probability.DilutedSpin.PerturbedSizeCoupling
import OAI.Probability.DilutedSpin.RootAE
import OAI.Probability.DilutedSpin.SelectedRegularity

namespace OAI

section
section
namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
variable {Ω I X Y : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)]
    [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    [MeasurableSpace X] [MeasurableSpace Y] {L M : ℕ}

noncomputable def fullSelectedLog
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin L → ℝ)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω L → ℝ)
    (sel : I → Bool) (fixed D E : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (t : ℝ) (z : FullRootState Y X I M) (u : ℝ) : ℝ :=
  packRoot (fun h k x n y => root T Q m (base h k x) (rootArray n y)
    (selectedFactor sel fixed D E t u)+(2*u^2)*n) z

noncomputable def fullSelectedScore
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin L → ℝ)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω L → ℝ)
    (sel : I → Bool) (fixed D E : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (t : ℝ) (z : FullRootState Y X I M) (u : ℝ) : ℝ :=
  packRoot (fun h k x n y => selectedScore T Q m (base h k x) (rootArray n y) sel fixed D E t u+4*n*u) z

variable (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin L → ℝ)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω L → ℝ)
    (sel : I → Bool) (fixed D E : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (t : ℝ)

omit [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I] [MeasurableSpace X] [MeasurableSpace Y] in
theorem fullSelectedLog_eq (z : FullRootState Y X I M) (u : ℝ) :
    fullSelectedLog T Q m base sel fixed D E t z u =
      KernelTower.correctedPerturbLog (tower (rootArray z.2.2.1 z.2.2.2) L T Q) m
        (otherLog (base z.1 z.2.1.1 z.2.1.2) (rootArray z.2.2.1 z.2.2.2) sel fixed)
        (selectedCoefficient (rootArray z.2.2.1 z.2.2.2) sel D)
        (selectedCoefficient (rootArray z.2.2.1 z.2.2.2) sel E) t u := by
  rw [corrected_log_eq]
  unfold fullSelectedLog packRoot
  ring

omit [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I] [MeasurableSpace X] [MeasurableSpace Y] in
theorem fullSelectedScore_eq (z : FullRootState Y X I M) (u : ℝ) :
    fullSelectedScore T Q m base sel fixed D E t z u =
      KernelTower.correctedPerturbScore (tower (rootArray z.2.2.1 z.2.2.2) L T Q) m
        (otherLog (base z.1 z.2.1.1 z.2.1.2) (rootArray z.2.2.1 z.2.2.2) sel fixed)
        (selectedCoefficient (rootArray z.2.2.1 z.2.2.2) sel D)
        (selectedCoefficient (rootArray z.2.2.1 z.2.2.2) sel E) t u := by
  rw [corrected_score_eq]
  rfl

theorem measurable_fullSelectedLog
    (hb : ∀ k y, Measurable (fun z : RootPath Y M × RootPath X k => base z.1 k z.2 y)) (u : ℝ) :
    Measurable (fun z => fullSelectedLog T Q m base sel fixed D E t z u) := by
  apply measurable_packRoot
  intro k n
  exact (measurable_root_base T Q m (fun z : RootPath Y M × RootPath X k => base z.1 k z.2)
    (hb k) (selectedFactor sel fixed D E t u) n).add measurable_const

theorem measurable_fullSelectedScore
    (hb : ∀ k y, Measurable (fun z : RootPath Y M × RootPath X k => base z.1 k z.2 y)) :
    Measurable (fun z : FullRootState Y X I M × ℝ => fullSelectedScore T Q m base sel fixed D E t z.1 z.2) := by
  apply measurable_packRoot_param (F := fun h k x n y u =>
    selectedScore T Q m (base h k x) (rootArray n y) sel fixed D E t u+4*n*u)
  intro k n
  have hh : Measurable (fun z : ((RootPath Y M × RootPath X k) × ℝ) × RootPath I n =>
      selectedScore T Q m (base z.1.1.1 k z.1.1.2) (rootArray n z.2) sel fixed D E t z.1.2+4*n*z.1.2) := by
    apply measurable_from_prod_countable_left
    intro roots
    exact measurable_selected_correctedScore T Q m
      (fun z : RootPath Y M × RootPath X k => base z.1 k z.2) (rootArray n roots) sel fixed D E (hb k) t
  exact hh.comp ((measurable_fst.fst.prodMk measurable_snd).prodMk measurable_fst.snd)

end DilutedSpinGlass.HeterogeneousMarks
end

end

section
section
namespace DilutedSpinGlass
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped NNReal

/-- A bounded representative, used only with a proof of AE equality. It does
not impose a pointwise bound on all values of an unrestricted sample space. -/
noncomputable def clipReal (C x : ℝ) : ℝ := max (-C) (min C x)

lemma clipReal_bound {C : ℝ} (hC : 0 ≤ C) (x : ℝ) : |clipReal C x| ≤ C := by
  apply abs_le.mpr
  exact ⟨le_max_left _ _,max_le (by linarith) (min_le_left _ _)⟩

lemma clipReal_eq {C x : ℝ} (hx : |x| ≤ C) : clipReal C x = x := by
  simp only [clipReal,min_eq_right (abs_le.mp hx).2,max_eq_right (abs_le.mp hx).1]

lemma measurable_clipReal (C : ℝ) : Measurable (clipReal C) :=
  measurable_const.max (measurable_const.min measurable_id)

noncomputable def clipSample {p : ℕ} (C : ℝ) (z : InteractionSample p) : InteractionSample p :=
  (fun σ => clipReal C (z.1 σ),z.2)

lemma clipSample_bound {p : ℕ} {C : ℝ} (hC : 0 ≤ C) (z : InteractionSample p) (σ) :
    |(clipSample C z).1 σ| ≤ C := clipReal_bound hC _

lemma clipSample_eq {p : ℕ} {C : ℝ} {z : InteractionSample p}
    (hz : ∀ σ, |z.1 σ| ≤ C) : clipSample C z = z := by
  apply Prod.ext
  · funext σ; exact clipReal_eq (hz σ)
  · rfl

lemma measurable_clipSample {p : ℕ} (C : ℝ) : Measurable (clipSample (p := p) C) := by
  apply Measurable.prodMk
  · exact Measurable.of_eval (fun σ => (measurable_clipReal C).comp ((measurable_pi_apply σ).comp measurable_fst))
  · exact measurable_snd

namespace SizeCoupling
variable {X Y I : Type} [MeasurableSpace X] [MeasurableSpace Y]
    [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    {A : I → Type} [∀ i, Fintype (A i)]

omit [Countable I] [MeasurableSingletonClass I] in
lemma perturbedMean_congr (μ : Measure X) [IsProbabilityMeasure μ]
    (ξ : Measure Y) [IsProbabilityMeasure ξ] (ν : Measure I)
    {p r N : ℕ} [NeZero N] (theta theta' : X → InteractionSample p) (field field' : Y → ℝ)
    (hθ : theta =ᵐ[μ] theta') (hh : field =ᵐ[ξ] field')
    (Q : (i : I) → Fin (r+1) → FiniteLaw (A i)) (m : Fin (r+1) → ℝ)
    (ψ : (i : I) → Spin → FinitePath (A i) (r+1) → ℝ) (u v : ℝ≥0) :
    perturbedMean (N := N) μ ξ ν theta field Q m ψ u v =
      perturbedMean (N := N) μ ξ ν theta' field' Q m ψ u v := by
  unfold perturbedMean twoPoissonMean
  simp_rw [countedMean_congr μ ξ ν theta theta' field field' hθ hh Q m ψ]

/-- The genuine bounded-model increment estimate, with AE (not vacuous global)
bounds on the original physical law. -/
theorem actual_uniform_increment_ae (ν : Measure I) [IsProbabilityMeasure ν]
    {p r N : ℕ} [NeZero N] (M : Model p)
    {C H : ℝ} (hC : 0 ≤ C) (hH : 0 ≤ H)
    (hθ : ∀ᵐ z ∂M.disorder.toMeasure, ∀ σ, |z.1 σ| ≤ C)
    (hh : ∀ᵐ h ∂M.field.toMeasure, |h| ≤ H)
    (Q : (i : I) → Fin (r+1) → FiniteLaw (A i)) (m : Fin (r+1) → ℝ)
    (hm : ∀ j, 0 < m j) (ψ : (i : I) → Spin → FinitePath (A i) (r+1) → ℝ)
    {D : ℝ} (hD : 0 ≤ D) (hψ : ∀ i σ a, |Real.log (ψ i σ a)| ≤ D) :
    |perturbedMean (N := N+1) M.disorder.toMeasure M.field.toMeasure ν id id Q m ψ
        (M.alpha*(N+1)) (scoreRate (N+1))-
      perturbedMean (N := N) M.disorder.toMeasure M.field.toMeasure ν id id Q m ψ
        (M.alpha*N) (scoreRate N)| ≤ Real.log 2+H+(2*p+1)*C*M.alpha+3*D := by
  have heθ : id =ᵐ[M.disorder.toMeasure] clipSample C := hθ.mono (fun z hz => (clipSample_eq hz).symm)
  have heh : id =ᵐ[M.field.toMeasure] clipReal H := hh.mono (fun h hh => (clipReal_eq hh).symm)
  rw [perturbedMean_congr _ _ ν id (clipSample C) id (clipReal H) heθ heh,
    perturbedMean_congr _ _ ν id (clipSample C) id (clipReal H) heθ heh]
  exact perturbedMean_uniform_increment _ _ ν (clipSample C) (clipReal H)
    (fun σ => (measurable_clipReal C).comp ((measurable_pi_apply σ).comp measurable_fst))
    (measurable_clipReal H) Q m hm ψ hC hD (clipSample_bound hC) (clipReal_bound hH) hψ M.alpha

end SizeCoupling
end DilutedSpinGlass
end

end

end OAI
