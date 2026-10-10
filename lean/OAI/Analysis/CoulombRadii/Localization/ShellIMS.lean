import Mathlib
import OAI.Analysis.CoulombRadii.FieldAnalysis.RawObservable
import OAI.Analysis.CoulombRadii.Screening.CountMoments
import OAI.Analysis.CoulombRadii.Variational.PhysicalBridge
import OAI.Analysis.CoulombRadii.FieldAnalysis.PoissonInterior

namespace OAI

section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical ContDiff Topology
noncomputable section
namespace Coulomb

def imsShell (y : Space) (r : ℝ) : Set Space :=
  {x | r ≤ ‖x-y‖ ∧ ‖x-y‖ ≤ 2*r}

lemma measurableSet_imsShell (y : Space) (r : ℝ) : MeasurableSet (imsShell y r) := by
  exact ((isClosed_le continuous_const (continuous_id.sub continuous_const).norm).inter
    (isClosed_le (continuous_id.sub continuous_const).norm continuous_const)).measurableSet

lemma radialCut_fderiv_zero_inner (y : Space) {r : ℝ} (hr : 0 < r)
    (l : Fin 2) (x : Space) (hx : ‖x-y‖ < r) :
    fderiv ℝ (radialCut y r l) x = 0 := by
  have he : radialCut y r l =ᶠ[𝓝 x] (fun _ => if l=0 then (1:ℝ) else 0) := by
    have hh : ∀ᶠ z in 𝓝 x, ‖z-y‖ < r :=
      (isOpen_lt (continuous_id.sub continuous_const).norm continuous_const).mem_nhds hx
    filter_upwards [hh] with z hz
    have hs : ‖r⁻¹ • (z-y)‖ ≤ 1 := by
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hr)]
      exact (inv_mul_le_one₀ hr).2 hz.le
    simp only [radialCut,cutAngle,cutSeed_one _ hs,mul_one,
      Real.sin_pi_div_two,Real.cos_pi_div_two]
  rw [he.fderiv_eq]
  simp

lemma radialCut_gradient_shell_bound (y : Space) {r : ℝ} (hr : 0 < r)
    (b : Fin 3) (x : Space) :
    (∑ l : Fin 2, (fderiv ℝ (radialCut y r l) x (EuclideanSpace.single b 1))^2) ≤
      (2*(radialCutCoefficient/r)^2) * (imsShell y r).indicator (fun _ => (1:ℝ)) x := by
  by_cases hx : x ∈ imsShell y r
  · rw [indicator_of_mem hx,mul_one]
    calc
      _ ≤ ∑ _l : Fin 2, (radialCutCoefficient/r)^2 := by
        apply Finset.sum_le_sum
        intro l hl
        simpa only [sq_abs] using
          (sq_le_sq₀ (abs_nonneg _) (div_nonneg radialCutCoefficient_pos.le hr.le)).2
            (radialCut_derivative_bound y hr l b x)
      _ = _ := by simp
  · rw [indicator_of_notMem hx,mul_zero]
    have hd : ∀ l : Fin 2, fderiv ℝ (radialCut y r l) x = 0 := by
      have hnot : ¬ (r ≤ ‖x-y‖ ∧ ‖x-y‖ ≤ 2*r) := hx
      by_cases hinner : ‖x-y‖ < r
      · exact fun l => radialCut_fderiv_zero_inner y hr l x hinner
      · have houter : 2*r < ‖x-y‖ := lt_of_not_ge (fun h => hnot ⟨le_of_not_gt hinner,h⟩)
        exact fun l => radialCut_fderiv_zero y hr l x houter
    simp only [hd,zero_apply,ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true,
      zero_pow,Finset.sum_const_zero,le_refl]

theorem form_radial_labelCut_shell {J n : ℕ} (S : Nuclei J) (ψ : H1Vector n)
    (y : Space) {r : ℝ} (hr : 0 < r) :
    (∑ p : Fin n → Fin 2, form S (ψ.labelCut (radialCut y r) (radialCut_smooth y r)
      (radialCut_partition y r) (radialCutCoefficient/r) (div_nonneg radialCutCoefficient_pos.le hr.le)
      (radialCut_derivative_bound y hr) p)) ≤
      form S ψ+3*(radialCutCoefficient/r)^2*expectedPopulation ψ (imsShell y r) := by
  rw [form_labelCut]
  apply add_le_add_right
  let c : ℝ := 2*(radialCutCoefficient/r)^2
  have hi s i := population_integrable ψ (imsShell y r) (measurableSet_imsShell y r) s i
  have H (s : Spins n) (a : Fin n × Fin 3) :
      (∫ x, (∑ l, (fderiv ℝ (radialCut y r l) (position x a.1) (EuclideanSpace.single a.2 1))^2)*‖ψ.value s x‖^2) ≤
      c*(∫ x, (imsShell y r).indicator (fun _ => (1:ℝ)) (position x a.1)*‖ψ.value s x‖^2) := by
    rw [← integral_const_mul]
    apply integral_mono_of_nonneg
    · filter_upwards [] with x
      exact mul_nonneg (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) (sq_nonneg _)
    · exact (hi s a.1).const_mul c
    · filter_upwards [] with x
      simpa only [c,mul_assoc] using mul_le_mul_of_nonneg_right
        (radialCut_gradient_shell_bound y hr a.2 (position x a.1)) (sq_nonneg ‖ψ.value s x‖)
  calc
    _ ≤ (1/2:ℝ)*∑ s, ∑ a : Fin n × Fin 3, c*(∫ x,
          (imsShell y r).indicator (fun _ => (1:ℝ)) (position x a.1)*‖ψ.value s x‖^2) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun s _ => Finset.sum_le_sum (fun a _ => H s a))) (by norm_num)
    _ = _ := by
      simp only [Fintype.sum_prod_type,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
        ← Finset.mul_sum,expectedPopulation,c]
      ring

end Coulomb

namespace NeutralAtom

theorem fromH1_expectedPopulation {N : ℕ} (ψ : Coulomb.H1Vector (N+1))
    (ha : Coulomb.Antisymmetric ψ) {A : Set Position} (hA : MeasurableSet A) :
    Coulomb.expectedPopulation ψ A = ∫ x in A, density (fromH1Wave ψ) x := by
  have hd := fromH1_domain ψ ha
  rw [← rawExpectation_count_eq_density hd.1 hd.2.2.1 hA,
    Coulomb.expectedPopulation_eq ψ hA]
  unfold rawExpectation configurationDensity
  simp_rw [Finset.mul_sum]
  have hi s : Integrable (fun x => rawCount A x * ‖fromH1Wave ψ s x‖^2) := by
    simp_rw [rawCount, Finset.sum_mul]
    exact integrable_finsetSum _ fun i _ =>
      integrable_siteWeight (hd.2.2.1 s).norm.integrable_sq hA i
  rw [integral_finsetSum _ (fun s _ => hi s)]
  apply Finset.sum_congr rfl
  intro s _
  exact ((flattenConfiguration_measurePreserving (N+1)).integral_comp'
    (fun x => Coulomb.localCount A x*‖ψ.value s x‖^2)).symm

end NeutralAtom

namespace Coulomb

lemma expectedPopulation_labelCut {n : ℕ} {L : Type*} [Fintype L] (ψ : H1Vector n)
    (χ : L → Space → ℝ) (hχ : ∀ l, ContDiff ℝ ∞ (χ l))
    (hp : ∀ z, ∑ l, χ l z^2=1) (D : ℝ) (hD : 0 ≤ D)
    (hd : ∀ l b z, |fderiv ℝ (χ l) z (EuclideanSpace.single b 1)| ≤ D)
    {A : Set Space} (hA : MeasurableSet A) :
    (∑ p : Fin n → L, expectedPopulation (ψ.labelCut χ hχ hp D hD hd p) A) =
      expectedPopulation ψ A := by
  simp only [expectedPopulation_eq _ hA]
  exact potentialForm_labelCut ψ χ hχ hp D hD hd (localCount A)
    (localCount_measurable hA) (fun x => by rw [abs_of_nonneg (localCount_nonneg A x)]; exact localCount_le A x)

end Coulomb
end

end

end OAI
