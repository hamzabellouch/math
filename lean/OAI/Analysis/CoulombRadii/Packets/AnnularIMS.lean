import Mathlib
import OAI.Analysis.CoulombRadii.Screening.UniformCountConsequences
import OAI.Analysis.CoulombRadii.Localization.ShellIMS
import OAI.Analysis.CoulombRadii.Localization.AnnularCut

namespace OAI

section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical ContDiff Topology
noncomputable section
namespace Coulomb

def annularBand (u : ℝ) : Set Space := {x | u/2 ≤ ‖x‖ ∧ ‖x‖ ≤ 4*u}
lemma measurableSet_annularBand (u : ℝ) : MeasurableSet (annularBand u) :=
  ((isClosed_le continuous_const continuous_norm).inter (isClosed_le continuous_norm continuous_const)).measurableSet

lemma annularAngle_zero {u : ℝ} (hu : 0<u) {x : Space} (hx : ‖x‖≤u/2 ∨ 4*u≤‖x‖) :
    annularAngle u x=0 := by
  rcases hx with hx|hx
  · have h1 := cutAngle_inner 0 (by positivity : 0<2*u) (x:=x) (by simp only [sub_zero]; linarith)
    have h2 := cutAngle_inner 0 (by positivity : 0<u/2) (x:=x) (by simpa using hx)
    simp only [annularAngle,h1,h2,sub_self]
  · have h1 := cutAngle_outer 0 (by positivity : 0<2*u) (x:=x) (by simp only [sub_zero]; linarith)
    have h2 := cutAngle_outer 0 (by positivity : 0<u/2) (x:=x) (by simp only [sub_zero]; linarith)
    simp only [annularAngle,h1,h2,sub_self]

lemma annularCut_derivative_zero {u : ℝ} (hu : 0<u) (l : Fin 2) {x : Space}
    (hx : x ∉ annularBand u) : fderiv ℝ (annularCut u l) x=0 := by
  have he : annularCut u l =ᶠ[𝓝 x] (fun _ => if l=0 then (0:ℝ) else 1) := by
    have hnot : ¬ (u/2 ≤ ‖x‖ ∧ ‖x‖ ≤ 4*u) := hx
    by_cases hi : ‖x‖ < u/2
    · have hn := (isOpen_lt continuous_norm continuous_const).mem_nhds hi
      filter_upwards [hn] with z hz
      simp only [annularCut,annularAngle_zero hu (Or.inl hz.le),Real.sin_zero,Real.cos_zero]
    · have ho : 4*u < ‖x‖ := lt_of_not_ge (fun h => hnot ⟨le_of_not_gt hi,h⟩)
      have hn := (isOpen_lt continuous_const continuous_norm).mem_nhds ho
      filter_upwards [hn] with z hz
      simp only [annularCut,annularAngle_zero hu (Or.inr hz.le),Real.sin_zero,Real.cos_zero]
  rw [he.fderiv_eq]
  simp

lemma annularCut_gradient_band_bound {u : ℝ} (hu : 0<u) (b : Fin 3) (x : Space) :
    (∑ l : Fin 2, (fderiv ℝ (annularCut u l) x (EuclideanSpace.single b 1))^2) ≤
      (2*(3*radialCutCoefficient/u)^2)*(annularBand u).indicator (fun _ => (1:ℝ)) x := by
  by_cases hx : x∈annularBand u
  · rw [indicator_of_mem hx,mul_one]
    calc
      _ ≤ ∑ _l : Fin 2, (3*radialCutCoefficient/u)^2 := by
        apply Finset.sum_le_sum
        intro l hl
        simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (div_nonneg (mul_nonneg (by norm_num) radialCutCoefficient_pos.le) hu.le)).2 (annularCut_derivative_bound hu l b x)
      _ = _ := by simp
  · rw [indicator_of_notMem hx,mul_zero]
    simp only [annularCut_derivative_zero hu _ hx,zero_apply,ne_eq,OfNat.ofNat_ne_zero,
      not_false_eq_true,zero_pow,Finset.sum_const_zero,le_refl]

theorem form_annular_labelCut {J n : ℕ} (S : Nuclei J) (ψ : H1Vector n)
    {u : ℝ} (hu : 0<u) :
    (∑ p : Fin n → Fin 2, form S (ψ.labelCut (annularCut u) (annularCut_smooth u)
      (annularCut_partition u) (3*radialCutCoefficient/u) (div_nonneg (mul_nonneg (by norm_num) radialCutCoefficient_pos.le) hu.le)
      (annularCut_derivative_bound hu) p)) ≤
      form S ψ+3*(3*radialCutCoefficient/u)^2*expectedPopulation ψ (annularBand u) := by
  rw [form_labelCut]
  apply add_le_add_right
  let c : ℝ := 2*(3*radialCutCoefficient/u)^2
  have hi s i := population_integrable ψ (annularBand u) (measurableSet_annularBand u) s i
  have H (s : Spins n) (a : Fin n × Fin 3) :
      (∫ x, (∑ l, (fderiv ℝ (annularCut u l) (position x a.1) (EuclideanSpace.single a.2 1))^2)*‖ψ.value s x‖^2) ≤
      c*(∫ x, (annularBand u).indicator (fun _ => (1:ℝ)) (position x a.1)*‖ψ.value s x‖^2) := by
    rw [←integral_const_mul]
    apply integral_mono_of_nonneg
    · filter_upwards [] with x
      exact mul_nonneg (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) (sq_nonneg _)
    · exact (hi s a.1).const_mul c
    · filter_upwards [] with x
      simpa only [c,mul_assoc] using mul_le_mul_of_nonneg_right
        (annularCut_gradient_band_bound hu a.2 (position x a.1)) (sq_nonneg ‖ψ.value s x‖)
  calc
    _ ≤ (1/2:ℝ)*∑ s, ∑ a : Fin n × Fin 3, c*(∫ x,
          (annularBand u).indicator (fun _ => (1:ℝ)) (position x a.1)*‖ψ.value s x‖^2) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun s _ => Finset.sum_le_sum (fun a _ => H s a))) (by norm_num)
    _ = _ := by
      simp only [Fintype.sum_prod_type,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
        ←Finset.mul_sum,expectedPopulation,c]
      ring

def annularIMSCost {n : ℕ} (ψ : H1Vector n) (u : ℝ) : ℝ :=
  3*(3*radialCutCoefficient/u)^2*expectedPopulation ψ (annularBand u)

theorem exists_annular_recorded_ensemble {J n : ℕ} (S : Nuclei J)
    (ψ : H1Vector n) (hψ : Antisymmetric ψ) {u : ℝ} (hu : 0<u) :
    ∃ T : RecordedEnsemble n, T.Conserves ψ ∧ T.CoreFermionic ∧ T.OutFermionic ∧
      T.CoreSupported (imsShell 0 u)ᶜ ∧
      T.OutSupported {x : Space | u/2<‖x‖ ∧ ‖x‖<4*u} ∧
      T.totalMass=mass ψ ∧ T.totalForm S ≤ form S ψ+annularIMSCost ψ u := by
  obtain ⟨T,hc,hf,ho,hcs,hos,hm,he⟩ := RecordedEnsemble.binary_localization S ψ hψ
    (annularCut u) (annularCut_smooth u) (annularCut_partition u)
    (3*radialCutCoefficient/u) (div_nonneg (mul_nonneg (by norm_num) radialCutCoefficient_pos.le) hu.le) (annularCut_derivative_bound hu)
    {x : Space | u/2<‖x‖ ∧ ‖x‖<4*u} (imsShell 0 u)ᶜ
    (by
      intro z hz
      apply annularCut_out_zero hu
      by_cases hi : ‖z‖≤u/2
      · exact Or.inl hi
      · exact Or.inr (le_of_not_gt (fun h => hz ⟨lt_of_not_ge hi,h⟩)))
    (by
      intro z hz
      apply annularCut_core_zero hu
      simpa only [mem_compl_iff,not_not,imsShell,mem_ofPred_eq,sub_zero] using hz)
  refine ⟨T,hc,hf,ho,hcs,hos,hm,?_⟩
  rw [he]
  exact form_annular_labelCut S ψ hu

theorem exists_atomic_annular_IMS_bound : ∃ C : ℝ, 0≤C ∧
    ∀ {J n : ℕ} (S : Nuclei J), (∀ i, S.position i=0) →
    ∀ (ψ : H1Vector n), Antisymmetric ψ → mass ψ=1 →
    ∀ {E δ : ℝ}, (E:EReal)≤unrestrictedFormBottom S → form S ψ≤E+δ → 0≤δ →
    ∀ {u : ℝ}, 0<u → annularIMSCost ψ u ≤ C*screenMass δ u/u^2 := by
  obtain ⟨C,hC,H⟩ := atomic_annular_second_moment (α:=1/4) (β:=5) (by norm_num) (by norm_num)
  refine ⟨27*radialCutCoefficient^2*Real.sqrt C,by positivity,?_⟩
  intro J n S hatom ψ ha hm E δ hE hstate hδ u hu
  have hA : MeasurableSet {x : Space | (1/4:ℝ)*u<‖x‖ ∧ ‖x‖<5*u} :=
    ((isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)).measurableSet
  have hsub : annularBand u ⊆ {x : Space | (1/4:ℝ)*u<‖x‖ ∧ ‖x‖<5*u} := by
    intro x hx
    constructor <;> linarith [hx.1,hx.2]
  have hb := ((expectedPopulation_sq_le ψ (measurableSet_annularBand u) hm).trans
    (localCountSecondMoment_mono ψ hA hsub)).trans (H S hatom ψ ha hm hE hstate hδ hu)
  have hh : expectedPopulation ψ (annularBand u) ≤ Real.sqrt C*screenMass δ u := by
    rw [←Real.sq_sqrt hC,←mul_pow] at hb
    exact (sq_le_sq₀ (expectedPopulation_nonneg _ _) (mul_nonneg (Real.sqrt_nonneg C) (screenMass_pos _ _).le)).mp hb
  calc
    _ ≤ 3*(3*radialCutCoefficient/u)^2*(Real.sqrt C*screenMass δ u) :=
      mul_le_mul_of_nonneg_left hh (by positivity)
    _ = _ := by ring

end Coulomb
end

end

end OAI
