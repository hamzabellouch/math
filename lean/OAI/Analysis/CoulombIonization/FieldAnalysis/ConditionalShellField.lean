import Mathlib
import OAI.Analysis.CoulombIonization.FieldAnalysis.ShellMeanStatistic
import OAI.Analysis.CoulombIonization.Variational.FullSliceStatistics
import OAI.Analysis.CoulombIonization.FormDomain.InnerLinearCap

namespace OAI

noncomputable section

namespace CoulombAtom

section
open MeasureTheory Set Filter
open scoped BigOperators
attribute [local irreducible] oneBodySquareTotal graphFormVector fermionGraph

lemma shell_closed_inner_term_integrable {N : ℕ} {psi : FormVector N}
    (hpsi : SobolevVector psi) (p : SmoothMultiplier spaceDirections) (Z : ℝ)
    {h a : ℝ} (ha : 0 < a) (hh : h ≤ a) (hp : ∀ y, p.value y ≠ 0 → 2*a ≤ ‖y‖)
    (y : Space) (S : ℝ) (s : Spins N) :
    Integrable (fun x => (p.value y^2/S)*(closedRawInnerField Z h x y*‖psi.value s x‖^2)) := by
  by_cases hz : p.value y = 0
  · simp only [hz,zero_pow (by decide : 2 ≠ 0),zero_div,zero_mul]
    exact integrable_zero _ _ _
  have hf : Measurable (fun x : Configuration N => closedRawInnerField Z h x y) :=
    by simpa only [Function.comp_def,id_eq] using
      (closedRawInnerField_measurable N Z h).comp (measurable_id.prodMk measurable_const)
  exact (rawFormPair_integrable hpsi hf
    (closedRawInnerField_bound Z ha (by linarith) (hp y hz)) s).const_mul _

lemma fullSlicePair_shellMean {N M : ℕ} {psi : FormVector (N+M)}
    (p : SmoothMultiplier spaceDirections) (Z : ℝ) {h a : ℝ}
    (ha : 0 < a) (hh : h ≤ a) (hp : ∀ y, p.value y ≠ 0 → 2*a ≤ ‖y‖)
    (hs : SplitPositionSupport psi (fun z => p.value z = 0) (fun z => h < ‖z‖))
    (t : Spins M) (v : Configuration M) (hpsi : SobolevVector (coreSlice psi t v))
    (hm : formMass (coreSlice psi t v) ≠ 0) :
    fullSlicePair psi (shellMeanStatistic p Z ha hh hp) t v =
      ∑ i : Fin M, (p.value (v i)^2/(oneBodySquareTotal p).value v)*
        rawFormPair (coreSlice psi t v) (fun x => closedRawInnerField Z h x (v i)) := by
  have hv := hs.outer_of_mass_ne_zero t v hm
  have he (s : Spins N) :
      (∫ x : Configuration N, shellMeanField p Z h (joinLists x v)*‖(coreSlice psi t v).value s x‖^2) =
      ∑ i : Fin M, (p.value (v i)^2/(oneBodySquareTotal p).value v)*
        (∫ x : Configuration N, closedRawInnerField Z h x (v i)*‖(coreSlice psi t v).value s x‖^2) := by
    calc
      _ = ∫ x : Configuration N, ∑ i : Fin M,
          (p.value (v i)^2/(oneBodySquareTotal p).value v)*
            (closedRawInnerField Z h x (v i)*‖(coreSlice psi t v).value s x‖^2) := by
        apply integral_congr_ae
        apply ae_of_all
        intro x
        dsimp only
        by_cases hz : (coreSlice psi t v).value s x = 0
        · simp only [hz,norm_zero,zero_pow (by decide : 2 ≠ 0),mul_zero,Finset.sum_const_zero]
        · rw [shellMeanField_join p Z h x v (hs s t x v hz).1 hv]
          simp only [Finset.sum_div,Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro i _
          ring
      _ = ∑ i : Fin M, ∫ x : Configuration N,
          (p.value (v i)^2/(oneBodySquareTotal p).value v)*
            (closedRawInnerField Z h x (v i)*‖(coreSlice psi t v).value s x‖^2) :=
        integral_finsetSum _ (fun i _ => shell_closed_inner_term_integrable hpsi p Z ha hh hp _ _ s)
      _ = _ := by simp only [integral_const_mul]
  change (∑ s : Spins N, ∫ x : Configuration N,
    shellMeanField p Z h (joinLists x v)*‖(coreSlice psi t v).value s x‖^2) = _
  simp_rw [he]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [←Finset.mul_sum]
  rfl

lemma fullSlicePair_shellMean_le {N M : ℕ} {psi : FormVector (N+M)}
    (p : SmoothMultiplier spaceDirections) {Z lam h a : ℝ}
    (hZ : 0 ≤ Z) (hlam : 0 ≤ lam) (hh : 0 < h) (ha : h ≤ a)
    (hp : ∀ y, p.value y ≠ 0 → 2*a ≤ ‖y‖)
    (hs : SplitPositionSupport psi (fun z => p.value z = 0) (fun z => h < ‖z‖))
    (t : Spins M) (v : Configuration M) (hpsi : SobolevVector (coreSlice psi t v)) :
    fullSlicePair psi (shellMeanStatistic p Z (hh.trans_le ha) ha hp) t v ≤
      (h/a)*Real.sqrt (innerCapStatistic (coreSlice psi t v) Z lam h)*
        Real.sqrt (formMass (coreSlice psi t v)) := by
  let C := (h/a)*Real.sqrt (innerCapStatistic (coreSlice psi t v) Z lam h)*
        Real.sqrt (formMass (coreSlice psi t v))
  have hap : 0 < a := hh.trans_le ha
  have hC : 0 ≤ C := by dsimp [C]; positivity
  by_cases hm : formMass (coreSlice psi t v) = 0
  · rw [fullSlicePair_eq_zero_of_mass _ t v hpsi hm]
    exact hC
  rw [fullSlicePair_shellMean p Z (hh.trans_le ha) ha hp hs t v hpsi hm]
  have hS := oneBodySquareTotal_nonneg p v
  calc
    _ ≤ ∑ i : Fin M, (p.value (v i)^2/(oneBodySquareTotal p).value v)*C := by
      apply Finset.sum_le_sum
      intro i _
      by_cases hi : p.value (v i) = 0
      · simp only [hi,zero_pow (by decide : 2 ≠ 0),zero_div,zero_mul,le_refl]
      · have hy := hp _ hi
        have hr := rawFormPair_closedRawInnerField (Z := Z) hpsi (hh.trans_le ha)
          (show h+a ≤ ‖v i‖ by linarith) hm
        rw [hr]
        exact mul_le_mul_of_nonneg_left (actual_inner_linear_statistic hpsi hZ hlam hh ha hy)
          (div_nonneg (sq_nonneg _) hS)
    _ = ((oneBodySquareTotal p).value v/(oneBodySquareTotal p).value v)*C := by
      rw [←Finset.sum_mul,←Finset.sum_div,oneBodySquareTotal_value]
    _ ≤ C := by
      by_cases hz : (oneBodySquareTotal p).value v = 0
      · rw [hz,div_zero,zero_mul]; exact hC
      · rw [div_self hz,one_mul]

end
open MeasureTheory Filter
open scoped BigOperators
namespace CoreObservationEnsemble
lemma fullAverage_shellMean_le (E : CoreObservationEnsemble)
    (p : SmoothMultiplier spaceDirections) {Z lam h a : ℝ}
    (hZ : 0 ≤ Z) (hlam : 0 ≤ lam) (hh : 0 < h) (ha : h ≤ a)
    (hp : ∀ y, p.value y ≠ 0 → 2*a ≤ ‖y‖)
    (hs : E.supported (fun z => p.value z = 0) (fun z => h < ‖z‖)) :
    E.fullAverage (shellMeanStatistic p Z (hh.trans_le ha) ha hp) ≤
      (h/a)*Real.sqrt (E.innerCapAverage Z lam h)*Real.sqrt E.mass := by
  let I := Σ i : E.Branch, Spins (E.graph i).outSize
  let X : I → Type := fun i => Configuration (E.graph i.1).outSize
  let H : ∀ i : I, X i → ℝ := fun i v => innerCapStatistic (coreSlice (E.graph i.1).vector i.2 v) Z lam h
  let W : ∀ i : I, X i → ℝ := fun i v => formMass (coreSlice (E.graph i.1).vector i.2 v)
  have hH (i : I) : Integrable (H i) := innerCapStatistic_coreSlice_integrable (E.graph i.1).sobolev i.2 hZ hlam hh
  have hW (i : I) : Integrable (W i) := (E.graph i.1).sobolev.coreSlice_mass_integrable i.2
  have hnH (i : I) (v : X i) : 0 ≤ H i v := innerCapStatistic_nonneg ..
  have hnW (i : I) (v : X i) : 0 ≤ W i v := formMass_nonneg _
  have hc := sum_integral_sqrt_mul_sqrt_le (fun i : I => (volume : Measure (X i))) H W hH hW hnH hnW
  let F := shellMeanStatistic p Z (hh.trans_le ha) ha hp
  have hi (i : I) :
      (∫ v : X i, fullSlicePair (E.graph i.1).vector F i.2 v) ≤
        (h/a)*(∫ v : X i, Real.sqrt (H i v)*Real.sqrt (W i v)) := by
    rw [←integral_const_mul]
    apply integral_mono_ae (fullSlicePair_integrable (E.graph i.1).sobolev F i.2)
      ((integrable_sqrt_mul_sqrt (hH i) (hW i) (hnH i) (hnW i)).const_mul _)
    filter_upwards [(E.graph i.1).sobolev.ae_coreSlice i.2] with v hv
    simpa only [mul_assoc] using fullSlicePair_shellMean_le p hZ hlam hh ha hp (hs i.1) i.2 v hv
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hi i)
  rw [←Finset.mul_sum] at hsum
  have heF : (∑ i : I, ∫ v : X i, fullSlicePair (E.graph i.1).vector F i.2 v) = E.fullAverage F := by
    rw [Fintype.sum_sigma]
    exact Finset.sum_congr rfl (fun i _ => fullSlicePair_fubini (E.graph i).sobolev F)
  have heH : (∑ i : I, ∫ v : X i, H i v) = E.innerCapAverage Z lam h := by
    rw [Fintype.sum_sigma]
    rfl
  have heW : (∑ i : I, ∫ v : X i, W i v) = E.mass := by
    rw [Fintype.sum_sigma]
    exact Finset.sum_congr rfl (fun i _ => (E.graph i).sobolev.integral_coreSlice_mass)
  rw [heF] at hsum
  rw [heH,heW] at hc
  exact hsum.trans (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hc (div_nonneg hh.le (hh.trans_le ha).le))
end CoreObservationEnsemble

 theorem exists_actual_shellMean_constant : ∃ C : ℝ, 1 ≤ C ∧
    ∀ (Z lam : ℝ) (N : ℕ) (psi : FormVector N), SobolevFermion psi →
      formMass psi = 1 → 0 ≤ Z → 0 < lam → ∀ D h u : ℝ, 0 ≤ D → 0 < h → h < u/4 →
      max (corePriceExcess Z lam psi) 0 ≤ D →
      ∀ p : SmoothMultiplier spaceDirections,
      (∀ y, p.value y ≠ 0 → u/2 ≤ ‖y‖ ∧ ‖y‖ ≤ 4*u) →
      rawFormPair psi (shellMeanField p Z h) ≤
        (4*h/u)*Real.sqrt (C*(innerScale D h+lam^2)) := by
  obtain ⟨L,hL⟩ := exists_scaled_shell_stencil
  obtain ⟨C,hC,hbound⟩ := exists_actual_observed_innerCap_constant (by norm_num : (0:ℝ)<1/2) (beta := 4) L
  refine ⟨C,hC,?_⟩
  intro Z lam N psi hpsi hm hZ hlam D h u hD hh hu he p hp
  have hup : 0 < u := by linarith
  obtain ⟨ys,hlen,hys,hcover⟩ := hL u hup
  let E := (CoreObservationEnsemble.initial psi hpsi).observeCells ys
  have hs := CoreObservationEnsemble.annular_stencil_support psi hpsi hup ys (fun y hy => (hys y hy).1) hcover
  have hsupport : E.supported (fun z => p.value z = 0) (fun z => h < ‖z‖) := by
    intro i
    exact (hs i).mono (fun z hz => by by_contra hn; exact hz (hp z hn)) (fun z hz => hu.trans_le hz)
  have hap : 0 < u/4 := by positivity
  have hha : h ≤ u/4 := hu.le
  have hpa : ∀ y, p.value y ≠ 0 → 2*(u/4) ≤ ‖y‖ := fun y hy => by linarith [(hp y hy).1]
  have hmean := E.fullAverage_shellMean_le p hZ hlam.le hh hha hpa hsupport
  have hmass : E.mass = 1 := (CoreObservationEnsemble.observeCells_mass ..).trans ((CoreObservationEnsemble.initial_mass ..).trans hm)
  have hav : E.innerCapAverage Z lam h ≤ C*(innerScale D h+lam^2) :=
    hbound Z lam N psi hpsi hm hZ hlam D h u hD hh (by linarith) he ys hlen (by
      intro y hy; constructor <;> nlinarith [(hys y hy).1,(hys y hy).2])
  have heq : E.fullAverage (shellMeanStatistic p Z hap hha hpa) = rawFormPair psi (shellMeanField p Z h) := by
    rw [CoreObservationEnsemble.observeCells_fullAverage,CoreObservationEnsemble.initial_fullAverage]
    rfl
  rw [heq,hmass,Real.sqrt_one,mul_one] at hmean
  calc
    _ ≤ (h/(u/4))*Real.sqrt (E.innerCapAverage Z lam h) := hmean
    _ ≤ (h/(u/4))*Real.sqrt (C*(innerScale D h+lam^2)) :=
      mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hav) (div_nonneg hh.le hap.le)
    _ = _ := by congr 1; field_simp

end CoulombAtom

end

end OAI
