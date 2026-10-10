import Mathlib
import OAI.Analysis.CoulombIonization.Localization.CoreHistoryAverageBarrier
import OAI.Analysis.CoulombIonization.RadialBounds.dShellForm

namespace OAI

noncomputable section

namespace CoulombAtom

section
open MeasureTheory Filter
open scoped BigOperators
attribute [local irreducible] graphComponent graphFormVector fermionGraph weakGraph
  FermionMultiplier.apply oneBodySquareTotal fermionGraphValue

lemma weightedMass_eq_integral {N : ℕ} (F : fermionGraph N)
    (w : Configuration N → ℝ) (hm : Measurable w) {A : ℝ} (hb : ∀ x, ‖w x‖ ≤ A) :
    weightedMass F w = ∫ x, w x ∂graphRawLaw F := by
  have hh := rawFormPair_eq_integral (graphFormVector_sobolev F).sobolevVector hm hb
  simpa only [rawFormPair,weightedMass,graphFormVector_value_eq,formRawLaw_graph] using hh

lemma graph_weight_integrable {N : ℕ} (F : fermionGraph N)
    (w : Configuration N → ℝ) (hm : Measurable w) {A : ℝ} (hb : ∀ x, ‖w x‖ ≤ A) :
    Integrable w (graphRawLaw F) :=
  Integrable.of_bound hm.aestronglyMeasurable A (ae_of_all _ hb)

lemma gradientError_eq_weightedMass {N : ℕ} (p : SmoothMultiplier spaceDirections)
    (F : fermionGraph N) : oneBodyGradientError p F =
      ∑ i : Fin N,∑ a : Fin 3,weightedMass F (fun x =>
        (lineDeriv ℝ p.value (x i) (spaceDirections a))^2) := by
  unfold oneBodyGradientError weightedMass
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]

def rawGradientWeight {N : ℕ} (p : SmoothMultiplier spaceDirections)
    (x : Configuration N) : ℝ := ∑ i : Fin N, ∑ a : Fin 3,
      (lineDeriv ℝ p.value (x i) (spaceDirections a))^2
lemma rawGradientWeight_nonneg {N : ℕ} (p : SmoothMultiplier spaceDirections)
    (x : Configuration N) : 0 ≤ rawGradientWeight p x :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
lemma rawGradientWeight_measurable {N : ℕ} (p : SmoothMultiplier spaceDirections) :
    Measurable (rawGradientWeight (N := N) p) :=
  Finset.measurable_sum _ (fun i _ => Finset.measurable_sum _ (fun a _ =>
    (((smooth_lineDeriv_continuous p.regular (spaceDirections a)).comp (continuous_apply i)).pow 2).measurable))
lemma rawGradientWeight_le {N : ℕ} (p : SmoothMultiplier spaceDirections) {D : ℝ}
    (hD : ∀ a x, |lineDeriv ℝ p.value x (spaceDirections a)| ≤ D) (x : Configuration N) :
    rawGradientWeight p x ≤ 3*N*D^2 := by
  calc
    _ ≤ ∑ _i : Fin N, ∑ _a : Fin 3, D^2 := Finset.sum_le_sum fun i _ =>
      Finset.sum_le_sum fun a _ => by simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hD a (x i)) 2
    _ = _ := by simp; ring
lemma rawGradientWeight_integrable {N : ℕ} (p : SmoothMultiplier spaceDirections)
    (F : fermionGraph N) {D : ℝ} (hD : ∀ a x, |lineDeriv ℝ p.value x (spaceDirections a)| ≤ D) :
    Integrable (rawGradientWeight p) (graphRawLaw F) :=
  graph_weight_integrable F _ (rawGradientWeight_measurable p) (fun x => by
    rw [Real.norm_of_nonneg (rawGradientWeight_nonneg p x)]; exact rawGradientWeight_le p hD x)

lemma gradientError_eq_integral {N : ℕ} (p : SmoothMultiplier spaceDirections)
    (F : fermionGraph N) {D : ℝ} (hD : ∀ a x, |lineDeriv ℝ p.value x (spaceDirections a)| ≤ D) :
    oneBodyGradientError p F = ∫ x, rawGradientWeight p x ∂graphRawLaw F := by
  have hm (i : Fin N) (a : Fin 3) : Measurable (fun x : Configuration N =>
      (lineDeriv ℝ p.value (x i) (spaceDirections a))^2) :=
    (((smooth_lineDeriv_continuous p.regular (spaceDirections a)).comp (continuous_apply i)).pow 2).measurable
  have hb (i : Fin N) (a : Fin 3) (x : Configuration N) :
      ‖(lineDeriv ℝ p.value (x i) (spaceDirections a))^2‖ ≤ D^2 := by
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hD a (x i)) 2
  have hi (i : Fin N) (a : Fin 3) := graph_weight_integrable F _ (hm i a) (hb i a)
  rw [gradientError_eq_weightedMass]
  simp_rw [weightedMass_eq_integral F _ (hm _ _) (hb _ _)]
  unfold rawGradientWeight
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun a _ => hi i a))]
  apply Finset.sum_congr rfl
  intro i _
  exact (integral_finsetSum _ (fun a _ => hi i a)).symm

end
open MeasureTheory Filter
open scoped BigOperators
attribute [local irreducible] graphComponent fermionGraph weakGraph FermionMultiplier.apply

lemma graph_sum_value {α : Type*} {N : ℕ} (T : Finset α) (G : α → fermionGraph N) (s : Spins N) :
    ∀ᵐ x, graphComponent s none (∑ k ∈ T, G k) x = ∑ k ∈ T, graphComponent s none (G k) x := by
  have he := map_sum (graphComponent s none) G T
  rw [he]
  exact l2_coe_finset_sum volume T (fun k => graphComponent s none (G k))

lemma graph_sub_value {N : ℕ} (F G : fermionGraph N) (s : Spins N) :
    ∀ᵐ x, graphComponent s none (F-G) x = graphComponent s none F x-graphComponent s none G x := by
  have he := map_sub (graphComponent s none) F G
  rw [he]
  exact Lp.coeFn_sub _ _

lemma finite_apply_sum_value {α : Type*} {N : ℕ} (T : Finset α)
    (p : α → FermionMultiplier N) (F : fermionGraph N) (s : Spins N) :
    ∀ᵐ x, graphComponent s none (∑ k ∈ T, (p k).apply F) x =
      ((∑ k ∈ T, (p k).value x : ℝ) : ℂ)*graphComponent s none F x := by
  classical
  have ha : ∀ᵐ x : Configuration N, ∀ k ∈ T,
      graphComponent s none ((p k).apply F) x = ((p k).value x : ℂ)*graphComponent s none F x := by
    apply (ae_ball_iff T.finite_toSet.countable).mpr
    intro k hk
    exact (p k).apply_value F s
  filter_upwards [ha,graph_sum_value T (fun k => (p k).apply F) s] with x ha hx
  calc
    _ = ∑ k ∈ T, graphComponent s none ((p k).apply F) x := hx
    _ = ∑ k ∈ T, ((p k).value x : ℂ)*graphComponent s none F x := Finset.sum_congr rfl ha
    _ = (∑ k ∈ T, ((p k).value x : ℂ))*graphComponent s none F x := (Finset.sum_mul ..).symm
    _ = _ := congrArg (fun z : ℂ => z*graphComponent s none F x) (Complex.ofReal_sum _ _).symm

lemma ofReal_sub_mul_complex (a b : ℝ) (z : ℂ) :
    ((a-b:ℝ):ℂ)*z = (a:ℂ)*z-(b:ℂ)*z := by rw [Complex.ofReal_sub,sub_mul]

lemma finite_apply_sum_eq_sub {α : Type*} {N : ℕ} (T : Finset α)
    (p : α → FermionMultiplier N) (q t : FermionMultiplier N)
    (he : ∀ x, (∑ k ∈ T, (p k).value x) = q.value x-t.value x) (F : fermionGraph N) :
    (∑ k ∈ T, (p k).apply F) = q.apply F-t.apply F := by
  classical
  apply graph_value_components_ext
  intro s
  apply Lp.ext
  filter_upwards [finite_apply_sum_value T p F s,
    graph_sub_value (q.apply F) (t.apply F) s,q.apply_value F s,t.apply_value F s] with x hx hs hq ht
  calc
    _ = ((∑ k ∈ T, (p k).value x : ℝ) : ℂ)*graphComponent s none F x := hx
    _ = ((q.value x-t.value x : ℝ) : ℂ)*graphComponent s none F x := congrArg (fun z : ℝ => (z:ℂ)*graphComponent s none F x) (he x)
    _ = (q.value x : ℂ)*graphComponent s none F x-(t.value x : ℂ)*graphComponent s none F x := ofReal_sub_mul_complex _ _ _
    _ = graphComponent s none ((q.apply F)-(t.apply F)) x := (congrArg₂ (fun a b : ℂ => a-b) hq ht).symm.trans hs.symm

end CoulombAtom

end

end OAI
