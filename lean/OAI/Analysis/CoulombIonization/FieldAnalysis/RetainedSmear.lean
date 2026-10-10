import Mathlib
import OAI.Analysis.CoulombIonization.FieldAnalysis.ScaledSmearPressure
import OAI.Analysis.CoulombIonization.Variational.RetainedRepulsion

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Set Filter
open scoped BigOperators

namespace CoulombNeumann
open CoulombAtom
variable {N : ℕ}

def retainedSmear (b : ℝ) (S : Finset (Fin N)) (x : Configuration N) (y : Space) : ℝ :=
  ∑ i ∈ S, varthetaScaled b (y-x i)

lemma retainedSmear_nonneg {b : ℝ} (hb : 0 < b) (S : Finset (Fin N))
    (x : Configuration N) (y : Space) : 0 ≤ retainedSmear b S x y :=
  Finset.sum_nonneg (fun _ _ => varthetaScaled_nonneg hb _)

lemma retainedSmear_le_full {b : ℝ} (hb : 0 < b) (S : Finset (Fin N))
    (x : Configuration N) (y : Space) : retainedSmear b S x y ≤ physicalSmear b x y := by
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
    (fun _ _ _ => varthetaScaled_nonneg hb _)

lemma retainedSmear_ite (b : ℝ) (S : Finset (Fin N)) (x : Configuration N) (y : Space) :
    retainedSmear b S x y = ∑ i, if i ∈ S then varthetaScaled b (y-x i) else 0 := by
  classical
  simp [retainedSmear]

lemma retainedSmear_measurable (b : ℝ) (S : Configuration N → Finset (Fin N))
    (hS : ∀ i, MeasurableSet {x | i ∈ S x}) :
    Measurable (fun p : Configuration N × Space => retainedSmear b (S p.1) p.1 p.2) := by
  simp_rw [retainedSmear_ite]
  apply Finset.measurable_sum
  intro i _
  exact Measurable.ite (measurable_fst (hS i))
    ((varthetaScaled_measurable b).comp (measurable_snd.sub ((measurable_pi_apply i).comp measurable_fst)))
    measurable_const

lemma retainedSmear_pressure_integrable {b : ℝ} (hb : 0 < b) (S : Finset (Fin N))
    (x : Configuration N) : Integrable (fun y => retainedSmear b S x y^(5/3:ℝ)) := by
  have hm : Measurable (fun y => retainedSmear b S x y) := by
    unfold retainedSmear
    exact Finset.measurable_sum _ (fun i _ => (varthetaScaled_measurable b).comp (measurable_id.sub_const (x i)))
  apply (physicalSmear_pressure_integrable hb x).mono' (hm.pow_const _).aestronglyMeasurable
  exact Eventually.of_forall fun y => by
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (retainedSmear_nonneg hb S x y) _)]
    exact Real.rpow_le_rpow (retainedSmear_nonneg hb S x y) (retainedSmear_le_full hb S x y) (by norm_num)

def retainedPressure (b : ℝ) (S : Finset (Fin N)) (x : Configuration N) : ℝ :=
  ∫ y, retainedSmear b S x y^(5/3:ℝ)

lemma retainedPressure_measurable (b : ℝ) (S : Configuration N → Finset (Fin N))
    (hS : ∀ i, MeasurableSet {x | i ∈ S x}) :
    Measurable (fun x => retainedPressure b (S x) x) :=
  ((retainedSmear_measurable b S hS).pow_const _).stronglyMeasurable.integral_prod_right.measurable

lemma retainedPressure_nonneg {b : ℝ} (hb : 0 < b) (S : Finset (Fin N))
    (x : Configuration N) : 0 ≤ retainedPressure b S x :=
  integral_nonneg (fun y => Real.rpow_nonneg (retainedSmear_nonneg hb S x y) _)

lemma retainedPressure_le_full {b : ℝ} (hb : 0 < b) (S : Finset (Fin N))
    (x : Configuration N) : retainedPressure b S x ≤ physicalPressure b x := by
  exact integral_mono (retainedSmear_pressure_integrable hb S x) (physicalSmear_pressure_integrable hb x)
    (fun y => Real.rpow_le_rpow (retainedSmear_nonneg hb S x y) (retainedSmear_le_full hb S x y) (by norm_num))

lemma retainedPressure_le_average {b : ℝ} (hb : 0 < b) (S : Finset (Fin N))
    (x : Configuration N) : retainedPressure b S x ≤ physicalPressureAverage b x :=
  (retainedPressure_le_full hb S x).trans (physicalPressure_le_average hb x)

lemma retainedSmear_support {b : ℝ} (hb : 0 < b) (S : Finset (Fin N))
    (x : Configuration N) (y : Space)
    (hy : ∀ i ∈ S, Real.sqrt 3*b ≤ ‖y-x i‖) : retainedSmear b S x y = 0 := by
  exact Finset.sum_eq_zero (fun i hi => varthetaScaled_support hb _ (hy i hi))

lemma integral_retainedSmear {b : ℝ} (hb : 0 < b) (S : Finset (Fin N))
    (x : Configuration N) : (∫ y, retainedSmear b S x y) = (S.card:ℝ) := by
  unfold retainedSmear
  rw [integral_finsetSum _ (fun i _ => (varthetaScaled_integrable hb).comp_sub_right (x i))]
  simp only [integral_sub_right_eq_self,integral_varthetaScaled hb,Finset.sum_const, nsmul_eq_mul,mul_one]

end CoulombNeumann

open MeasureTheory Set Filter
open scoped BigOperators

namespace CoulombNeumann
open CoulombAtom
variable {N : ℕ}

lemma varthetaScaled_support_bound {b : ℝ} (hb : 0 < b) (x : Space)
    (hx : varthetaScaled b x ≠ 0) : ‖x‖ ≤ Real.sqrt 3*b := by
  by_contra! h
  exact hx (varthetaScaled_support hb x h.le)

lemma finiteSmear_retention (b : ℝ) (S : Finset (Fin N)) (x : Configuration N) (y : Space) :
    finiteSmear (varthetaScaled b) (x ∘ (S.orderEmbOfFin rfl).toEmbedding) y = retainedSmear b S x y := by
  classical
  change (∑ i : Fin S.card, varthetaScaled b (y-x ((S.orderIsoOfFin rfl i):Fin N))) = _
  exact ((S.orderIsoOfFin rfl).toEquiv.sum_comp (fun i : ↥S => varthetaScaled b (y-x i))).trans
    (Finset.sum_attach S (fun i => varthetaScaled b (y-x i)))

theorem retained_physical_coulomb_lower {b : ℝ} (hb : 0 < b) (S : Finset (Fin N))
    (x : Configuration N) (hx : Function.Injective x) :
    (1/2:ℝ)*(∫ r : Space × Space, retainedSmear b S x r.1*retainedSmear b S x r.2/‖r.1-r.2‖)-
      ((2*Real.pi+1)/2)*(N:ℝ)/b ≤
        ∑ i : Fin N, ∑ j : Fin N, if i < j then 1/‖x i-x j‖ else 0 := by
  have h := selected_coulomb_lower (varthetaScaled_measurable b) (varthetaScaled_nonneg hb)
    (show 0 ≤ Real.sqrt 3*b by positivity) (varthetaScaled_support_bound hb) hb
    (varthetaScaled_le hb) (fun _ _ h => varthetaScaled_radial b h) (integral_varthetaScaled hb)
    x hx (S.orderEmbOfFin rfl).toEmbedding
  simpa only [finiteSmear_retention] using h

theorem ae_retained_physical_coulomb_lower {b : ℝ} (hb : 0 < b)
    (S : Configuration N → Finset (Fin N)) :
    ∀ᵐ x : Configuration N,
      (1/2:ℝ)*(∫ r : Space × Space, retainedSmear b (S x) x r.1*retainedSmear b (S x) x r.2/‖r.1-r.2‖)-
        ((2*Real.pi+1)/2)*(N:ℝ)/b ≤
          ∑ i : Fin N, ∑ j : Fin N, if i < j then 1/‖x i-x j‖ else 0 := by
  filter_upwards [configuration_ae_nonsingular N] with x hx
  exact retained_physical_coulomb_lower hb (S x) x hx.2

end CoulombNeumann

open MeasureTheory Set Filter
open scoped BigOperators

namespace CoulombNeumann
open CoulombAtom
variable {N : ℕ}

def retainedDirect (b : ℝ) (S : Finset (Fin N)) (x : Configuration N) : ℝ :=
  (1/2:ℝ)*∫ r : Space × Space,
    retainedSmear b S x r.1*retainedSmear b S x r.2/‖r.1-r.2‖

lemma retainedDirect_nonneg {b : ℝ} (hb : 0 < b) (S : Finset (Fin N)) (x : Configuration N) :
    0 ≤ retainedDirect b S x := by
  apply mul_nonneg (by norm_num)
  exact integral_nonneg (fun r => div_nonneg
    (mul_nonneg (retainedSmear_nonneg hb S x r.1) (retainedSmear_nonneg hb S x r.2)) (norm_nonneg _))

lemma retainedDirect_measurable (b : ℝ) (S : Configuration N → Finset (Fin N))
    (hS : ∀ i, MeasurableSet {x | i ∈ S x}) :
    Measurable (fun x => retainedDirect b (S x) x) := by
  have h1 : Measurable (fun p : Configuration N × (Space × Space) => retainedSmear b (S p.1) p.1 p.2.1) := by
    have hf : Measurable (fun p : Configuration N × (Space × Space) => (p.1,p.2.1)) :=
      measurable_fst.prodMk (measurable_fst.comp measurable_snd)
    have hh := (retainedSmear_measurable b S hS).comp hf
    simpa only [Function.comp_def] using hh
  have h2 : Measurable (fun p : Configuration N × (Space × Space) => retainedSmear b (S p.1) p.1 p.2.2) := by
    have hf : Measurable (fun p : Configuration N × (Space × Space) => (p.1,p.2.2)) :=
      measurable_fst.prodMk (measurable_snd.comp measurable_snd)
    have hh := (retainedSmear_measurable b S hS).comp hf
    simpa only [Function.comp_def] using hh
  have hk : Measurable (fun p : Configuration N × (Space × Space) => ‖p.2.1-p.2.2‖) := by fun_prop
  exact ((h1.mul h2).div hk).stronglyMeasurable.integral_prod_right.measurable.const_mul _

def pointRepulsion (x : Configuration N) : ℝ :=
  ∑ i : Fin N, ∑ j : Fin N, if i < j then 1/‖x i-x j‖ else 0

lemma pointRepulsion_nonneg (x : Configuration N) : 0 ≤ pointRepulsion x := by
  unfold pointRepulsion
  exact Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => by split_ifs <;> positivity))

lemma pointRepulsion_mul (x : Configuration N) (w : ℝ) :
    pointRepulsion x*w = ∑ i : Fin N, ∑ j : Fin N, if i < j then w/‖x i-x j‖ else 0 := by
  unfold pointRepulsion
  simp only [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> simp [div_eq_mul_inv, mul_comm]

lemma pointRepulsion_value_integrable {ψ : FormVector N} (hψ : SobolevFermion ψ) (s : Spins N) :
    Integrable (fun x => pointRepulsion x*‖ψ.value s x‖^2) := by
  simp_rw [pointRepulsion_mul]
  apply integrable_finsetSum
  intro i _
  apply integrable_finsetSum
  intro j _
  split_ifs with hij
  · exact hψ.sobolevVector.pair_integrable s i j (ne_of_lt hij)
  · exact integrable_zero _ _ _

lemma integral_pointRepulsion_value {ψ : FormVector N} (hψ : SobolevFermion ψ) (s : Spins N) :
    (∫ x, pointRepulsion x*‖ψ.value s x‖^2) =
      ∑ i : Fin N, ∑ j : Fin N, if i < j then ∫ x, ‖ψ.value s x‖^2/‖x i-x j‖ else 0 := by
  simp_rw [pointRepulsion_mul]
  have hi (i j : Fin N) : Integrable (fun x => if i < j then ‖ψ.value s x‖^2/‖x i-x j‖ else 0) := by
    split_ifs with hij
    · exact hψ.sobolevVector.pair_integrable s i j (ne_of_lt hij)
    · exact integrable_zero _ _ _
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hi i j))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum _ (fun j _ => hi i j)]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> simp

lemma retainedDirect_value_integrable {ψ : FormVector N} (hψ : SobolevFermion ψ)
    {b : ℝ} (hb : 0 < b) (S : Configuration N → Finset (Fin N))
    (hS : ∀ i, MeasurableSet {x | i ∈ S x}) (s : Spins N) :
    Integrable (fun x => retainedDirect b (S x) x*‖ψ.value s x‖^2) := by
  have hc := ((hψ.1 s).norm.integrable_sq.const_mul (((2*Real.pi+1)/2)*(N:ℝ)/b))
  apply ((pointRepulsion_value_integrable hψ s).add hc).mono'
    ((retainedDirect_measurable b S hS).aestronglyMeasurable.mul ((hψ.1 s).aestronglyMeasurable.norm.pow 2))
  filter_upwards [ae_retained_physical_coulomb_lower hb S] with x hx
  change ‖retainedDirect b (S x) x*‖ψ.value s x‖^2‖ ≤
    pointRepulsion x*‖ψ.value s x‖^2+(((2*Real.pi+1)/2)*(N:ℝ)/b)*‖ψ.value s x‖^2
  rw [Real.norm_of_nonneg (mul_nonneg (retainedDirect_nonneg hb _ _) (sq_nonneg _)), ←add_mul]
  exact mul_le_mul_of_nonneg_right (by change retainedDirect b (S x) x-_ ≤ pointRepulsion x at hx; linarith) (sq_nonneg _)

end CoulombNeumann
namespace CoulombAtom
open CoulombNeumann
variable {N : ℕ}

theorem SobolevFermion.retained_repulsion {ψ : FormVector N} (hψ : SobolevFermion ψ)
    {b : ℝ} (hb : 0 < b) (S : Spins N → Configuration N → Finset (Fin N))
    (hS : ∀ s i, MeasurableSet {x | i ∈ S s x}) :
    (∑ s, ∫ x, retainedDirect b (S s x) x*‖ψ.value s x‖^2) ≤
      formRepulsion ψ+(((2*Real.pi+1)/2)*(N:ℝ)/b)*formMass ψ := by
  have hs (s : Spins N) :
      (∫ x, retainedDirect b (S s x) x*‖ψ.value s x‖^2) ≤
      (∫ x, pointRepulsion x*‖ψ.value s x‖^2)+
        (((2*Real.pi+1)/2)*(N:ℝ)/b)*(∫ x, ‖ψ.value s x‖^2) := by
    rw [←integral_const_mul,←integral_add (pointRepulsion_value_integrable hψ s)
      ((hψ.1 s).norm.integrable_sq.const_mul _)]
    apply integral_mono_ae (retainedDirect_value_integrable hψ hb (S s) (hS s) s)
      ((pointRepulsion_value_integrable hψ s).add ((hψ.1 s).norm.integrable_sq.const_mul _))
    filter_upwards [ae_retained_physical_coulomb_lower hb (S s)] with x hx
    change retainedDirect b (S s x) x*‖ψ.value s x‖^2 ≤
      pointRepulsion x*‖ψ.value s x‖^2+(((2*Real.pi+1)/2)*(N:ℝ)/b)*‖ψ.value s x‖^2
    rw [←add_mul]
    exact mul_le_mul_of_nonneg_right
      (by change retainedDirect b (S s x) x-_ ≤ pointRepulsion x at hx; linarith) (sq_nonneg _)
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun s _ => hs s)
  simpa only [Finset.sum_add_distrib,←Finset.mul_sum,integral_pointRepulsion_value hψ,formRepulsion,formMass] using hh

end CoulombAtom

end

end OAI
