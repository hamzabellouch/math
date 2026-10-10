import Mathlib
import OAI.Probability.SKGap.Localization.QueryColumn

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Matrix.Norms.Elementwise
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Matrix.Norms.Elementwise
open scoped BigOperators
open scoped BigOperators NNReal ENNReal
open MeasureTheory Metric Set
open scoped BigOperators NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators NNReal ENNReal Matrix.Norms.L2Operator
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Matrix.Norms.L2Operator
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Set
namespace SKGapCutoff.Regression

local instance adaptiveMatrixMeasurable {n m : ℕ} : MeasurableSpace (Matrix (Fin n) (Fin m) ℝ) :=
  inferInstanceAs (MeasurableSpace (Fin n → Fin m → ℝ))

local instance adaptiveMatrixBorel {n m : ℕ} : BorelSpace (Matrix (Fin n) (Fin m) ℝ) :=
  inferInstanceAs (BorelSpace (Fin n → Fin m → ℝ))

lemma map_prod_section_congr {H A B C : Type*}
    [MeasurableSpace H] [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
    (ρ : Measure H) (μ : Measure A) (ν : Measure B) [SFinite μ] [SFinite ν]
    (f : H × A → C) (g : H × B → C) (hf : Measurable f) (hg : Measurable g)
    (hfg : ∀ h, μ.map (fun a => f (h,a)) = ν.map (fun b => g (h,b))) :
    (ρ.prod μ).map f = (ρ.prod ν).map g := by
  ext s hs
  rw [Measure.map_apply hf hs, Measure.map_apply hg hs,
    Measure.prod_apply (hf hs), Measure.prod_apply (hg hs)]
  apply lintegral_congr
  intro h
  have hh := congrArg (fun m : Measure C => m s) (hfg h)
  exact (Measure.map_apply (hf.comp measurable_prodMk_left) hs).symm.trans
    (hh.trans (Measure.map_apply (hg.comp measurable_prodMk_left) hs))

noncomputable def queryResidual {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ)
    (q : Fin n → ℝ) (g : (Fin n × Fin n) → ℝ) : (Fin n × Fin n) → ℝ :=
  fun p => (queryComplement P q * goe g * queryComplement P q) p.1 p.2

noncomputable def queryAnswer {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ)
    (q : Fin n → ℝ) (g : (Fin n × Fin n) → ℝ) : Fin n → ℝ :=
  fun i => (P * goe g * queryColumn q) i 0

lemma queryComplement_apply {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ)
    (q : Fin n → ℝ) (i j : Fin n) : queryComplement P q i j = P i j - q i*q j := by
  simp [queryComplement, queryColumn, Matrix.mul_apply]

@[fun_prop] lemma measurable_queryResidual {n : ℕ} :
    Measurable (fun x : (Matrix (Fin n) (Fin n) ℝ × (Fin n → ℝ)) ×
      ((Fin n × Fin n) → ℝ) => queryResidual x.1.1 x.1.2 x.2) := by
  apply Measurable.of_eval
  intro p
  simp only [queryResidual, Matrix.mul_apply, queryComplement_apply, goe]
  fun_prop

@[fun_prop] lemma measurable_queryAnswer {n : ℕ} :
    Measurable (fun x : (Matrix (Fin n) (Fin n) ℝ × (Fin n → ℝ)) ×
      ((Fin n × Fin n) → ℝ) => queryAnswer x.1.1 x.1.2 x.2) := by
  apply Measurable.of_eval
  intro i
  simp only [queryAnswer, Matrix.mul_apply, queryColumn, goe]
  fun_prop

@[fun_prop] lemma measurable_queryInnovation {n : ℕ} :
    Measurable (fun x : (Matrix (Fin n) (Fin n) ℝ × (Fin n → ℝ)) ×
      ((Fin n ⊕ Unit) → ℝ) => queryInnovation x.1.1 x.1.2 x.2) := by
  apply Measurable.of_eval
  intro i
  simp only [queryInnovation, queryComplement_apply]
  fun_prop

lemma measurable_queryResidual_comp {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Ω → Matrix (Fin n) (Fin n) ℝ) (q : Ω → Fin n → ℝ)
    (g : Ω → (Fin n × Fin n) → ℝ)
    (hP : Measurable P) (hq : Measurable q) (hg : Measurable g) :
    Measurable (fun ω => queryResidual (P ω) (q ω) (g ω)) := by
  apply Measurable.of_eval
  intro p
  simp only [queryResidual, Matrix.mul_apply, queryComplement_apply, goe]
  have hP' : Measurable (fun ω => fun i j => P ω i j) := hP
  fun_prop

lemma measurable_queryAnswer_comp {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Ω → Matrix (Fin n) (Fin n) ℝ) (q : Ω → Fin n → ℝ)
    (g : Ω → (Fin n × Fin n) → ℝ)
    (hP : Measurable P) (hq : Measurable q) (hg : Measurable g) :
    Measurable (fun ω => queryAnswer (P ω) (q ω) (g ω)) := by
  apply Measurable.of_eval
  intro i
  simp only [queryAnswer, Matrix.mul_apply, queryColumn, goe]
  have hP' : Measurable (fun ω => fun i j => P ω i j) := hP
  fun_prop

lemma measurable_queryInnovation_comp {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Ω → Matrix (Fin n) (Fin n) ℝ) (q : Ω → Fin n → ℝ)
    (g : Ω → (Fin n ⊕ Unit) → ℝ)
    (hP : Measurable P) (hq : Measurable q) (hg : Measurable g) :
    Measurable (fun ω => queryInnovation (P ω) (q ω) (g ω)) := by
  apply Measurable.of_eval
  intro i
  simp only [queryInnovation, queryComplement_apply]
  have hP' : Measurable (fun ω => fun i j => P ω i j) := hP
  fun_prop

lemma queryResidual_measurable {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ)
    (q : Fin n → ℝ) : Measurable (queryResidual P q) := by
  exact measurable_queryResidual_comp (fun _ => P) (fun _ => q) id
    measurable_const measurable_const measurable_id

lemma queryAnswer_measurable {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ)
    (q : Fin n → ℝ) : Measurable (queryAnswer P q) := by
  exact measurable_queryAnswer_comp (fun _ => P) (fun _ => q) id
    measurable_const measurable_const measurable_id

lemma queryInnovation_measurable {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ)
    (q : Fin n → ℝ) : Measurable (queryInnovation P q) := by
  exact measurable_queryInnovation_comp (fun _ => P) (fun _ => q) id
    measurable_const measurable_const measurable_id

lemma query_joint_law {n : ℕ} (hn : 0 < n)
    (P : Matrix (Fin n) (Fin n) ℝ) (hP : Pᵀ = P) (hPP : P*P = P)
    (q : Fin n → ℝ) (hq : ∑ i, q i ^ 2 = 1) (hPq : P * queryColumn q = queryColumn q) :
    (standardArrayLaw (Fin n × Fin n)).map (fun g =>
      (queryResidual P q g, queryAnswer P q g)) =
    ((standardArrayLaw (Fin n × Fin n)).prod (standardArrayLaw (Fin n ⊕ Unit))).map
      (fun z => (queryResidual P q z.1, queryInnovation P q z.2)) := by
  rw [(fresh_residual_independent hn P hP q hq hPq).map_prod_eq_prod_map_map
    (queryResidual_measurable P q).aemeasurable (queryAnswer_measurable P q).aemeasurable]
  rw [show (standardArrayLaw (Fin n × Fin n)).map (queryAnswer P q) =
      (standardArrayLaw (Fin n ⊕ Unit)).map (queryInnovation P q) from
    query_innovation_law hn P hP hPP q hq hPq]
  exact Measure.map_prod_map _ _ (queryResidual_measurable P q)
    (queryInnovation_measurable P q)

theorem adaptive_query_joint_law {n : ℕ} (hn : 0 < n) {H : Type*}
    [MeasurableSpace H] (ρ : Measure H)
    (P : H → Matrix (Fin n) (Fin n) ℝ) (q : H → Fin n → ℝ)
    (hPm : Measurable P) (hqm : Measurable q)
    (hP : ∀ h, (P h)ᵀ = P h) (hPP : ∀ h, P h * P h = P h)
    (hq : ∀ h, ∑ i, q h i ^ 2 = 1)
    (hPq : ∀ h, P h * queryColumn (q h) = queryColumn (q h)) :
    (ρ.prod (standardArrayLaw (Fin n × Fin n))).map (fun z =>
      (z.1, queryResidual (P z.1) (q z.1) z.2, queryAnswer (P z.1) (q z.1) z.2)) =
    (ρ.prod ((standardArrayLaw (Fin n × Fin n)).prod
      (standardArrayLaw (Fin n ⊕ Unit)))).map (fun z =>
        (z.1, queryResidual (P z.1) (q z.1) z.2.1,
          queryInnovation (P z.1) (q z.1) z.2.2)) := by
  have hmL : Measurable (fun z : H × ((Fin n × Fin n) → ℝ) =>
      (z.1, queryResidual (P z.1) (q z.1) z.2, queryAnswer (P z.1) (q z.1) z.2)) :=
    measurable_fst.prodMk ((measurable_queryResidual_comp _ _ _
      (hPm.comp measurable_fst) (hqm.comp measurable_fst) measurable_snd).prodMk
      (measurable_queryAnswer_comp _ _ _ (hPm.comp measurable_fst)
        (hqm.comp measurable_fst) measurable_snd))
  have hmR : Measurable (fun z : H × (((Fin n × Fin n) → ℝ) × ((Fin n ⊕ Unit) → ℝ)) =>
      (z.1, queryResidual (P z.1) (q z.1) z.2.1,
        queryInnovation (P z.1) (q z.1) z.2.2)) :=
    measurable_fst.prodMk ((measurable_queryResidual_comp _ _ _
      (hPm.comp measurable_fst) (hqm.comp measurable_fst) measurable_snd.fst).prodMk
      (measurable_queryInnovation_comp _ _ _ (hPm.comp measurable_fst)
        (hqm.comp measurable_fst) measurable_snd.snd))
  apply map_prod_section_congr _ _ _ _ _ hmL hmR
  intro h
  have hh := congrArg (Measure.map (Prod.mk h))
    (query_joint_law hn (P h) (hP h) (hPP h) (q h) (hq h) (hPq h))
  have hm1 := (queryResidual_measurable (P h) (q h)).prodMk
    (queryAnswer_measurable (P h) (q h))
  have hm2 : Measurable (fun z : (((Fin n × Fin n) → ℝ) × ((Fin n ⊕ Unit) → ℝ)) =>
      (queryResidual (P h) (q h) z.1, queryInnovation (P h) (q h) z.2)) :=
    ((queryResidual_measurable (P h) (q h)).comp measurable_fst).prodMk
      ((queryInnovation_measurable (P h) (q h)).comp measurable_snd)
  rw [Measure.map_map measurable_prodMk_left hm1,
    Measure.map_map measurable_prodMk_left hm2] at hh
  exact hh

lemma map_triple_exchange {H A B C : Type*}
    [MeasurableSpace H] [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
    (ρ : Measure H) (μ : Measure A) (ν : Measure B)
    [SFinite ρ] [SFinite μ] [SFinite ν]
    (f : H × (A × B) → C) (hf : Measurable f) :
    (ρ.prod (μ.prod ν)).map f =
      ((ρ.prod ν).prod μ).map (fun z => f (z.1.1, z.2, z.1.2)) := by
  calc
    _ = (ρ.prod (ν.prod μ)).map (fun z => f (z.1, z.2.2, z.2.1)) := by
      apply map_prod_section_congr ρ (μ.prod ν) (ν.prod μ) _ _ hf
        (hf.comp (measurable_fst.prodMk
          (measurable_snd.snd.prodMk measurable_snd.fst)))
      intro h
      have hm : Measurable (fun z : B × A => f (h,z.2,z.1)) :=
        hf.comp (measurable_const.prodMk (measurable_snd.prodMk measurable_fst))
      have hh := congrArg (Measure.map (fun z : B × A => f (h,z.2,z.1)))
        (Measure.prod_swap (μ := μ) (ν := ν))
      simpa only [Measure.map_map hm measurable_swap, Function.comp_def,
        Prod.fst_swap, Prod.snd_swap] using hh
    _ = _ := by
      rw [← Measure.prodAssoc_prod]
      exact Measure.map_map
        (show Measurable (fun z : H × (B × A) => f (z.1,z.2.2,z.2.1)) from
          hf.comp (measurable_fst.prodMk (measurable_snd.snd.prodMk measurable_snd.fst)))
        MeasurableEquiv.prodAssoc.measurable

noncomputable def answerHistoryLaw {n : ℕ} {H : Type*} [MeasurableSpace H]
    (ρ : Measure H) (P : H → Matrix (Fin n) (Fin n) ℝ) (q : H → Fin n → ℝ) :
    Measure (H × (Fin n → ℝ)) :=
  (ρ.prod (standardArrayLaw (Fin n ⊕ Unit))).map
    (fun z => (z.1, queryInnovation (P z.1) (q z.1) z.2))

theorem adaptive_query_regeneration {n : ℕ} (hn : 0 < n) {H : Type*}
    [MeasurableSpace H] (ρ : Measure H) [SFinite ρ]
    (P : H → Matrix (Fin n) (Fin n) ℝ) (q : H → Fin n → ℝ)
    (hPm : Measurable P) (hqm : Measurable q)
    (hP : ∀ h, (P h)ᵀ = P h) (hPP : ∀ h, P h * P h = P h)
    (hq : ∀ h, ∑ i, q h i ^ 2 = 1)
    (hPq : ∀ h, P h * queryColumn (q h) = queryColumn (q h)) :
    (ρ.prod (standardArrayLaw (Fin n × Fin n))).map (fun z =>
      ((z.1, queryAnswer (P z.1) (q z.1) z.2),
        queryResidual (P z.1) (q z.1) z.2)) =
    ((answerHistoryLaw ρ P q).prod (standardArrayLaw (Fin n × Fin n))).map
      (fun z => (z.1, queryResidual (P z.1.1) (q z.1.1) z.2)) := by
  let μ := standardArrayLaw (Fin n × Fin n)
  let ν := standardArrayLaw (Fin n ⊕ Unit)
  let hist : H × ((Fin n ⊕ Unit) → ℝ) → H × (Fin n → ℝ) :=
    fun z => (z.1, queryInnovation (P z.1) (q z.1) z.2)
  have hhist : Measurable hist := measurable_fst.prodMk
    (measurable_queryInnovation_comp _ _ _ (hPm.comp measurable_fst)
      (hqm.comp measurable_fst) measurable_snd)
  let out : (H × (Fin n → ℝ)) × ((Fin n × Fin n) → ℝ) →
      (H × (Fin n → ℝ)) × ((Fin n × Fin n) → ℝ) :=
    fun z => (z.1, queryResidual (P z.1.1) (q z.1.1) z.2)
  have hout : Measurable out := measurable_fst.prodMk
    (measurable_queryResidual_comp _ _ _ (hPm.comp measurable_fst.fst)
      (hqm.comp measurable_fst.fst) measurable_snd)
  have hleft : Measurable (fun z : H × ((Fin n × Fin n) → ℝ) =>
      (z.1, queryResidual (P z.1) (q z.1) z.2, queryAnswer (P z.1) (q z.1) z.2)) :=
    measurable_fst.prodMk ((measurable_queryResidual_comp _ _ _
      (hPm.comp measurable_fst) (hqm.comp measurable_fst) measurable_snd).prodMk
      (measurable_queryAnswer_comp _ _ _ (hPm.comp measurable_fst)
        (hqm.comp measurable_fst) measurable_snd))
  have hright : Measurable (fun z : H × (((Fin n × Fin n) → ℝ) × ((Fin n ⊕ Unit) → ℝ)) =>
      (z.1, queryResidual (P z.1) (q z.1) z.2.1,
        queryInnovation (P z.1) (q z.1) z.2.2)) :=
    measurable_fst.prodMk ((measurable_queryResidual_comp _ _ _
      (hPm.comp measurable_fst) (hqm.comp measurable_fst) measurable_snd.fst).prodMk
      (measurable_queryInnovation_comp _ _ _ (hPm.comp measurable_fst)
        (hqm.comp measurable_fst) measurable_snd.snd))
  have hreorder : Measurable (fun z : H × (((Fin n × Fin n) → ℝ) × (Fin n → ℝ)) =>
      ((z.1,z.2.2),z.2.1)) := (measurable_fst.prodMk measurable_snd.snd).prodMk
        measurable_snd.fst
  have hj := congrArg (Measure.map (fun z : H × (((Fin n × Fin n) → ℝ) × (Fin n → ℝ)) =>
      ((z.1,z.2.2),z.2.1)))
    (adaptive_query_joint_law hn ρ P q hPm hqm hP hPP hq hPq)
  rw [Measure.map_map hreorder hleft, Measure.map_map hreorder hright] at hj
  calc
    _ = (ρ.prod (μ.prod ν)).map (fun z => out (hist (z.1,z.2.2),z.2.1)) := hj
    _ = ((ρ.prod ν).prod μ).map (fun z => out (hist z.1,z.2)) :=
      map_triple_exchange ρ μ ν _ (hout.comp
        ((hhist.comp (measurable_fst.prodMk measurable_snd.snd)).prodMk measurable_snd.fst))
    _ = _ := by
      change _ = (((ρ.prod ν).map hist).prod μ).map out
      conv_rhs => rw [← Measure.map_id (μ := μ)]
      rw [Measure.map_prod_map _ _ hhist measurable_id, Measure.map_map hout
        (hhist.prodMap measurable_id)]
      rfl

end SKGapCutoff.Regression

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal

end

end OAI
