import OAI.Combinatorics.SparsestCut.FiniteNets

namespace OAI

universe u1 u2 u3 u4 u5

open scoped BigOperators Topology NNReal RealInnerProductSpace InnerProductSpace Matrix ContDiff ENNReal
open MeasureTheory ProbabilityTheory Set Filter Matrix

noncomputable section

namespace UniformSparsestCut.Directions
open GaussianTools FiniteNets MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators NNReal Topology

section ProductMeasures
variable {E : Type u1} [MeasurableSpace E] {μ : Measure E} [IsProbabilityMeasure μ]

lemma integral_eval {n : ℕ} {f : E → ℝ} (hf : Measurable f) (i : Fin n) :
    (∫ x : Fin n → E, f (x i) ∂Measure.pi (fun _ => μ)) = ∫ x, f x ∂μ := by
  have hp := measurePreserving_eval (fun _ : Fin n => μ) i
  have hh := integral_map hp.aemeasurable (hf.aestronglyMeasurable :
    AEStronglyMeasurable f ((Measure.pi (fun _ : Fin n => μ)).map (Function.eval i)))
  rw [hp.map_eq] at hh
  exact hh.symm

lemma real_measure_eval {n : ℕ} {A : Set E} (hA : MeasurableSet A) (i : Fin n) :
    (Measure.pi (fun _ : Fin n => μ)).real {x | x i ∈ A} = μ.real A := by
  have hp := (measurePreserving_eval (fun _ : Fin n => μ) i).measure_preimage hA.nullMeasurableSet
  exact congrArg ENNReal.toReal hp

lemma iid_bounded_concentration {n : ℕ} (hn : 0 < n) {f : E → ℝ}
    (hf : Measurable f) {B : ℝ} (hB : 0 < B) (hfB : ∀ x, |f x| ≤ B)
    {u : ℝ} (hu : 0 ≤ u) :
    (Measure.pi (fun _ : Fin n => μ)).real
      {x | u < |(∑ i, f (x i)) / (n : ℝ) - ∫ z, f z ∂μ|} ≤
      2 * Real.exp (-(n : ℝ)*u^2/(2*B^2)) := by
  have h := bounded_concentration hn (fun i (x : Fin n → E) => f (x i))
    (fun i => (hf.comp (measurable_pi_apply i)).aemeasurable)
    (iIndepFun_pi (μ := fun _ : Fin n => μ) (fun _ => hf.aemeasurable)) hB
    (fun i => ae_of_all _ (fun x => hfB (x i))) hu
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have heq (x : Fin n → E) :
      (∑ i, (f (x i) - ∫ z : Fin n → E, f (z i) ∂Measure.pi (fun _ => μ))) / (n : ℝ) =
        (∑ i, f (x i)) / (n : ℝ) - ∫ z, f z ∂μ := by
    simp_rw [integral_eval hf]
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  simpa only [heq] using h

lemma real_measure_exists_le {n : ℕ} (A : Fin n → Set E) (hA : ∀ i, MeasurableSet (A i))
    {p : ℝ} (hp : ∀ i, μ.real (A i) ≤ p) :
    (Measure.pi (fun _ : Fin n => μ)).real {x | ∃ i, x i ∈ A i} ≤ (n : ℝ)*p := by
  calc
    _ = (Measure.pi (fun _ : Fin n => μ)).real (⋃ i : Fin n, {x | x i ∈ A i}) := by
      congr 1; ext x; simp
    _ ≤ ∑ i : Fin n, (Measure.pi (fun _ : Fin n => μ)).real {x | x i ∈ A i} :=
      measureReal_iUnion_fintype_le _
    _ = ∑ i : Fin n, μ.real (A i) := by simp_rw [real_measure_eval (hA _)]
    _ ≤ ∑ _ : Fin n, p := Finset.sum_le_sum (fun i _ => hp i)
    _ = _ := by simp

noncomputable def badCount {S : ℕ} (A : Set E) (x : Fin S → E) : ℕ := by
  classical
  exact (Finset.univ.filter (fun s => x s ∈ A)).card

lemma bad_chart_fraction {S : ℕ} (hS : 0 < S) {A : Set E} (hA : MeasurableSet A)
    (hp : μ.real A ≤ 1/4) :
    (Measure.pi (fun _ : Fin S => μ)).real
      {x | (S : ℝ)/2 < (badCount A x : ℝ)} ≤
      2 * Real.exp (-(S : ℝ)/32) := by
  classical
  let f : E → ℝ := A.indicator (fun _ => 1)
  have hf : Measurable f := measurable_const.indicator hA
  have hbound (x : E) : |f x| ≤ 1 := by
    by_cases hx : x ∈ A <;> simp [f, hx]
  have hmean : (∫ x, f x ∂μ) = μ.real A := integral_indicator_one hA
  have h := iid_bounded_concentration (μ := μ) hS hf (by norm_num : (0 : ℝ) < 1) hbound
    (u := 1/4) (by norm_num)
  have hcount (x : Fin S → E) : (∑ s : Fin S, f (x s)) =
      (badCount A x : ℝ) := by
    dsimp [badCount]
    simp only [f, Set.indicator]
    rw [← Finset.sum_filter]
    simp
  have hspos : (0 : ℝ) < S := by exact_mod_cast hS
  have hsub : {x : Fin S → E | (S : ℝ)/2 < (badCount A x : ℝ)} ⊆
      {x | (1/4 : ℝ) < |(∑ s, f (x s))/(S : ℝ) - ∫ z, f z ∂μ|} := by
    intro x hx
    change (S : ℝ)/2 < (badCount A x : ℝ) at hx
    change (1/4 : ℝ) < |(∑ s, f (x s))/(S : ℝ) - ∫ z, f z ∂μ|
    rw [hcount, hmean]
    apply (lt_abs.mpr (Or.inl ?_))
    have hh : (1/2 : ℝ) < (badCount A x : ℝ)/(S : ℝ) :=
      (lt_div_iff₀ hspos).mpr (by linarith)
    linarith
  calc
    _ ≤ _ := measureReal_mono hsub
    _ ≤ 2 * Real.exp (-(S : ℝ) * (1/4)^2 / (2*1^2)) := h
    _ = _ := by congr 2; ring

lemma exists_outside_of_real_lt_one {Ω : Type u2} [MeasurableSpace Ω]
    {ν : Measure Ω} [IsProbabilityMeasure ν] {A : Set Ω} (hA : (ν).real A < 1) :
    ∃ x, x ∉ A := by
  by_contra h
  push Not at h
  have heq : A = Set.univ := Set.eq_univ_of_forall h
  simp [heq, measureReal_def] at hA

lemma exists_outside_with_ae {Ω : Type u3} [MeasurableSpace Ω]
    {ν : Measure Ω} [IsProbabilityMeasure ν] {A : Set Ω} (hA : (ν).real A < 1)
    {P : Ω → Prop} (hP : ∀ᵐ x ∂ν, P x) : ∃ x, x ∉ A ∧ P x := by
  have hnull : (ν).real {x | ¬ P x} = 0 := by
    rw [measureReal_def, ae_iff.mp hP, ENNReal.toReal_zero]
  have hlt : (ν).real (A ∪ {x | ¬ P x}) < 1 :=
    ((measureReal_union_le _ _).trans_eq (by rw [hnull, add_zero])).trans_lt hA
  obtain ⟨x,hx⟩ := exists_outside_of_real_lt_one hlt
  exact ⟨x, fun ha => hx (Or.inl ha), by_contra (fun hn => hx (Or.inr hn))⟩

end ProductMeasures

lemma finite_union_bound {Ω : Type u4} {I : Type u5} [MeasurableSpace Ω] [Fintype I]
    {ν : Measure Ω} [IsProbabilityMeasure ν] (A : I → Set Ω) {p : ℝ}
    (hA : ∀ i, (ν).real (A i) ≤ p) :
    (ν).real {x | ∃ i, x ∈ A i} ≤ (Fintype.card I : ℝ)*p := by
  calc
    _ = (ν).real (⋃ i, A i) := by congr 1; ext; simp
    _ ≤ ∑ i, (ν).real (A i) := measureReal_iUnion_fintype_le _
    _ ≤ ∑ _ : I, p := Finset.sum_le_sum (fun i _ => hA i)
    _ = _ := by simp

section GaussianSelection
variable {m N S : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "μ" => stdGaussian E
local notation "ν" => Measure.pi (fun _ : Fin N => μ)
local notation "π" => Measure.pi (fun _ : Fin S => ν)

noncomputable def fourierSummand (v w : E) : E → ℝ :=
  truncate m (fun g => inner ℝ g v * Real.sin (inner ℝ g w))
noncomputable def covarianceSummand (v : E) : E → ℝ :=
  truncate m (fun g => (inner ℝ v g)^2)

def normBad : Set (Fin N → E) :=
  {x | ∃ i, ‖x i‖^2 < (m : ℝ)/4 ∨ 4*(m : ℝ) < ‖x i‖^2}
noncomputable def fourierBad (u : ℝ) (v w : E) : Set (Fin N → E) :=
  {x | u < |(∑ i, fourierSummand v w (x i))/(N : ℝ) - ∫ g, fourierSummand v w g ∂μ|}
noncomputable def covarianceBad (v : E) : Set (Fin N → E) :=
  {x | (1/8 : ℝ) < |(∑ i, covarianceSummand v (x i))/(N : ℝ) - ∫ g, covarianceSummand v g ∂μ|}
def projectionBad (q : ℝ) (v : E) : Set (Fin N → E) :=
  {x | ∃ i, q < |inner ℝ v (x i)|}

lemma fourierSummand_measurable (v w : E) : Measurable (fourierSummand v w) :=
  (by fun_prop : Measurable (fun g : E => inner ℝ g v * Real.sin (inner ℝ g w))).indicator
    measurable_truncation_set
lemma covarianceSummand_measurable (v : E) : Measurable (covarianceSummand v) :=
  (by fun_prop : Measurable (fun g : E => (inner ℝ v g)^2)).indicator measurable_truncation_set
lemma normBad_measurable : MeasurableSet (normBad (m := m) (N := N)) := by
  unfold normBad; measurability
lemma fourierBad_measurable (u : ℝ) (v w : E) : MeasurableSet (fourierBad (N := N) u v w) := by
  unfold fourierBad
  have hf (i : Fin N) : Measurable (fun x : Fin N → E => fourierSummand v w (x i)) :=
    (fourierSummand_measurable v w).comp (measurable_pi_apply i)
  measurability
lemma covarianceBad_measurable (v : E) : MeasurableSet (covarianceBad (N := N) v) := by
  unfold covarianceBad
  have hf (i : Fin N) : Measurable (fun x : Fin N → E => covarianceSummand v (x i)) :=
    (covarianceSummand_measurable v).comp (measurable_pi_apply i)
  measurability
lemma projectionBad_measurable (q : ℝ) (v : E) : MeasurableSet (projectionBad (N := N) q v) := by
  unfold projectionBad; measurability

lemma normBad_bound : (ν).real (normBad (m := m) (N := N)) ≤
    (N : ℝ)* (2*Real.exp (-(m : ℝ)/8)) :=
  real_measure_exists_le (fun _ => {g : E | ‖g‖^2 < (m : ℝ)/4 ∨ 4*(m : ℝ) < ‖g‖^2})
    (fun _ => by measurability) (fun _ => by
      have h := (measureReal_union_le
        {g : E | ‖g‖^2 < (m : ℝ)/4} {g : E | 4*(m : ℝ) < ‖g‖^2}).trans
        (add_le_add (gaussian_norm_lower (n := m)) (gaussian_norm_upper (n := m)))
      have he : Real.exp (-(m : ℝ)/2) ≤ Real.exp (-(m : ℝ)/8) :=
        Real.exp_le_exp.mpr (by have := Nat.cast_nonneg (α := ℝ) m; linarith)
      exact h.trans (by linarith))

lemma fourierBad_bound (hm : 0 < m) (hN : 0 < N) {u : ℝ} (hu : 0 ≤ u)
    (v w : E) (hv : ‖v‖ = 1) :
    (ν).real (fourierBad (N := N) u v w) ≤
      2*Real.exp (-(N : ℝ)*u^2/(2*(2*Real.sqrt m)^2)) := by
  exact iid_bounded_concentration hN (fourierSummand_measurable v w)
    (by positivity) (truncate_fourier_bound v w hv) hu
lemma covarianceBad_bound (hm : 0 < m) (hN : 0 < N) (v : E) (hv : ‖v‖ = 1) :
    (ν).real (covarianceBad (N := N) v) ≤
      2*Real.exp (-(N : ℝ)*(1/8)^2/(2*(4*(m : ℝ))^2)) := by
  exact iid_bounded_concentration hN (covarianceSummand_measurable v)
    (by positivity) (truncate_covariance_bound v hv) (by norm_num)
lemma projectionBad_bound {q : ℝ} (hq : 0 ≤ q) (v : E) (hv : ‖v‖ = 1) :
    (ν).real (projectionBad (N := N) q v) ≤ (N : ℝ)*(2*Real.exp (-q^2/2)) :=
  real_measure_exists_le (fun _ => {g : E | q < |inner ℝ v g|})
    (fun _ => by measurability) (fun _ => gaussian_inner_tail v hv hq)

noncomputable def chartBad (V W : Finset E) (u : ℝ) : Set (Fin N → E) :=
  normBad ∪ {x | ∃ z : V × W, x ∈ fourierBad u z.1 z.2} ∪
    {x | ∃ v : V, x ∈ covarianceBad v}

lemma chartBad_measurable (V W : Finset E) (u : ℝ) :
    MeasurableSet (chartBad (N := N) V W u) := by
  classical
  have hFm : MeasurableSet {x : Fin N → E | ∃ z : V × W, x ∈ fourierBad u z.1 z.2} := by
    rw [show {x : Fin N → E | ∃ z : V × W, x ∈ fourierBad u z.1 z.2} =
      ⋃ z : V × W, fourierBad (N := N) u z.1 z.2 by ext x; simp]
    exact MeasurableSet.iUnion (fun z : V × W => fourierBad_measurable (m := m) (N := N) u z.1 z.2)
  have hCm : MeasurableSet {x : Fin N → E | ∃ v : V, x ∈ covarianceBad v} := by
    rw [show {x : Fin N → E | ∃ v : V, x ∈ covarianceBad v} =
      ⋃ v : V, covarianceBad (N := N) v by ext x; simp]
    exact MeasurableSet.iUnion (fun v : V => covarianceBad_measurable (m := m) (N := N) v)
  exact (normBad_measurable.union hFm).union hCm

lemma chartBad_bound (hm : 0 < m) (hN : 0 < N) (V W : Finset E)
    (hV : ∀ v ∈ V, ‖v‖ = 1) {u : ℝ} (hu : 0 ≤ u) :
    (ν).real (chartBad (N := N) V W u) ≤ (N : ℝ)*(2*Real.exp (-(m : ℝ)/8)) +
        (V.card : ℝ)*(W.card : ℝ)*(2*Real.exp (-(N : ℝ)*u^2/(2*(2*Real.sqrt m)^2))) +
        (V.card : ℝ)*(2*Real.exp (-(N : ℝ)*(1/8)^2/(2*(4*(m : ℝ))^2))) := by
  classical
  have h1 := finite_union_bound («ν» := ν) (fun z : V × W => fourierBad u z.1 z.2)
    (fun z => fourierBad_bound hm hN hu z.1 z.2 (hV z.1 z.1.property))
  have h2 := finite_union_bound («ν» := ν) (fun v : V => covarianceBad v)
    (fun v => covarianceBad_bound hm hN v (hV v v.property))
  simp only [Fintype.card_prod, Fintype.card_coe, Nat.cast_mul] at h1 h2
  exact (measureReal_union_le _ _).trans
    (add_le_add ((measureReal_union_le _ _).trans (add_le_add normBad_bound h1)) h2)

lemma projection_chart_fraction (hS : 0 < S) (v : E) (hv : ‖v‖ = 1)
    {q : ℝ} (hq : 0 ≤ q) (hqprob : (N : ℝ)*(2*Real.exp (-q^2/2)) ≤ 1/4) :
    (π).real {g | (S : ℝ)/2 < (badCount (projectionBad q v) g : ℝ)} ≤
      2*Real.exp (-(S : ℝ)/32) := by
  have hmeas : MeasurableSet (projectionBad (N := N) q v) := projectionBad_measurable q v
  have hbound : (ν).real (projectionBad (N := N) q v) ≤ 1/4 :=
    (projectionBad_bound hq v hv).trans hqprob
  exact bad_chart_fraction hS hmeas hbound

lemma goodBad_bound (hS : 0 < S) (V : Finset E) (hV : ∀ v ∈ V, ‖v‖ = 1)
    {q : ℝ} (hq : 0 ≤ q) (hqprob : (N : ℝ)*(2*Real.exp (-q^2/2)) ≤ 1/4) :
    (π).real {g | ∃ v : V, (S : ℝ)/2 < (badCount (projectionBad q v) g : ℝ)} ≤
      (V.card : ℝ)*(2*Real.exp (-(S : ℝ)/32)) := by
  classical
  have h := finite_union_bound («ν» := π)
    (fun v : V => {g | (S : ℝ)/2 < (badCount (projectionBad q v) g : ℝ)})
    (fun v => projection_chart_fraction hS (v : E) (hV v v.property) hq hqprob)
  simpa only [Fintype.card_coe, Set.mem_ofPred_eq] using h

theorem select_on_nets (hm : 0 < m) (hN : 0 < N) (hS : 0 < S)
    (V W : Finset E) (hV : ∀ v ∈ V, ‖v‖ = 1)
    {u q : ℝ} (hu : 0 ≤ u) (hq : 0 ≤ q)
    (hqprob : (N : ℝ)*(2*Real.exp (-q^2/2)) ≤ 1/4)
    {P : (Fin S → Fin N → E) → Prop} (hP : ∀ᵐ g ∂π, P g)
    (hprob : (S : ℝ) * ((N : ℝ)*(2*Real.exp (-(m : ℝ)/8)) +
        (V.card : ℝ)*(W.card : ℝ)*(2*Real.exp (-(N : ℝ)*u^2/(2*(2*Real.sqrt m)^2))) +
        (V.card : ℝ)*(2*Real.exp (-(N : ℝ)*(1/8)^2/(2*(4*(m : ℝ))^2)))) +
        (V.card : ℝ)*(2*Real.exp (-(S : ℝ)/32)) < 1) :
    ∃ g : Fin S → Fin N → E, P g ∧
      (∀ s, g s ∉ normBad) ∧
      (∀ s, ∀ v ∈ V, ∀ w ∈ W, g s ∉ fourierBad u v w) ∧
      (∀ s, ∀ v ∈ V, g s ∉ covarianceBad v) ∧
      (∀ v ∈ V, (badCount (projectionBad q v) g : ℝ) ≤ (S : ℝ)/2) := by
  classical
  let A := chartBad (N := N) V W u
  let B : Set (Fin S → Fin N → E) := {g | ∃ s, g s ∈ A}
  let C : Set (Fin S → Fin N → E) :=
    {g | ∃ v : V, (S : ℝ)/2 < (badCount (projectionBad q v) g : ℝ)}
  have hBbound := real_measure_exists_le (fun _ : Fin S => A)
    (fun _ => chartBad_measurable V W u) (fun _ => chartBad_bound hm hN V W hV hu)
  have hCbound := goodBad_bound hS V hV hq hqprob
  have hBC : (π).real (B ∪ C) < 1 :=
    ((measureReal_union_le B C).trans (add_le_add hBbound hCbound)).trans_lt hprob
  obtain ⟨g, hg, hgP⟩ := exists_outside_with_ae hBC hP
  have hgB : ∀ s, g s ∉ A := by
    intro s hs; exact hg (Or.inl ⟨s, hs⟩)
  refine ⟨g, hgP, ?_, ?_, ?_, ?_⟩
  · intro s hs; exact hgB s (Or.inl (Or.inl hs))
  · intro s v hv w hw hs; exact hgB s (Or.inl (Or.inr ⟨(⟨v,hv⟩,⟨w,hw⟩), hs⟩))
  · intro s v hv hs; exact hgB s (Or.inr ⟨⟨v,hv⟩, hs⟩)
  · intro v hv; by_contra h
    exact hg (Or.inr ⟨⟨v,hv⟩, lt_of_not_ge h⟩)

end GaussianSelection

end UniformSparsestCut.Directions

end

end OAI
