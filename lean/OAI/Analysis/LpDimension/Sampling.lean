import OAI.Analysis.LpDimension.Retractions

namespace OAI

noncomputable section
open MeasureTheory Filter Matrix NormedSpace Metric Module Set ProbabilityTheory
open scoped BigOperators Topology Matrix Matrix.Norms.Operator ENNReal NNReal
universe u uE uH uJ uV uΩ

namespace SubpolynomialLp

lemma bounded_sample_exists {E : Type uE} {Ω : Type uΩ} [Fintype E] [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → E → ℝ)
    (hXm : ∀ e, Measurable (fun ω => X ω e)) (M : ℝ) (hM : 0 ≤ M)
    (hX : ∀ ω e, X ω e ∈ Set.Icc 0 M)
    (d : ℕ) (hd : 0 < d) (ε : ℝ) (hε : 0 < ε)
    (hprob : (2*Fintype.card E:ℝ)*Real.exp (-((d:ℝ)*ε)^2/(2*d*(M/2)^2)) < 1) :
    ∃ ω : Fin d → Ω, ∀ e,
      |(∑ a, X (ω a) e)/(d:ℝ) - ∫ t, X t e ∂μ| < ε := by
  classical
  let ν : Measure (Fin d → Ω) := Measure.pi (fun _ => μ)
  let m : E → ℝ := fun e => ∫ t, X t e ∂μ
  let c : ℝ≥0 := (‖M‖₊/2)^2
  let Z : E → (Fin d → Ω) → ℝ := fun e ω => ∑ a, (X (ω a) e-m e)
  have hc : (c:ℝ) = (M/2)^2 := by simp [c, Real.norm_eq_abs, abs_of_nonneg hM]
  have hsg (e : E) : HasSubgaussianMGF (Z e) (d*c) ν := by
    have hs := hasSubgaussianMGF_of_mem_Icc (hXm e).aemeasurable (ae_of_all μ (fun ω => hX ω e))
    have hs' : HasSubgaussianMGF (fun ω => X ω e-m e) c μ := by
      simpa only [sub_zero] using hs
    have hi : iIndepFun (fun a : Fin d => fun ω : Fin d → Ω => X (ω a) e-m e) ν :=
      iIndepFun_pi (fun _ => ((hXm e).sub_const (m e)).aemeasurable)
    have hh := HasSubgaussianMGF.sum_of_iIndepFun (c := fun _ : Fin d => c) (s := Finset.univ) hi (fun a _ => by
      have ha := measurePreserving_eval (fun _ : Fin d => μ) a
      have hh : HasSubgaussianMGF (fun ω => X ω e-m e) c (Measure.map (Function.eval a) ν) := by
        rw [ha.map_eq]
        exact hs'
      exact hh.of_map ha.aemeasurable)
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using hh
  let t : ℝ := d*ε
  have ht : 0 ≤ t := by dsimp [t]; positivity
  let q := Real.exp (-((d:ℝ)*ε)^2/(2*d*(M/2)^2))
  have htail (e : E) : ν.real {ω | t ≤ |Z e ω|} ≤ 2*q := by
    have hp := (hsg e).measure_ge_le ht
    have hn := (hsg e).neg.measure_ge_le ht
    have he : {ω | t ≤ |Z e ω|} = {ω | t ≤ Z e ω} ∪ {ω | t ≤ -Z e ω} := by
      ext ω
      simp only [mem_ofPred_eq, mem_union]
      rw [le_abs]
    rw [he]
    apply (measureReal_union_le _ _).trans
    have hq : Real.exp (-t^2/(2*((d*c:ℝ≥0):ℝ))) = q := by
      simp only [NNReal.coe_mul, NNReal.coe_natCast, hc, q, t, mul_assoc]
    change ν.real {ω | t ≤ Z e ω} + ν.real {ω | t ≤ -Z e ω} ≤ _
    rw [hq] at hp hn
    change ν.real {ω | t ≤ -Z e ω} ≤ q at hn
    linarith
  have hbad : ν.real (⋃ e, {ω | t ≤ |Z e ω|}) < 1 := by
    apply (measureReal_iUnion_fintype_le _).trans_lt
    calc
      ∑ e, ν.real {ω | t ≤ |Z e ω|} ≤ ∑ _ : E, 2*q := Finset.sum_le_sum (fun e _ => htail e)
      _ = (2*Fintype.card E:ℝ)*q := by simp; ring
      _ < 1 := hprob
  have hnotuniv : (⋃ e, {ω | t ≤ |Z e ω|}) ≠ Set.univ := by
    intro he
    rw [he] at hbad
    have : IsProbabilityMeasure ν := inferInstance
    simp at hbad
  have hex : ∃ ω, ω ∉ (⋃ e, {ω | t ≤ |Z e ω|}) := by
    by_contra h
    push Not at h
    exact hnotuniv (Set.eq_univ_of_forall h)
  obtain ⟨ω,hω⟩ := hex
  refine ⟨ω,fun e => ?_⟩
  have hze : |Z e ω| < t := lt_of_not_ge (fun h => hω (Set.mem_iUnion.mpr ⟨e,h⟩))
  have hdR : 0 < (d:ℝ) := by exact_mod_cast hd
  have he : (∑ a, X (ω a) e)/(d:ℝ)-m e = Z e ω/(d:ℝ) := by
    simp only [Z, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    field_simp
  rw [he, abs_div, abs_of_pos hdR]
  exact (div_lt_iff₀ hdR).mpr (by simpa only [t, mul_comm] using hze)


lemma sample_convexHull {E : Type uE} [Fintype E] {S : Set (E → ℝ)}
    {v : E → ℝ} (hv : v ∈ convexHull ℝ S) (M : ℝ) (hM : 0 ≤ M)
    (hS : ∀ z ∈ S, ∀ e, z e ∈ Set.Icc 0 M)
    (d : ℕ) (hd : 0 < d) (ε : ℝ) (hε : 0 < ε)
    (hprob : (2*Fintype.card E:ℝ)*Real.exp (-((d:ℝ)*ε)^2/(2*d*(M/2)^2)) < 1) :
    ∃ z : Fin d → E → ℝ, (∀ a, z a ∈ S) ∧
      ∀ e, |(∑ a, z a e)/(d:ℝ)-v e| < ε := by
  classical
  obtain ⟨I, hI, z, w, hz, _, hw, hws, hsum⟩ := eq_pos_convex_span_of_mem_convexHull hv
  let : MeasurableSpace I := ⊤
  let μ : Measure I := Measure.sum (fun i => ENNReal.ofReal (w i) • Measure.dirac i)
  have : IsProbabilityMeasure μ := by
    constructor
    simp only [μ, Measure.sum_apply _ MeasurableSet.univ, Measure.smul_apply, Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one, tsum_fintype]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => (hw i).le), hws, ENNReal.ofReal_one]
  have hXm (e : E) : Measurable (fun i => z i e) := measurable_of_countable _
  have hint (e : E) : ∫ i, z i e ∂μ = v e := by
    rw [show μ = Measure.sum (fun i => ENNReal.ofReal (w i) • Measure.dirac i) from rfl,
      integral_sum_dirac_eq_tsum (fun _ => ENNReal.ofReal_ne_top) (hasSum_fintype _).summable, tsum_fintype]
    simp only [ENNReal.toReal_ofReal (hw _).le, smul_eq_mul]
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using congr_fun hsum e
  obtain ⟨ω,hω⟩ := bounded_sample_exists μ z hXm M hM
    (fun i => hS _ (hz ⟨i,rfl⟩)) d hd ε hε hprob
  refine ⟨z ∘ ω,fun a => hz ⟨ω a,rfl⟩,fun e => ?_⟩
  simpa only [hint, Function.comp_apply] using hω e

lemma weighted_moments_samples {E : Type uE} [Fintype E] [Nonempty E]
    {S : Set (E → ℝ)} (M : ℝ) (hM : 0 ≤ M) (hS : ∀ z ∈ S, ∀ e, z e ∈ Set.Icc 0 M)
    (b ε : ℝ) (hε : 0 < ε)
    (hw : ∀ w : E → ℝ, (∀ e, 0 < w e) → (∑ e, w e) = 1 →
      ∃ m ∈ closedConvexHull ℝ S, (∑ e, w e * |m e-b|) ≤ ε)
    (d : ℕ) (hd : 0 < d)
    (hprob : (2*Fintype.card E:ℝ)*Real.exp (-((d:ℝ)*ε)^2/(2*d*(M/2)^2)) < 1) :
    ∃ z : Fin d → E → ℝ, (∀ a, z a ∈ S) ∧
      ∀ e, |(∑ a, z a e)/(d:ℝ)-b| < 3*ε := by
  classical
  obtain ⟨m,hm,hme⟩ := weighted_error_to_uniform convex_closedConvexHull b ε hε hw
  rw [closedConvexHull_eq_closure_convexHull] at hm
  have hb : m ∈ Metric.ball (fun _ => b) (2*ε) := by
    simpa only [Metric.mem_ball, dist_pi_lt_iff (show 0 < 2*ε by positivity), Real.dist_eq] using hme
  obtain ⟨v,hvB,hv⟩ := mem_closure_iff.mp hm _ Metric.isOpen_ball hb
  have hve : ∀ e, |v e-b| < 2*ε := by
    simpa only [Metric.mem_ball, dist_pi_lt_iff (show 0 < 2*ε by positivity), Real.dist_eq] using hvB
  obtain ⟨z,hz,hze⟩ := sample_convexHull hv M hM hS d hd ε hε hprob
  refine ⟨z,hz,fun e => ?_⟩
  have htriangle := abs_add_le ((∑ a, z a e)/(d:ℝ)-v e) (v e-b)
  have ha := hze e
  have hb := hve e
  rw [sub_add_sub_cancel] at htriangle
  linarith


section RetractionBounds
open Matrix MeasureTheory
variable {E : Type uE} {V : Type uV} {J : Type uJ} {H : Type uH} [Fintype E] [Fintype V] [Fintype J]
  [DecidableEq E] [DecidableEq V] [Nonempty E]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

lemma controlled_retraction_bounds
    (src dst : E → V) (δ lam : E → ℝ) (hδ : ∀ e, 0 < δ e)
    (hlam : ∀ e, 0 < lam e) (hls : ∑ e, lam e = 1)
    (hcard : 2 ≤ Fintype.card V)
    (hinc : ∀ i : V, ∃ e, src e = i ∨ dst e = i)
    (hconn : ∀ i j : V, i ≠ j → ∃ e,
      (src e = i ∧ dst e = j) ∨ (src e = j ∧ dst e = i))
    (x : J → E → H) (B : J → ℝ) (hB : ∀ j, 0 < B j)
    (hx : ∀ j e, ‖x j e‖^2 ≤ B j) :
    ∃ P ∈ retractions (normalizedGradient src dst δ),
      (∀ e, matrixRowNorm P e ≤ 4*Real.log (Fintype.card V : ℝ)) ∧
      (∀ j, (∑ e, lam e * ‖hilbertMul P (x j) e‖^2) ≤ 4*B j) := by
  let y : J → E → H := fun j e => (Real.sqrt (B j))⁻¹ • x j e
  have hy (j : J) (e : E) : ‖y j e‖^2 ≤ 1 := by
    dsimp [y]
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (Real.sqrt_nonneg _),
      mul_pow, inv_pow, Real.sq_sqrt (hB j).le, inv_mul_eq_div]
    exact (div_le_one (hB j)).mpr (hx j e)
  obtain ⟨P,hP,hrow,henergy⟩ := controlled_retraction src dst δ lam hδ hlam hls hcard hinc hconn y hy
  refine ⟨P,hP,hrow,fun j => ?_⟩
  have hem (e : E) : hilbertMul P (y j) e = (Real.sqrt (B j))⁻¹ • hilbertMul P (x j) e := by
    simp only [hilbertMul, y, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro a _
    exact smul_comm _ _ _
  have he := henergy j
  simp only [hem, norm_smul, Real.norm_eq_abs, abs_inv,
    abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, inv_pow, Real.sq_sqrt (hB j).le] at he
  have halg : (∑ e, lam e*((B j)⁻¹*‖hilbertMul P (x j) e‖^2)) =
      (∑ e, lam e*‖hilbertMul P (x j) e‖^2)/(B j) := by
    simp only [div_eq_mul_inv, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro e _
    ring
  rw [halg] at he
  exact (div_le_iff₀ (hB j)).mp he
end RetractionBounds

end SubpolynomialLp

end

end OAI
