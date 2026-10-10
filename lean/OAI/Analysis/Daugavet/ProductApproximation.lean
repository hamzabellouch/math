import OAI.Analysis.Daugavet.ProductOperators

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators

universe uB uR uIota uKappa

namespace ExactModuli
section MeasureMetric
variable {B : Type uB} {R : Type uR} [MeasurableSpace B] [MeasurableSpace R]
  {μ : Measure B} {ν : Measure R} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

omit [IsProbabilityMeasure μ] in
lemma measureDistance_le_of_tail [IsProbabilityMeasure μ] (f g : Lp ℝ 1 μ) {h : ℝ} (hh : 0 < h)
    (ht : μ.real {b | h < |f b - g b|} < h) : measureDistance μ f g ≤ h :=
  csInf_le ⟨0, fun _ ha => ha.1.le⟩ ⟨hh, ht⟩

omit [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] in
lemma measureDistance_pullback [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {F : B → R} (hF : MeasurePreserving F μ ν) (f g : Lp ℝ 1 ν) :
    measureDistance μ (Lp.compMeasurePreserving F hF f) (Lp.compMeasurePreserving F hF g) =
      measureDistance ν f g := by
  have ht (h : ℝ) :
      μ.real {b | h < |Lp.compMeasurePreserving F hF f b - Lp.compMeasurePreserving F hF g b|} =
      ν.real {r | h < |f r - g r|} := by
    have hae : {b | h < |Lp.compMeasurePreserving F hF f b - Lp.compMeasurePreserving F hF g b|} =ᵐ[μ]
        F ⁻¹' {r | h < |f r - g r|} := by
      filter_upwards [Lp.coeFn_compMeasurePreserving f hF, Lp.coeFn_compMeasurePreserving g hF] with b hb hb'
      change (h < |Lp.compMeasurePreserving F hF f b - Lp.compMeasurePreserving F hF g b|) =
          (h < |f (F b) - g (F b)|)
      simp only [hb, hb', Function.comp_apply]
    rw [measureReal_congr hae]
    exact hF.measureReal_preimage (measurableSet_lt measurable_const
      ((Lp.stronglyMeasurable f).measurable.sub (Lp.stronglyMeasurable g).measurable).abs).nullMeasurableSet
  simp only [measureDistance, ht]

end MeasureMetric
end ExactModuli

namespace ExactModuli.KW
section ProductAverages
variable {B : Type uB} [MeasurableSpace B] {μ : Measure B} [IsProbabilityMeasure μ]
variable {κ : Type uKappa} [Fintype κ]

lemma atoms_average_norm {p : ℝ} (hp : 1 < p) {n : ℕ} (u : Lp ℝ 1 μ) (hu : ‖u‖ = 1) (k : κ) :
    ‖oldL1 u - (n : ℝ)⁻¹ • ∑ j : Fin n, atomL1 hp u k j‖ =
      ∫ v : cube (Fin n), |(n : ℝ)⁻¹ * (∑ j, multiplier p (v j)) - 1| ∂cubeMeasure (Fin n) := by
  let A : (κ → cube (Fin n)) → ℝ := fun v => 1 - (n : ℝ)⁻¹ * ∑ j, multiplier p (v k j)
  have hae : (oldL1 u - (n : ℝ)⁻¹ • ∑ j : Fin n, atomL1 hp u k j : Lp ℝ 1 (μ.prod (arrayMeasure κ (Fin n))))
      =ᵐ[μ.prod (arrayMeasure κ (Fin n))] fun z => u z.1 * A z.2 := by
    filter_upwards [Lp.coeFn_sub (oldL1 u) ((n : ℝ)⁻¹ • ∑ j : Fin n, atomL1 hp u k j),
      oldL1_ae u, Lp.coeFn_smul (n : ℝ)⁻¹ (∑ j : Fin n, atomL1 hp u k j),
      coeFn_L1_sum Finset.univ (fun j : Fin n => atomL1 hp u k j),
      ae_all_iff.mpr (fun j : Fin n => atomL1_ae hp u k j)] with z hz hu' hs hsum hj
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hu', hs, hsum] at hz
    rw [hz]
    simp only [hj, arrayMultiplier, ← Finset.mul_sum, A]
    ring
  rw [L1_norm_of_ae _ hae]
  simp only [abs_mul]
  rw [integral_prod_mul (fun b => |u b|) (fun v => |A v|)]
  have hun : (∫ b, |u b| ∂μ) = 1 := (L1.norm_eq_integral_norm u).symm.trans hu
  rw [hun, one_mul]
  have heq := mp_integral (measurePreserving_eval (fun _ : κ => cubeMeasure (Fin n)) k)
    (((integrable_rowSum hp (fun _ : Fin n => 1)).const_mul (n : ℝ)⁻¹).sub (integrable_const 1)).abs.aestronglyMeasurable
  simp only [rowSum, one_mul, Pi.sub_apply] at heq
  dsimp [A]
  simp_rw [abs_sub_comm (1 : ℝ)]
  exact heq

end ProductAverages

section Normalize
variable {B : Type uB} [MeasurableSpace B] {μ : Measure B}

def normalizeL1 (f : Lp ℝ 1 μ) : Lp ℝ 1 μ := (max 1 ‖f‖)⁻¹ • f

lemma normalizeL1_mem (G : Submodule ℝ (Lp ℝ 1 μ)) {f : Lp ℝ 1 μ} (hf : f ∈ G) :
    normalizeL1 f ∈ G := G.smul_mem _ hf

lemma normalizeL1_norm (f : Lp ℝ 1 μ) : ‖normalizeL1 f‖ ≤ 1 := by
  have hm : 0 < max 1 ‖f‖ := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  rw [normalizeL1, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hm)]
  rw [← div_eq_inv_mul, div_le_one hm]
  exact le_max_right _ _

lemma normalizeL1_ae (f : Lp ℝ 1 μ) {g : B → ℝ} (hfg : f =ᵐ[μ] g) :
    normalizeL1 f =ᵐ[μ] normalizeFunction μ g := by
  have hn := L1_norm_of_ae f hfg
  filter_upwards [Lp.coeFn_smul (max 1 ‖f‖)⁻¹ f, hfg] with b hb hb'
  dsimp [normalizeL1]
  rw [hb]
  simp only [Pi.smul_apply, smul_eq_mul, hb', hn, normalizeFunction, div_eq_mul_inv, mul_comm]

lemma oldCombination_ae (x : Lp ℝ 1 μ) {κ : Type uKappa} [Fintype κ]
    (u : κ → Lp ℝ 1 μ) (c : κ → ℝ) :
    (x + ∑ k, c k • u k : Lp ℝ 1 μ) =ᵐ[μ] oldCombination x (fun k => (u k : B → ℝ)) c := by
  filter_upwards [Lp.coeFn_add x (∑ k, c k • u k), coeFn_L1_smul_sum c u] with b hb hb'
  simpa only [Pi.add_apply, hb', oldCombination] using hb

end Normalize

section WholeBallL1
variable {B : Type uB} [MeasurableSpace B] {μ : Measure B} [IsProbabilityMeasure μ]
variable {κ : Type uKappa} {ι : Type uIota} [Fintype κ] [Fintype ι]

lemma productOperator_control {p r q h : ℝ} (hp : 1 < p) (hpmax : p ≤ 3/2)
    (hr : 0 < r) (hq : 0 < q) (hh : 0 < h)
    (hmq : (Fintype.card κ : ℝ) * q < 1)
    (herr : (Fintype.card κ : ℝ) * q + h⁻¹ *
      (2 * (Fintype.card κ : ℝ) * r + (1 - (Fintype.card κ : ℝ) * q)⁻¹ - 1) < h)
    (hpq : 10 * (108 * scale p / r)^p < q)
    (G : Submodule ℝ (Lp ℝ 1 μ)) (x : G) (u : κ → G) (hu : ∀ k, ‖u k‖ = 1)
    (a : κ → ι → ℝ) (hg : ‖productOperator hp (fun k => (u k : Lp ℝ 1 μ)) (x,a)‖ ≤ 1) :
    ∃ ψ : G, ‖ψ‖ ≤ 1 ∧
      measureDistance (μ.prod (arrayMeasure κ ι))
        (productOperator hp (fun k => (u k : Lp ℝ 1 μ)) (x,a)) (oldL1 (ψ : Lp ℝ 1 μ)) ≤ h := by
  classical
  have he := productOperator_ae hp (x : Lp ℝ 1 μ) (fun k => (u k : Lp ℝ 1 μ)) a
  have hgn : (∫ z, |enlargedFunction p (x : Lp ℝ 1 μ) (fun k => (u k : Lp ℝ 1 μ)) a z|
      ∂μ.prod (arrayMeasure κ ι)) ≤ 1 := (L1_norm_of_ae _ he) ▸ hg
  obtain ⟨c, hc, htail⟩ := whole_ball_approximation hp hpmax hr hq hh hmq herr hpq
    (L1.integrable_coeFn (x : Lp ℝ 1 μ)) (fun k => L1.integrable_coeFn (u k : Lp ℝ 1 μ))
    (fun k => by simpa only [Real.norm_eq_abs] using (L1.norm_eq_integral_norm (u k : Lp ℝ 1 μ)).symm.trans (hu k)) a hgn
  let ψ : G := ⟨normalizeL1 ((x : Lp ℝ 1 μ) + ∑ k, c k • (u k : Lp ℝ 1 μ)),
    normalizeL1_mem G (G.add_mem x.property (G.sum_mem (fun k _ => G.smul_mem _ (u k).property)))⟩
  refine ⟨ψ, normalizeL1_norm _, measureDistance_le_of_tail _ _ hh ?_⟩
  have hψ : (ψ : Lp ℝ 1 μ) =ᵐ[μ]
      normalizeFunction μ (oldCombination (x : Lp ℝ 1 μ) (fun k => (u k : Lp ℝ 1 μ)) c) :=
    normalizeL1_ae _ (oldCombination_ae _ _ _)
  have hψpull := (measurePreserving_fst (μ := μ) (ν := arrayMeasure κ ι)).quasiMeasurePreserving.ae_eq_comp hψ
  have hevent : {z | h < |productOperator hp (fun k => (u k : Lp ℝ 1 μ)) (x,a) z - oldL1 (ν := arrayMeasure κ ι) (ψ : Lp ℝ 1 μ) z|}
      =ᵐ[μ.prod (arrayMeasure κ ι)] {z | h < |enlargedFunction p (x : Lp ℝ 1 μ) (fun k => (u k : Lp ℝ 1 μ)) a z -
        normalizeFunction μ (oldCombination (x : Lp ℝ 1 μ) (fun k => (u k : Lp ℝ 1 μ)) c) z.1|} := by
    filter_upwards [he, oldL1_ae (ν := arrayMeasure κ ι) (ψ : Lp ℝ 1 μ), hψpull] with z hz hz' hψz
    simp only [Function.comp_apply] at hψz
    rw [hz, hz', hψz]
  rw [measureReal_congr hevent]
  exact htail

end WholeBallL1
end ExactModuli.KW

end

end OAI
