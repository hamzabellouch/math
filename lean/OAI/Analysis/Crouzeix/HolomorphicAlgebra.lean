import Mathlib
import OAI.Analysis.Crouzeix.DiskHolomorphic

namespace OAI

/-! Holomorphic Algebra. -/

noncomputable section

open Set Filter Metric Topology Complex MeasureTheory

open scoped InnerProductSpace Matrix.Norms.L2Operator

namespace CrouzeixHilbert

lemma exists_polynomial_tendstoUniformlyOn {K U : Set ℂ}
    (hK : IsCompact K) (hc : Convex ℝ K) (hU : IsOpen U) (hKU : K ⊆ U)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U) :
    ∃ p : ℕ → Polynomial ℂ, TendstoUniformlyOn (fun n z => (p n).eval z) f atTop K := by
  have happrox (n : ℕ) : ∃ p : Polynomial ℂ, ∀ z ∈ K, ‖p.eval z - f z‖ < (1 : ℝ)/(n+1) :=
    exists_polynomial_uniform_approx hK hc hU hKU hf (by positivity)
  choose p hp using happrox
  refine ⟨p, Metric.tendstoUniformlyOn_iff.mpr (fun ε hε => ?_)⟩
  have ht : Tendsto (fun n : ℕ => (1 : ℝ)/(n+1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  filter_upwards [ht.eventually (gt_mem_nhds hε)] with n hn z hz
  rw [dist_comm, dist_eq_norm]
  exact (hp n z hz).trans hn

section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [Nontrivial H]

variable (A : Operator H)

lemma holomorphicEval_polynomial {U : Set ℂ} (hU : IsOpen U)
    (hKU : numericalClosure A ⊆ U) (p : Polynomial ℂ) :
    holomorphicEval A U p.eval = Polynomial.aeval A p := by
  obtain ⟨Γ⟩ := exists_calculusContour (isCompact_numericalClosure A)
    (convex_numericalClosure A) (numericalClosure_nonempty A) hU hKU
  rw [holomorphicEval_eq_contourEval A hU p.differentiable.differentiableOn Γ,
    contourEval_polynomial]

lemma holomorphicEval_const {U : Set ℂ} (hU : IsOpen U)
    (hKU : numericalClosure A ⊆ U) (c : ℂ) :
    holomorphicEval A U (fun _ => c) = algebraMap ℂ (Operator H) c := by
  simpa only [Polynomial.eval_C, Polynomial.aeval_C] using
    holomorphicEval_polynomial A hU hKU (Polynomial.C c)

lemma holomorphicEval_restrict {U V : Set ℂ} (hU : IsOpen U) (hV : IsOpen V)
    (hKU : numericalClosure A ⊆ U) (hUV : U ⊆ V) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f V) :
    holomorphicEval A U f = holomorphicEval A V f := by
  obtain ⟨Γ⟩ := exists_calculusContour (isCompact_numericalClosure A)
    (convex_numericalClosure A) (numericalClosure_nonempty A) hU hKU
  let Δ : CalculusContour (numericalClosure A) V := {
    toSmoothContour := Γ.toSmoothContour
    avoids := fun t ht => ⟨hUV (Γ.avoids t ht).1, (Γ.avoids t ht).2⟩
    index_inside := Γ.index_inside
    index_outside := fun z hz => Γ.index_outside z (fun h => hz (hUV h)) }
  rw [holomorphicEval_eq_contourEval A hU (hf.mono hUV) Γ,
    holomorphicEval_eq_contourEval A hV hf Δ]

lemma holomorphicEval_add {U : Set ℂ} (hU : IsOpen U)
    (hKU : numericalClosure A ⊆ U) {f g : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f U) (hg : DifferentiableOn ℂ g U) :
    holomorphicEval A U (fun z => f z + g z) = holomorphicEval A U f + holomorphicEval A U g := by
  obtain ⟨Γ⟩ := exists_calculusContour (isCompact_numericalClosure A)
    (convex_numericalClosure A) (numericalClosure_nonempty A) hU hKU
  rw [holomorphicEval_eq_contourEval A hU (hf.fun_add hg) Γ,
    holomorphicEval_eq_contourEval A hU hf Γ, holomorphicEval_eq_contourEval A hU hg Γ]
  simp only [contourEval_eq_kernel, add_smul]
  rw [intervalIntegral.integral_add
    (intervalIntegrable_contourIntegrand A Γ (hf.continuousOn.mono (by
      rintro z ⟨t,ht,rfl⟩; exact (Γ.avoids t ht).1)))
    (intervalIntegrable_contourIntegrand A Γ (hg.continuousOn.mono (by
      rintro z ⟨t,ht,rfl⟩; exact (Γ.avoids t ht).1))), smul_add]

lemma holomorphicEval_smul {U : Set ℂ} (hU : IsOpen U)
    (hKU : numericalClosure A ⊆ U) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f U) (c : ℂ) :
    holomorphicEval A U (fun z => c * f z) = c • holomorphicEval A U f := by
  obtain ⟨Γ⟩ := exists_calculusContour (isCompact_numericalClosure A)
    (convex_numericalClosure A) (numericalClosure_nonempty A) hU hKU
  rw [holomorphicEval_eq_contourEval A hU (hf.const_mul c) Γ,
    holomorphicEval_eq_contourEval A hU hf Γ, contourEval_const_mul]

lemma holomorphicEval_mul {U : Set ℂ} (hU : IsOpen U)
    (hKU : numericalClosure A ⊆ U) {f g : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f U) (hg : DifferentiableOn ℂ g U) :
    holomorphicEval A U (fun z => f z * g z) = holomorphicEval A U f * holomorphicEval A U g := by
  obtain ⟨ε,hε,hεU⟩ := (isCompact_numericalClosure A).exists_cthickening_subset_open hU hKU
  let K := cthickening ε (numericalClosure A)
  have hK : IsCompact K := (isCompact_numericalClosure A).cthickening
  have hc : Convex ℝ K := (convex_numericalClosure A).cthickening ε
  have hAK : numericalClosure A ⊆ interior K :=
    (self_subset_thickening hε _).trans (thickening_subset_interior_cthickening _ _)
  obtain ⟨Γ⟩ := exists_calculusContour (isCompact_numericalClosure A)
    (convex_numericalClosure A) (numericalClosure_nonempty A) isOpen_interior hAK
  let Δ : CalculusContour (numericalClosure A) U := {
    toSmoothContour := Γ.toSmoothContour
    avoids := fun t ht => ⟨hεU (interior_subset (Γ.avoids t ht).1), (Γ.avoids t ht).2⟩
    index_inside := Γ.index_inside
    index_outside := fun z hz => Γ.index_outside z (fun h => hz (hεU (interior_subset h))) }
  have htrace : Δ.toSmoothContour.trace ⊆ K := by
    rintro z ⟨t,ht,rfl⟩
    exact interior_subset (Γ.avoids t ht).1
  obtain ⟨p,hp⟩ := exists_polynomial_tendstoUniformlyOn hK hc hU hεU hf
  obtain ⟨q,hq⟩ := exists_polynomial_tendstoUniformlyOn hK hc hU hεU hg
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let fK : C(K,ℂ) := ⟨fun z => f z, (hf.continuousOn.mono hεU).domRestrict⟩
  let gK : C(K,ℂ) := ⟨fun z => g z, (hg.continuousOn.mono hεU).domRestrict⟩
  have hpK : Tendsto (fun n => (p n).toContinuousMapOn K) atTop (𝓝 fK) := by
    rw [ContinuousMap.tendsto_iff_tendstoUniformly]
    exact (tendstoUniformlyOn_iff_tendstoUniformly_comp_coe.mp hp)
  have hqK : Tendsto (fun n => (q n).toContinuousMapOn K) atTop (𝓝 gK) := by
    rw [ContinuousMap.tendsto_iff_tendstoUniformly]
    exact (tendstoUniformlyOn_iff_tendstoUniformly_comp_coe.mp hq)
  have hpq : TendstoUniformlyOn (fun n z => (p n * q n).eval z)
      (fun z => f z * g z) atTop K := by
    have hs := ContinuousMap.tendsto_iff_tendstoUniformly.mp (hpK.mul hqK)
    change TendstoUniformly (fun n (z : K) => (p n).eval (z : ℂ) * (q n).eval (z : ℂ))
      (fun z : K => f z * g z) atTop at hs
    rw [tendstoUniformlyOn_iff_tendstoUniformly_comp_coe]
    simpa only [Function.comp_def, Polynomial.eval_mul] using hs
  have hpf := tendsto_contourEval A Δ (fun n => (p n).continuous.continuousOn) (hp.mono htrace)
  have hqg := tendsto_contourEval A Δ (fun n => (q n).continuous.continuousOn) (hq.mono htrace)
  have hmul := tendsto_contourEval A Δ (fun n => (p n * q n).continuous.continuousOn) (hpq.mono htrace)
  simp_rw [contourEval_polynomial] at hpf hqg hmul
  simp only [map_mul] at hmul
  have he := tendsto_nhds_unique hmul (hpf.mul hqg)
  simpa only [← holomorphicEval_eq_contourEval A hU (hf.fun_mul hg) Δ,
    ← holomorphicEval_eq_contourEval A hU hf Δ, ← holomorphicEval_eq_contourEval A hU hg Δ] using he

end

end CrouzeixHilbert

end

end OAI
