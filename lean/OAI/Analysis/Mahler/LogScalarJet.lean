import OAI.Analysis.Mahler.LogUniform
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Congr
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Normed.Module.FiniteDimension

namespace OAI

open Set Filter ContinuousLinearMap
open scoped Topology

namespace SymmetricMahler
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def logD (t : ℝ) (A : E →L[ℝ] ℝ) := t⁻¹ • A

def logD2 (t : ℝ) (A : E →L[ℝ] ℝ) (B : E →L[ℝ] (E →L[ℝ] ℝ)) :=
  t⁻¹ • B + (-(t^2)⁻¹ • A).smulRight A

lemma hasFDerivAt_logD {f : E → ℝ} {a : E → (E →L[ℝ] ℝ)}
    {b : E →L[ℝ] (E →L[ℝ] ℝ)} {x : E}
    (hf : HasFDerivAt f (a x) x) (ha : HasFDerivAt a b x) (hx : f x ≠ 0) :
    HasFDerivAt (fun y => logD (f y) (a y)) (logD2 (f x) (a x) b) x := by
  exact ((hasDerivAt_inv hx).comp_hasFDerivAt x hf).fun_smul ha

/-- Actual nested real derivative, from the local derivative field and the
inverse/product rule. Positivity is used locally, not assumed as a log jet. -/
lemma fderiv_log_twice {f : E → ℝ} {a : E → (E →L[ℝ] ℝ)}
    {b : E →L[ℝ] (E →L[ℝ] ℝ)} {x : E}
    (hf : ∀ᶠ y in 𝓝 x, HasFDerivAt f (a y) y)
    (ha : HasFDerivAt a b x) (hx : f x ≠ 0) :
    fderiv ℝ (fderiv ℝ (fun y => Real.log (f y))) x = logD2 (f x) (a x) b := by
  have hfx := hf.self_of_nhds
  have he : (fun y => logD (f y) (a y)) =ᶠ[𝓝 x]
      fderiv ℝ (fun y => Real.log (f y)) := by
    filter_upwards [hf, hfx.continuousAt.eventually_ne hx] with y hy hne
    exact (hy.log hne).fderiv.symm
  exact ((hasFDerivAt_logD hfx ha hx).congr_of_eventuallyEq he.symm).fderiv

/-- Uniform convergence of the explicit logarithmic jets. The positive
cutoff makes each algebraic operation globally continuous; it agrees with
the actual formula on the limit and eventually on the entire compact set. -/
theorem uniform_log_jets [FiniteDimensional ℝ E]
    {I X : Type*} [TopologicalSpace X] {K : Set X} {l : Filter I}
    {u : I → X → ℝ} {a : I → X → (E →L[ℝ] ℝ)}
    {b : I → X → (E →L[ℝ] (E →L[ℝ] ℝ))}
    {t : X → ℝ} {A : X → (E →L[ℝ] ℝ)} {B : X → (E →L[ℝ] (E →L[ℝ] ℝ))}
    (hK : IsCompact K) (ht : ContinuousOn t K) (hA : ContinuousOn A K)
    (hB : ContinuousOn B K) (hp : ∀ x ∈ K, 0 < t x)
    (hu : TendstoUniformlyOn u t l K) (ha : TendstoUniformlyOn a A l K)
    (hb : TendstoUniformlyOn b B l K) :
    (∃ c : ℝ, 0 < c ∧ ∀ᶠ i in l, ∀ x ∈ K, c ≤ u i x) ∧
    TendstoUniformlyOn (fun i x => Real.log (u i x)) (fun x => Real.log (t x)) l K ∧
    TendstoUniformlyOn (fun i x => logD (u i x) (a i x))
      (fun x => logD (t x) (A x)) l K ∧
    TendstoUniformlyOn (fun i x => logD2 (u i x) (a i x) (b i x))
      (fun x => logD2 (t x) (A x) (B x)) l K := by
  obtain ⟨c, hc, htc, huc⟩ := eventually_uniform_pos hK ht hp hu
  have htc' : ∀ x ∈ K, c ≤ t x := fun x hx => by linarith [htc x hx]
  have hab : TendstoUniformlyOn (fun i x => (a i x, b i x))
      (fun x => (A x, B x)) l K := uniform_pair ha hb
  have hq : TendstoUniformlyOn (fun i x => (u i x, a i x, b i x))
      (fun x => (t x, A x, B x)) l K := uniform_pair hu hab
  have hcont := ht.prodMk (hA.prodMk hB)
  have hg0 : Continuous (fun r : ℝ => Real.log (max c r)) := by
    apply Continuous.log (continuous_const.max continuous_id)
    intro r
    exact ne_of_gt (lt_of_lt_of_le hc (le_max_left _ _))
  have h0 := uniform_comp_of_compact hK ht hu hg0
  have hg1 : Continuous (fun q : ℝ × (E →L[ℝ] ℝ) × (E →L[ℝ] (E →L[ℝ] ℝ)) =>
      logD (max c q.1) q.2.1) := by
    have hv : Continuous (fun q : ℝ × (E →L[ℝ] ℝ) × (E →L[ℝ] (E →L[ℝ] ℝ)) => max c q.1) :=
      continuous_const.max continuous_fst
    exact (hv.inv₀ (fun q => ne_of_gt (lt_of_lt_of_le hc (le_max_left _ _)))).smul
      (continuous_fst.comp continuous_snd)
  have hg2 : Continuous (fun q : ℝ × (E →L[ℝ] ℝ) × (E →L[ℝ] (E →L[ℝ] ℝ)) =>
      logD2 (max c q.1) q.2.1 q.2.2) := by
    have : ContinuousAdd (E →L[ℝ] (E →L[ℝ] ℝ)) :=
      (inferInstance : IsTopologicalAddGroup (E →L[ℝ] (E →L[ℝ] ℝ))).toContinuousAdd
    have hv : Continuous (fun q : ℝ × (E →L[ℝ] ℝ) × (E →L[ℝ] (E →L[ℝ] ℝ)) => max c q.1) :=
      continuous_const.max continuous_fst
    have hn (q : ℝ × (E →L[ℝ] ℝ) × (E →L[ℝ] (E →L[ℝ] ℝ))) : max c q.1 ≠ 0 :=
      ne_of_gt (lt_of_lt_of_le hc (le_max_left _ _))
    have hpa : Continuous (fun q : ℝ × (E →L[ℝ] ℝ) × (E →L[ℝ] (E →L[ℝ] ℝ)) => q.2.1) :=
      continuous_fst.comp continuous_snd
    have hpb : Continuous (fun q : ℝ × (E →L[ℝ] ℝ) × (E →L[ℝ] (E →L[ℝ] ℝ)) => q.2.2) :=
      continuous_snd.comp continuous_snd
    exact ((hv.inv₀ hn).smul hpb).add
      (((smulRightL ℝ E (E →L[ℝ] ℝ)).continuous.comp
        ((((hv.pow 2).inv₀ (fun q => pow_ne_zero _ (hn q))).neg).smul hpa)).clm_apply hpa)
  have h1 := uniform_comp_of_compact (E := ℝ × (E →L[ℝ] ℝ) × (E →L[ℝ] (E →L[ℝ] ℝ))) (H := E →L[ℝ] ℝ) hK hcont hq hg1
  have h2 := uniform_comp_of_compact (E := ℝ × (E →L[ℝ] ℝ) × (E →L[ℝ] (E →L[ℝ] ℝ))) (H := E →L[ℝ] (E →L[ℝ] ℝ)) hK hcont hq hg2
  refine ⟨⟨c, hc, huc⟩, ?_, ?_, ?_⟩
  · apply (h0.congr_right (fun x hx => by rw [max_eq_right (htc' x hx)])).congr
    filter_upwards [huc] with i hi
    intro x hx
    simp only [max_eq_right (hi x hx)]
  · apply (h1.congr_right (fun x hx => by simp only [max_eq_right (htc' x hx)])).congr
    filter_upwards [huc] with i hi
    intro x hx
    dsimp only
    simp only [max_eq_right (hi x hx)]
  · apply (h2.congr_right (fun x hx => by simp only [max_eq_right (htc' x hx)])).congr
    filter_upwards [huc] with i hi
    intro x hx
    dsimp only
    simp only [max_eq_right (hi x hx)]

end
end SymmetricMahler

end OAI
