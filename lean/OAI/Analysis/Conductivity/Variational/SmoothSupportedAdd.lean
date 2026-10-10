import Mathlib
import OAI.Analysis.Conductivity.Variational.SmoothPrimitive
import OAI.Analysis.Conductivity.Flux.LocalizedTwoFlux

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ScalarConductivity

section

theorem smooth_supported_add {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K : Set E} {f g : SmoothScalar E}
    (hf : tsupport f.val ⊆ K) (hg : tsupport g.val ⊆ K) :
    tsupport (f + g).val ⊆ K :=
  (tsupport_add f.val g.val).trans (Set.union_subset hf hg)

theorem smooth_supported_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K : Set E} (c : ℝ) {f : SmoothScalar E} (hf : tsupport f.val ⊆ K) :
    tsupport (c • f).val ⊆ K :=
  (tsupport_smul_subset_right (fun _ => c) f.val).trans hf

theorem smooth_supported_neg {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K : Set E} {f : SmoothScalar E} (hf : tsupport f.val ⊆ K) :
    tsupport (-f).val ⊆ K := by
  change tsupport (-f.val) ⊆ K
  rwa [tsupport_neg]

theorem smooth_supported_sub {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K : Set E} {f g : SmoothScalar E}
    (hf : tsupport f.val ⊆ K) (hg : tsupport g.val ⊆ K) :
    tsupport (f - g).val ⊆ K :=
  (tsupport_sub f.val g.val).trans (Set.union_subset hf hg)

theorem localizedFirstPotential_support {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (χ : SmoothScalar E) (L : E →L[ℝ] ℝ)
    (H : SmoothScalar ℝ) (k : ℝ) :
    tsupport (localizedFirstPotential χ L H k).val ⊆ tsupport χ.val := by
  apply smooth_supported_smul
  exact tsupport_mul_subset_left

theorem localizedSecondPotential_support {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (χ : SmoothScalar E) (L : E →L[ℝ] ℝ)
    (H : SmoothScalar ℝ) (k : ℝ) :
    tsupport (localizedSecondPotential χ L H k).val ⊆ tsupport χ.val := by
  apply smooth_supported_smul
  exact tsupport_mul_subset_left

theorem airyFlux_support {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v : Fin 3 → E) (φ : SmoothScalar E) (i : Fin 5) :
    tsupport (airyFlux v φ i).val ⊆ tsupport φ.val := by
  have hd (j l : Fin 3) :=
    (tsupport_smoothDirection_subset (v j) (smoothDirection (v l) φ)).trans
      (tsupport_smoothDirection_subset (v l) φ)
  fin_cases i
  · exact hd 1 1
  · exact smooth_supported_neg (hd 0 1)
  · exact hd 0 0
  · change tsupport (0 : E → ℝ) ⊆ _
    simp
  · change tsupport (0 : E → ℝ) ⊆ _
    simp

theorem transverseFlux_support {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v : Fin 3 → E) {K : Set E} {ψ η ω : SmoothScalar E}
    (hψ : tsupport ψ.val ⊆ K) (hη : tsupport η.val ⊆ K)
    (hω : tsupport ω.val ⊆ K) (i : Fin 5) :
    tsupport (transverseFlux v ψ η ω i).val ⊆ K := by
  have hd {f : SmoothScalar E} (hf : tsupport f.val ⊆ K) (j : Fin 3) :=
    (tsupport_smoothDirection_subset (v j) f).trans hf
  fin_cases i
  · exact hd hψ 2
  · exact hd hη 2
  · exact hd hω 2
  · exact smooth_supported_sub (smooth_supported_neg (hd hψ 0)) (hd hη 1)
  · exact smooth_supported_sub (smooth_supported_neg (hd hη 0)) (hd hω 1)

theorem localizedTwoFlux_support {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v : Fin 3 → E) (χ : SmoothScalar E) (L : E →L[ℝ] ℝ)
    (H₁ H₂ : SmoothScalar ℝ) (α p q r k : ℝ) (i : Fin 5) :
    tsupport (localizedTwoFlux v χ L H₁ H₂ α p q r k i).val ⊆ tsupport χ.val := by
  apply smooth_supported_add
  · exact smooth_supported_smul α
      ((airyFlux_support v (localizedSecondPotential χ L H₂ k) i).trans
        (localizedSecondPotential_support χ L H₂ k))
  · exact transverseFlux_support v
      (smooth_supported_smul p (localizedFirstPotential_support χ L H₁ k))
      (smooth_supported_smul q (localizedFirstPotential_support χ L H₁ k))
      (smooth_supported_smul r (localizedFirstPotential_support χ L H₁ k)) i

open Matrix

theorem exists_localized_two_flux {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v : Fin 3 → E) (χ : SmoothScalar E) (L : E →L[ℝ] ℝ)
    (h : SmoothScalar ℝ) (R : Fin 5 → ℝ)
    (hχ : HasCompactSupport χ.val) (hξ : (fun j => L (v j)) ≠ 0)
    (hR : divSymbolTwo (fun j => L (v j)) *ᵥ R = 0)
    (hp : Function.Periodic h.val 1) (hm : ∫ t in (0 : ℝ)..1, h.val t = 0) :
    ∃ G : ℝ → Fin 5 → SmoothScalar E,
      (∀ k, twoFluxDivergence v (G k) = 0) ∧
      (∀ k i, tsupport (G k i).val ⊆ tsupport χ.val) ∧
      ∀ i, TendstoUniformly
        (fun k x => (G k i).val x - R i * (χ.val x * h.val (k * L x)))
        (fun _ => 0) Filter.atTop := by
  obtain ⟨α, p, q, r, hspan⟩ := airy_transverse_span hξ hR
  obtain ⟨H₁, H₂, h₁, h₂, _, _, hB₁, hB₂⟩ := periodic_two_primitives h hp hm
  refine ⟨localizedTwoFlux v χ L H₁ H₂ α p q r,
    localizedTwoFlux_divergence v χ L H₁ H₂ α p q r,
    localizedTwoFlux_support v χ L H₁ H₂ α p q r, ?_⟩
  intro i
  rw [hspan]
  exact localizedTwoFlux_error_tendsto v χ L h H₁ H₂ α p q r hχ h₁ h₂ hB₁ hB₂ i

end

def lineShift {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (d : E) (f : E → ℝ) (x : E) : E := x + f x • d

theorem lineShift_bijective {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (d : E) (f : E → ℝ) (hf : Differentiable ℝ f)
    (hpos : ∀ x, 0 < 1 + fderiv ℝ f x d)
    (hbound : ∃ B : ℝ, ∀ x, |f x| ≤ B) :
    Function.Bijective (lineShift d f) := by
  have hd (y : E) (t : ℝ) : HasDerivAt (fun s => s + f (y + s • d))
      (1 + fderiv ℝ f (y + t • d) d) t := by
    have hline : HasDerivAt (fun s : ℝ => y + s • d) d t := by
      simpa using ((hasDerivAt_id t).smul_const d).const_add y
    exact (hasDerivAt_id t).add ((hf _).hasFDerivAt.comp_hasDerivAt t hline)
  have hm (y : E) : StrictMono (fun s : ℝ => s + f (y + s • d)) := by
    apply strictMono_of_deriv_pos
    intro t
    rw [(hd y t).deriv]
    exact hpos _
  constructor
  · intro x y hxy
    have hx : x = y + (f y - f x) • d := by
      dsimp [lineShift] at hxy
      calc
        x = (x + f x • d) - f x • d := by abel
        _ = (y + f y • d) - f x • d := congrArg (fun z => z - f x • d) hxy
        _ = y + (f y - f x) • d := by module
    have harg : (f y - f x) + f (y + (f y - f x) • d) =
        (0 : ℝ) + f (y + (0 : ℝ) • d) := by
      rw [← hx]
      simp
    have heq := (hm y).injective harg
    rw [heq] at hx
    simpa using hx
  · obtain ⟨B, hB⟩ := hbound
    have hB0 : 0 ≤ B := (abs_nonneg (f 0)).trans (hB 0)
    intro y
    have hcont : Continuous (fun t : ℝ => t + f (y + t • d)) :=
      continuous_id.add (hf.continuous.comp (continuous_const.add
        (continuous_id.smul continuous_const)))
    have hlo : (-B - 1) + f (y + (-B - 1) • d) ≤ 0 := by
      have := (abs_le.mp (hB (y + (-B - 1) • d))).2
      linarith
    have hhi : 0 ≤ (B + 1) + f (y + (B + 1) • d) := by
      have := (abs_le.mp (hB (y + (B + 1) • d))).1
      linarith
    obtain ⟨t, _, ht⟩ := intermediate_value_Icc (by linarith : -B - 1 ≤ B + 1)
      hcont.continuousOn ⟨hlo, hhi⟩
    refine ⟨y + t • d, ?_⟩
    change t + f (y + t • d) = 0 at ht
    dsimp [lineShift]
    rw [add_assoc, ← add_smul, ht, zero_smul, add_zero]

def rankOneEquiv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (d : E) (L : E →L[ℝ] ℝ) (h : 1 + L d ≠ 0) : E ≃L[ℝ] E := by
  let T := ContinuousLinearMap.id ℝ E + L.smulRight d
  let S := ContinuousLinearMap.id ℝ E - (1 + L d)⁻¹ • L.smulRight d
  have hTS (x : E) : T (S x) = x := by
    change x - (1 + L d)⁻¹ • (L x • d) +
      L (x - (1 + L d)⁻¹ • (L x • d)) • d = x
    simp only [smul_smul, map_sub, map_smul]
    have hscalar : -((1 + L d)⁻¹ * L x) +
        (L x - (1 + L d)⁻¹ * L x * L d) = 0 := by field_simp [h]; ring
    calc
      _ = x + (-((1 + L d)⁻¹ * L x) +
        (L x - (1 + L d)⁻¹ * L x * L d)) • d := by module
      _ = x := by rw [hscalar, zero_smul, add_zero]
  have hST (x : E) : S (T x) = x := by
    change x + L x • d - (1 + L d)⁻¹ • (L (x + L x • d) • d) = x
    simp only [smul_smul, map_add, map_smul]
    have hscalar : L x - (1 + L d)⁻¹ * (L x + L x * L d) = 0 := by
      field_simp [h]; ring
    calc
      _ = x + (L x - (1 + L d)⁻¹ * (L x + L x * L d)) • d := by module
      _ = x := by rw [hscalar, zero_smul, add_zero]
  exact {
    toLinearEquiv := {
      T.toLinearMap with
      invFun := S
      left_inv := hST
      right_inv := hTS }
    continuous_toFun := T.continuous
    continuous_invFun := S.continuous }

@[simp] theorem rankOneEquiv_apply {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (d : E) (L : E →L[ℝ] ℝ) (h : 1 + L d ≠ 0) (x : E) :
    rankOneEquiv d L h x = x + L x • d := rfl

theorem exists_smooth_lineShift_inverse {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E]
    (d : E) (f : SmoothScalar E)
    (hpos : ∀ x, 0 < 1 + fderiv ℝ f.val x d)
    (hbound : ∃ B : ℝ, ∀ x, |f.val x| ≤ B) :
    ∃ X : E ≃ E, (∀ x, X x = lineShift d f.val x) ∧
      ContDiff ℝ (↑(⊤ : ℕ∞)) X ∧ ContDiff ℝ (↑(⊤ : ℕ∞)) X.symm := by
  let X := Equiv.ofBijective (lineShift d f.val)
    (lineShift_bijective d f.val ((smoothScalar_contDiff f).differentiable (by simp)) hpos hbound)
  have hs : ContDiff ℝ (↑(⊤ : ℕ∞)) (lineShift d f.val) :=
    contDiff_id.add ((smoothScalar_contDiff f).smul contDiff_const)
  refine ⟨X, fun _ => rfl, hs, ?_⟩
  rw [contDiff_iff_contDiffAt]
  intro y
  let x := X.symm y
  let T := rankOneEquiv d (fderiv ℝ f.val x) (ne_of_gt (hpos x))
  have hT : HasFDerivAt (lineShift d f.val) (T : E →L[ℝ] E) x := by
    exact (hasFDerivAt_id x).add
      (((smoothScalar_contDiff f).differentiable (by simp) x).hasFDerivAt.smul_const d)
  have hh := hs.contDiffAt.to_localInverse hT (by simp)
  have he := (hs.contDiffAt.hasStrictFDerivAt' hT (by simp)).localInverse_unique
    (g := X.symm) (Filter.Eventually.of_forall X.symm_apply_apply)
  have hxy : lineShift d f.val x = y := X.apply_symm_apply y
  rw [hxy] at hh he
  exact hh.congr_of_eventuallyEq he

end ScalarConductivity

end

end OAI
