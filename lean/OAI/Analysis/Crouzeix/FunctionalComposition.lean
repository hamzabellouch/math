import Mathlib
import OAI.Analysis.Crouzeix.HolomorphicSpectrum

namespace OAI

/-! Functional Composition. -/

noncomputable section

open Set Filter Metric Topology Complex MeasureTheory

open scoped InnerProductSpace Matrix.Norms.L2Operator

namespace CrouzeixHilbert

lemma intertwines_aeval {B : Type*} [Ring B] [Algebra ℂ B]
    (S T D : B) (h : S * T = D * S) (p : Polynomial ℂ) :
    S * Polynomial.aeval T p = Polynomial.aeval D p * S := by
  have hp (n : ℕ) : S * T^n = D^n * S := by
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, ← mul_assoc, ih, mul_assoc, h, ← mul_assoc, ← pow_succ]
  induction p using Polynomial.induction_on' with
  | add p q hq hr => simp only [map_add, mul_add, add_mul, hq, hr]
  | monomial n c =>
    simp only [Polynomial.aeval_monomial]
    rw [← mul_assoc, (Algebra.commutes c S).symm, mul_assoc, hp, ← mul_assoc]

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [Nontrivial H]

lemma holomorphicEval_comp_intertwines (A D S : Operator H) (hN : ‖D‖ ≤ 1)
    {U V : Set ℂ} (hU : IsOpen U) (hKU : numericalClosure A ⊆ U)
    (hV : IsOpen V) (hKV : closedBall (0 : ℂ) 1 ⊆ V)
    {f g : ℂ → ℂ} (hf : DifferentiableOn ℂ f U) (hg : DifferentiableOn ℂ g V)
    (hfU : MapsTo f U V) (hfK : MapsTo f (numericalClosure A) (closedBall 0 1))
    (hI : S * holomorphicEval A U f = D * S) :
    S * holomorphicEval A U (g ∘ f) = holomorphicEval D V g * S := by
  let K : Set ℂ := closedBall 0 1
  have hK : IsCompact K := isCompact_closedBall _ _
  have hKc : Convex ℝ K := convex_closedBall _ _
  have hDK : numericalClosure D ⊆ K :=
    (numericalClosure_subset_closedBall D).trans (closedBall_subset_closedBall hN)
  obtain ⟨ε,hε,hεV⟩ := hK.exists_cthickening_subset_open hV hKV
  let L := cthickening ε K
  have hKL : K ⊆ interior L :=
    (self_subset_thickening hε _).trans (thickening_subset_interior_cthickening _ _)
  let W := U ∩ f ⁻¹' interior L
  have hW : IsOpen W := hf.continuousOn.isOpen_inter_preimage hU isOpen_interior
  have hAW : numericalClosure A ⊆ W := fun z hz => ⟨hKU hz,hKL (hfK hz)⟩
  have hfW : DifferentiableOn ℂ f W := hf.mono inter_subset_left
  have hAWL : MapsTo f W L := fun z hz => interior_subset hz.2
  have hWL : W ⊆ U := inter_subset_left
  have hgf := hg.comp hf hfU
  obtain ⟨Γ⟩ := exists_calculusContour (isCompact_numericalClosure A)
    (convex_numericalClosure A) (numericalClosure_nonempty A) hW hAW
  obtain ⟨Δ₀⟩ := exists_calculusContour (isCompact_numericalClosure D)
    (convex_numericalClosure D) (numericalClosure_nonempty D) isOpen_interior (hDK.trans hKL)
  let Δ : CalculusContour (numericalClosure D) V := {
    toSmoothContour := Δ₀.toSmoothContour
    avoids := fun t ht => ⟨hεV (interior_subset (Δ₀.avoids t ht).1), (Δ₀.avoids t ht).2⟩
    index_inside := Δ₀.index_inside
    index_outside := fun z hz => Δ₀.index_outside z (fun he => hz (hεV (interior_subset he))) }
  have hΔL : Δ.toSmoothContour.trace ⊆ L := by
    rintro z ⟨t,ht,rfl⟩
    exact interior_subset (Δ₀.avoids t ht).1
  have hΓW : Γ.toSmoothContour.trace ⊆ W := by
    rintro z ⟨t,ht,rfl⟩
    exact (Γ.avoids t ht).1
  obtain ⟨p,hp⟩ := exists_polynomial_tendstoUniformlyOn hK.cthickening (hKc.cthickening ε) hV hεV hg
  have hpd := tendsto_contourEval D Δ (fun n => (p n).continuous.continuousOn) (hp.mono hΔL)
  simp_rw [contourEval_polynomial, ← holomorphicEval_eq_contourEval D hV hg Δ] at hpd
  have hpa : Tendsto (fun n => Polynomial.aeval (holomorphicEval A U f) (p n)) atTop
      (𝓝 (holomorphicEval A U (g ∘ f))) := by
    have hp' : TendstoUniformlyOn (fun n z => (p n).eval (f z)) (g ∘ f) atTop Γ.toSmoothContour.trace := by
      apply Metric.tendstoUniformlyOn_iff.mpr
      intro δ hδ
      filter_upwards [Metric.tendstoUniformlyOn_iff.mp hp δ hδ] with n hn z hz
      exact hn (f z) (hAWL (hΓW hz))
    have hh := tendsto_contourEval A Γ
      (fun n => (p n).continuous.comp_continuousOn (hf.continuousOn.mono (hΓW.trans hWL))) hp'
    have he (n : ℕ) : contourEval A Γ.toSmoothContour (fun z => (p n).eval (f z)) =
        Polynomial.aeval (holomorphicEval A U f) (p n) := by
      calc
        _ = holomorphicEval A W (fun z => (p n).eval (f z)) :=
          (holomorphicEval_eq_contourEval A hW ((p n).differentiable.comp_differentiableOn hfW) Γ).symm
        _ = Polynomial.aeval (holomorphicEval A W f) (p n) :=
          holomorphicEval_polynomial_comp A hW hAW hfW (p n)
        _ = _ := by rw [holomorphicEval_restrict A hW hU hAW hWL hf]
    change Tendsto (fun n => contourEval A Γ.toSmoothContour (fun z => (p n).eval (f z))) atTop
      (𝓝 (contourEval A Γ.toSmoothContour (g ∘ f))) at hh
    simp_rw [he, ← holomorphicEval_eq_contourEval A hW (hgf.mono hWL) Γ,
      holomorphicEval_restrict A hW hU hAW hWL hgf] at hh
    exact hh
  have hh := (tendsto_const_nhds (x := S)).mul hpa
  have he (n : ℕ) : S * Polynomial.aeval (holomorphicEval A U f) (p n) =
      Polynomial.aeval D (p n) * S := intertwines_aeval S _ D hI (p n)
  simp_rw [he] at hh
  exact (tendsto_nhds_unique hh (hpd.mul tendsto_const_nhds))

end CrouzeixHilbert

end

end OAI
