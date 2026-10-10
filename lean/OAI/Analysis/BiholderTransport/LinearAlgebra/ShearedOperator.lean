import Mathlib
import OAI.Analysis.BiholderTransport.CostGeometry.RadialBounds
import OAI.Analysis.BiholderTransport.LinearAlgebra.ShearBounds

namespace OAI

section
section
noncomputable section
open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff

namespace WeakMTWTransport
section ShearedOperator
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]
local instance (x : M) : FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,Model n) x) :=
  inferInstanceAs (FiniteDimensional ℝ (Model n))

def shearedRadialOperator (x : M) (p q : TangentSpace 𝓘(ℝ,Model n) x) (δ t : ℝ) :
    TangentSpace 𝓘(ℝ,Model n) x →L[ℝ] TangentSpace 𝓘(ℝ,Model n) x :=
  (InnerProductSpace.toDual ℝ _).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((radialHessianDefectBilinear x (p+t • q) δ).bilinearComp (spectralShear p q t) (spectralShear p q t))

omit [CompactSpace M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma inner_shearedRadialOperator (x : M) (p q : TangentSpace 𝓘(ℝ,Model n) x) (δ t : ℝ)
    (v w : TangentSpace 𝓘(ℝ,Model n) x) :
    inner ℝ (shearedRadialOperator x p q δ t v) w =
      radialHessianDefectBilinear x (p+t • q) δ (spectralShear p q t v) (spectralShear p q t w) :=
  InnerProductSpace.toDual_symm_apply

lemma shearedRadialOperator_symmetric {x : M} {p q : TangentSpace 𝓘(ℝ,Model n) x}
    {δ t : ℝ} (hp : (1-δ) • (p+t • q)∈injectivityDomain x) :
    (shearedRadialOperator x p q δ t).toLinearMap.IsSymmetric := by
  intro v w
  change inner ℝ (shearedRadialOperator x p q δ t v) w =
    inner ℝ v (shearedRadialOperator x p q δ t w)
  rw [real_inner_comm (shearedRadialOperator x p q δ t w) v,inner_shearedRadialOperator,inner_shearedRadialOperator]
  exact radialHessianDefect_symm hp _ _

lemma uniform_sheared_radial_quadratic_bounds {a B : ℝ} (ha : 0<a) (hB : 0<B)
    (haB : a*B≤1/2) :
    ∃ C : ℝ, 0<C ∧ ∀ x : M, ∀ p q : TangentSpace 𝓘(ℝ,Model n) x,
      0 < inner ℝ p q → ‖q‖^2/inner ℝ p q≤B →
      (∀ t∈Icc (-a) 1, p+t • q∈minimizingVectors x) →
      ∀ δ∈Ioc (0:ℝ) (1/2), ∀ t∈Icc (-a) 1, ∀ v,
      -C*δ*‖v‖^2 ≤ inner ℝ (shearedRadialOperator x p q δ t v) v ∧
      |inner ℝ (shearedRadialOperator x p q δ t v) v|≤C*‖v‖^2 := by
  obtain ⟨C,hC,H⟩ := uniform_radial_defect_quadratic_bounds (n := n) (M := M)
  refine ⟨C*(2+B)^2,by positivity,?_⟩
  intro x p q hpq hβ hline δ hd t ht v
  rw [inner_shearedRadialOperator]
  have hs := (spectralShear_uniform_bounds p q ha hB haB hpq hβ ht v).2
  have hs2 : ‖spectralShear p q t v‖^2 ≤ (2+B)^2*‖v‖^2 := by
    simpa only [mul_pow] using (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hs
  have hh := H x (p+t • q) (hline t ht) δ hd (spectralShear p q t v)
  constructor
  · have HH := mul_le_mul_of_nonpos_left hs2 (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hC.le) hd.1.le)
    have := HH.trans hh.1
    nlinarith only [this]
  · have HH := mul_le_mul_of_nonneg_left hs2 hC.le
    have := hh.2.trans HH
    nlinarith only [this]

lemma WeakMTW.shearedRadialOperator_convexOn (hmtw : WeakMTW (n := n) (M := M))
    (x : M) (p q : TangentSpace 𝓘(ℝ,Model n) x) (hpq : inner ℝ p q≠0)
    {a δ : ℝ} (hd : δ∈Ioc (0:ℝ) (1/2))
    (hline : ∀ t∈Icc (-a) 1, p+t • q∈minimizingVectors x)
    (v : TangentSpace 𝓘(ℝ,Model n) x) :
    ConvexOn ℝ (Icc (-a) 1) (fun t => inner ℝ (shearedRadialOperator x p q δ t v) v) := by
  simpa only [inner_shearedRadialOperator] using hmtw.spectralShear_convexOn x p q hpq hd.1.le
    (show δ≠1 by linarith [hd.2]) (convex_Icc _ _)
    (fun t ht => contracted_minimizer_mem_injectivityDomain (hline t ht)
      (show 0<1-δ by linarith [hd.2]) (show 1-δ<1 by linarith [hd.1])) v
end ShearedOperator
end WeakMTWTransport

end

end

section

noncomputable section
namespace WeakMTWTransport
section BackgroundSpectrum
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma ordered_sheared_background_spectrum {F K : E →ₗ[ℝ] E}
    (hF : F.IsSymmetric) (hK : K.IsPositive) (L : E →ₗ[ℝ] E)
    (hL : Function.Bijective L) {l u δ b : ℝ} (hl : 0<l) (hu : 0≤u) (hd : 0≤δ)
    (hLn : ∀ v, l*‖v‖≤‖L v‖ ∧ ‖L v‖≤u*‖v‖)
    (hbg : ∀ v, |inner ℝ (F v) v-δ*inner ℝ (K (L v)) (L v)|≤b*‖v‖^2)
    {n : ℕ} (hn : Module.finrank ℝ E=n) (i : Fin n) :
    l^2*(δ*hK.isSymmetric.eigenvalues hn i)-b ≤ hF.eigenvalues hn i ∧
    hF.eigenvalues hn i ≤ u^2*(δ*hK.isSymmetric.eigenvalues hn i)+b := by
  let W := L.adjoint ∘ₗ K ∘ₗ L
  have hW : W.IsPositive := hK.adjoint_conj L
  have hw (v : E) : inner ℝ (W v) v=inner ℝ (K (L v)) (L v) := by
    simp only [W,LinearMap.comp_apply,LinearMap.adjoint_inner_left]
  have hcong := ordered_eigenvalues_bounded_congruence hW hK L hL hl hu hLn hw hn hn i
  have hup := ordered_eigenvalue_quadratic_comparison hF hW.isSymmetric hd
    (fun v => by have H := (abs_le.mp (hbg v)).2; rw [←hw] at H; linarith) hn i
  have hδW := hW.isSymmetric.smul (show starRingEnd ℝ δ=δ by simp)
  have hlo := ordered_eigenvalue_quadratic_comparison hδW hF (a := 1) (b := b)
    (by norm_num) (fun v => by
      have H := (abs_le.mp (hbg v)).1
      change inner ℝ (δ • W v) v ≤ 1*inner ℝ (F v) v+b*‖v‖^2
      rw [real_inner_smul_left,hw]
      linarith) hn i
  rw [ordered_eigenvalues_nonneg_smul hW.isSymmetric hd hn i] at hlo
  have hcl : l^2*hK.isSymmetric.eigenvalues hn i ≤ hW.isSymmetric.eigenvalues hn i := by
    have H := mul_le_mul_of_nonneg_left hcong.2 (sq_nonneg l)
    have he : l^2*(1/l)^2=1 := by field_simp
    rw [←mul_assoc,he,one_mul] at H
    exact H
  constructor
  · have H := mul_le_mul_of_nonneg_left hcl hd
    nlinarith only [H,hlo]
  · have H := mul_le_mul_of_nonneg_left hcong.1 hd
    nlinarith only [H,hup]
end BackgroundSpectrum
end WeakMTWTransport

end

end

end

end OAI
