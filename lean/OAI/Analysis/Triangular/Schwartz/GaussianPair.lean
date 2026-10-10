import OAI.Analysis.Triangular.Construction.Normalization
import OAI.Analysis.Triangular.Lattice.LatticeGeometry

namespace OAI

noncomputable section
open scoped FourierTransform SchwartzMap
open Complex MeasureTheory
namespace AtomicTriangular
open Construction

def gaussianSchwartz (α : ℝ) (hα : 0<α) : 𝓢(Plane,ℝ) :=
  Analysis.gaussianSchwartz (Real.pi*α) (mul_pos Real.pi_pos hα)
lemma gaussianSchwartz_apply (α : ℝ) (hα : 0<α) (x : Plane) :
    gaussianSchwartz α hα x=gaussian α x := by
  simp only [gaussianSchwartz,Analysis.gaussianSchwartz_apply,gaussian,neg_mul]
lemma gaussianSchwartz_coe (α : ℝ) (hα : 0<α) :
    (gaussianSchwartz α hα : Plane → ℝ)=gaussian α := funext (gaussianSchwartz_apply α hα)
lemma gaussian_radial (α : ℝ) : Radial (gaussian α) := by
  intro x y hxy
  simp only [gaussian,hxy]
lemma realFourier_gaussian {α : ℝ} (hα : 0<α) (w : Plane) :
    realFourier (gaussian α) w=(α⁻¹*gaussian α⁻¹ w:ℝ) := by
  have he : (fun x => (gaussian α x:ℂ))=(fun x : Plane => exp (-(Real.pi:ℂ)*(α:ℂ)*‖x‖^2)) := by
    ext x
    simp [gaussian]
  rw [realFourier,he,complex_gaussian_transform (α:ℂ) hα]
  simp only [gaussian,ofReal_mul,ofReal_inv]
  congr 1
  rw [ofReal_exp]
  congr 1
  push_cast
  ring
lemma realFourier_smul (c : ℝ) (f : Plane → ℝ) (w : Plane) :
    realFourier (c • f) w=(c:ℂ)*realFourier f w := by
  unfold realFourier
  simp only [Pi.smul_apply,smul_eq_mul,ofReal_mul]
  change 𝓕 ((c:ℂ) • (fun x => (f x:ℂ))) w=_
  rw [complex_fourier_smul]
  rfl
lemma realFourier_sub (f g : 𝓢(Plane,ℝ)) (w : Plane) :
    realFourier ((f-g : 𝓢(Plane,ℝ)) : Plane → ℝ) w=realFourier f w-realFourier g w := by
  have hf : Integrable (fun x => (f x:ℂ)) := f.integrable.ofReal
  have hg : Integrable (fun x => (g x:ℂ)) := g.integrable.ofReal
  simp only [realFourier,sub_apply,ofReal_sub,Real.fourier_eq,smul_sub]
  rw [integral_sub ((Real.fourierIntegral_convergent_iff w).mpr hf)
    ((Real.fourierIntegral_convergent_iff w).mpr hg)]

structure GaussianPair (α : ℝ) where
  first : 𝓢(Plane,ℝ)
  second : 𝓢(Plane,ℝ)
  first_radial : Radial first
  second_radial : Radial second
  fourier_first : ∀ w, realFourier first w=(second w:ℂ)
  fourier_second : ∀ w, realFourier second w=(first w:ℂ)
  minorant : ∀ x, first x ≤ gaussian α x
  positive : ∀ x, 0 ≤ second x
  contact : ∀ x (n : Construction.Node), Construction.radial x=n.val → first x=gaussian α x
  zeros : ∀ x (n : Construction.Node), Construction.radial x=n.val → second x=0

def largeGaussianPair {α : ℝ} (hα : 1 ≤ α) : GaussianPair α where
  first := actualSchwartz 0 (gaussianZ α) (gaussianZ_bounds hα).1 (gaussianZ_bounds hα).2.le
  second := actualSchwartz 1 (gaussianZ α) (gaussianZ_bounds hα).1 (gaussianZ_bounds hα).2.le
  first_radial := actualSchwartz_radial 0 _ _
  second_radial := actualSchwartz_radial 1 _ _
  fourier_first := actualSchwartz_fourier _ _
  fourier_second := actualSchwartz_fourier_side 1 _ _
  minorant x := (actualSchwartz_signs hα x).1
  positive x := (actualSchwartz_signs hα x).2
  contact x n hx := (actualSchwartz_node hα x n hx).1
  zeros x n hx := (actualSchwartz_node hα x n hx).2

def reciprocalGaussianPair {α : ℝ} (hα : 0<α) (p : GaussianPair α⁻¹) : GaussianPair α where
  first := gaussianSchwartz α hα-α⁻¹ • p.second
  second := α⁻¹ • (gaussianSchwartz α⁻¹ (inv_pos.mpr hα)-p.first)
  first_radial := by
    intro x y hxy
    simp only [sub_apply,smul_apply,smul_eq_mul,gaussianSchwartz_apply,
      gaussian_radial α x y hxy,p.second_radial x y hxy]
  second_radial := by
    intro x y hxy
    simp only [sub_apply,smul_apply,smul_eq_mul,gaussianSchwartz_apply,
      gaussian_radial α⁻¹ x y hxy,p.first_radial x y hxy]
  fourier_first w := by
    rw [realFourier_sub,gaussianSchwartz_coe]
    change realFourier (gaussian α) w-realFourier (α⁻¹ • (p.second:Plane → ℝ)) w=_
    rw [realFourier_gaussian hα,realFourier_smul,p.fourier_second]
    simp only [smul_apply,sub_apply,smul_eq_mul,gaussianSchwartz_apply,ofReal_mul,ofReal_sub]
    ring
  fourier_second w := by
    change realFourier (α⁻¹ • ((gaussianSchwartz α⁻¹ (inv_pos.mpr hα)-p.first : 𝓢(Plane,ℝ)):Plane → ℝ)) w=_
    rw [realFourier_smul,realFourier_sub,gaussianSchwartz_coe]
    rw [realFourier_gaussian (inv_pos.mpr hα),p.fourier_first,inv_inv]
    simp only [sub_apply,smul_apply,smul_eq_mul,gaussianSchwartz_apply,ofReal_mul,ofReal_sub,ofReal_inv]
    field_simp [hα.ne']
  minorant x := by
    change gaussianSchwartz α hα x-α⁻¹*p.second x ≤ _
    rw [gaussianSchwartz_apply]
    exact sub_le_self _ (mul_nonneg (inv_nonneg.mpr hα.le) (p.positive x))
  positive x := by
    change 0 ≤ α⁻¹*(gaussianSchwartz α⁻¹ (inv_pos.mpr hα) x-p.first x)
    rw [gaussianSchwartz_apply]
    exact mul_nonneg (inv_nonneg.mpr hα.le) (sub_nonneg.mpr (p.minorant x))
  contact x n hx := by
    change gaussianSchwartz α hα x-α⁻¹*p.second x=_
    rw [p.zeros x n hx,mul_zero,sub_zero,gaussianSchwartz_apply]
  zeros x n hx := by
    change α⁻¹*(gaussianSchwartz α⁻¹ (inv_pos.mpr hα) x-p.first x)=0
    rw [p.contact x n hx,gaussianSchwartz_apply,sub_self,mul_zero]

def gaussianPair (α : ℝ) (hα : 0<α) : GaussianPair α :=
  if h : 1 ≤ α then largeGaussianPair h else
    reciprocalGaussianPair hα (largeGaussianPair ((one_le_inv₀ hα).mpr (le_of_not_ge h)))

theorem sharp_gaussian_minorants (α : ℝ) (hα : 0 < α) :
    ∃ f : SchwartzMap Plane ℝ,
      Radial f ∧ (∀ x, f x ≤ gaussian α x) ∧
      (∀ w, (realFourier f w).im = 0 ∧ 0 ≤ (realFourier f w).re) ∧
      (∀ a ∈ A, a ≠ 0 → f a = gaussian α a) ∧
      (∀ w ∈ dualA, w ≠ 0 → realFourier f w = 0) := by
  let p := gaussianPair α hα
  refine ⟨p.first,p.first_radial,p.minorant,?_,?_,?_⟩
  · intro w
    rw [p.fourier_first]
    exact ⟨rfl,p.positive w⟩
  · intro a ha ha0
    obtain ⟨n,hn⟩ := A_radial_node ha ha0
    exact p.contact a n hn
  · intro w hw hw0
    obtain ⟨n,hn⟩ := dualA_radial_node hw hw0
    rw [p.fourier_first,p.zeros w n hn,ofReal_zero]
end AtomicTriangular
end

end OAI
