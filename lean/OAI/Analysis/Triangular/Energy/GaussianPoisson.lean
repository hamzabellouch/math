import OAI.Analysis.Triangular.Energy.PairPoisson
import OAI.Analysis.Triangular.Schwartz.GaussianPair

namespace OAI

noncomputable section
open scoped BigOperators FourierTransform SchwartzMap
open Complex
namespace AtomicTriangular.Construction
lemma actualSchwartz_lattice_summable (side : Fin 2) {z : ℝ} (hz : 0<z) (hzB : z ≤ Z) :
    Summable (fun v : ℤ × ℤ => actualSchwartz side z hz hzB (AtomicTriangular.triangularPoint v)) := by
  exact (pairSchwartz_lattice_summable _ _).const_smul (normalizingDen z)⁻¹
lemma actualSchwartz_lattice_poisson {z : ℝ} (hz : 0<z) (hzB : z ≤ Z) :
    (∑' v : ℤ × ℤ, actualSchwartz 0 z hz hzB (AtomicTriangular.triangularPoint v))=
      ∑' v : ℤ × ℤ, actualSchwartz 1 z hz hzB (AtomicTriangular.triangularPoint v) := by
  simp only [actualSchwartz,smul_apply,smul_eq_mul,tsum_mul_left]
  rw [pairSchwartz_lattice_poisson]
  rfl
end AtomicTriangular.Construction
end

noncomputable section
open scoped BigOperators SchwartzMap
open Complex
namespace AtomicTriangular
lemma gaussian_eq_radial (α : ℝ) (x : Plane) :
    gaussian α x=Construction.gaussian (α/b) x := by
  unfold gaussian Construction.gaussian Construction.radial
  congr 1
  field_simp [b_pos.ne']
  rfl
lemma gaussian_lattice_summable {α : ℝ} (hα : 0<α) :
    Summable (fun v : ℤ × ℤ => gaussian α (triangularPoint v)) := by
  simp_rw [gaussian_eq_radial]
  exact Construction.lattice_gaussian_summable (div_pos hα b_pos)
lemma complex_gaussian_lattice (α : ℝ) :
    (∑' v : ℤ × ℤ, (gaussian α (triangularPoint v):ℂ))=
      TriangularUniversal.Theta.theta ((α/b:ℝ):ℂ) := by
  apply tsum_congr
  intro v
  rw [gaussian_eq_radial,Construction.gaussian,Construction.radial_triangularPoint,ofReal_exp]
  congr 1
  push_cast
  ring
lemma gaussian_lattice_theta {α : ℝ} (hα : 0<α) :
    (∑' v : ℤ × ℤ, gaussian α (triangularPoint v))=
      α⁻¹*∑' v : ℤ × ℤ, gaussian α⁻¹ (triangularPoint v) := by
  have ha0 : (α:ℂ)≠0 := by exact_mod_cast hα.ne'
  have hb0 : (b:ℂ)≠0 := by exact_mod_cast b_pos.ne'
  have hr := congrArg (fun r : ℝ => (r:ℂ)) b_sq
  push_cast at hr
  have he1 : (2:ℂ)/((Real.sqrt 3:ℂ)*((α/b:ℝ):ℂ))=((α⁻¹:ℝ):ℂ) := by
    unfold b
    push_cast
    field_simp
  have he2 : (4:ℂ)/(3*((α/b:ℝ):ℂ))=((α⁻¹/b:ℝ):ℂ) := by
    push_cast
    field_simp [ha0,hb0]
    linear_combination 4*hr
  have ht := TriangularUniversal.Theta.theta_transform (show 0<((α/b:ℝ):ℂ).re from div_pos hα b_pos)
  rw [he1,he2,←complex_gaussian_lattice,←complex_gaussian_lattice] at ht
  have hfirst := Complex.ofRealCLM.map_tsum (gaussian_lattice_summable hα)
  have hsecond := Complex.ofRealCLM.map_tsum (gaussian_lattice_summable (inv_pos.mpr hα))
  simp only [Complex.ofRealCLM_apply] at hfirst hsecond
  rw [←hfirst,←hsecond,←ofReal_mul] at ht
  exact_mod_cast ht

structure GaussianLatticePoisson {α : ℝ} (p : GaussianPair α) : Prop where
  first_summable : Summable (fun v : ℤ × ℤ => p.first (triangularPoint v))
  second_summable : Summable (fun v : ℤ × ℤ => p.second (triangularPoint v))
  poisson : (∑' v : ℤ × ℤ, p.first (triangularPoint v))=∑' v : ℤ × ℤ, p.second (triangularPoint v)
lemma largeGaussianPair_poisson {α : ℝ} (hα : 1 ≤ α) :
    GaussianLatticePoisson (largeGaussianPair hα) where
  first_summable := Construction.actualSchwartz_lattice_summable 0 _ _
  second_summable := Construction.actualSchwartz_lattice_summable 1 _ _
  poisson := Construction.actualSchwartz_lattice_poisson _ _
lemma reciprocalGaussianPair_poisson {α : ℝ} (hα : 0<α) (p : GaussianPair α⁻¹)
    (hp : GaussianLatticePoisson p) : GaussianLatticePoisson (reciprocalGaussianPair hα p) where
  first_summable := by
    change Summable (fun v => gaussianSchwartz α hα (triangularPoint v)-α⁻¹*p.second (triangularPoint v))
    simp_rw [gaussianSchwartz_apply]
    exact (gaussian_lattice_summable hα).sub (hp.second_summable.mul_left _)
  second_summable := by
    change Summable (fun v => α⁻¹*(gaussianSchwartz α⁻¹ (inv_pos.mpr hα) (triangularPoint v)-p.first (triangularPoint v)))
    simp_rw [gaussianSchwartz_apply]
    exact ((gaussian_lattice_summable (inv_pos.mpr hα)).sub hp.first_summable).mul_left _
  poisson := by
    change (∑' v, (gaussianSchwartz α hα (triangularPoint v)-α⁻¹*p.second (triangularPoint v)))=
      ∑' v, α⁻¹*(gaussianSchwartz α⁻¹ (inv_pos.mpr hα) (triangularPoint v)-p.first (triangularPoint v))
    simp_rw [gaussianSchwartz_apply]
    rw [(gaussian_lattice_summable hα).tsum_sub (hp.second_summable.mul_left _),
      tsum_mul_left,tsum_mul_left,(gaussian_lattice_summable (inv_pos.mpr hα)).tsum_sub hp.first_summable,
      gaussian_lattice_theta hα,hp.poisson,mul_sub]
lemma gaussianPair_poisson (α : ℝ) (hα : 0<α) : GaussianLatticePoisson (gaussianPair α hα) := by
  unfold gaussianPair
  split_ifs with h
  · exact largeGaussianPair_poisson h
  · exact reciprocalGaussianPair_poisson hα _ (largeGaussianPair_poisson _)
end AtomicTriangular
end

end OAI
