import OAI.Analysis.PlanarPacking.Theta
import OAI.Analysis.PlanarPacking.FourierPairSupport
import OAI.Analysis.PlanarPacking.HexLattice

namespace OAI

namespace SharpPlanar
open MeasureTheory
open scoped FourierTransform
noncomputable def latticePoint (p : ℤ×ℤ) : Plane := hexPoint (p.2,p.1)
lemma latticePoint_zero : latticePoint 0=0 := by
  ext i
  fin_cases i <;> simp [latticePoint,hexPoint]
lemma latticePoint_norm (p : ℤ×ℤ) :
    ‖latticePoint p‖^2=((p.2:ℝ)+(p.1:ℝ)/2)^2/b+b*(p.1:ℝ)^2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [latticePoint,hexPoint,Fin.sum_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one,
    PiLp.toLp_apply,Real.norm_eq_abs,sq_abs]
  rw [div_pow,mul_pow,Real.sq_sqrt b_pos.le]
lemma thetaKernel_lattice (a : ℂ) (p : ℤ×ℤ) :
    thetaKernel a b p.1 p.2=Complex.exp (-(Real.pi:ℂ)*a*(‖latticePoint p‖:ℂ)^2) := by
  rw [thetaKernel]
  congr 1
  have hh : ((p.2:ℂ)+(p.1:ℂ)/2)^2/(b:ℂ)+(b:ℂ)*(p.1:ℂ)^2=(‖latticePoint p‖:ℂ)^2 := by
    exact_mod_cast (latticePoint_norm p).symm
  rw [hh]
noncomputable def spectralParameter (t : ℝ) : ℂ := (b:ℂ)*((h:ℂ)-Complex.I*t)
lemma spectralParameter_re (t : ℝ) : (spectralParameter t).re=b*h := by
  simp [spectralParameter]
lemma spectralParameter_pos (t : ℝ) : 0<(spectralParameter t).re := by
  rw [spectralParameter_re]; exact mul_pos b_pos h_pos
lemma spectralParameter_ne (t : ℝ) : spectralParameter t≠0 := by
  intro hh
  have hpos:=spectralParameter_pos t
  simp [hh] at hpos
lemma gaussianCoeff_parameter (t : ℝ) : gaussianCoeff t=(Real.pi:ℂ)*spectralParameter t := by
  unfold gaussianCoeff spectralParameter
  ring
lemma spectralGaussian_lattice (t : ℝ) (p : ℤ×ℤ) :
    spectralGaussian t (latticePoint p)=thetaKernel (spectralParameter t) b p.1 p.2 := by
  rw [thetaKernel_lattice,spectralGaussian,gaussianCoeff_parameter]
  congr 1; ring
lemma spectralGaussian_fourier_lattice (t : ℝ) (p : ℤ×ℤ) :
    𝓕 (spectralGaussian t) (latticePoint p)=
    1/spectralParameter t*thetaKernel (1/spectralParameter t) b p.1 p.2 := by
  rw [thetaKernel_lattice]
  change 𝓕 (fun x : Plane => Complex.exp (-gaussianCoeff t*(‖x‖:ℂ)^2)) (latticePoint p)=_
  rw [poisson_gaussian_plane (gaussianCoeff_re_pos t),gaussianCoeff_parameter]
  have hp : (Real.pi:ℂ)≠0 := by exact_mod_cast Real.pi_ne_zero
  have he : (Real.pi:ℂ)/((Real.pi:ℂ)*spectralParameter t)=1/spectralParameter t := by field_simp
  rw [he]
  congr 2
  field_simp
lemma spectralGaussian_hex_poisson (t : ℝ) :
    (∑' p : ℤ×ℤ, spectralGaussian t (latticePoint p)) =
      ∑' p : ℤ×ℤ, 𝓕 (spectralGaussian t) (latticePoint p) := by
  simp_rw [spectralGaussian_lattice,spectralGaussian_fourier_lattice]
  rw [tsum_mul_left,theta_poisson (spectralParameter_pos t) b_pos]
noncomputable def latticeDamping (p : ℤ×ℤ) : ℝ :=
  Real.exp (-Real.pi*b*h*‖latticePoint p‖^2)
lemma latticeDamping_nonneg (p : ℤ×ℤ) : 0≤latticeDamping p := (Real.exp_pos _).le
lemma latticeDamping_summable : Summable latticeDamping := by
  change Summable (fun p : ℤ×ℤ => Real.exp (-Real.pi*b*h*‖latticePoint p‖^2))
  have hh: Summable (fun p : ℤ×ℤ => thetaKernel (spectralParameter 0) b p.1 p.2) :=
    thetaKernel_summable (spectralParameter_pos 0) b_pos
  have hn:=hh.norm
  simpa only [← spectralGaussian_lattice,spectralGaussian_norm,latticeDamping] using hn
lemma lattice_spectral_bound (t : ℝ) (p : ℤ×ℤ) :
    ‖spectralGaussian t (latticePoint p)‖=latticeDamping p := spectralGaussian_norm t _
lemma lattice_fourier_spectral_bound {t : ℝ} (ht : |t|≤1) (p : ℤ×ℤ) :
    ‖𝓕 (spectralGaussian t) (latticePoint p)‖≤1/(b*h)*latticeDamping p := by
  rw [spectralGaussian_fourier,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  have hs : 0≤b*‖latticePoint p‖^2 := mul_nonneg b_pos.le (sq_nonneg _)
  have hh:=kernelMoment_bound 0 hs ht
  norm_num only [pow_zero,mul_one] at hh
  have he : Real.exp (-kappa*(b*‖latticePoint p‖^2))≤1 := by
    rw [Real.exp_le_one_iff]; simpa only [neg_mul] using neg_nonpos.mpr (mul_nonneg kappa_pos.le hs)
  have hu: ‖kernelMoment 0 (b*‖latticePoint p‖^2) t‖≤1/(b*h) :=
    hh.trans (by nlinarith [mul_nonneg (one_div_pos.mpr (mul_pos b_pos h_pos)).le (sub_nonneg.mpr he)])
  have heq : Real.exp (-Real.pi*h*(b*‖latticePoint p‖^2))=latticeDamping p := by
    unfold latticeDamping; congr 1; ring
  rw [heq,mul_comm]
  exact mul_le_mul_of_nonneg_right hu (latticeDamping_nonneg p)
end SharpPlanar

end OAI
