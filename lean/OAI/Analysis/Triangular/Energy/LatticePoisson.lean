import OAI.Analysis.Triangular.Energy.Theta
import OAI.Analysis.Triangular.Schwartz.FourierPair
import OAI.Analysis.Triangular.Envelope.Analytic
import OAI.Analysis.Triangular.Lattice.LatticeGeometry

namespace OAI

noncomputable section
open scoped BigOperators FourierTransform SchwartzMap
open Complex
namespace AtomicTriangular.Construction
lemma radial_triangularPoint (v : ℤ × ℤ) :
    radial (AtomicTriangular.triangularPoint v)=(v.1:ℝ)^2+(v.1:ℝ)*v.2+(v.2:ℝ)^2 :=
  AtomicTriangular.triangularPoint_norm_sq v.1 v.2
lemma lattice_gaussian_summable {k : ℝ} (hk : 0<k) :
    Summable (fun v : ℤ × ℤ => gaussian k (AtomicTriangular.triangularPoint v)) := by
  have H := (TriangularUniversal.Theta.triangular_summable (show 0<(k:ℂ).re from hk)).norm
  convert H using 1
  ext v
  rw [gaussian,radial_triangularPoint,Complex.norm_exp]
  congr 1
  simp [pow_two,mul_re,mul_im]
lemma atom_lattice_summable {k : ℝ} (hk : 0<k) :
    Summable (fun v : ℤ × ℤ => atomFunction k (AtomicTriangular.triangularPoint v)) := by
  exact Summable.of_norm ((lattice_gaussian_summable hk).of_nonneg_of_le
    (fun _ => norm_nonneg _) (fun v => atomFunction_bound k _))
def dualAtomFunction (q : Fin 2) (x : Plane) : C(Spectrum,ℂ) :=
  exp (-(Real.pi:ℂ)*h*(radial x:ℂ)) • transformedFunction (damping q) h (damping_pos q) (radial x:ℂ)
lemma dualAtomFunction_apply (q : Fin 2) (x : Plane) (t : Spectrum) :
    dualAtomFunction q x t=exp (-(Real.pi:ℂ)*h*(radial x:ℂ))*transformedWave (damping q) h t.val (radial x:ℂ) := by
  simp only [dualAtomFunction,ContinuousMap.smul_apply,smul_eq_mul,transformedFunction_apply]
lemma dualAtomFunction_bound (q : Fin 2) (x : Plane) :
    ‖dualAtomFunction q x‖ ≤ ‖lambdaFunction (damping q) (damping_pos q)‖*Real.exp (-radial x) := by
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro t
  have ht : |t.val|≤5/6 := abs_le.mpr t.property
  have hx := damping_Xwave_lower q (abs_nonneg t.val) ht
  have he : Xwave (damping q) |t.val|=Xwave (damping q) t.val := by simp [Xwave,waveDen]
  rw [he] at hx
  have hl : ‖lambda (damping q) t.val‖ ≤ ‖lambdaFunction (damping q) (damping_pos q)‖ :=
    (lambdaFunction (damping q) (damping_pos q)).norm_coe_le_norm t
  rw [dualAtomFunction_apply,transformedWave,norm_mul,norm_mul,norm_exp,norm_exp]
  have h1 : (-(Real.pi:ℂ)*h*(radial x:ℂ)).re=-Real.pi*h*radial x := by simp
  have h2 : (I*Real.pi*zeta (damping q) h t.val*(radial x:ℂ)).re=
      -Real.pi*(damping q*Xwave (damping q) t.val-h)*radial x := by
    rw [mul_re]
    simp only [ofReal_re,ofReal_im,mul_zero,sub_zero,wavePhase_re]
  rw [h1,h2]
  calc
    _ = ‖lambda (damping q) t.val‖*Real.exp (-(Real.pi*damping q*Xwave (damping q) t.val)*radial x) := by
      rw [mul_left_comm,←Real.exp_add]
      congr 2
      ring
    _ ≤ _ := mul_le_mul hl (Real.exp_le_exp.mpr (by nlinarith [show 0 ≤ radial x from mul_nonneg b_pos.le (sq_nonneg ‖x‖)])) (Real.exp_pos _).le (norm_nonneg _)
lemma dualAtom_lattice_summable (q : Fin 2) :
    Summable (fun v : ℤ × ℤ => dualAtomFunction q (AtomicTriangular.triangularPoint v)) := by
  have hs := lattice_gaussian_summable (inv_pos.mpr Real.pi_pos)
  have he (v : ℤ × ℤ) : gaussian Real.pi⁻¹ (AtomicTriangular.triangularPoint v)=
      Real.exp (-radial (AtomicTriangular.triangularPoint v)) := by
    unfold gaussian
    congr 1
    field_simp
  simp_rw [he] at hs
  exact Summable.of_norm ((hs.mul_left ‖lambdaFunction (damping q) (damping_pos q)‖).of_nonneg_of_le
    (fun _ => norm_nonneg _) (fun v => dualAtomFunction_bound q _))
lemma dualAtom_gaussian (q : Fin 2) (x : Plane) (t : Spectrum) :
    dualAtomFunction q x t=(spectralParameter (damping q) t.val)⁻¹*
      exp (-(Real.pi:ℂ)*(‖x‖:ℂ)^2/spectralParameter (damping q) t.val) := by
  rw [spectralParameter_inv (damping_pos q),spectral_exponent (damping_pos q) h]
  rw [dualAtomFunction_apply,transformedWave,exp_add]
  ring
lemma scalar_lattice_poisson (q : Fin 2) (t : Spectrum) :
    (∑' v : ℤ × ℤ, atomFunction (damping q) (AtomicTriangular.triangularPoint v) t)=
      ∑' v : ℤ × ℤ, dualAtomFunction q (AtomicTriangular.triangularPoint v) t := by
  let c : ℂ := (damping q:ℂ)-I*(t.val:ℂ)
  have hc : 0<c.re := by simpa [c] using damping_pos q
  have hc0 : c≠0 := by intro he; simp [he] at hc
  have hb : (b:ℂ)≠0 := by exact_mod_cast b_pos.ne'
  have hr := congrArg (fun r : ℝ => (r:ℂ)) b_sq
  push_cast at hr
  have hatom (v : ℤ × ℤ) : atomFunction (damping q) (AtomicTriangular.triangularPoint v) t=
      exp (-Real.pi*c*((v.1:ℂ)^2+(v.1:ℂ)*v.2+(v.2:ℂ)^2)) := by
    rw [atomFunction_apply,←exp_add,radial_triangularPoint]
    congr 1
    dsimp [c]
    push_cast
    ring
  have hlam : (spectralParameter (damping q) t.val)⁻¹=2/((Real.sqrt 3:ℂ)*c) := by
    change ((b:ℂ)*c)⁻¹=_
    unfold b
    push_cast
    ring_nf
  have hdual (v : ℤ × ℤ) : dualAtomFunction q (AtomicTriangular.triangularPoint v) t=
      (2/((Real.sqrt 3:ℂ)*c))*exp (-Real.pi*(4/(3*c))*((v.1:ℂ)^2+(v.1:ℂ)*v.2+(v.2:ℂ)^2)) := by
    rw [dualAtom_gaussian,hlam]
    congr 1
    congr 1
    have hv := congrArg (fun r : ℝ => (r:ℂ)) (radial_triangularPoint v)
    dsimp [radial] at hv
    push_cast at hv
    change -(Real.pi:ℂ)*(‖AtomicTriangular.triangularPoint v‖:ℂ)^2/((b:ℂ)*c)=_
    field_simp [hb,hc0]
    linear_combination -(4:ℂ)*(b:ℂ)*hv + (4:ℂ)*(‖AtomicTriangular.triangularPoint v‖:ℂ)^2*hr
  simp_rw [hatom,hdual]
  rw [tsum_mul_left]
  exact TriangularUniversal.Theta.theta_transform hc
lemma atom_lattice_poisson (q : Fin 2) :
    (∑' v : ℤ × ℤ, atomFunction (damping q) (AtomicTriangular.triangularPoint v))=
      ∑' v : ℤ × ℤ, dualAtomFunction q (AtomicTriangular.triangularPoint v) := by
  ext t
  have h1 := (ContinuousMap.evalCLM ℂ t).map_tsum (atom_lattice_summable (damping_pos q))
  have h2 := (ContinuousMap.evalCLM ℂ t).map_tsum (dualAtom_lattice_summable q)
  change (∑' v : ℤ × ℤ, atomFunction (damping q) (AtomicTriangular.triangularPoint v)) t=
    ∑' v : ℤ × ℤ, atomFunction (damping q) (AtomicTriangular.triangularPoint v) t at h1
  change (∑' v : ℤ × ℤ, dualAtomFunction q (AtomicTriangular.triangularPoint v)) t=
    ∑' v : ℤ × ℤ, dualAtomFunction q (AtomicTriangular.triangularPoint v) t at h2
  rw [h1,h2,scalar_lattice_poisson]
end AtomicTriangular.Construction
end

end OAI
