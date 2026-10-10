import Mathlib
import OAI.Geometry.TamingCompatibility.DifferentialForms.FiberMap

namespace OAI

section
section
section

section
noncomputable section
namespace TamingCompatibility.EuclideanSobolevOperators
open MeasureTheory TemperedDistribution
open scoped SchwartzMap LineDeriv
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

def affineSchwartz (p : E) (r : ℝ) (hr : r ≠ 0) : 𝓢(E,ℂ) →L[ℂ] 𝓢(E,ℂ) :=
  (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (ContinuousLinearEquiv.smulLeft (R₁ := ℝ) (M₁ := E) (Units.mk0 r hr))).comp
      (SchwartzMap.compSubConstCLM ℂ (-p))

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma affineSchwartz_apply (p x : E) (r : ℝ) (hr : r ≠ 0) (φ : 𝓢(E,ℂ)) :
    affineSchwartz p r hr φ x = φ (r • x + p) := by
  simp [affineSchwartz, Units.smul_def]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma affineSchwartz_derivative (p : E) (r : ℝ) (hr : r ≠ 0) (φ : 𝓢(E,ℂ)) (v : E) :
    ∂_{v} (affineSchwartz p r hr φ) = r • affineSchwartz p r hr (∂_{v} φ) := by
  ext x
  rw [SchwartzMap.lineDerivOp_apply_eq_fderiv]
  have he : (affineSchwartz p r hr φ : E → ℂ) = fun y => φ (r • y + p) := by
    funext y
    exact affineSchwartz_apply p y r hr φ
  have hd := (φ.hasFDerivAt (r • x + p)).comp x
    (((hasFDerivAt_id x).const_smul r).add_const p)
  dsimp only [Function.comp_def, Pi.smul_apply, id_eq] at hd
  rw [he, hd.fderiv]
  simp [affineSchwartz_apply, SchwartzMap.lineDerivOp_apply_eq_fderiv]

def affineDistribution (p : E) (r : ℝ) (hr : r ≠ 0) : 𝓢'(E,F) →L[ℂ] 𝓢'(E,F) :=
  PointwiseConvergenceCLM.precomp F (affineSchwartz p r hr)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace F] in
lemma affineDistribution_apply (p : E) (r : ℝ) (hr : r ≠ 0)
    (u : 𝓢'(E,F)) (φ : 𝓢(E,ℂ)) :
    affineDistribution p r hr u φ = u (affineSchwartz p r hr φ) := rfl

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace F] in
lemma affineDistribution_derivative (p : E) (r : ℝ) (hr : r ≠ 0)
    (u : 𝓢'(E,F)) (v : E) :
    affineDistribution p r hr (∂_{v} u) = r • ∂_{v} (affineDistribution p r hr u) := by
  ext φ
  simp only [affineDistribution_apply, lineDerivOp_apply_apply,
    affineSchwartz_derivative, map_neg, smul_apply, smul_neg]
  congr 1
  exact ContinuousLinearMap.map_smul_of_tower (show 𝓢(E,ℂ) →L[ℂ] F from u) r _

omit [InnerProductSpace ℂ F] [CompleteSpace F] in
lemma memLp_comp_affine (p : E) (r : ℝ) (hr : r ≠ 0) {f : E → F}
    (hf : MemLp f 2 (volume : Measure E)) :
    MemLp (fun x => f (r • x + p)) 2 (volume : Measure E) := by
  have ht := hf.comp_measurePreserving (measurePreserving_add_right volume p)
  have hm : MemLp (fun x => f (x+p)) 2 (Measure.map (fun x : E => r • x) volume) := by
    rw [Measure.map_addHaar_smul volume hr]
    exact ht.smul_measure ENNReal.ofReal_ne_top
  exact hm.comp_of_map (measurable_const_smul r).aemeasurable

lemma affineDistribution_lp (p : E) (r : ℝ) (hr : r ≠ 0)
    (f : Lp F 2 (volume : Measure E)) :
    ∃ g : Lp F 2 (volume : Measure E),
      affineDistribution p r hr (f : 𝓢'(E,F)) = (g : 𝓢'(E,F)) := by
  let c : ℝ := |(r ^ Module.finrank ℝ E)⁻¹|
  let h : E → F := fun y => c • f (r⁻¹ • y + (-(r⁻¹ • p)))
  have hh : MemLp h 2 (volume : Measure E) :=
    (memLp_comp_affine (-(r⁻¹ • p)) r⁻¹ (inv_ne_zero hr) (Lp.memLp f)).const_smul c
  refine ⟨hh.toLp h, ?_⟩
  ext φ
  rw [affineDistribution_apply, Lp.toTemperedDistribution_apply,
    Lp.toTemperedDistribution_apply]
  have hi : (∫ y, φ y • (hh.toLp h) y) = ∫ y, φ y • h y := by
    apply integral_congr_ae
    filter_upwards [hh.coeFn_toLp] with y hy
    rw [hy]
  rw [hi]
  simp only [affineSchwartz_apply]
  let k : E → F := fun y => φ (y+p) • f (r⁻¹ • y)
  have he : (∫ x, φ (r • x+p) • f x) = c • ∫ y, k y := by
    have heq : (fun x => φ (r • x+p) • f x) = fun x => k (r • x) := by
      funext x
      simp [k, inv_smul_smul₀ hr]
    rw [heq, Measure.integral_comp_smul]
  rw [he]
  have ha := integral_add_right_eq_self (μ := (volume : Measure E)) (fun y : E => φ y • h y) p
  rw [← ha]
  rw [← integral_smul]
  apply integral_congr_ae
  filter_upwards [] with y
  change c • (φ (y+p) • f (r⁻¹ • y)) =
    φ (y+p) • (c • f (r⁻¹ • (y+p) + -(r⁻¹ • p)))
  rw [smul_add, add_neg_cancel_right]
  exact smul_comm c (φ (y+p)) _

lemma memSobolev_zero_affine (p : E) (r : ℝ) (hr : r ≠ 0)
    {u : 𝓢'(E,F)} (hu : MemSobolev 0 2 u) :
    MemSobolev 0 2 (affineDistribution p r hr u) := by
  obtain ⟨f, hf⟩ := hu
  have he : u = (f : 𝓢'(E,F)) := by simpa using hf
  rw [he]
  obtain ⟨g,hg⟩ := affineDistribution_lp p r hr f
  refine ⟨g, ?_⟩
  simpa using hg

theorem memSobolev_nat_affine (n : ℕ) (p : E) (r : ℝ) (hr : r ≠ 0)
    {u : 𝓢'(E,F)} (hu : MemSobolev n 2 u) :
    MemSobolev n 2 (affineDistribution p r hr u) := by
  induction n generalizing u with
  | zero =>
    simp only [Nat.cast_zero] at hu ⊢
    exact memSobolev_zero_affine p r hr hu
  | succ n ih =>
    have hu' : MemSobolev n 2 u := hu.mono (by exact_mod_cast Nat.le_succ n)
    have hd (i : Fin (Module.finrank ℝ E)) :
        MemSobolev n 2 (∂_{stdOrthonormalBasis ℝ E i} (affineDistribution p r hr u)) := by
      have hdu : MemSobolev n 2 (∂_{stdOrthonormalBasis ℝ E i} u) := by
        convert hu.lineDerivOp using 1
        simp
      have ha := (ih hdu).smul (r⁻¹:ℝ)
      rw [affineDistribution_derivative] at ha
      have hc (w : 𝓢'(E,F)) : ((r⁻¹:ℝ):ℂ) • (r • w) = w := by
        rw [← algebraMap_smul ℂ r w, show algebraMap ℝ ℂ r = (r:ℂ) from rfl,
          smul_smul, ← Complex.ofReal_mul, inv_mul_cancel₀ hr, Complex.ofReal_one, one_smul]
      rw [hc] at ha
      exact ha
    simpa using memSobolev_succ_of_derivatives (stdOrthonormalBasis ℝ E) (ih hu') hd

end TamingCompatibility.EuclideanSobolevOperators

end
end

section
noncomputable section
namespace TamingCompatibility.EuclideanSobolevOperators
open MeasureTheory TemperedDistribution Set LineDeriv
open scoped SchwartzMap LineDeriv
variable {E F G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] in
lemma affine_inverse_point (p x : E) {r : ℝ} (hr : r ≠ 0) :
    r⁻¹ • (r • x+p) + -(r⁻¹ • p) = x := by
  simp only [smul_add,smul_smul,inv_mul_cancel₀ hr,one_smul,add_neg_cancel_right]

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [CompleteSpace F] in
lemma affineDistribution_product (p : E) (r : ℝ) (hr : r ≠ 0)
    (g : 𝓢(E,ℂ)) (u : 𝓢'(E,F)) :
    affineDistribution p r hr (smulLeftCLM F g u) =
      smulLeftCLM F (affineSchwartz (-(r⁻¹ • p)) r⁻¹ (inv_ne_zero hr) g)
        (affineDistribution p r hr u) := by
  ext φ
  simp only [affineDistribution_apply,smulLeftCLM_apply_apply]
  congr 1
  ext x
  rw [affineSchwartz_apply]
  rw [SchwartzMap.smulLeftCLM_apply_apply g.hasTemperateGrowth,
    SchwartzMap.smulLeftCLM_apply_apply
      (affineSchwartz (-(r⁻¹ • p)) r⁻¹ (inv_ne_zero hr) g).hasTemperateGrowth]
  simp only [affineSchwartz_apply,affine_inverse_point p x hr]

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [CompleteSpace F] [CompleteSpace G] in
lemma affineDistribution_fiberMap (p : E) (r : ℝ) (hr : r ≠ 0)
    (K : F →L[ℂ] G) (u : 𝓢'(E,F)) :
    affineDistribution p r hr (HilbertSobolev.fiberMap K u) =
      HilbertSobolev.fiberMap K (affineDistribution p r hr u) := rfl

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [CompleteSpace F] in
lemma affineDistribution_inverse (p : E) (r : ℝ) (hr : r ≠ 0) (u : 𝓢'(E,F)) :
    affineDistribution (-(r⁻¹ • p)) r⁻¹ (inv_ne_zero hr) (affineDistribution p r hr u) = u := by
  ext φ
  simp only [affineDistribution_apply]
  congr 1
  ext x
  simp only [affineSchwartz_apply,affine_inverse_point p x hr]

def zoomDistribution (p : E) (r : ℝ) (hr : r ≠ 0) : 𝓢'(E,F) →L[ℂ] 𝓢'(E,F) :=
  affineDistribution (-(r⁻¹ • p)) r⁻¹ (inv_ne_zero hr)

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [CompleteSpace F] in
lemma zoomDistribution_product (p : E) (r : ℝ) (hr : r ≠ 0)
    (g : 𝓢(E,ℂ)) (u : 𝓢'(E,F)) :
    zoomDistribution p r hr (smulLeftCLM F g u) =
      smulLeftCLM F (affineSchwartz p r hr g) (zoomDistribution p r hr u) := by
  rw [zoomDistribution,affineDistribution_product]
  have hp : -((r⁻¹)⁻¹ • -(r⁻¹ • p)) = p := by
    simp only [inv_inv,smul_neg,smul_smul,mul_inv_cancel₀ hr,one_smul,neg_neg]
  rw [hp]
  simp only [inv_inv]

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [CompleteSpace F] in
lemma zoomDistribution_second (p : E) (r : ℝ) (hr : r ≠ 0)
    (v w : E) (u : 𝓢'(E,F)) :
    zoomDistribution p r hr (∂_{v} (∂_{w} u)) =
      (r⁻¹*r⁻¹) • ∂_{v} (∂_{w} (zoomDistribution p r hr u)) := by
  simp only [zoomDistribution,affineDistribution_derivative,lineDerivOp_smul,smul_smul]

lemma zoomDistribution_memSobolev (n : ℕ) (p : E) (r : ℝ) (hr : r ≠ 0)
    {u : 𝓢'(E,F)} (hu : MemSobolev n 2 u) :
    MemSobolev n 2 (zoomDistribution p r hr u) :=
  memSobolev_nat_affine n _ _ _ hu

end TamingCompatibility.EuclideanSobolevOperators

end
end

end
end
end

end OAI
