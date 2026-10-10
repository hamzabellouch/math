import OAI.Analysis.AncientFlat.Kernel.KernelChangingPair
import OAI.Analysis.AncientFlat.Kernel.SchwartzIBP

namespace OAI
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff SchwartzMap Laplacian
namespace FlatDuality
open BiharmonicKernel InnerProductSpace
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]
def adjointTime (c ε : ℝ) (s : ℝ) : ℝ := ε+c^2/16*(Real.exp (-s)-Real.exp (-1))
def adjointAmplitude (s : ℝ) : ℝ := Real.exp ((s-1)/2)
lemma adjointTime_bounds (c ε : ℝ) {s : ℝ} (hs : s ∈ Icc (0:ℝ) 1) :
    adjointTime c ε s ∈ Icc ε (ε+c^2/16) := by
  have h0 : 0≤c^2/16 := by positivity
  have h1 : Real.exp (-1)≤Real.exp (-s) := Real.exp_le_exp.mpr (by linarith [hs.2])
  have h2 : Real.exp (-s)≤1 := Real.exp_le_one_iff.mpr (by linarith [hs.1])
  dsimp [adjointTime]
  constructor
  · exact le_add_of_nonneg_right (mul_nonneg h0 (sub_nonneg.mpr h1))
  · nlinarith [Real.exp_pos (-1)]
lemma adjointAmplitude_bounds {s : ℝ} (hs : s ∈ Icc (0:ℝ) 1) :
    0<adjointAmplitude s ∧ adjointAmplitude s≤1 := by
  exact ⟨Real.exp_pos _,Real.exp_le_one_iff.mpr (by linarith [hs.2])⟩
lemma hasDerivAt_adjointTime (c ε s : ℝ) :
    HasDerivAt (adjointTime c ε) (-c^2/16*Real.exp (-s)) s := by
  convert! ((((hasDerivAt_id s).neg.exp).sub_const (Real.exp (-1))).const_mul (c^2/16)).const_add ε using 1
  dsimp only [adjointTime,id_eq,Pi.neg_apply]
  ring
lemma hasDerivAt_adjointAmplitude (s : ℝ) :
    HasDerivAt adjointAmplitude (adjointAmplitude s/2) s := by
  convert! ((((hasDerivAt_id s).sub_const 1).div_const 2).exp) using 1
  dsimp only [adjointAmplitude,id_eq]
  ring
lemma contDiff_adjointTime (c ε : ℝ) : ContDiff ℝ 1 (adjointTime c ε) := by unfold adjointTime; fun_prop
lemma contDiff_adjointAmplitude : ContDiff ℝ 1 adjointAmplitude := by unfold adjointAmplitude; fun_prop
lemma laplacian_translate (f : V → ℂ) (z : V) (x : V) :
    Δ (fun y => f (y-z)) x=Δ f (x-z) := by
  simp only [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis,iteratedFDeriv_comp_sub]
lemma bilaplacian_translate (f : V → ℂ) (z : V) (x : V) :
    Δ (Δ (fun y => f (y-z))) x=Δ (Δ f) (x-z) := by
  have he : Δ (fun y => f (y-z))=fun y => Δ f (y-z) := funext (laplacian_translate f z)
  rw [he,laplacian_translate]
variable [MeasurableSpace V] [BorelSpace V]
def adjointSchwartz (c ε s : ℝ) (z : V) (h : 0<adjointTime c ε s) : SchwartzMap V ℂ :=
  adjointAmplitude s • SchwartzMap.compSubConstCLM ℝ z (heatKernel _ h)
lemma adjointSchwartz_apply (c ε s : ℝ) (z : V) (h : 0<adjointTime c ε s) (x : V) :
    adjointSchwartz c ε s z h x=kernelTest (adjointTime c ε) adjointAmplitude z s x := by
  simp only [adjointSchwartz,smul_apply,SchwartzMap.compSubConstCLM_apply,
    heatKernel_eq_kernel,Complex.real_smul,kernelTest]
lemma adjointSchwartz_bilap (c ε s : ℝ) (z : V) (h : 0<adjointTime c ε s) (x : V) :
    (Δ (Δ (adjointSchwartz c ε s z h) : SchwartzMap V ℂ) : SchwartzMap V ℂ) x=
      (adjointAmplitude s : ℂ)*bilapKernel (adjointTime c ε s) (x-z) := by
  let φ := SchwartzMap.compSubConstCLM ℝ z (heatKernel (adjointTime c ε s) h)
  change (Δ (Δ ((adjointAmplitude s) • φ) : SchwartzMap V ℂ) : SchwartzMap V ℂ) x=_
  simp only [←SchwartzMap.laplacianCLM_eq',map_smul,smul_apply]
  rw [Complex.real_smul]
  congr 1
  have he : (φ : V → ℂ)=fun y => kernel (adjointTime c ε s) (y-z) := by
    funext y
    exact congrFun (heatKernel_eq_kernel _ h) (y-z)
  change (Δ (Δ φ : SchwartzMap V ℂ) : SchwartzMap V ℂ) x=_
  simp only [SchwartzMap.laplacian_apply]
  have he' : ((Δ φ : SchwartzMap V ℂ) : V → ℂ)=Δ (φ : V → ℂ) :=
    funext (SchwartzMap.laplacian_apply φ)
  rw [he',he,bilaplacian_translate]
  rfl
lemma adjointSchwartz_equation (c ε s : ℝ) (z : V) (h : 0<adjointTime c ε s) (x : V) :
    kernelTestDeriv (adjointTime c ε) adjointAmplitude z s x=
      ((c^2*Real.exp (-s)/16 : ℝ) : ℂ)*(Δ (Δ (adjointSchwartz c ε s z h) : SchwartzMap V ℂ) : SchwartzMap V ℂ) x+
      (1/2:ℂ)*adjointSchwartz c ε s z h x := by
  rw [adjointSchwartz_apply,adjointSchwartz_bilap]
  simp only [kernelTestDeriv,kernelTest,(hasDerivAt_adjointTime c ε s).deriv,
    (hasDerivAt_adjointAmplitude s).deriv,Complex.ofReal_div,Complex.ofReal_mul,
    Complex.ofReal_neg,Complex.ofReal_pow,Complex.ofReal_ofNat]
  ring
end FlatDuality

end

end OAI
