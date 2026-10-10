import Mathlib
import OAI.Analysis.Conductivity.Flux.CompactBoxDivergence
import OAI.Analysis.Conductivity.Flux.FiberDivergenceC1

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

variable {E P : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup P] [NormedSpace ℝ P]

def UniformC1Bound (f : E → ℝ) (M : ℝ) : Prop :=
  ∀ x,|f x|≤M ∧ ‖fderiv ℝ f x‖≤M

lemma UniformC1Bound.mono {f : E → ℝ} {M N : ℝ} (h : UniformC1Bound f M) (hMN : M≤N) :
    UniformC1Bound f N := fun x => ⟨(h x).1.trans hMN,(h x).2.trans hMN⟩

lemma UniformC1Bound.sub {f g : E → ℝ} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    {M N : ℝ} (hb : UniformC1Bound f M) (hc : UniformC1Bound g N) :
    UniformC1Bound (fun x => f x-g x) (M+N) := by
  intro x
  constructor
  · exact (abs_sub (f x) (g x)).trans (add_le_add (hb x).1 (hc x).1)
  · rw [fderiv_fun_sub (hf x) (hg x)]
    exact (norm_sub_le _ _).trans (add_le_add (hb x).2 (hc x).2)

lemma UniformC1Bound.mul {f g : E → ℝ} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    {M N : ℝ} (hM : 0≤M) (hN : 0≤N) (hb : UniformC1Bound f M) (hc : UniformC1Bound g N) :
    UniformC1Bound (fun x => f x*g x) (2*M*N) := by
  intro x
  constructor
  · rw [abs_mul]
    exact (mul_le_mul (hb x).1 (hc x).1 (abs_nonneg _) hM).trans (by nlinarith [mul_nonneg hM hN])
  · rw [fderiv_fun_mul (hf x) (hg x)]
    calc
      _ ≤ ‖f x • fderiv ℝ g x‖+‖g x • fderiv ℝ f x‖ := norm_add_le _ _
      _ = |f x| *‖fderiv ℝ g x‖+|g x| *‖fderiv ℝ f x‖ := by simp only [norm_smul,Real.norm_eq_abs]
      _ ≤ M*N+N*M := add_le_add
        (mul_le_mul (hb x).1 (hc x).2 (norm_nonneg _) hM)
        (mul_le_mul (hc x).1 (hb x).2 (norm_nonneg _) hN)
      _ = _ := by ring

lemma UniformC1Bound.comp_linear {f : E → ℝ} (hf : Differentiable ℝ f)
    {M : ℝ} (hM : 0≤M) (hb : UniformC1Bound f M)
    (L : P →L[ℝ] E) (hL : ‖L‖≤1) : UniformC1Bound (fun x => f (L x)) M := by
  intro x
  refine ⟨(hb (L x)).1,?_⟩
  have hd := (hf (L x)).hasFDerivAt.comp x L.hasFDerivAt
  simp only [Function.comp_def] at hd
  rw [hd.fderiv]
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    ((mul_le_mul (hb (L x)).2 hL (norm_nonneg _) hM).trans_eq (mul_one M))

lemma UniformC1Bound.comp_fst {f : E → ℝ} (hf : Differentiable ℝ f)
    {M : ℝ} (hM : 0≤M) (hb : UniformC1Bound f M) :
    UniformC1Bound (fun x : E×P => f x.1) M :=
  hb.comp_linear hf hM (ContinuousLinearMap.fst ℝ E P) (ContinuousLinearMap.norm_fst_le ..)

lemma UniformC1Bound.comp_snd {f : P → ℝ} (hf : Differentiable ℝ f)
    {M : ℝ} (hM : 0≤M) (hb : UniformC1Bound f M) :
    UniformC1Bound (fun x : E×P => f x.2) M :=
  hb.comp_linear hf hM (ContinuousLinearMap.snd ℝ E P) (ContinuousLinearMap.norm_snd_le ..)

lemma exists_uniformC1Bound {f : E → ℝ}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (hs : HasCompactSupport f) :
    ∃ M : ℝ,0<M ∧ UniformC1Bound f M := by
  obtain ⟨A,hA⟩ := hs.exists_bound_of_continuous hf.continuous
  obtain ⟨B,hB⟩ := (hs.fderiv ℝ).exists_bound_of_continuous (hf.continuous_fderiv (by simp))
  refine ⟨|A|+|B|+1,by positivity,?_⟩
  intro x
  constructor
  · have := hA x
    rw [Real.norm_eq_abs] at this
    exact this.trans (by linarith [le_abs_self A,abs_nonneg B])
  · exact (hB x).trans (by linarith [le_abs_self B,abs_nonneg A])

lemma compactFiberMarginal_C1Bound [ProperSpace E] {a b : ℝ} (hab : a≤b)
    {f : E×ℝ → ℝ} (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f)
    {M : ℝ} (hM : 0≤M) (hb : UniformC1Bound f M) :
    UniformC1Bound (compactFiberMarginal a b f) ((b-a)*M) := by
  intro x
  refine ⟨compactFiberMarginal_abs_bound hab (fun p => (hb p).1) x,?_⟩
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro d
  rw [Real.norm_eq_abs,compactFiberMarginal_fderiv d hf]
  simpa only [mul_assoc] using compactFiberMarginal_abs_bound hab
    (wallAlong_opNorm_bound d (fun p => (hb p).2)) x

lemma compact_scalar_primitive_bounded {a b : ℝ} (hab : a<b)
    {r : ℝ → ℝ} (hr : ContDiff ℝ (↑(⊤ : ℕ∞)) r)
    (hv : ∀ t,r t≠0 → t∈Ioo a b) (hz : (∫ t,r t)=0)
    {M : ℝ} (hM : 0≤M) (hb : ∀ t,|r t|≤M) :
    ∃ P : ℝ → ℝ,ContDiff ℝ (↑(⊤ : ℕ∞)) P ∧ HasCompactSupport P ∧
      (∀ t,deriv P t=r t) ∧ tsupport P⊆Icc a b ∧ UniformC1Bound P ((b-a+1)*M) := by
  let f : ℝ×ℝ → ℝ := fun p => r p.2
  have hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f := hr.comp contDiff_snd
  let P : ℝ → ℝ := fun t => fiberPrimitive a f (0,t)
  have hP : ContDiff ℝ (↑(⊤ : ℕ∞)) P :=
    (fiberPrimitive_smooth a hf).comp (contDiff_const.prodMk contDiff_id)
  have hvf : ∀ p,f p≠0 → p.2∈Ioo a b := fun p hp => hv p.2 hp
  have hzf : ∀ x,(∫ t in a..b,f (x,t))=0 := by
    intro x
    exact (interval_integral_eq_integral_of_support hab.le hv).trans hz
  have hs : Function.support P⊆Icc a b := by
    intro t ht
    refine ⟨?_,?_⟩
    · by_contra hn
      exact ht (fiberPrimitive_below hf.continuous hvf (0,t) (le_of_not_ge hn))
    · by_contra hn
      exact ht (fiberPrimitive_above hf.continuous hvf hzf (0,t) (le_of_not_ge hn))
  have hdP (t : ℝ) : deriv P t=r t := by
    have hd := (((fiberPrimitive_smooth a hf).differentiable (by simp)) (0,t)).hasFDerivAt.comp_hasDerivAt t
      ((hasDerivAt_const t (0:ℝ)).prodMk (hasDerivAt_id t))
    exact hd.deriv.trans (fiberPrimitive_derivative a hf (0,t))
  refine ⟨P,hP,HasCompactSupport.of_support_subset_isCompact isCompact_Icc hs,hdP,
    closure_minimal hs isClosed_Icc,?_⟩
  intro t
  constructor
  · exact (fiberPrimitive_abs_bound hab.le hf.continuous hvf hzf hM (fun p => hb p.2) (0,t)).trans
      (by nlinarith [sub_nonneg.mpr hab.le])
  · rw [←norm_deriv_eq_norm_fderiv,hdP,Real.norm_eq_abs]
    exact (hb t).trans (by nlinarith [sub_nonneg.mpr hab.le])

end ScalarConductivity

end

end OAI
