import Mathlib
import OAI.Analysis.Conductivity.Variational.FiberTangentialDerivative

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]

omit [ProperSpace E] in
lemma wallAlong_pullback (d : E) {f : E → ℝ} (hf : Differentiable ℝ f) (p : E×ℝ) :
    wallAlong d (fun q : E×ℝ => f q.1) p=fderiv ℝ f p.1 d := by
  have hh := (hf p.1).hasFDerivAt.comp p (hasFDerivAt_fst (𝕜 := ℝ) (p := p))
  simp only [Function.comp_def] at hh
  rw [wallAlong,hh.fderiv]
  rfl

omit [ProperSpace E] in
lemma wallAlong_normal (d : E) {f : ℝ → ℝ} (hf : Differentiable ℝ f) (p : E×ℝ) :
    wallAlong d (fun q : E×ℝ => f q.2) p=0 := by
  have hh := (hf p.2).hasFDerivAt.comp p (hasFDerivAt_snd (𝕜 := ℝ) (p := p))
  simp only [Function.comp_def] at hh
  rw [wallAlong,hh.fderiv]
  simp

omit [ProperSpace E] in
lemma wallAlong_sub (d : E) {f g : E×ℝ → ℝ}
    (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) (p : E×ℝ) :
    wallAlong d (fun q => f q-g q) p=wallAlong d f p-wallAlong d g p := by
  simp only [wallAlong,fderiv_fun_sub (hf p) (hg p),sub_apply]

omit [ProperSpace E] in
lemma wallAlong_opNorm_bound (d : E) {f : E×ℝ → ℝ} {M : ℝ}
    (h : ∀ p,‖fderiv ℝ f p‖≤M) (p : E×ℝ) : |wallAlong d f p|≤M*‖d‖ := by
  have hh := (fderiv ℝ f p).le_opNorm (d,0)
  simp only [Prod.norm_def,norm_zero,max_eq_left (norm_nonneg d),Real.norm_eq_abs] at hh
  exact hh.trans (mul_le_mul_of_nonneg_right (h p) (norm_nonneg d))

omit [ProperSpace E] in
lemma fderiv_normal_tangent (f : E×ℝ → ℝ) (p v : E×ℝ) :
    fderiv ℝ f p v=wallAlong v.1 f p+v.2*wallDerivative f p := by
  have he : v=(v.1,0)+v.2 • ((0:E),1) := by ext <;> simp
  calc
    _ = fderiv ℝ f p ((v.1,0)+v.2 • ((0:E),1)) := congrArg (fderiv ℝ f p) he
    _ = _ := by simp only [map_add,map_smul,smul_eq_mul,wallAlong,wallDerivative]

theorem compact_fiber_decomposition_C1 {a b : ℝ} (hab : a<b)
    {f : E×ℝ → ℝ} (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f)
    (hs : HasCompactSupport f) (hv : ∀ p∈tsupport f,p.2∈Ioo a b)
    {η : ℝ → ℝ} (hη : ContDiff ℝ (↑(⊤ : ℕ∞)) η) (hsη : HasCompactSupport η)
    (hvη : tsupport η⊆Ioo a b) (hiη : (∫ t in a..b,η t)=1)
    {M K : ℝ} (hM : 0≤M) (hK : 0≤K)
    (hb : ∀ p,|f p|≤M) (hdb : ∀ p,‖fderiv ℝ f p‖≤M) (hηb : ∀ t,|η t|≤K) :
    ∃ F : E×ℝ → ℝ,ContDiff ℝ (↑(⊤ : ℕ∞)) F ∧ HasCompactSupport F ∧
      (∀ p,wallDerivative F p+η p.2*compactFiberMarginal a b f p.1=f p) ∧
      tsupport F⊆(Prod.fst '' tsupport f) ×ˢ Icc a b ∧
      (∀ p,|F p|≤(b-a)*(1+K*(b-a))*M) ∧
      (∀ p,‖fderiv ℝ F p‖≤(b-a+1)*(1+K*(b-a))*M) := by
  obtain ⟨F,hF,hsF,heF,htF,hbF,hdbF,hformula⟩ := compact_fiber_decomposition_bounded hab hf hs
    (fun p hp => hv p (subset_tsupport f hp)) hη hsη hvη hiη hM hK hb hηb
  let R := compactFiberMarginal a b f
  have hR := compactFiberMarginal_smooth hab.le hf
  let g : E×ℝ → ℝ := fun p => f p-η p.2*R p.1
  have hg : ContDiff ℝ (↑(⊤ : ℕ∞)) g := hf.sub ((hη.comp contDiff_snd).mul (hR.comp contDiff_fst))
  have hvG : ∀ p∈tsupport g,p.2∈Ioo a b := by
    intro p hp
    rcases tsupport_sub _ _ hp with hp|hp
    · exact hv p hp
    · exact hvη ((tsupport_comp_subset_preimage η continuous_snd)
        (tsupport_mul_subset_left hp))
  have hzG : ∀ x,(∫ t in a..b,g (x,t))=0 := by
    intro x
    rw [show (fun t => g (x,t))=(fun t => f (x,t)-η t*R x) from rfl,
      intervalIntegral.integral_sub (f := fun t => f (x,t)) (g := fun t => η t*R x)
        ((hf.continuous.comp (continuous_const.prodMk continuous_id)).intervalIntegrable a b)
        ((hη.continuous.mul continuous_const).intervalIntegrable a b)]
    rw [intervalIntegral.integral_mul_const,hiη,one_mul]
    exact sub_self _
  have hdg (d : E) (p : E×ℝ) : wallAlong d g p=
      wallAlong d f p-η p.2*compactFiberMarginal a b (wallAlong d f) p.1 := by
    change wallAlong d (fun p => f p-(η ∘ Prod.snd) p*(compactFiberMarginal a b f ∘ Prod.fst) p) p = _
    rw [wallAlong_sub d (hf.differentiable (by simp))
        (((hη.comp contDiff_snd).mul (hR.comp contDiff_fst)).differentiable (by simp)),
      wallAlong_mul d ((hη.comp contDiff_snd).differentiable (by simp))
        ((hR.comp contDiff_fst).differentiable (by simp))]
    dsimp only [Function.comp_def]
    rw [wallAlong_normal d (hη.differentiable (by simp)),
      wallAlong_pullback d (hR.differentiable (by simp)),compactFiberMarginal_fderiv d hf]
    ring
  have hbg (d : E) (p : E×ℝ) : |wallAlong d g p|≤(1+K*(b-a))*M*‖d‖ := by
    rw [hdg]
    calc
      _ ≤ |wallAlong d f p|+|η p.2| * |compactFiberMarginal a b (wallAlong d f) p.1| := by
        simpa only [abs_mul] using abs_sub (wallAlong d f p) (η p.2*compactFiberMarginal a b (wallAlong d f) p.1)
      _ ≤ M*‖d‖+K*((b-a)*(M*‖d‖)) := add_le_add (wallAlong_opNorm_bound d hdb p)
        (mul_le_mul (hηb p.2) (compactFiberMarginal_abs_bound hab.le (wallAlong_opNorm_bound d hdb) p.1)
          (abs_nonneg _) hK)
      _ = _ := by ring
  have htang (d : E) (p : E×ℝ) : |wallAlong d F p|≤(b-a)*(1+K*(b-a))*M*‖d‖ := by
    rw [hformula]
    simpa only [mul_assoc] using fiberPrimitive_tangential_bound d hab.le hg hvG hzG
      (by positivity : 0≤(1+K*(b-a))*M*‖d‖) (hbg d) p
  refine ⟨F,hF,hsF,heF,htF,hbF,?_⟩
  intro p
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  rw [Real.norm_eq_abs,fderiv_normal_tangent]
  calc
    _ ≤ |wallAlong v.1 F p|+|v.2| * |wallDerivative F p| := by
      simpa only [abs_mul] using abs_add_le (wallAlong v.1 F p) (v.2*wallDerivative F p)
    _ ≤ (b-a)*(1+K*(b-a))*M*‖v.1‖+|v.2| *((1+K*(b-a))*M) :=
      add_le_add (htang v.1 p) (mul_le_mul_of_nonneg_left (hdbF p) (abs_nonneg _))
    _ ≤ (b-a)*(1+K*(b-a))*M*‖v‖+‖v‖*((1+K*(b-a))*M) := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left (norm_fst_le v) (by positivity)
      · exact mul_le_mul_of_nonneg_right (by simpa only [Real.norm_eq_abs] using norm_snd_le v) (by positivity)
    _ = _ := by ring

end ScalarConductivity

end

end OAI
