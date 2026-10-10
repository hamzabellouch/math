import Mathlib
import OAI.Analysis.Conductivity.Variational.CompactParametricIntegral

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]

def wallDerivative (f : E × ℝ → ℝ) (p : E × ℝ) : ℝ :=
  fderiv ℝ f p (0,1)

def wallQuotient (f : E × ℝ → ℝ) (p : E × ℝ) : ℝ :=
  ∫ t in Icc (0:ℝ) 1, wallDerivative f (p.1,t*p.2)

omit [ProperSpace E] in
lemma wallDerivative_smooth {f : E × ℝ → ℝ}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (wallDerivative f) :=
  (hf.fderiv_right (by simp)).clm_apply contDiff_const

lemma wallQuotient_smooth {f : E × ℝ → ℝ}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (wallQuotient f) := by
  change ContDiff ℝ (↑(⊤ : ℕ∞)) (fun p : E × ℝ =>
    ∫ t in Icc (0:ℝ) 1, wallDerivative f (p.1,t*p.2))
  apply contDiff_compact_integral (μ := volume)
    (F := fun p : (E × ℝ) × ℝ => wallDerivative f (p.1.1,p.2*p.1.2))
    (K := Icc (0:ℝ) 1) _ isCompact_Icc
  exact (wallDerivative_smooth hf).comp
    (contDiff_fst.fst.prodMk (contDiff_snd.mul contDiff_fst.snd))

omit [ProperSpace E] in
lemma wallQuotient_identity {f : E × ℝ → ℝ}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (x : E) (z : ℝ) :
    f (x,z)-f (x,0)=z*wallQuotient f (x,z) := by
  have hd (t : ℝ) : HasDerivAt (fun q : ℝ => f (x,q*z))
      (z*wallDerivative f (x,t*z)) t := by
    have h := (hf.differentiable (by simp) (x,t*z)).hasFDerivAt.comp_hasDerivAt t
      ((hasDerivAt_const t x).prodMk ((hasDerivAt_id t).mul_const z))
    have he : (0,z) = z • ((0:E),1) := by simp
    simpa only [Function.comp_def,id_eq,one_mul,wallDerivative,he,map_smul,smul_eq_mul] using h
  have hc : Continuous (fun t : ℝ => z*wallDerivative f (x,t*z)) :=
    continuous_const.mul ((wallDerivative_smooth hf).continuous.comp
      (continuous_const.prodMk (continuous_id.mul continuous_const)))
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := 1)
    (fun t _ => hd t) (hc.intervalIntegrable _ _)
  simp only [one_mul,zero_mul] at h
  rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1),
    ←integral_Icc_eq_integral_Ioc,integral_const_mul] at h
  exact h.symm

omit [ProperSpace E] in
lemma wallQuotient_zero {f : E × ℝ → ℝ} (x : E) :
    wallQuotient f (x,0)=wallDerivative f (x,0) := by
  simp [wallQuotient]

lemma smooth_wall_division {f : E × ℝ → ℝ}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (hzero : ∀ x, f (x,0)=0) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (wallQuotient f) ∧
      ∀ p : E × ℝ, f p=p.2*wallQuotient f p := by
  refine ⟨wallQuotient_smooth hf,?_⟩
  rintro ⟨x,z⟩
  simpa only [hzero,sub_zero] using wallQuotient_identity hf x z

lemma smooth_wall_double_division {f : E × ℝ → ℝ}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (hzero : ∀ x, f (x,0)=0)
    (hdzero : ∀ x, wallDerivative f (x,0)=0) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (wallQuotient (wallQuotient f)) ∧
      ∀ p : E × ℝ, f p=p.2^2*wallQuotient (wallQuotient f) p := by
  have hq := smooth_wall_division hf hzero
  have hqq := smooth_wall_division hq.1 (fun x => (wallQuotient_zero x).trans (hdzero x))
  refine ⟨hqq.1,fun p => ?_⟩
  rw [hq.2 p,hqq.2 p]
  ring

lemma wall_ratio_extension {f g : E × ℝ → ℝ}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (hg : ContDiff ℝ (↑(⊤ : ℕ∞)) g)
    (hf0 : ∀ x, f (x,0)=0) (hg0 : ∀ x, g (x,0)=0)
    (x : E) (hdg : wallDerivative g (x,0)≠0) :
    ContDiffAt ℝ (↑(⊤ : ℕ∞)) (fun p => wallQuotient f p/wallQuotient g p) (x,0) ∧
      ∀ p : E × ℝ, p.2≠0 → wallQuotient f p/wallQuotient g p=f p/g p := by
  refine ⟨(wallQuotient_smooth hf).contDiffAt.div (wallQuotient_smooth hg).contDiffAt
    (by simpa only [wallQuotient_zero] using hdg),?_⟩
  intro p hp
  rw [(smooth_wall_division hf hf0).2 p,(smooth_wall_division hg hg0).2 p]
  exact (mul_div_mul_left _ _ hp).symm

end ScalarConductivity

end

end OAI
