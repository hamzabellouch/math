import Mathlib
import OAI.Analysis.Conductivity.Variational.ParametricSpatialDerivative

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology Matrix
open scoped Matrix.Norms.Elementwise
variable {P E : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [ProperSpace P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]

omit [ProperSpace P] [ProperSpace E] in
lemma wallDerivative_parametric_smooth {f : P×(E×ℝ) → ℝ}
    (hf : ContDiff ℝ (↑(⊤:ℕ∞)) f) :
    ContDiff ℝ (↑(⊤:ℕ∞)) (fun q : P×(E×ℝ) => wallDerivative (fun x => f (q.1,x)) q.2) :=
  (spatialFDeriv_smooth hf).clm_apply contDiff_const

omit [ProperSpace P] [ProperSpace E] in
lemma wallAlong_parametric_smooth (d : E) {f : P×(E×ℝ) → ℝ}
    (hf : ContDiff ℝ (↑(⊤:ℕ∞)) f) :
    ContDiff ℝ (↑(⊤:ℕ∞)) (fun q : P×(E×ℝ) => wallAlong d (fun x => f (q.1,x)) q.2) :=
  (spatialFDeriv_smooth hf).clm_apply contDiff_const

lemma wallPrimitive_parametric_smooth {f : P×(E×ℝ) → ℝ}
    (hf : ContDiff ℝ (↑(⊤:ℕ∞)) f) :
    ContDiff ℝ (↑(⊤:ℕ∞)) (fun q : P×(E×ℝ) => wallPrimitive (fun x => f (q.1,x)) q.2) := by
  apply contDiff_snd.snd.mul
  apply contDiff_compact_integral (μ:=volume) (K:=Icc (0:ℝ) 1)
    (F:=fun z : (P×(E×ℝ))×ℝ => f (z.1.1,(z.1.2.1,z.2*z.1.2.2))) _ isCompact_Icc
  exact hf.comp (contDiff_fst.fst.prodMk (contDiff_fst.snd.fst.prodMk
    (contDiff_snd.mul contDiff_fst.snd.snd)))

lemma wallQuotient_parametric_smooth {f : P×(E×ℝ) → ℝ}
    (hf : ContDiff ℝ (↑(⊤:ℕ∞)) f) :
    ContDiff ℝ (↑(⊤:ℕ∞)) (fun q : P×(E×ℝ) => wallQuotient (fun x => f (q.1,x)) q.2) := by
  apply contDiff_compact_integral (μ:=volume) (K:=Icc (0:ℝ) 1)
    (F:=fun z : (P×(E×ℝ))×ℝ => wallDerivative (fun x => f (z.1.1,x))
      (z.1.2.1,z.2*z.1.2.2)) _ isCompact_Icc
  exact (wallDerivative_parametric_smooth hf).comp
    (contDiff_fst.fst.prodMk (contDiff_fst.snd.fst.prodMk
      (contDiff_snd.mul contDiff_fst.snd.snd)))

lemma wallParticularNumerator_parametric_smooth (d : E) {v r₁ r₂ : P×(E×ℝ) → ℝ}
    (hv : ContDiff ℝ (↑(⊤:ℕ∞)) v) (h₁ : ContDiff ℝ (↑(⊤:ℕ∞)) r₁)
    (h₂ : ContDiff ℝ (↑(⊤:ℕ∞)) r₂) :
    ContDiff ℝ (↑(⊤:ℕ∞)) (fun q : P×(E×ℝ) =>
      wallParticularNumerator d (fun x => v (q.1,x)) (fun x => r₁ (q.1,x)) (fun x => r₂ (q.1,x)) q.2) := by
  exact (wallPrimitive_parametric_smooth (h₂.sub (wallAlong_parametric_smooth d
    ((wallPrimitive_parametric_smooth h₁).mul (wallDerivative_parametric_smooth hv))))).sub
    ((wallPrimitive_parametric_smooth h₁).mul (wallAlong_parametric_smooth d hv))

omit [ProperSpace P] [ProperSpace E] in
lemma wallHomogeneousNumerator_parametric_smooth (d : E) {v : P×(E×ℝ) → ℝ} {a : P×E → ℝ}
    (hv : ContDiff ℝ (↑(⊤:ℕ∞)) v) (ha : ContDiff ℝ (↑(⊤:ℕ∞)) a) :
    ContDiff ℝ (↑(⊤:ℕ∞)) (fun q : P×(E×ℝ) =>
      wallHomogeneousNumerator d (fun x => v (q.1,x)) (fun x => a (q.1,x)) q.2) := by
  have hA : ContDiff ℝ (↑(⊤:ℕ∞)) (fun q : P×(E×ℝ) => a (q.1,q.2.1)) :=
    ha.comp (contDiff_fst.prodMk contDiff_snd.fst)
  have hm : ContDiff ℝ (↑(⊤:ℕ∞)) (fun q : P×(E×ℝ) => (q.1,(q.2.1,(0:ℝ)))) :=
    contDiff_fst.prodMk (contDiff_snd.fst.prodMk contDiff_const)
  have hs := wallAlong_parametric_smooth d hv
  exact ((contDiff_const.mul hA).mul (hs.sub (hs.comp hm))).sub
    ((wallAlong_parametric_smooth d hA).mul (hv.sub (hv.comp hm)))

lemma parametric_smooth_wall_cutoff_ratio {χ : E×ℝ → ℝ} {f g : P×(E×ℝ) → ℝ}
    (hχ : ContDiff ℝ (↑(⊤:ℕ∞)) χ) (hf : ContDiff ℝ (↑(⊤:ℕ∞)) f)
    (hg : ContDiff ℝ (↑(⊤:ℕ∞)) g) {V : Set P} (hV : IsOpen V)
    (hne : ∀ p∈V,∀ x∈tsupport χ,wallQuotient (fun y => g (p,y)) x≠0) :
    ContDiffOn ℝ (↑(⊤:ℕ∞)) (fun q : P×(E×ℝ) =>
      χ q.2*(wallQuotient (fun x => f (q.1,x)) q.2 / wallQuotient (fun x => g (q.1,x)) q.2))
      (V×ˢuniv) := by
  apply (hV.prod isOpen_univ).contDiffOn_iff.mpr
  intro q hq
  by_cases hx : q.2∈tsupport χ
  · exact (hχ.comp contDiff_snd).contDiffAt.mul
      ((wallQuotient_parametric_smooth hf).contDiffAt.div
        (wallQuotient_parametric_smooth hg).contDiffAt (hne q.1 hq.1 q.2 hx))
  · apply (show ContDiffAt ℝ (↑(⊤:ℕ∞)) (fun _ : P×(E×ℝ) => (0:ℝ)) q from
      contDiffAt_const).congr_of_eventuallyEq
    have he := continuous_snd.continuousAt.eventually (notMem_tsupport_iff_eventuallyEq.mp hx)
    filter_upwards [he] with z hz
    change χ z.2=0 at hz
    simp only [hz,zero_mul]

end ScalarConductivity

end

end OAI
