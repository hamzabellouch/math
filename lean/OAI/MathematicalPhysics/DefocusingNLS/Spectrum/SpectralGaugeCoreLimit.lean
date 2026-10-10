import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralPhysicalGaugePair

namespace OAI

/-! The regular-core conditions pass to a continuous free physical solution. -/

open Set
namespace DefocusingNLS
local notation "E₄" => (ℂ × ℂ) × (ℂ × ℂ)

theorem spectralPhysicalGaugePair_core_of_open_eq (ell : ℕ) (L R : ℝ) (hLR : L < R)
    (Q f g : ℝ → ℂ) (X : ℝ → E₄)
    (hQ : ContinuousOn Q (Ico L R)) (hDQ : ContinuousOn (deriv Q) (Ico L R))
    (hf : ContinuousOn f (Ico L R)) (hg : ContinuousOn g (Ico L R))
    (hDg : ContinuousOn (deriv g) (Ico L R)) (hX : ContinuousOn X (Ico L R))
    (he : EqOn X (spectralPhysicalGaugePair Q f g) (Ioo L R))
    (hQL : Q L=1) (hDQL : deriv Q L=0) (hfL : f L=0)
    (hgL : deriv g L=(ell : ℂ)/(L : ℂ)*g L) :
    spectralFreeCoreBoundary ell L (X L)=0 := by
  have hcl : Ico L R ⊆ closure (Ioo L R) := by
    rw [closure_Ioo hLR.ne]
    exact Ico_subset_Icc_self
  have hp : EqOn (fun r => (X r).1.1) (fun r => Q r*(f r+Complex.I*g r)) (Ioo L R) := by
    intro r hr
    exact congrArg (fun v : E₄ => v.1.1) (he hr)
  have hm : EqOn (fun r => (X r).2.1) (fun r => star (Q r)*(f r-Complex.I*g r)) (Ioo L R) := by
    intro r hr
    exact congrArg (fun v : E₄ => v.2.1) (he hr)
  have hdc : EqOn (fun r => star (Q r)*(X r).1.2-Q r*(X r).2.2)
      (fun r => star (Q r)*deriv Q r*(f r+Complex.I*g r)-
        Q r*star (deriv Q r)*(f r-Complex.I*g r)+
        2*Complex.I*star (Q r)*Q r*deriv g r) (Ioo L R) := by
    intro r hr
    dsimp only
    rw [he hr]
    dsimp [spectralPhysicalGaugePair]
    ring
  have hpL := (hp.of_subset_closure hX.fst.fst
    (hQ.mul (hf.add (continuousOn_const.mul hg))) Ioo_subset_Ico_self hcl) ⟨le_rfl,hLR⟩
  have hmL := (hm.of_subset_closure hX.snd.fst
    (hQ.star.mul (hf.sub (continuousOn_const.mul hg))) Ioo_subset_Ico_self hcl) ⟨le_rfl,hLR⟩
  have hdL := (hdc.of_subset_closure
    ((hQ.star.mul hX.fst.snd).sub (hQ.mul hX.snd.snd))
    ((((hQ.star.mul hDQ).mul (hf.add (continuousOn_const.mul hg))).sub
      ((hQ.mul hDQ.star).mul (hf.sub (continuousOn_const.mul hg)))).add
      ((((continuousOn_const.mul hQ.star).mul hQ).mul hDg)))
    Ioo_subset_Ico_self hcl) ⟨le_rfl,hLR⟩
  simp only [hQL,hDQL,star_one,star_zero,one_mul,mul_one,zero_mul,mul_zero,
    sub_zero,zero_add] at hpL hmL hdL
  funext j
  fin_cases j
  · dsimp [spectralFreeCoreBoundary]
    rw [hpL,hmL,hfL]
    ring
  · dsimp [spectralFreeCoreBoundary]
    rw [hdL,hpL,hmL,hgL]
    ring

end DefocusingNLS

end OAI
