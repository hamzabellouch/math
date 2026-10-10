import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialJordanState

namespace OAI

/-! Smooth radial sources give smooth generalized modes away from the origin. -/

open Set
open scoped ContDiff
namespace DefocusingNLS
local notation "E₄" => (ℂ × ℂ) × (ℂ × ℂ)

theorem harmonicRadialSourcePair_contDiffOn (a b : ℝ) (m : ℕ)
    (Q f g F G : ℝ → ℂ) (eta lam : ℂ)
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (heq : IsHarmonicRadialSourcePair a b m Q eta lam f g F G)
    (R : ℝ) (hR : 0≤R) (hQ : ContDiffOn ℝ ∞ Q (Ioi R))
    (hF : ContDiffOn ℝ ∞ F (Ioi R)) (hG : ContDiffOn ℝ ∞ G (Ioi R)) :
    ContDiffOn ℝ ∞ f (Ioi R) ∧ ContDiffOn ℝ ∞ g (Ioi R) := by
  have hstate : ContDiffOn ℝ ∞ (harmonicRadialState f g) (Ioi R) := by
    intro r hr
    change R<r at hr
    let α := (R+r)/2
    let β := r+1
    have hα : R<α := by dsimp only [α]; linarith [hr]
    have hαr : α<r := by dsimp only [α]; linarith [hr]
    have hrβ : r<β := by dsimp only [β]; linarith
    have hsub : Icc α β ⊆ Ioi R := fun t ht => hα.trans_le ht.1
    have hbase := spectralPhysicalCircularField_contDiffOn
      (-2*(a : ℂ)+2*Complex.I*(b : ℂ)-2*lam)
      (-2*(a : ℂ)-2*Complex.I*(b : ℂ)-2*lam) eta m Q (Icc α β)
      (hQ.mono hsub) (fun t ht => (hR.trans_lt (hsub ht)).ne')
    have hFc : ContDiffOn ℝ ∞ (fun p : ℝ × E₄ => F p.1) (Icc α β ×ˢ univ) :=
      (hF.mono hsub).comp contDiff_fst.contDiffOn (fun _ hp => hp.1)
    have hGc : ContDiffOn ℝ ∞ (fun p : ℝ × E₄ => G p.1) (Icc α β ×ˢ univ) :=
      (hG.mono hsub).comp contDiff_fst.contDiffOn (fun _ hp => hp.1)
    have hsource : ContDiffOn ℝ ∞ (fun p : ℝ × E₄ =>
        (((0 : ℂ),-Complex.I*F p.1),((0 : ℂ),Complex.I*G p.1))) (Icc α β ×ˢ univ) :=
      (contDiffOn_const.prodMk (contDiffOn_const.mul hFc)).prodMk
        (contDiffOn_const.prodMk (contDiffOn_const.mul hGc))
    have hv : ContDiffOn ℝ ∞ (harmonicRadialState f g) (Icc α β) := by
      apply ODE.contDiffOn_enat_Icc_of_hasDerivWithinAt
        (f := fun t U => spectralPhysicalCircularField
          (-2*(a : ℂ)+2*Complex.I*(b : ℂ)-2*lam)
          (-2*(a : ℂ)-2*Complex.I*(b : ℂ)-2*lam) eta m (Q t) t U+
            ((0,-Complex.I*F t),(0,Complex.I*G t)))
        (u := (univ : Set E₄)) (hbase.add hsource)
      · exact fun t ht => (harmonicRadialSourcePair_hasDerivAt a b m Q f g F G eta lam
          hf hg heq t (hR.trans_lt (hsub ht))).hasDerivWithinAt
      · exact fun _ _ => mem_univ _
    exact (hv.contDiffAt (Icc_mem_nhds hαr hrβ)).contDiffWithinAt
  exact ⟨hstate.fst.fst,hstate.snd.fst⟩

end DefocusingNLS

end OAI
