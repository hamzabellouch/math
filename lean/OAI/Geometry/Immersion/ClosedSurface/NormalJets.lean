import OAI.Geometry.Immersion.ClosedSurface.JetBounds
import OAI.Geometry.Immersion.ClosedSurface.RealModes

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.RealModes
open ClosedSurfaceR4.SmallModes
open ClosedSurfaceR4.WeightedEstimates

abbrev RealTwoJet := Fin 5 → RVec 4

def realTwoJet (F : RField 4) (p : Base) : RealTwoJet :=
  ![coordDeriv dx F p, coordDeriv dy F p, coordDeriv dx (coordDeriv dx F) p,
    coordDeriv dx (coordDeriv dy F) p, coordDeriv dy (coordDeriv dy F) p]

def normalFromJet (J : RealTwoJet) : RVec 4 :=
  NormalFrame.unitPerp (J 0) (J 1) (realNormalPart (J 0) (J 1) (J 4))

structure RealJetDomain (Ω : Set RealTwoJet) : Prop where
  isOpen : IsOpen Ω
  determinant : ∀ J ∈ Ω, NormalFrame.gramDet (J 0) (J 1) ≠ 0
  good : ∀ J ∈ Ω, realNormalPart (J 0) (J 1) (J 4) ≠ 0

lemma contDiffAt_realNormalPart {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {X Y W : E → RVec 4} {p : E} (hX : ContDiffAt ℝ ∞ X p)
    (hY : ContDiffAt ℝ ∞ Y p) (hW : ContDiffAt ℝ ∞ W p)
    (hD : NormalFrame.gramDet (X p) (Y p) ≠ 0) :
    ContDiffAt ℝ ∞ (fun q => realNormalPart (X q) (Y q) (W q)) p := by
  have hx := (complexifyCLM 4).contDiff.contDiffAt.comp p hX
  have hy := (complexifyCLM 4).contDiff.contDiffAt.comp p hY
  have hw := (complexifyCLM 4).contDiff.contDiffAt.comp p hW
  have hd : gramDet (complexify (X p)) (complexify (Y p)) ≠ 0 := by
    rw [complexify_gram]; exact Complex.ofReal_ne_zero.mpr hD
  have hh := LowJet.contDiffAt_normalPart hx hy hw hd
  apply contDiffAt_pi.mpr
  intro i
  have hi := Complex.reCLM.contDiff.contDiffAt.comp p (contDiffAt_pi.mp hh i)
  convert hi using 1
  funext q
  exact congrArg Complex.re (congrFun (complexify_normalPart (X q) (Y q) (W q)) i)

lemma RealJetDomain.smoothNormal {Ω : Set RealTwoJet} (hΩ : RealJetDomain Ω) :
    ContDiffOn ℝ ∞ normalFromJet Ω := by
  intro J hJ
  have hslot (i : Fin 5) : ContDiffAt ℝ ∞ (fun K : RealTwoJet => K i) J :=
    (ContinuousLinearMap.proj i : RealTwoJet →L[ℝ] RVec 4).contDiff.contDiffAt
  have hb := contDiffAt_realNormalPart (hslot 0) (hslot 1) (hslot 4) (hΩ.determinant J hJ)
  have hn := realNormalPart_perp (J 0) (J 1) (J 4) (hΩ.determinant J hJ)
  exact (NormalFrame.contDiffAt_unitPerp (hslot 0) (hslot 1) hb
    (hΩ.determinant J hJ) (hΩ.good J hJ) hn.1 hn.2).contDiffWithinAt

lemma contDiff_realTwoJet {F : RField 4} (hF : ContDiff ℝ ∞ F) : ContDiff ℝ ∞ (realTwoJet F) := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · exact contDiff_real_coordDeriv hF dx
  · exact contDiff_real_coordDeriv hF dy
  · exact contDiff_real_coordDeriv (contDiff_real_coordDeriv hF dx) dx
  · exact contDiff_real_coordDeriv (contDiff_real_coordDeriv hF dy) dx
  · exact contDiff_real_coordDeriv (contDiff_real_coordDeriv hF dy) dy




theorem compact_freeNormal_bound {U : Set Base} (hU : IsOpen U) {Ω K : Set RealTwoJet}
    (hΩ : RealJetDomain Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω) (m : ℕ) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ (F : RField 4) (s C : ℝ), 0 < s → 1 ≤ C →
      ContDiff ℝ ∞ F → MapsTo (realTwoJet F) U K → WeightedBound U s m C (realTwoJet F) →
      WeightedBound U s m ((m.factorial : ℝ) * D * C ^ m) (freeNormal F) := by
  obtain ⟨D, hD, hbD⟩ := smooth_compact_weighted_bound hU.uniqueDiffOn hΩ.isOpen.uniqueDiffOn
    hK hKΩ hΩ.smoothNormal m
  refine ⟨D, hD, ?_⟩
  intro F s C hs hC hF hFK hb
  exact hbD (realTwoJet F) s C hs hC (contDiff_realTwoJet hF).contDiffOn hFK hb

end ClosedSurfaceR4.RealModes

end

end OAI
