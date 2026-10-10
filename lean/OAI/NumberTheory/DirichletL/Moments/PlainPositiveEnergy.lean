import OAI.NumberTheory.DirichletL.Moments.PlainPositiveScale
import OAI.NumberTheory.DirichletL.Moments.OriginalRadialComparison

namespace OAI

noncomputable section
open scoped Classical SchwartzMap BigOperators
namespace SevenEighths.CenteredMomentPlainPositiveEnergy
open HeckeFamily HeckeDyadic CenteredMomentPlainPositiveScale CenteredMomentPlainGlobalEnergy
open CenteredMomentOriginalRadialComparison
open CenteredMomentRadialEligibleEnergy (Radial)
open QuadraticInitialBound ConcreteTraceCRT
local notation "O"=>HeckeFamily.O

 theorem actual_radial_pair_bound (a b:ℝ)(ha:0<a):
    ∃S:Finset (ℕ×ℕ),∃C:ℝ,0<C ∧
    ∀(W₁ W₂:SchwartzMap ℝ ℂ),Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b→
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b→
    ∀(χ:O→Character)(r:Radial)(R X₁ X₂ freq₁ freq₂:ℝ),0≤R→0<X₁→0<X₂→
      (∀z,r.keep z→(χ z).residue≠1)→
      (∀z,r.keep z→((χ z).modulus.absNorm:ℝ)≤R)→
    radialEnergy (fun z=>polynomial (χ z) false W₁ X₁ 0 freq₁*
      polynomial (χ z) false W₂ X₂ 0 freq₂) r.keep r.profile r.scale≤
      C*diagonalControl r.profile*max 1 r.scale*
        ((S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₁)*
         (S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₂))^2*R^4*
        (3+|freq₁|)^4*(3+|freq₂|)^4:=by
  obtain ⟨S,C,hC,hg⟩:=global_positive_scale a b ha
  refine ⟨S,C^4,pow_pos hC _,?_⟩
  intro W₁ W₂ hs₁ hs₂ χ r R X₁ X₂ freq₁ freq₂ hR hX₁ hX₂ hχ hmod
  let B₁:=S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₁
  let B₂:=S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₂
  have hB₁:0≤B₁:=apply_nonneg _ _
  have hB₂:0≤B₂:=apply_nonneg _ _
  let B:=C^2*(B₁*B₂)*R^2*(3+|freq₁|)^2*(3+|freq₂|)^2
  have hB:0≤B:=by dsimp [B];positivity
  have hp (z:O)(hz:r.keep z):
      ‖polynomial (χ z) false W₁ X₁ 0 freq₁*polynomial (χ z) false W₂ X₂ 0 freq₂‖≤B:=by
    rw [norm_mul]
    have h₁:‖polynomial (χ z) false W₁ X₁ 0 freq₁‖≤C*B₁*R*(3+|freq₁|)^2:=
      (hg W₁ hs₁ (χ z) (hχ z hz) X₁ freq₁ hX₁).trans (by gcongr;exact hmod z hz)
    have h₂:‖polynomial (χ z) false W₂ X₂ 0 freq₂‖≤C*B₂*R*(3+|freq₂|)^2:=
      (hg W₂ hs₂ (χ z) (hχ z hz) X₂ freq₂ hX₂).trans (by gcongr;exact hmod z hz)
    exact (mul_le_mul h₁ h₂ (norm_nonneg _) (by positivity)).trans_eq (by dsimp [B];ring)
  have hh:=radial_bound_on_keep _ r B hB hp
  exact hh.trans_eq (by dsimp [B];ring)

end SevenEighths.CenteredMomentPlainPositiveEnergy

end

end OAI
