import Mathlib
import OAI.Analysis.AffineBernstein.TubeDensityVariation

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

section HessianVariation
open Filter
open scoped Topology
variable {P Q R : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup Q] [NormedSpace ℝ Q]
  [NormedAddCommGroup R] [NormedSpace ℝ R]

lemma second_fderiv_add_const_smul {F G : P → Q} {x : P}
    (hF : ContDiffAt ℝ ∞ F x) (hG : ContDiffAt ℝ ∞ G x) (t : ℝ) :
    fderiv ℝ (fderiv ℝ (fun y => F y+t • G y)) x =
      fderiv ℝ (fderiv ℝ F) x+t • fderiv ℝ (fderiv ℝ G) x := by
  have he : fderiv ℝ (fun y => F y+t • G y) =ᶠ[𝓝 x]
      (fun y => fderiv ℝ F y+t • fderiv ℝ G y) := by
    filter_upwards [(hF.of_le (show (1 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) by simp)).eventually (by simp),
      (hG.of_le (show (1 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) by simp)).eventually (by simp)] with y hf hg
    simpa only [Pi.smul_def,Pi.add_def] using
      ((hf.differentiableAt (by norm_num)).hasFDerivAt.add
        ((hg.differentiableAt (by norm_num)).hasFDerivAt.const_smul t)).fderiv
  rw [he.fderiv_eq]
  have hf := (hF.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)
  have hg := (hG.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)
  simpa only [Pi.smul_def,Pi.add_def] using (hf.hasFDerivAt.add (hg.hasFDerivAt.const_smul t)).fderiv

lemma contDiffAt_partialSecond {F : P × Q → R} {p : P × Q}
    (hF : ContDiffAt ℝ ∞ F p) :
    ContDiffAt ℝ ∞ (fun r : P × Q =>
      fderiv ℝ (fderiv ℝ (fun y : Q => F (r.1,y))) r.2) p := by
  have hd : ContDiffAt ℝ ∞ (fun r : P × Q =>
      fderiv ℝ (fun y => F (r.1,y)) r.2) p := by
    apply ContDiffAt.fderiv (n := ∞) (g := Prod.snd) _ contDiffAt_snd (by simp)
    exact hF.comp (p,p.2) (contDiffAt_fst.fst.prodMk contDiffAt_snd)
  apply ContDiffAt.fderiv (n := ∞) (g := Prod.snd) _ contDiffAt_snd (by simp)
  exact hd.comp (p,p.2) (contDiffAt_fst.fst.prodMk contDiffAt_snd)

end HessianVariation

open Filter
open scoped Topology
variable {S E F : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

omit [Fintype ι] [DecidableEq ι] in
lemma tubeBaseMatrix_variation {H G : S × E → ℝ} {q : S × E}
    (hH : ContDiffAt ℝ ∞ H q) (hG : ContDiffAt ℝ ∞ G q)
    (bS : Module.Basis ι ℝ S) (t : ℝ) :
    tubeBaseMatrix (fun r => H r+t*G r) q bS =
      tubeBaseMatrix H q bS+t • tubeBaseMatrix G q bS := by
  ext i j
  have hh := congrArg (fun A : (S × E) →L[ℝ] (S × E) →L[ℝ] ℝ => A (bS i,0) (bS j,0))
    (second_fderiv_add_const_smul hH hG t)
  simp only [add_apply,smul_apply,smul_eq_mul] at hh
  change -fderiv ℝ (fderiv ℝ (fun r => H r+t*G r)) q (bS i,0) (bS j,0) =
    -fderiv ℝ (fderiv ℝ H) q (bS i,0) (bS j,0)+
      t * (-fderiv ℝ (fderiv ℝ G) q (bS i,0) (bS j,0))
  rw [hh]
  ring

omit [DecidableEq κ] in
lemma tubeRadiusMatrix_variation {H G : S × E → ℝ} {q : S × E}
    (hH : ContDiffAt ℝ ∞ H q) (hG : ContDiffAt ℝ ∞ G q)
    (bE : OrthonormalBasis (κ ⊕ Unit) ℝ E) (t : ℝ) :
    tubeRadiusMatrix (fun r => H r+t*G r) q bE =
      tubeRadiusMatrix H q bE+t • tubeRadiusMatrix G q bE := by
  ext i j
  exact congrArg (fun A : (S × E) →L[ℝ] (S × E) →L[ℝ] ℝ =>
    A (0,bE (Sum.inl i)) (0,bE (Sum.inl j))) (second_fderiv_add_const_smul hH hG t)

omit [DecidableEq ι] [DecidableEq κ] in
lemma contDiffAt_tubeMatrices_variation {H G : S × E → ℝ}
    (q₀ : S × E) (J : F →L[ℝ] (S × E)) {p : ℝ × F}
    (hH : ContDiffAt ℝ ∞ H (q₀+J p.2)) (hG : ContDiffAt ℝ ∞ G (q₀+J p.2))
    (bS : Module.Basis ι ℝ S) (bE : OrthonormalBasis (κ ⊕ Unit) ℝ E) :
    ContDiffAt ℝ ∞ (fun r : ℝ × F => fun i j => tubeBaseMatrix (fun q => H q+r.1*G q) (q₀+J r.2) bS i j) p ∧
    ContDiffAt ℝ ∞ (fun r : ℝ × F => fun i j => tubeRadiusMatrix (fun q => H q+r.1*G q) (q₀+J r.2) bE i j) p := by
  have hF : ContDiffAt ℝ ∞ (fun r : ℝ × (S × E) => H r.2+r.1*G r.2) (p.1,q₀+J p.2) :=
    (hH.comp (f := Prod.snd) (p.1,q₀+J p.2) contDiffAt_snd).add
      (contDiffAt_fst.mul (hG.comp (f := Prod.snd) (p.1,q₀+J p.2) contDiffAt_snd))
  have hD := (contDiffAt_partialSecond hF).comp
    (f := fun r : ℝ × F => (r.1,q₀+J r.2)) p
    (contDiffAt_fst.prodMk (contDiffAt_const.add (J.contDiff.contDiffAt.comp p contDiffAt_snd)))
  constructor
  · exact contDiffAt_pi.mpr (fun i => contDiffAt_pi.mpr (fun j =>
      ((hD.clm_apply contDiffAt_const).clm_apply contDiffAt_const).neg))
  · exact contDiffAt_pi.mpr (fun i => contDiffAt_pi.mpr (fun j =>
      (hD.clm_apply contDiffAt_const).clm_apply contDiffAt_const))

def tubeAreaFirstVariation (B D : Matrix ι ι ℝ) (R T : Matrix κ κ ℝ) (δ : ℝ) : ℝ :=
  δ * Real.rpow B.det (δ-1) * Real.rpow R.det (1-δ) *
    (∑ i, ∑ j, B.adjugate j i * D i j) +
  (1-δ) * Real.rpow B.det δ * Real.rpow R.det (-δ) *
    (∑ i, ∑ j, R.adjugate j i * T i j)

lemma hasDerivAt_tubeDensity_variation {H G : S × E → ℝ} {q : S × E}
    (hH : ContDiffAt ℝ ∞ H q) (hG : ContDiffAt ℝ ∞ G q)
    (bS : Module.Basis ι ℝ S) (bE : OrthonormalBasis (κ ⊕ Unit) ℝ E)
    (hB : (tubeBaseMatrix H q bS).PosDef) (hR : (tubeRadiusMatrix H q bE).PosDef) (δ : ℝ) :
    HasDerivAt (fun t : ℝ => tubeAreaDensity
      (tubeBaseMatrix (fun r => H r+t*G r) q bS)
      (tubeRadiusMatrix (fun r => H r+t*G r) q bE) δ)
      (tubeAreaFirstVariation (tubeBaseMatrix H q bS) (tubeBaseMatrix G q bS)
        (tubeRadiusMatrix H q bE) (tubeRadiusMatrix G q bE) δ) 0 := by
  simp_rw [tubeBaseMatrix_variation hH hG,tubeRadiusMatrix_variation hH hG]
  exact hasDerivAt_tubeAreaDensity _ _ _ _ hB hR δ

lemma contDiffAt_tubeDensity_variation {H G : S × E → ℝ}
    (q₀ : S × E) (J : F →L[ℝ] (S × E)) {p : ℝ × F}
    (hH : ContDiffAt ℝ ∞ H (q₀+J p.2)) (hG : ContDiffAt ℝ ∞ G (q₀+J p.2))
    (bS : Module.Basis ι ℝ S) (bE : OrthonormalBasis (κ ⊕ Unit) ℝ E)
    (hB : (tubeBaseMatrix (fun q => H q+p.1*G q) (q₀+J p.2) bS).det ≠ 0)
    (hR : (tubeRadiusMatrix (fun q => H q+p.1*G q) (q₀+J p.2) bE).det ≠ 0) (δ : ℝ) :
    ContDiffAt ℝ ∞ (fun r : ℝ × F => tubeAreaDensity
      (tubeBaseMatrix (fun q => H q+r.1*G q) (q₀+J r.2) bS)
      (tubeRadiusMatrix (fun q => H q+r.1*G q) (q₀+J r.2) bE) δ) p := by
  obtain ⟨hb,hr⟩ := contDiffAt_tubeMatrices_variation q₀ J hH hG bS bE
  exact (((continuousDetRows (ι := ι)).contDiff.contDiffAt.comp p hb).rpow_const_of_ne hB).mul
    (((continuousDetRows (ι := κ)).contDiff.contDiffAt.comp p hr).rpow_const_of_ne hR)

end AffineBernstein
end

end OAI
