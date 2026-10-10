import Mathlib
import OAI.Analysis.AffineBernstein.FlatBlockCalculus
import OAI.Analysis.AffineBernstein.NewtonBasis

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

open Filter
open scoped Topology
open scoped Matrix
variable {S E : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

omit [CompleteSpace E] [DecidableEq ι] in
lemma contDiffAt_tubeFullRadiusMatrix {H : S × E → ℝ} {q : S × E}
    (hH : ContDiffAt ℝ ∞ H q) (b : OrthonormalBasis ι ℝ E) :
    ContDiffAt ℝ ∞ (fun y i j => tubeFullRadiusMatrix H y b i j) q := by
  have hh := (hH.fderiv_right (m := ∞) (by simp)).fderiv_right (m := ∞) (by simp)
  exact contDiffAt_pi.mpr (fun i => contDiffAt_pi.mpr (fun j =>
    (hh.clm_apply contDiffAt_const).clm_apply contDiffAt_const))

omit [CompleteSpace E] [DecidableEq ι] in
lemma contDiffAt_tubeBaseMatrix {H : S × E → ℝ} {q : S × E}
    (hH : ContDiffAt ℝ ∞ H q) (b : Module.Basis ι ℝ S) :
    ContDiffAt ℝ ∞ (fun y i j => tubeBaseMatrix H y b i j) q := by
  have hh := (hH.fderiv_right (m := ∞) (by simp)).fderiv_right (m := ∞) (by simp)
  exact contDiffAt_pi.mpr (fun i => contDiffAt_pi.mpr (fun j =>
    ((hh.clm_apply contDiffAt_const).clm_apply contDiffAt_const).neg))

omit [CompleteSpace E] in
lemma contDiffAt_tubeAngularDensity {H : S × E → ℝ} {q : S × E}
    (hH : ContDiffAt ℝ ∞ H q) (b : OrthonormalBasis ι ℝ E) :
    ContDiffAt ℝ ∞ (fun y => tubeAngularDensity H y b) q := by
  change ContDiffAt ℝ ∞ (fun y => ∑ i, (tubeFullRadiusMatrix H y b).adjugate i i) q
  apply ContDiffAt.sum
  intro i _
  exact contDiffAt_adjugate_entries (contDiffAt_tubeFullRadiusMatrix hH b) i i

omit [CompleteSpace E] in
lemma contDiffAt_invariantTubeF {H : S × E → ℝ} {q : S × E}
    (hH : ContDiffAt ℝ ∞ H q) (bS : Module.Basis ι ℝ S)
    (b : OrthonormalBasis (κ ⊕ Unit) ℝ E) (δ : ℝ)
    (hB : (tubeBaseMatrix H q bS).det ≠ 0)
    (hQ : tubeAngularDensity H q b ≠ 0) (hh : H q ≠ 0) (he : q.2 ≠ 0) :
    ContDiffAt ℝ ∞ (invariantTubeF H bS b δ) q := by
  have hb := (continuousDetRows (ι := ι)).contDiff.contDiffAt.comp q
    (contDiffAt_tubeBaseMatrix hH bS)
  have hn : ContDiffAt ℝ ∞ (fun y : S × E => inner ℝ y.2 y.2) q :=
    contDiffAt_snd.inner ℝ contDiffAt_snd
  exact (contDiffAt_const.mul (((hb.log hB).add
    (hn.log (real_inner_self_pos.mpr he).ne')).sub
      ((contDiffAt_tubeAngularDensity hH b).log hQ))).sub (hH.log hh)

omit [CompleteSpace E] in
lemma zeroHomogeneous_fderiv_radial {F : S × E → ℝ} {s : S} {e : E}
    (hF : DifferentiableAt ℝ F (s,e))
    (hhom : ∀ c : ℝ, 0 < c → F (s,c • e) = F (s,e)) :
    fderiv ℝ F (s,e) (0,e) = 0 := by
  have hd : HasDerivAt (fun c : ℝ => (s,c • e)) (0,e) 1 := by
    simpa using (hasDerivAt_const (1 : ℝ) s).prodMk ((hasDerivAt_id (1 : ℝ)).smul_const e)
  have hf : HasDerivAt (fun c : ℝ => F (s,c • e)) (fderiv ℝ F (s,e) (0,e)) 1 := by
    have hF' : HasFDerivAt F (fderiv ℝ F (s,e)) (s,(1 : ℝ) • e) := by simpa using hF.hasFDerivAt
    exact hF'.comp_hasDerivAt 1 hd
  have heq : (fun c : ℝ => F (s,c • e)) =ᶠ[𝓝 1] (fun _ => F (s,e)) := by
    filter_upwards [Ioi_mem_nhds (show (0 : ℝ) < 1 by norm_num)] with c hc
    exact hhom c hc
  exact (heq.hasDerivAt_iff.mp hf).unique (hasDerivAt_const _ _)

omit [CompleteSpace E] in
lemma exists_orthonormalBasis_last [FiniteDimensional ℝ E]
    (b : OrthonormalBasis (κ ⊕ Unit) ℝ E) {e : E} (he : ‖e‖ = 1) :
    ∃ c : OrthonormalBasis (κ ⊕ Unit) ℝ E, c (Sum.inr ()) = e := by
  let v : κ ⊕ Unit → E := fun _ => e
  let A : Set (κ ⊕ Unit) := {Sum.inr ()}
  have hv : Orthonormal ℝ (A.domRestrict v) := by
    apply orthonormal_iff_ite.mpr
    intro i j
    have hij : i = j := by
      apply Subtype.ext
      exact (Set.mem_singleton_iff.mp i.property).trans (Set.mem_singleton_iff.mp j.property).symm
    simp [hij,A,v,Set.domRestrict,he]
  obtain ⟨c,hc⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq
    (Module.finrank_eq_card_basis b.toBasis) hv
  exact ⟨c,hc _ (by simp [A])⟩

end AffineBernstein
end

end OAI
