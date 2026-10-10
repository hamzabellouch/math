import Mathlib
import OAI.Probability.LogConcave.LowerBounds.FrameTransport
import OAI.Probability.LogConcave.Sampling.StateLaw

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section LowerProof
open Matrix Topology TopologicalSpace ProbabilityTheory Classical WithLp
open scoped Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory

namespace LogConcaveSampling.LowerBound

def roundFrames {d k : ℕ} (hk : k+1 < d) (Λ : Point d →L[ℝ] Point d)
    (F : Frames d) (x : Point d) (r : Point d × Point d × Point d) : Frames d :=
  let F₁ := inverseFrameUpdate (Nat.lt_of_succ_lt hk) F x r.1
  let u := (frameTransport F₁).symm x
  let y := Λ u
  forwardFrameUpdate hk F₁ (filledObservation (k := k+1) F₁.2 y r.2.1) r.2.2

@[fun_prop] lemma measurable_inverse_frameTransport {d : ℕ} :
    Measurable (fun p : Frames d × Point d => (frameTransport p.1).symm p.2) := by
  simp only [← frameTransport_swap]
  have h := (measurable_frameTransport (d := d)).comp
    (show Measurable (fun p : Frames d × Point d => (p.1.swap,p.2)) by fun_prop)
  exact h

@[fun_prop] lemma measurable_roundFrames {d k : ℕ} (hk : k+1 < d) (Λ : Point d →L[ℝ] Point d) :
    Measurable (fun p : (Frames d × Point d) × (Point d × Point d × Point d) =>
      roundFrames hk Λ p.1.1 p.1.2 p.2) := by
  let Z := (Frames d × Point d) × (Point d × Point d × Point d)
  let f : Z → Frames d := fun p => inverseFrameUpdate (Nat.lt_of_succ_lt hk) p.1.1 p.1.2 p.2.1
  have hf : Measurable f := (measurable_inverseFrameUpdate (Nat.lt_of_succ_lt hk)).comp
    (f := fun p : Z => (p.1.1,p.1.2,p.2.1)) ((measurable_fst.fst).prodMk (measurable_fst.snd.prodMk measurable_snd.fst))
  let u : Z → Point d := fun p => (frameTransport (f p)).symm p.1.2
  have hu : Measurable u := (measurable_inverse_frameTransport (d := d)).comp
    (f := fun p : Z => (f p,p.1.2)) (hf.prodMk measurable_fst.snd)
  let y : Z → Point d := fun p => Λ (u p)
  have hy : Measurable y := Λ.continuous.measurable.comp (f := u) hu
  let z : Z → Point d := fun p => filledObservation (k := k+1) (f p).2 (y p) p.2.2.1
  have hz : Measurable z := (measurable_filledObservation (d := d) (k := k+1)).comp
    (f := fun p : Z => ((f p).2,y p,p.2.2.1)) (hf.snd.prodMk (hy.prodMk measurable_snd.snd.fst))
  change Measurable (fun p : Z => forwardFrameUpdate hk (f p) (z p) p.2.2.2)
  exact (measurable_forwardFrameUpdate hk).comp
    (f := fun p : Z => (f p,z p,p.2.2.2)) (hf.prodMk (hz.prodMk measurable_snd.snd.snd))

lemma filledForward_law {d k : ℕ} (hk : k < d) (F : Frames d) (y : Point d) :
    (((stdGaussian (Point d)).prod (stdGaussian (Point d))).prod
      (remainingHaar (prefixSpace d (k+1)))).map
        (fun p => frameCompletion (forwardFrameUpdate hk F
          (filledObservation (k := k) F.2 y p.1.1) p.1.2) p.2) =
      (remainingHaar (prefixSpace d k)).map (frameCompletion F) := by
  have ha := Measure.prodAssoc_prod (μ := stdGaussian (Point d)) (ν := stdGaussian (Point d))
    (τ := remainingHaar (prefixSpace d (k+1)))
  calc
    _ = ((stdGaussian (Point d)).prod ((stdGaussian (Point d)).prod
        (remainingHaar (prefixSpace d (k+1))))).map
        (fun p => frameCompletion (forwardFrameUpdate hk F
          (filledObservation (k := k) F.2 y p.1) p.2.1) p.2.2) := by
      rw [← ha, Measure.map_map (by fun_prop) MeasurableEquiv.prodAssoc.measurable]
      rfl
    _ = _ := by
      apply map_prod_eq_of_constant_fiber_law (by fun_prop)
      intro g
      exact forwardFrameUpdate_law hk F (filledObservation (k := k) F.2 y g)

theorem roundFrames_law {d k : ℕ} (hk : k+1 < d) (Λ : Point d →L[ℝ] Point d)
    (F : Frames d) (x : Point d) :
    (((stdGaussian (Point d)).prod ((stdGaussian (Point d)).prod (stdGaussian (Point d)))).prod
      (remainingHaar (prefixSpace d (k+2)))).map
        (fun p => frameCompletion (roundFrames hk Λ F x p.1) p.2) =
      (remainingHaar (prefixSpace d k)).map (frameCompletion F) := by
  let f : (Point d × Point d × Point d) × Rotations d → Rotations d :=
    fun p => frameCompletion (roundFrames hk Λ F x p.1) p.2
  let g : Point d × Rotations d → Rotations d :=
    fun p => frameCompletion (inverseFrameUpdate (Nat.lt_of_succ_lt hk) F x p.1) p.2
  have hf : Measurable f := (measurable_frameCompletion (d := d)).comp
    (f := fun p : (Point d × Point d × Point d) × Rotations d =>
      (roundFrames hk Λ F x p.1,p.2))
    (((measurable_roundFrames hk Λ).comp
      (f := fun p : (Point d × Point d × Point d) × Rotations d => ((F,x),p.1))
      (measurable_const.prodMk measurable_fst)).prodMk measurable_snd)
  have hg : Measurable g := by unfold g; fun_prop
  have hh (z : Point d) :
      (((stdGaussian (Point d)).prod (stdGaussian (Point d))).prod
        (remainingHaar (prefixSpace d (k+2)))).map (fun p => f ((z,p.1),p.2)) =
        (remainingHaar (prefixSpace d (k+1))).map (fun h => g (z,h)) := by
    exact filledForward_law hk (inverseFrameUpdate (Nat.lt_of_succ_lt hk) F x z)
      (Λ ((frameTransport (inverseFrameUpdate (Nat.lt_of_succ_lt hk) F x z)).symm x))
  have he := eliminate_fresh_residual (μ := stdGaussian (Point d))
    (γ := (stdGaussian (Point d)).prod (stdGaussian (Point d)))
    (η := remainingHaar (prefixSpace d (k+1)))
    (η' := remainingHaar (prefixSpace d (k+2)))
    (step := id) measurable_id hf hg hh
  rw [Measure.map_id] at he
  exact he.trans (inverseFrameUpdate_law (Nat.lt_of_succ_lt hk) F x)

lemma roundFrames_compatible {d k : ℕ} (hk : k+1 < d) (Λ : Point d →L[ℝ] Point d)
    (F : Frames d) (x : Point d) (r : Point d × Point d × Point d) :
    CompatibleFrames (prefixSpace d k) F (roundFrames hk Λ F x r) := by
  unfold roundFrames
  exact compatibleFrames_trans (compatibleFrames_inverseUpdate _ _ _ _)
    (compatibleFrames_mono (prefixSpace_mono d (Nat.le_succ k))
      (compatibleFrames_forwardUpdate _ _ _ _))

end LogConcaveSampling.LowerBound

namespace LogConcaveSampling.LowerBound
open scoped RealInnerProductSpace

def linearReply {d : ℕ} (Λ : Point d →L[ℝ] Point d) (O : Rotations d) (x : Point d) :
    ℝ × Point d :=
  let u := (rotationIsometry O).symm x
  (⟪u,Λ u⟫ / 2, rotationIsometry O (Λ u))

@[fun_prop] lemma measurable_linearReply {d : ℕ} (Λ : Point d →L[ℝ] Point d) :
    Measurable (fun p : Rotations d × Point d => linearReply Λ p.1 p.2) := by
  unfold linearReply
  simp only [← rotationIsometry_inv_apply]
  fun_prop

def roundCoordinate {d k : ℕ} (hk : k+1 < d) (F : Frames d) (x g : Point d) : Point d :=
  (frameTransport (inverseFrameUpdate (Nat.lt_of_succ_lt hk) F x g)).symm x

@[fun_prop] lemma measurable_roundCoordinate {d k : ℕ} (hk : k+1 < d) :
    Measurable (fun p : (Frames d × Point d) × Point d => roundCoordinate hk p.1.1 p.1.2 p.2) := by
  let Z := (Frames d × Point d) × Point d
  let f : Z → Frames d := fun p => inverseFrameUpdate (Nat.lt_of_succ_lt hk) p.1.1 p.1.2 p.2
  have hf : Measurable f := (measurable_inverseFrameUpdate (Nat.lt_of_succ_lt hk)).comp
    (measurable_fst.fst.prodMk (measurable_fst.snd.prodMk measurable_snd))
  change Measurable (fun p : Z => (frameTransport (f p)).symm p.1.2)
  exact (measurable_inverse_frameTransport (d := d)).comp
    (f := fun p : Z => (f p,p.1.2)) (hf.prodMk measurable_fst.snd)

lemma roundCoordinate_mem {d k : ℕ} (hk : k+1 < d) (F : Frames d) (x g : Point d) :
    roundCoordinate hk F x g ∈
      frameSpace (inverseFrameUpdate (Nat.lt_of_succ_lt hk) F x g).2 (prefixSpace d (k+1)) := by
  apply frameTransport_preimage_mem
  exact mem_frameSpace_extendFrame _ _ _

lemma replyCoordinate_mem {d k : ℕ} (hk : k+1 < d) (Λ : Point d →L[ℝ] Point d)
    (F : Frames d) (x : Point d) (r : Point d × Point d × Point d) :
    Λ (roundCoordinate hk F x r.1) ∈ frameSpace (roundFrames hk Λ F x r).2 (prefixSpace d (k+2)) :=
  mem_frameSpace_filledExtend hk _ _ _

theorem roundReply_correct {d k : ℕ} (hk : k+1 < d) (Λ : Point d →L[ℝ] Point d)
    (F : Frames d) (x : Point d) (r : Point d × Point d × Point d)
    {H : Rotations d} (hH : H ∈ subspaceStabilizer (prefixSpace d (k+2))) :
    linearReply Λ (frameCompletion (roundFrames hk Λ F x r) H) x =
      (⟪roundCoordinate hk F x r.1, Λ (roundCoordinate hk F x r.1)⟫ / 2,
        frameTransport (roundFrames hk Λ F x r) (Λ (roundCoordinate hk F x r.1))) := by
  let F₁ := inverseFrameUpdate (Nat.lt_of_succ_lt hk) F x r.1
  have hc : CompatibleFrames (prefixSpace d (k+1)) F₁ (roundFrames hk Λ F x r) :=
    compatibleFrames_forwardUpdate hk _ _ _
  obtain ⟨H',hH',he⟩ := compatibleFrames_reconstruct _ hc
    (subspaceStabilizer_anti (prefixSpace_mono d (Nat.le_succ (k+1))) hH)
  have hq : (rotationIsometry (frameCompletion (roundFrames hk Λ F x r) H)).symm x =
      roundCoordinate hk F x r.1 := by
    rw [he]
    exact frameCompletion_symm_eq_transport _ F₁ hH' (mem_frameSpace_extendFrame _ _ _)
  unfold linearReply
  simp only [hq]
  rw [frameCompletion_eq_transport _ _ hH (replyCoordinate_mem hk Λ F x r)]

theorem roundFrames_span_growth {d k : ℕ} (hk : k+1 < d) (Λ : Point d →L[ℝ] Point d)
    (F : Frames d) (x : Point d) (r : Point d × Point d × Point d)
    (hq : (prefixSpace d k)ᗮ.orthogonalProjectionOnto (rotationIsometry F.2⁻¹ r.1) ≠ 0)
    (hr : (prefixSpace d (k+1))ᗮ.orthogonalProjectionOnto
      (rotationIsometry (inverseFrameUpdate (Nat.lt_of_succ_lt hk) F x r.1).2⁻¹ r.2.1) ≠ 0) :
    frameSpace (roundFrames hk Λ F x r).2 (prefixSpace d (k+2)) ≤
      ((frameSpace F.2 (prefixSpace d k) ⊔ ℝ ∙ r.1) ⊔
        (frameSpace F.2 (prefixSpace d k) ⊔ ℝ ∙ r.1).map Λ.toLinearMap) ⊔ ℝ ∙ r.2.1 := by
  let F₁ := inverseFrameUpdate (Nat.lt_of_succ_lt hk) F x r.1
  let K := frameSpace F.2 (prefixSpace d k) ⊔ ℝ ∙ r.1
  have hK : frameSpace F₁.2 (prefixSpace d (k+1)) ≤ K :=
    frameSpace_extendFrame_le _ _ _ hq
  have hu : roundCoordinate hk F x r.1 ∈ K := hK (roundCoordinate_mem hk F x r.1)
  have hΛ : Λ (roundCoordinate hk F x r.1) ∈ K.map Λ.toLinearMap := ⟨_,hu,rfl⟩
  have hy : ℝ ∙ Λ (roundCoordinate hk F x r.1) ≤ K.map Λ.toLinearMap := by
    apply Submodule.span_le.mpr
    intro y hy
    rcases Set.mem_singleton_iff.mp hy with rfl
    exact hΛ
  exact (frameSpace_filledExtend_le hk F₁.2 _ _ hr).trans
    (sup_le_sup (sup_le_sup hK hy) le_rfl)

end LogConcaveSampling.LowerBound

end LowerProof
end
end
end

end OAI
