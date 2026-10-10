import Mathlib
import OAI.Probability.LogConcave.LowerBounds.RoundFrames
import OAI.Probability.LogConcave.Sampling.TapeSnocEquiv

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
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

lemma remainingHaar_bot (d : ℕ) : remainingHaar (⊥ : Submodule ℝ (Point d)) = rotationHaar d := by
  have hmem (P : Rotations d) : P ∈ subspaceStabilizer (⊥ : Submodule ℝ (Point d)) := by
    intro x hx
    have hx' : x = 0 := hx
    simp [hx']
  have hi : (remainingHaar (⊥ : Submodule ℝ (Point d))).IsMulLeftInvariant := by
    constructor
    intro P
    change ((subspaceHaar (⊥ : Submodule ℝ (Point d))).map Subtype.val).map (P * ·) = _
    let P' : subspaceStabilizer (⊥ : Submodule ℝ (Point d)) := ⟨P,hmem P⟩
    rw [Measure.map_map (by fun_prop) measurable_subtype_coe]
    calc
      _ = ((subspaceHaar (⊥ : Submodule ℝ (Point d))).map (P' * ·)).map Subtype.val := by
        rw [Measure.map_map measurable_subtype_coe (by fun_prop)]
        rfl
      _ = _ := by rw [map_mul_left_eq_self]; rfl
  have h := Measure.isMulInvariant_eq_smul_of_compactSpace
    (remainingHaar (⊥ : Submodule ℝ (Point d))) (rotationHaar d)
  have hmass := congrArg (fun μ : Measure (Rotations d) => μ Set.univ) h
  simp only [measure_univ, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, mul_one] at hmass
  have hc : (remainingHaar (⊥ : Submodule ℝ (Point d))).haarScalarFactor (rotationHaar d) = 1 :=
    ENNReal.coe_injective hmass.symm
  rwa [hc, one_smul] at h

def linearHistory {Ω : Type*} [MeasurableSpace Ω] {d q : ℕ} (A : OracleAlgorithm Ω d q)
    (Λ : Point d →L[ℝ] Point d) (O : Rotations d) (ω : Ω) : ℕ → Transcript d q
  | 0 => 0
  | n+1 =>
    let h := linearHistory A Λ O ω n
    if hn : n < q then Function.update h ⟨n,hn⟩ (linearReply Λ O (A.query ⟨n,hn⟩ (ω,h))) else h

lemma measurable_linearHistory {Ω : Type*} [MeasurableSpace Ω] {d q : ℕ}
    (A : OracleAlgorithm Ω d q) (Λ : Point d →L[ℝ] Point d) (n : ℕ) :
    Measurable (fun p : Ω × Rotations d => linearHistory A Λ p.2 p.1 n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    simp only [linearHistory]
    split_ifs with hn
    · have hq := (A.query_measurable ⟨n,hn⟩).comp (measurable_fst.prodMk ih)
      have hr := (measurable_linearReply Λ).comp (measurable_snd.prodMk hq)
      apply Measurable.of_eval
      intro j
      by_cases hj : j = ⟨n,hn⟩
      · subst j
        simpa only [Function.update_self, Function.comp_def] using hr
      · simpa only [Function.update_of_ne hj, Function.comp_def] using (measurable_pi_apply j).comp ih
    · exact ih

abbrev RevealState (Ω : Type*) (d q n : ℕ) :=
  Ω × Frames d × Transcript d q × (Fin n → Point d × Point d)

abbrev RoundRandom (d : ℕ) := Point d × Point d × Point d

def roundRandomLaw (d : ℕ) : Measure (RoundRandom d) :=
  (stdGaussian (Point d)).prod ((stdGaussian (Point d)).prod (stdGaussian (Point d)))

instance roundRandomLaw_probability (d : ℕ) : IsProbabilityMeasure (roundRandomLaw d) := by
  unfold roundRandomLaw
  infer_instance

def initialRevealState {Ω : Type*} {d q : ℕ} (ω : Ω) : RevealState Ω d q 0 :=
  (ω,(1,1),0,Fin.elim0)

lemma measurable_initialRevealState {Ω : Type*} [MeasurableSpace Ω] {d q : ℕ} :
    Measurable (initialRevealState (Ω := Ω) (d := d) (q := q)) := by
  unfold initialRevealState
  fun_prop

def revealStep {Ω : Type*} [MeasurableSpace Ω] {d q : ℕ}
    (A : OracleAlgorithm Ω d q) (Λ : Point d →L[ℝ] Point d) (hd : 2*q+1 ≤ d)
    (n : ℕ) (p : RevealState Ω d q n × RoundRandom d) : RevealState Ω d q (n+1) :=
  let s := p.1
  let r := p.2
  let t := Fin.snoc (α := fun _ : Fin (n+1) => Point d × Point d) s.2.2.2 (r.1,r.2.1)
  if hn : n < q then
    let hk : 2*n+1 < d := by omega
    let x := A.query ⟨n,hn⟩ (s.1,s.2.2.1)
    let F := roundFrames hk Λ s.2.1 x r
    let u := roundCoordinate hk s.2.1 x r.1
    let reply := (⟪u,Λ u⟫ / 2,frameTransport F (Λ u))
    (s.1,F,Function.update s.2.2.1 ⟨n,hn⟩ reply,t)
  else (s.1,s.2.1,s.2.2.1,t)

lemma measurable_revealStep {Ω : Type*} [MeasurableSpace Ω] {d q : ℕ}
    (A : OracleAlgorithm Ω d q) (Λ : Point d →L[ℝ] Point d) (hd : 2*q+1 ≤ d) (n : ℕ) :
    Measurable (revealStep A Λ hd n) := by
  let Z := RevealState Ω d q n × RoundRandom d
  have hseed : Measurable (fun p : Z => p.1.1) := measurable_fst.fst
  have hframe : Measurable (fun p : Z => p.1.2.1) := measurable_fst.snd.fst
  have hhist : Measurable (fun p : Z => p.1.2.2.1) := measurable_fst.snd.snd.fst
  have htape : Measurable (fun p : Z => Fin.snoc (α := fun _ : Fin (n+1) => Point d × Point d)
      p.1.2.2.2 (p.2.1,p.2.2.1)) := measurable_fin_snoc n |>.comp
    (measurable_fst.snd.snd.snd.prodMk (measurable_snd.fst.prodMk measurable_snd.snd.fst))
  unfold revealStep
  split_ifs with hn
  · have hk : 2*n+1 < d := by omega
    let x : Z → Point d := fun p => A.query ⟨n,hn⟩ (p.1.1,p.1.2.2.1)
    have hx : Measurable x := (A.query_measurable _).comp (hseed.prodMk hhist)
    let F : Z → Frames d := fun p => roundFrames hk Λ p.1.2.1 (x p) p.2
    have hF : Measurable F := (measurable_roundFrames hk Λ).comp
      (f := fun p : Z => ((p.1.2.1,x p),p.2)) ((hframe.prodMk hx).prodMk measurable_snd)
    let u : Z → Point d := fun p => roundCoordinate hk p.1.2.1 (x p) p.2.1
    have hu : Measurable u := (measurable_roundCoordinate hk).comp
      (f := fun p : Z => ((p.1.2.1,x p),p.2.1)) ((hframe.prodMk hx).prodMk measurable_snd.fst)
    have hΛu : Measurable (fun p : Z => Λ (u p)) := Λ.continuous.measurable.comp hu
    have hreply : Measurable (fun p : Z => (⟪u p,Λ (u p)⟫ / 2,frameTransport (F p) (Λ (u p)))) :=
      ((hu.inner hΛu).div_const 2).prodMk ((measurable_frameTransport (d := d)).comp
        (f := fun p : Z => (F p,Λ (u p))) (hF.prodMk hΛu))
    have hupdate : Measurable (fun p : Z => Function.update p.1.2.2.1 ⟨n,hn⟩
        (⟪u p,Λ (u p)⟫ / 2,frameTransport (F p) (Λ (u p)))) := by
      apply Measurable.of_eval
      intro j
      by_cases hj : j = ⟨n,hn⟩
      · subst j; simpa only [Function.update_self, Function.comp_def] using hreply
      · simpa only [Function.update_of_ne hj, Function.comp_def] using (measurable_pi_apply j).comp hhist
    exact hseed.prodMk (hF.prodMk (hupdate.prodMk htape))
  · exact hseed.prodMk (hframe.prodMk (hhist.prodMk htape))

def HistoryConsistent {Ω : Type*} [MeasurableSpace Ω] {d q : ℕ}
    (A : OracleAlgorithm Ω d q) (Λ : Point d →L[ℝ] Point d) (n : ℕ)
    (s : RevealState Ω d q n) : Prop :=
  ∀ H ∈ subspaceStabilizer (prefixSpace d (2*n)),
    s.2.2.1 = linearHistory A Λ (frameCompletion s.2.1 H) s.1 n

lemma initial_historyConsistent {Ω : Type*} [MeasurableSpace Ω] {d q : ℕ}
    (A : OracleAlgorithm Ω d q) (Λ : Point d →L[ℝ] Point d) (ω : Ω) :
    HistoryConsistent A Λ 0 (initialRevealState ω) := by
  intro H hH
  rfl

lemma revealStep_historyConsistent {Ω : Type*} [MeasurableSpace Ω] {d q n : ℕ}
    (A : OracleAlgorithm Ω d q) (Λ : Point d →L[ℝ] Point d) (hd : 2*q+1 ≤ d) (hn : n < q)
    (s : RevealState Ω d q n) (r : RoundRandom d) (hs : HistoryConsistent A Λ n s) :
    HistoryConsistent A Λ (n+1) (revealStep A Λ hd n (s,r)) := by
  have hk : 2*n+1 < d := by omega
  let x := A.query ⟨n,hn⟩ (s.1,s.2.2.1)
  let F := roundFrames hk Λ s.2.1 x r
  intro H hH
  have hH₂ : H ∈ subspaceStabilizer (prefixSpace d (2*n+2)) := by
    simpa only [Nat.mul_add, Nat.mul_one] using hH
  have hH₀ : H ∈ subspaceStabilizer (prefixSpace d (2*n)) :=
    subspaceStabilizer_anti (prefixSpace_mono d (by omega)) hH₂
  obtain ⟨H',hH',he⟩ := compatibleFrames_reconstruct _ (roundFrames_compatible hk Λ s.2.1 x r) hH₀
  have hh : s.2.2.1 = linearHistory A Λ (frameCompletion F H) s.1 n := by
    rw [he]
    exact hs H' hH'
  change (revealStep A Λ hd n (s,r)).2.2.1 =
    linearHistory A Λ (frameCompletion (revealStep A Λ hd n (s,r)).2.1 H)
      (revealStep A Λ hd n (s,r)).1 (n+1)
  simp only [revealStep, dite_eq_left hn, linearHistory]
  rw [← hh]
  congr 1
  exact (roundReply_correct hk Λ s.2.1 x r hH₂).symm

def completeRevealState {Ω : Type*} {d q : ℕ} (n : ℕ)
    (p : RevealState Ω d q n × Rotations d) : Ω × Rotations d :=
  (p.1.1,frameCompletion p.1.2.1 p.2)

lemma measurable_completeRevealState {Ω : Type*} [MeasurableSpace Ω] {d q : ℕ} (n : ℕ) :
    Measurable (completeRevealState (Ω := Ω) (d := d) (q := q) n) :=
  measurable_fst.fst.prodMk ((measurable_frameCompletion (d := d)).comp
    (f := fun p : RevealState Ω d q n × Rotations d => (p.1.2.1,p.2))
    (measurable_fst.snd.fst.prodMk measurable_snd))

lemma revealStep_completion_law {Ω : Type*} [MeasurableSpace Ω] {d q : ℕ}
    (A : OracleAlgorithm Ω d q) (Λ : Point d →L[ℝ] Point d) (hd : 2*q+1 ≤ d)
    (n : ℕ) (hn : n < q) (s : RevealState Ω d q n) :
    ((roundRandomLaw d).prod (remainingHaar (prefixSpace d (2*(n+1))))).map
      (fun p => completeRevealState (n+1) (revealStep A Λ hd n (s,p.1),p.2)) =
      (remainingHaar (prefixSpace d (2*n))).map (fun h => completeRevealState n (s,h)) := by
  have hk : 2*n+1 < d := by omega
  have he := congrArg (fun ν : Measure (Rotations d) => ν.map (fun O => (s.1,O)))
    (roundFrames_law hk Λ s.2.1 (A.query ⟨n,hn⟩ (s.1,s.2.2.1)))
  have hf : Measurable (fun p : RoundRandom d × Rotations d =>
      frameCompletion (roundFrames hk Λ s.2.1 (A.query ⟨n,hn⟩ (s.1,s.2.2.1)) p.1) p.2) :=
    (measurable_frameCompletion (d := d)).comp
      (f := fun p : RoundRandom d × Rotations d =>
        (roundFrames hk Λ s.2.1 (A.query ⟨n,hn⟩ (s.1,s.2.2.1)) p.1,p.2))
      (((measurable_roundFrames hk Λ).comp
        (f := fun p : RoundRandom d × Rotations d =>
          ((s.2.1,A.query ⟨n,hn⟩ (s.1,s.2.2.1)),p.1))
        (measurable_const.prodMk measurable_fst)).prodMk measurable_snd)
  rw [Measure.map_map (by fun_prop) hf, Measure.map_map (by fun_prop) (by fun_prop)] at he
  simpa only [completeRevealState,revealStep,dite_eq_left hn,roundRandomLaw,
    Nat.mul_add,Nat.mul_one,Function.comp_def] using he

theorem revealState_completion_law {Ω : Type*} [MeasurableSpace Ω] {d q : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (A : OracleAlgorithm Ω d q)
    (Λ : Point d →L[ℝ] Point d) (hd : 2*q+1 ≤ d) :
    ((stateLaw (μ.map (initialRevealState (d := d) (q := q))) (roundRandomLaw d)
        (revealStep A Λ hd) q).prod (remainingHaar (prefixSpace d (2*q)))).map
      (completeRevealState q) = μ.prod (rotationHaar d) := by
  have hi := measurable_initialRevealState (Ω := Ω) (d := d) (q := q)
  rw [stateLaw_completion _ _ _ (measurable_revealStep A Λ hd)
    (fun n => remainingHaar (prefixSpace d (2*n)))
    (fun n => completeRevealState (Ω := Ω) (d := d) (q := q) n)
    (fun n => measurable_completeRevealState n) q
    (fun n hn s => revealStep_completion_law A Λ hd n hn s)]
  simp only [Nat.mul_zero, prefixSpace_zero, remainingHaar_bot]
  have hp := Measure.map_prod_map μ (rotationHaar d) hi measurable_id
  rw [Measure.map_id] at hp
  rw [hp,Measure.map_map (measurable_completeRevealState 0) (hi.prodMap measurable_id)]
  convert (Measure.map_id (μ := μ.prod (rotationHaar d))) using 1
  congr 1
  funext p
  simp [completeRevealState,initialRevealState,frameCompletion]

end LogConcaveSampling.LowerBound

namespace LogConcaveSampling.LowerBound

def finishFrame {Ω : Type*} [MeasurableSpace Ω] {d q : ℕ}
    (A : OracleAlgorithm Ω d q) (hd : 2*q < d)
    (p : RevealState Ω d q q × Point d) : Frames d :=
  inverseFrameUpdate hd p.1.2.1 (A.output (p.1.1,p.1.2.2.1)) p.2

lemma measurable_finishFrame {Ω : Type*} [MeasurableSpace Ω] {d q : ℕ}
    (A : OracleAlgorithm Ω d q) (hd : 2*q < d) : Measurable (finishFrame A hd) := by
  apply (measurable_inverseFrameUpdate hd).comp
    (f := fun p : RevealState Ω d q q × Point d =>
      (p.1.2.1,A.output (p.1.1,p.1.2.2.1),p.2))
  exact measurable_fst.snd.fst.prodMk
    ((A.output_measurable.comp (measurable_fst.fst.prodMk measurable_fst.snd.snd.fst)).prodMk measurable_snd)

def finishComplete {Ω : Type*} [MeasurableSpace Ω] {d q : ℕ}
    (A : OracleAlgorithm Ω d q) (hd : 2*q < d)
    (p : (RevealState Ω d q q × Point d) × Rotations d) : Ω × Rotations d :=
  (p.1.1.1,frameCompletion (finishFrame A hd p.1) p.2)

lemma measurable_finishComplete {Ω : Type*} [MeasurableSpace Ω] {d q : ℕ}
    (A : OracleAlgorithm Ω d q) (hd : 2*q < d) : Measurable (finishComplete A hd) := by
  exact measurable_fst.fst.fst.prodMk ((measurable_frameCompletion (d := d)).comp
    (f := fun p : (RevealState Ω d q q × Point d) × Rotations d =>
      (finishFrame A hd p.1,p.2))
    (((measurable_finishFrame A hd).comp measurable_fst).prodMk measurable_snd))

lemma finishComplete_law {Ω : Type*} [MeasurableSpace Ω] {d q : ℕ}
    (A : OracleAlgorithm Ω d q) (hd : 2*q < d)
    (ν : Measure (RevealState Ω d q q)) [IsProbabilityMeasure ν] :
    ((ν.prod (stdGaussian (Point d))).prod
      (remainingHaar (prefixSpace d (2*q+1)))).map (finishComplete A hd) =
      (ν.prod (remainingHaar (prefixSpace d (2*q)))).map (completeRevealState q) := by
  have hlocal (s : RevealState Ω d q q) :
      ((stdGaussian (Point d)).prod (remainingHaar (prefixSpace d (2*q+1)))).map
          (fun p => finishComplete A hd ((s,p.1),p.2)) =
        (remainingHaar (prefixSpace d (2*q))).map
          (fun h => completeRevealState q (s,h)) := by
    have he := congrArg (fun η : Measure (Rotations d) => η.map (fun O => (s.1,O)))
      (inverseFrameUpdate_law hd s.2.1 (A.output (s.1,s.2.2.1)))
    rw [Measure.map_map (by fun_prop) (by fun_prop),
      Measure.map_map (by fun_prop) (by fun_prop)] at he
    exact he
  have he := eliminate_fresh_residual (μ := ν) (γ := stdGaussian (Point d))
    (η := remainingHaar (prefixSpace d (2*q)))
    (η' := remainingHaar (prefixSpace d (2*q+1)))
    (step := id) measurable_id (measurable_finishComplete A hd)
    (measurable_completeRevealState q) hlocal
  rwa [Measure.map_id] at he

def finishCoordinate {Ω : Type*} [MeasurableSpace Ω] {d q : ℕ}
    (A : OracleAlgorithm Ω d q) (hd : 2*q < d)
    (p : RevealState Ω d q q × Point d) : Point d :=
  (frameTransport (finishFrame A hd p)).symm (A.output (p.1.1,p.1.2.2.1))

lemma measurable_finishCoordinate {Ω : Type*} [MeasurableSpace Ω] {d q : ℕ}
    (A : OracleAlgorithm Ω d q) (hd : 2*q < d) : Measurable (finishCoordinate A hd) := by
  exact (measurable_inverse_frameTransport (d := d)).comp
    (f := fun p : RevealState Ω d q q × Point d =>
      (finishFrame A hd p,A.output (p.1.1,p.1.2.2.1)))
    ((measurable_finishFrame A hd).prodMk
      (A.output_measurable.comp (measurable_fst.fst.prodMk measurable_fst.snd.snd.fst)))

lemma finishCoordinate_mem {Ω : Type*} [MeasurableSpace Ω] {d q : ℕ}
    (A : OracleAlgorithm Ω d q) (hd : 2*q < d) (p : RevealState Ω d q q × Point d)
    (hg : (prefixSpace d (2*q))ᗮ.orthogonalProjectionOnto (rotationIsometry p.1.2.1.2⁻¹ p.2) ≠ 0) :
    finishCoordinate A hd p ∈ frameSpace p.1.2.1.2 (prefixSpace d (2*q)) ⊔ ℝ ∙ p.2 := by
  have hx : A.output (p.1.1,p.1.2.2.1) ∈ frameSpace (finishFrame A hd p).1
      (prefixSpace d (2*q+1)) := by
    simp only [finishFrame,inverseFrameUpdate_eq]
    exact mem_frameSpace_extendFrame hd _ _
  have hu := frameTransport_preimage_mem _ (finishFrame A hd p) hx
  have hb := frameSpace_extendFrame_le hd p.1.2.1.2 p.2 hg
  exact hb hu

lemma finishCoordinate_correct {Ω : Type*} [MeasurableSpace Ω] {d q : ℕ}
    (A : OracleAlgorithm Ω d q) (Λ : Point d →L[ℝ] Point d) (hd : 2*q < d)
    (s : RevealState Ω d q q) (g : Point d) (hs : HistoryConsistent A Λ q s)
    {H : Rotations d} (hH : H ∈ subspaceStabilizer (prefixSpace d (2*q+1))) :
    finishCoordinate A hd (s,g) =
      (rotationIsometry (finishComplete A hd ((s,g),H)).2).symm
        (A.output (s.1,linearHistory A Λ (finishComplete A hd ((s,g),H)).2 s.1 q)) := by
  have hH₀ : H ∈ subspaceStabilizer (prefixSpace d (2*q)) :=
    subspaceStabilizer_anti (prefixSpace_mono d (Nat.le_succ _)) hH
  obtain ⟨H',hH',he⟩ := compatibleFrames_reconstruct _
    (compatibleFrames_inverseUpdate hd s.2.1 (A.output (s.1,s.2.2.1)) g) hH₀
  have hh : s.2.2.1 = linearHistory A Λ (finishComplete A hd ((s,g),H)).2 s.1 q := by
    change s.2.2.1 = linearHistory A Λ (frameCompletion (finishFrame A hd (s,g)) H) s.1 q
    rw [finishFrame,he]
    exact hs H' hH'
  rw [← hh]
  symm
  apply frameCompletion_symm_eq_transport _ (finishFrame A hd (s,g)) hH
  simp only [finishFrame,inverseFrameUpdate_eq]
  exact mem_frameSpace_extendFrame hd _ _

end LogConcaveSampling.LowerBound

namespace LogConcaveSampling.LowerBound
section
variable {E : Type*} [AddCommGroup E] [Module ℝ E]

def powerHull (L : E →ₗ[ℝ] E) : ℕ → Submodule ℝ E → Submodule ℝ E
  | 0, K => K
  | n+1, K => K ⊔ (powerHull L n K).map L

lemma powerHull_mono_base (L : E →ₗ[ℝ] E) (n : ℕ) {K K' : Submodule ℝ E} (h : K ≤ K') :
    powerHull L n K ≤ powerHull L n K' := by
  induction n with
  | zero => exact h
  | succ n ih => exact sup_le_sup h (Submodule.map_mono ih)

lemma le_powerHull (L : E →ₗ[ℝ] E) (n : ℕ) (K : Submodule ℝ E) : K ≤ powerHull L n K := by
  cases n with
  | zero => exact le_rfl
  | succ n => exact le_sup_left

lemma powerHull_le_succ (L : E →ₗ[ℝ] E) (n : ℕ) (K : Submodule ℝ E) :
    powerHull L n K ≤ powerHull L (n+1) K := by
  induction n with
  | zero => exact le_sup_left
  | succ n ih => exact sup_le_sup le_rfl (Submodule.map_mono ih)

lemma powerHull_mono_degree (L : E →ₗ[ℝ] E) {m n : ℕ} (h : m ≤ n) (K : Submodule ℝ E) :
    powerHull L m K ≤ powerHull L n K := by
  exact monotone_nat_of_le_succ (fun n => powerHull_le_succ L n K) h

def tapeHull {n : ℕ} (t : Fin n → E × E) : Submodule ℝ E :=
  Submodule.span ℝ (Set.range (fun i => (t i).1) ∪ Set.range (fun i => (t i).2))

lemma tapeHull_empty (t : Fin 0 → E × E) : tapeHull t = ⊥ := by
  simp [tapeHull]

lemma tapeHull_snoc {n : ℕ} (t : Fin n → E × E) (a b : E) :
    tapeHull (Fin.snoc (α := fun _ : Fin (n+1) => E × E) t (a,b)) =
      (tapeHull t ⊔ ℝ ∙ a) ⊔ ℝ ∙ b := by
  unfold tapeHull
  simp only [← Submodule.span_union]
  congr 1
  ext x
  simp only [Set.mem_union, Set.mem_range, Set.mem_singleton_iff]
  constructor
  · rintro (⟨i,hi⟩ | ⟨i,hi⟩)
    · refine Fin.lastCases ?_ (fun j => ?_) i hi
      · simp only [Fin.snoc_last]; intro h; exact Or.inl (Or.inr h.symm)
      · simp only [Fin.snoc_castSucc]; intro h; exact Or.inl (Or.inl (Or.inl ⟨j,h⟩))
    · refine Fin.lastCases ?_ (fun j => ?_) i hi
      · simp only [Fin.snoc_last]; intro h; exact Or.inr h.symm
      · simp only [Fin.snoc_castSucc]; intro h; exact Or.inl (Or.inl (Or.inr ⟨j,h⟩))
  · rintro (((⟨i,hi⟩ | ⟨i,hi⟩) | h) | h)
    · exact Or.inl ⟨i.castSucc, by simpa only [Fin.snoc_castSucc] using hi⟩
    · exact Or.inr ⟨i.castSucc, by simpa only [Fin.snoc_castSucc] using hi⟩
    · exact Or.inl ⟨Fin.last n, by simpa only [Fin.snoc_last] using h.symm⟩
    · exact Or.inr ⟨Fin.last n, by simpa only [Fin.snoc_last] using h.symm⟩

lemma powerHull_round_growth (L : E →ₗ[ℝ] E) {n : ℕ} {K : Submodule ℝ E}
    {t : Fin n → E × E} (hK : K ≤ powerHull L n (tapeHull t)) (a b : E) :
    ((K ⊔ ℝ ∙ a) ⊔ (K ⊔ ℝ ∙ a).map L) ⊔ ℝ ∙ b ≤
      powerHull L (n+1) (tapeHull (Fin.snoc (α := fun _ : Fin (n+1) => E × E) t (a,b))) := by
  rw [tapeHull_snoc]
  let K' := (tapeHull t ⊔ ℝ ∙ a) ⊔ ℝ ∙ b
  have hbase : tapeHull t ≤ K' := le_sup_left.trans le_sup_left
  have ha : ℝ ∙ a ≤ K' := le_sup_right.trans le_sup_left
  have hb : ℝ ∙ b ≤ K' := le_sup_right
  have hK' : K ⊔ ℝ ∙ a ≤ powerHull L n K' := sup_le
    (hK.trans (powerHull_mono_base L n hbase)) (ha.trans (le_powerHull L n K'))
  exact sup_le (sup_le (hK'.trans (powerHull_le_succ L n K'))
    ((Submodule.map_mono hK').trans le_sup_right)) (hb.trans (le_powerHull L (n+1) K'))

end
end LogConcaveSampling.LowerBound

namespace LogConcaveSampling.LowerBound

lemma measurable_frameProjection (d k : ℕ) :
    Measurable (fun p : Rotations d × Point d =>
      (prefixSpace d k)ᗮ.orthogonalProjectionOnto (rotationIsometry p.1⁻¹ p.2)) := by
  fun_prop

def roundGood {Ω : Type*} [MeasurableSpace Ω] {d q : ℕ}
    (A : OracleAlgorithm Ω d q) (hd : 2*q+1 ≤ d) (n : ℕ)
    (p : RevealState Ω d q n × RoundRandom d) : Prop :=
  if hn : n < q then
    let hk : 2*n < d := by omega
    (prefixSpace d (2*n))ᗮ.orthogonalProjectionOnto (rotationIsometry p.1.2.1.2⁻¹ p.2.1) ≠ 0 ∧
    (prefixSpace d (2*n+1))ᗮ.orthogonalProjectionOnto
      (rotationIsometry (inverseFrameUpdate hk p.1.2.1
        (A.query ⟨n,hn⟩ (p.1.1,p.1.2.2.1)) p.2.1).2⁻¹ p.2.2.1) ≠ 0
  else True

lemma measurableSet_roundGood {Ω : Type*} [MeasurableSpace Ω] {d q : ℕ}
    (A : OracleAlgorithm Ω d q) (hd : 2*q+1 ≤ d) (n : ℕ) :
    MeasurableSet {p | roundGood A hd n p} := by
  unfold roundGood
  split_ifs with hn
  · let Z := RevealState Ω d q n × RoundRandom d
    have hk : 2*n < d := by omega
    let x : Z → Point d := fun p => A.query ⟨n,hn⟩ (p.1.1,p.1.2.2.1)
    have hx : Measurable x := (A.query_measurable _).comp
      (measurable_fst.fst.prodMk measurable_fst.snd.snd.fst)
    let F : Z → Frames d := fun p => inverseFrameUpdate hk p.1.2.1 (x p) p.2.1
    have hF : Measurable F := (measurable_inverseFrameUpdate hk).comp
      (f := fun p : Z => (p.1.2.1,x p,p.2.1))
      (measurable_fst.snd.fst.prodMk (hx.prodMk measurable_snd.fst))
    have h₁ : Measurable (fun p : Z =>
        (prefixSpace d (2*n))ᗮ.orthogonalProjectionOnto (rotationIsometry p.1.2.1.2⁻¹ p.2.1)) :=
      (measurable_frameProjection d (2*n)).comp
      (f := fun p : Z => (p.1.2.1.2,p.2.1))
      (measurable_fst.snd.fst.snd.prodMk measurable_snd.fst)
    have h₂ : Measurable (fun p : Z =>
        (prefixSpace d (2*n+1))ᗮ.orthogonalProjectionOnto (rotationIsometry (F p).2⁻¹ p.2.2.1)) :=
      (measurable_frameProjection d (2*n+1)).comp
      (f := fun p : Z => ((F p).2,p.2.2.1)) (hF.snd.prodMk measurable_snd.snd.fst)
    exact ((measurableSet_singleton 0).compl.preimage h₁).inter
      ((measurableSet_singleton 0).compl.preimage h₂)
  · exact MeasurableSet.univ

lemma ae_roundGood {Ω : Type*} [MeasurableSpace Ω] {d q : ℕ}
    (A : OracleAlgorithm Ω d q) (hd : 2*q+1 ≤ d) (n : ℕ) (hn : n < q)
    (s : RevealState Ω d q n) : ∀ᵐ r ∂roundRandomLaw d, roundGood A hd n (s,r) := by
  have hk : 2*n < d := by omega
  have hk' : 2*n+1 < d := by omega
  apply (Measure.ae_prod_iff_ae_ae
    ((measurableSet_roundGood A hd n).preimage (measurable_const.prodMk measurable_id))).mpr
  filter_upwards [ae_frameGaussian_nonzero hk s.2.1.2] with g hg
  have h := (Measure.quasiMeasurePreserving_fst
    (μ := stdGaussian (Point d)) (ν := stdGaussian (Point d))).ae
    (ae_frameGaussian_nonzero hk'
      (inverseFrameUpdate hk s.2.1 (A.query ⟨n,hn⟩ (s.1,s.2.2.1)) g).2)
  filter_upwards [h] with r hr
  simpa only [roundGood,dite_eq_left hn, id_eq] using And.intro hg hr

def SpanConsistent {Ω : Type*} {d q : ℕ} (Λ : Point d →L[ℝ] Point d) (n : ℕ)
    (s : RevealState Ω d q n) : Prop :=
  frameSpace s.2.1.2 (prefixSpace d (2*n)) ≤ powerHull Λ.toLinearMap n (tapeHull s.2.2.2)

lemma revealStep_spanConsistent {Ω : Type*} [MeasurableSpace Ω] {d q n : ℕ}
    (A : OracleAlgorithm Ω d q) (Λ : Point d →L[ℝ] Point d) (hd : 2*q+1 ≤ d)
    (hn : n < q) (s : RevealState Ω d q n) (r : RoundRandom d)
    (hs : SpanConsistent Λ n s) (hg : roundGood A hd n (s,r)) :
    SpanConsistent Λ (n+1) (revealStep A Λ hd n (s,r)) := by
  have hk : 2*n+1 < d := by omega
  simp only [roundGood,dite_eq_left hn] at hg
  have h := (roundFrames_span_growth hk Λ s.2.1 (A.query ⟨n,hn⟩ (s.1,s.2.2.1)) r hg.1 hg.2).trans
    (powerHull_round_growth Λ.toLinearMap hs r.1 r.2.1)
  have hF : (revealStep A Λ hd n (s,r)).2.1 =
      roundFrames hk Λ s.2.1 (A.query ⟨n,hn⟩ (s.1,s.2.2.1)) r := by
    simp only [revealStep,dite_eq_left hn]
  have ht : (revealStep A Λ hd n (s,r)).2.2.2 =
      Fin.snoc (α := fun _ : Fin (n+1) => Point d × Point d) s.2.2.2 (r.1,r.2.1) := by
    simp only [revealStep,dite_eq_left hn]
  unfold SpanConsistent
  rw [hF,ht,show 2*(n+1) = 2*n+2 by omega]
  exact h

lemma revealRun_historyConsistent {Ω : Type*} [MeasurableSpace Ω] {d q : ℕ}
    (A : OracleAlgorithm Ω d q) (Λ : Point d →L[ℝ] Point d) (hd : 2*q+1 ≤ d)
    (n : ℕ) (hn : n ≤ q) (p : Ω × (Fin n → RoundRandom d)) :
    HistoryConsistent A Λ n (stateRun initialRevealState (revealStep A Λ hd) n p) := by
  induction n with
  | zero => exact initial_historyConsistent A Λ p.1
  | succ n ih =>
    exact revealStep_historyConsistent A Λ hd (by omega) _ _ (ih (by omega) _)

lemma revealRun_spanConsistent {Ω : Type*} [MeasurableSpace Ω] {d q : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (A : OracleAlgorithm Ω d q)
    (Λ : Point d →L[ℝ] Point d) (hd : 2*q+1 ≤ d) :
    ∀ᵐ p ∂μ.prod (Measure.pi (fun _ : Fin q => roundRandomLaw d)),
      SpanConsistent Λ q (stateRun initialRevealState (revealStep A Λ hd) q p) := by
  apply stateRun_ae_invariant μ (roundRandomLaw d) initialRevealState
    measurable_initialRevealState (revealStep A Λ hd) (measurable_revealStep A Λ hd)
    (fun n => SpanConsistent Λ n) q (roundGood A hd) (measurableSet_roundGood A hd)
    (ae_roundGood A hd)
  · intro ω
    simp [SpanConsistent,initialRevealState,frameSpace,prefixSpace_zero,powerHull]
  · intro n hn s r hs hg
    exact revealStep_spanConsistent A Λ hd hn s r hs hg

end LogConcaveSampling.LowerBound

namespace LogConcaveSampling.LowerBound
section
variable {E : Type*} [AddCommGroup E] [Module ℝ E]
def orbitHull {ι : Type*} (L : E →ₗ[ℝ] E) (n : ℕ) (t : ι → E) : Submodule ℝ E :=
  Submodule.span ℝ {v | ∃ i : ι, ∃ j : ℕ, j ≤ n ∧ v = (L^[j]) (t i)}

lemma orbitHull_mono {ι : Type*} (L : E →ₗ[ℝ] E) {m n : ℕ} (hmn : m ≤ n) (t : ι → E) :
    orbitHull L m t ≤ orbitHull L n t := by
  apply Submodule.span_mono
  rintro v ⟨i,j,hj,rfl⟩
  exact ⟨i,j,hj.trans hmn,rfl⟩

lemma map_orbitHull_le_succ {ι : Type*} (L : E →ₗ[ℝ] E) (n : ℕ) (t : ι → E) :
    (orbitHull L n t).map L ≤ orbitHull L (n+1) t := by
  rw [orbitHull,Submodule.map_span]
  apply Submodule.span_le.mpr
  rintro v ⟨u,⟨i,j,hj,rfl⟩,rfl⟩
  apply Submodule.subset_span
  refine ⟨i,j+1,Nat.succ_le_succ hj,?_⟩
  exact (Function.iterate_succ_apply' L j (t i)).symm

lemma span_range_le_orbitHull {ι : Type*} (L : E →ₗ[ℝ] E) (n : ℕ) (t : ι → E) :
    Submodule.span ℝ (Set.range t) ≤ orbitHull L n t := by
  apply Submodule.span_le.mpr
  rintro v ⟨i,rfl⟩
  exact Submodule.subset_span ⟨i,0,Nat.zero_le n,rfl⟩

lemma powerHull_le_orbitHull {ι : Type*} (L : E →ₗ[ℝ] E) (n : ℕ) (t : ι → E)
    {K : Submodule ℝ E} (hK : K ≤ Submodule.span ℝ (Set.range t)) :
    powerHull L n K ≤ orbitHull L n t := by
  induction n with
  | zero => exact hK.trans (span_range_le_orbitHull L 0 t)
  | succ n ih =>
    exact sup_le (hK.trans (span_range_le_orbitHull L (n+1) t))
      ((Submodule.map_mono ih).trans (map_orbitHull_le_succ L n t))

end
end LogConcaveSampling.LowerBound

end LowerProof
end
end
end

end OAI
