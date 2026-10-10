import Mathlib
import OAI.Probability.ThreeState.Expectations

namespace OAI

/-! Likelihood messages, compact couplings and subsequential posterior limits. -/

namespace ThreeState
open MeasureTheory

 
abbrev Message := {m : Spin → ℝ // (∀ i, 0 ≤ m i) ∧ ∑ i, m i = 3}

instance : CoeFun Message (fun _ => Spin → ℝ) := ⟨Subtype.val⟩

lemma Message.nonneg (m : Message) (i : Spin) : 0 ≤ m i := m.2.1 i
lemma Message.sum (m : Message) : ∑ i, m i = 3 := m.2.2
lemma Message.le_three (m : Message) (i : Spin) : m i ≤ 3 := by
  calc
    m i ≤ ∑ j, m j := Finset.single_le_sum (fun j _ => Message.nonneg m j) (Finset.mem_univ i)
    _ = 3 := Message.sum m

lemma message_isCompact : IsCompact {m : Spin → ℝ | (∀ i, 0 ≤ m i) ∧ ∑ i, m i = 3} := by
  have hc : IsClosed {m : Spin → ℝ | (∀ i, 0 ≤ m i) ∧ ∑ i, m i = 3} := by
    apply IsClosed.inter
    · have he : {m : Spin → ℝ | ∀ i, 0 ≤ m i} =
          ⋂ i : Spin, {m : Spin → ℝ | 0 ≤ m i} := by ext m; simp
      change IsClosed {m : Spin → ℝ | ∀ i, 0 ≤ m i}
      rw [he]
      exact isClosed_iInter (fun i : Spin => isClosed_le (continuous_const (y := (0:ℝ)))
          (continuous_apply i : Continuous (fun m : Spin → ℝ => m i)))
    · exact isClosed_eq (continuous_finsetSum _ (fun i _ => continuous_apply i)) continuous_const
  apply (isCompact_Icc (a := (fun _ : Spin => (0:ℝ))) (b := fun _ => (3:ℝ))).of_isClosed_subset hc
  intro m hm
  exact ⟨hm.1, fun i => Message.le_three ⟨m,hm⟩ i⟩

instance : CompactSpace Message := isCompact_iff_compactSpace.mp message_isCompact
noncomputable def uninformative : Message := ⟨fun _ => 1, by simp⟩

 
noncomputable def likelihood {α : Type*} (law : Spin → PMF α) (y : α) : Message :=
  ⟨fun i => 3*posterior law y i, by
    constructor
    · intro i; exact mul_nonneg (by norm_num) (posterior_nonneg law y i)
    · rw [← Finset.mul_sum, posterior_sum]; norm_num⟩

lemma likelihood_apply {α : Type*} (law : Spin → PMF α) (y : α) (i : Spin) :
    likelihood law y i = 3*posterior law y i := rfl

lemma weighted_likelihood {α : Type*} (law : Spin → PMF α) (y : α) (i : Spin) :
    mass (marginal law) y * likelihood law y i = mass (law i) y := by
  rw [likelihood_apply]
  have hh := weighted_posterior law y i
  nlinarith

lemma hasMean_likelihood {α : Type*} (law : Spin → PMF α) (i : Spin) :
    HasMean (marginal law) (fun y => likelihood law y i) := by
  exact (mass_summable (law i)).congr (fun y => (weighted_likelihood law y i).symm)

lemma mean_likelihood {α : Type*} (law : Spin → PMF α) (i : Spin) :
    mean (marginal law) (fun y => likelihood law y i) = 1 := by
  unfold mean
  simp_rw [weighted_likelihood]
  exact mass_sum _

noncomputable def likelihoodPMF {α : Type*} (law : Spin → PMF α) : PMF Message :=
  (marginal law).map (likelihood law)

noncomputable def likelihoodLaw {α : Type*} (law : Spin → PMF α) : ProbabilityMeasure Message :=
  ⟨(likelihoodPMF law).toMeasure, inferInstance⟩

lemma mean_likelihoodPMF {α : Type*} (law : Spin → PMF α) (f : Message → ℝ)
    (hf : HasMean (marginal law) (fun y => f (likelihood law y))) :
    mean (likelihoodPMF law) f = mean (marginal law) (fun y => f (likelihood law y)) :=
  mean_map hf

lemma integral_likelihoodLaw {α : Type*} (law : Spin → PMF α) (f : C(Message,ℝ)) :
    ∫ m, f m ∂(likelihoodLaw law : Measure Message) =
      mean (marginal law) (fun y => f (likelihood law y)) := by
  have hf : Integrable f (likelihoodPMF law).toMeasure := f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)
  change (∫ m, f m ∂(likelihoodPMF law).toMeasure) = _
  rw [PMF.integral_eq_tsum _ _ hf]
  change mean (likelihoodPMF law) f = _
  apply mean_likelihoodPMF
  obtain ⟨C,hC⟩ := isCompact_univ.exists_bound_of_continuousOn f.continuous.continuousOn
  apply HasMean.of_abs
  apply (hasMean_const (marginal law) C).mono (fun y => abs_nonneg _)
  intro y
  simpa only [Real.norm_eq_abs] using hC (likelihood law y) (Set.mem_univ _)

end ThreeState

namespace ThreeState
open MeasureTheory

lemma abs_likelihood {α : Type*} (law : Spin → PMF α) (y : α) (i : Spin) :
    |likelihood law y i| ≤ 3 := by
  rw [abs_of_nonneg (Message.nonneg _ _)]
  exact Message.le_three _ _

lemma abs_likelihood_square {α : Type*} (law : Spin → PMF α) (y : α) (i : Spin) :
    |(likelihood law y i)^2| ≤ 9 := by
  rw [abs_sq]
  have h := abs_likelihood law y i
  have hl := (abs_le.mp h).1
  have hu := (abs_le.mp h).2
  nlinarith

lemma mean_likelihood_mul {α : Type*} (law : Spin → PMF α) (i : Spin) (f : α → ℝ) :
    mean (marginal law) (fun y => likelihood law y i * f y) = mean (law i) f := by
  unfold mean
  apply tsum_congr
  intro y
  rw [← mul_assoc, weighted_likelihood]

 
lemma mean_joint_likelihood_mul {α β : Type*} (law : Spin → PMF α) (k : α → PMF β)
    (i : Spin) (f : β → ℝ) (C : ℝ) (hC : 0 ≤ C) (hf : ∀ b, |f b| ≤ C) :
    mean (joint (marginal law) k) (fun ab => likelihood law ab.1 i * f ab.2) =
      mean (marginal (fun j => (law j).bind k))
        (fun b => likelihood (fun j => (law j).bind k) b i * f b) := by
  rw [mean_joint_bounded _ _ _ (3*C) (fun ab => by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left (hf _) (abs_nonneg _)).trans
      (mul_le_mul_of_nonneg_right (abs_likelihood _ _ _) hC))]
  simp_rw [mean_const_mul]
  rw [mean_likelihood_mul, mean_likelihood_mul, mean_bind_bounded _ _ _ C hf]

lemma mean_joint_likelihood_square {α β : Type*} (law : Spin → PMF α) (k : α → PMF β)
    (i : Spin) :
    mean (joint (marginal law) k) (fun ab =>
      (likelihood law ab.1 i - likelihood (fun j => (law j).bind k) ab.2 i)^2) =
      mean (marginal law) (fun a => (likelihood law a i)^2) -
      mean (marginal (fun j => (law j).bind k))
        (fun b => (likelihood (fun j => (law j).bind k) b i)^2) := by
  let p := joint (marginal law) k
  let u := fun ab : α × β => likelihood law ab.1 i
  let v := fun ab : α × β => likelihood (fun j => (law j).bind k) ab.2 i
  have hu : ∀ ab, |u ab| ≤ 3 := fun ab => abs_likelihood _ _ _
  have hv : ∀ ab, |v ab| ≤ 3 := fun ab => abs_likelihood _ _ _
  have husq : ∀ ab, |(u ab)^2| ≤ 9 := fun ab => by
    rw [abs_sq]; nlinarith [sq_le_sq₀ (abs_nonneg (u ab)) (by norm_num : (0:ℝ) ≤ 3) |>.2 (hu ab), sq_abs (u ab)]
  have hvsq : ∀ ab, |(v ab)^2| ≤ 9 := fun ab => by
    rw [abs_sq]; nlinarith [sq_le_sq₀ (abs_nonneg (v ab)) (by norm_num : (0:ℝ) ≤ 3) |>.2 (hv ab), sq_abs (v ab)]
  have huv : ∀ ab, |u ab * v ab| ≤ 9 := fun ab => by
    rw [abs_mul]; exact (mul_le_mul (hu ab) (hv ab) (abs_nonneg _) (by norm_num)).trans_eq (by norm_num)
  change mean p (fun ab => (u ab-v ab)^2) = _
  rw [mean_congr p (g := fun ab => ((u ab)^2+(v ab)^2)+ (-2)*(u ab*v ab)) (fun ab => by ring),
    mean_add ((hasMean_bounded p 9 husq).add (hasMean_bounded p 9 hvsq))
      ((hasMean_bounded p 9 huv).const_mul (-2)),
    mean_add (hasMean_bounded p 9 husq) (hasMean_bounded p 9 hvsq), mean_const_mul]
  change mean (joint (marginal law) k) (fun ab => (likelihood law ab.1 i)^2) +
    mean (joint (marginal law) k) (fun ab => (likelihood (fun j => (law j).bind k) ab.2 i)^2) +
    -2 * mean (joint (marginal law) k) (fun ab => likelihood law ab.1 i * likelihood (fun j => (law j).bind k) ab.2 i) = _
  rw [mean_joint_fst (marginal law) k (fun a => (likelihood law a i)^2) 9
      (fun a => abs_likelihood_square law a i),
    mean_joint_snd (marginal law) k (fun b => (likelihood (fun j => (law j).bind k) b i)^2) 9
      (fun b => abs_likelihood_square _ b i),
    mean_joint_likelihood_mul law k i (fun b => likelihood (fun j => (law j).bind k) b i) 3
      (by norm_num) (fun b => abs_likelihood (fun j => (law j).bind k) b i),
    ← marginal_bind]
  simp only [← sq]
  ring

end ThreeState

namespace ThreeState
open MeasureTheory Filter Topology

lemma joint_map_fst {α β : Type*} (p : PMF α) (k : α → PMF β) :
    (joint p k).map Prod.fst = p := by
  simp only [joint, PMF.map_bind, PMF.map_comp, Function.comp_def]
  change (p.bind (fun a => (k a).map (Function.const β a))) = _
  simp only [PMF.map_const, PMF.bind_pure]

lemma joint_map_snd {α β : Type*} (p : PMF α) (k : α → PMF β) :
    (joint p k).map Prod.snd = p.bind k := by
  simp only [joint, PMF.map_bind, PMF.map_comp, Function.comp_def]
  change (p.bind (fun a => (k a).map id)) = _
  simp only [PMF.map_id]

noncomputable def messageCouplingPMF {α β : Type*} (law : Spin → PMF α) (k : α → PMF β) :
    PMF (Message × Message) :=
  (joint (marginal law) k).map (fun ab => (likelihood law ab.1, likelihood (fun j => (law j).bind k) ab.2))

noncomputable def messageCoupling {α β : Type*} (law : Spin → PMF α) (k : α → PMF β) :
    ProbabilityMeasure (Message × Message) := ⟨(messageCouplingPMF law k).toMeasure, inferInstance⟩

lemma messageCouplingPMF_fst {α β : Type*} (law : Spin → PMF α) (k : α → PMF β) :
    (messageCouplingPMF law k).map Prod.fst = likelihoodPMF law := by
  rw [messageCouplingPMF, PMF.map_comp]
  change (joint (marginal law) k).map (likelihood law ∘ Prod.fst) = _
  rw [← PMF.map_comp, joint_map_fst]
  rfl

lemma messageCouplingPMF_snd {α β : Type*} (law : Spin → PMF α) (k : α → PMF β) :
    (messageCouplingPMF law k).map Prod.snd = likelihoodPMF (fun j => (law j).bind k) := by
  rw [messageCouplingPMF, PMF.map_comp]
  change (joint (marginal law) k).map (likelihood (fun j => (law j).bind k) ∘ Prod.snd) = _
  rw [← PMF.map_comp, joint_map_snd, ← marginal_bind]
  rfl

lemma messageCoupling_fst {α β : Type*} (law : Spin → PMF α) (k : α → PMF β) :
    (messageCoupling law k).map Prod.fst = likelihoodLaw law := by
  apply Subtype.ext
  change (messageCouplingPMF law k).toMeasure.map Prod.fst = (likelihoodPMF law).toMeasure
  rw [PMF.toMeasure_map _ _ measurable_fst, messageCouplingPMF_fst]

lemma messageCoupling_snd {α β : Type*} (law : Spin → PMF α) (k : α → PMF β) :
    (messageCoupling law k).map Prod.snd = likelihoodLaw (fun j => (law j).bind k) := by
  apply Subtype.ext
  change (messageCouplingPMF law k).toMeasure.map Prod.snd = (likelihoodPMF _).toMeasure
  rw [PMF.toMeasure_map _ _ measurable_snd, messageCouplingPMF_snd]

lemma integral_messageCoupling {α β : Type*} (law : Spin → PMF α) (k : α → PMF β)
    (f : C(Message × Message,ℝ)) :
    ∫ mm, f mm ∂(messageCoupling law k : Measure (Message × Message)) =
      mean (joint (marginal law) k) (fun ab => f (likelihood law ab.1, likelihood (fun j => (law j).bind k) ab.2)) := by
  have hi : Integrable f (messageCouplingPMF law k).toMeasure :=
    f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)
  change (∫ mm, f mm ∂(messageCouplingPMF law k).toMeasure) = _
  rw [PMF.integral_eq_tsum _ _ hi]
  change mean ((joint (marginal law) k).map _) f = _
  obtain ⟨C,hC⟩ := isCompact_univ.exists_bound_of_continuousOn f.continuous.continuousOn
  exact mean_map_bounded _ _ _ C (fun ab => by simpa only [Real.norm_eq_abs] using hC _ (Set.mem_univ _))

noncomputable def coordinateSecond {α : Type*} (law : Spin → PMF α) (i : Spin) : ℝ :=
  mean (marginal law) (fun a => (likelihood law a i)^2)

lemma coordinateSecond_nonneg {α : Type*} (law : Spin → PMF α) (i : Spin) :
    0 ≤ coordinateSecond law i := mean_nonneg _ (fun value => sq_nonneg (likelihood law value i))

lemma coordinateSecond_bind_le {α β : Type*} (law : Spin → PMF α) (k : α → PMF β) (i : Spin) :
    coordinateSecond (fun j => (law j).bind k) i ≤ coordinateSecond law i := by
  have hn := mean_nonneg (joint (marginal law) k) (fun ab =>
    sq_nonneg (likelihood law ab.1 i - likelihood (fun j => (law j).bind k) ab.2 i))
  rw [mean_joint_likelihood_square] at hn
  exact sub_nonneg.mp hn

noncomputable def squareJump (i : Spin) : C(Message × Message,ℝ) :=
  ⟨fun mm => (mm.1 i-mm.2 i)^2,
    (((continuous_apply i).comp (continuous_subtype_val.comp continuous_fst)).sub
      ((continuous_apply i).comp (continuous_subtype_val.comp continuous_snd))).pow 2⟩

lemma squareJump_nonneg (i : Spin) (mm : Message × Message) : 0 ≤ squareJump i mm := sq_nonneg _

lemma integral_squareJump {α β : Type*} (law : Spin → PMF α) (k : α → PMF β) (i : Spin) :
    ∫ mm, squareJump i mm ∂(messageCoupling law k : Measure (Message × Message)) =
      coordinateSecond law i - coordinateSecond (fun j => (law j).bind k) i := by
  rw [integral_messageCoupling]
  exact mean_joint_likelihood_square law k i

 

theorem likelihood_common_subsequence {α : ℕ → Type*} (law : ∀ n, Spin → PMF (α n))
    (k : ∀ n, α n → PMF (α (n+1)))
    (hstep : ∀ n i, law (n+1) i = (law n i).bind (k n)) :
    ∃ Q : ProbabilityMeasure Message, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun n => likelihoodLaw (law (φ n))) atTop (𝓝 Q) ∧
      Tendsto (fun n => likelihoodLaw (law (φ n+1))) atTop (𝓝 Q) := by
  have he (n : ℕ) : law (n+1) = (fun i => (law n i).bind (k n)) := funext (hstep n)
  have ha (i : Spin) : Antitone (fun n => coordinateSecond (law n) i) := by
    apply antitone_nat_of_succ_le
    intro n
    rw [he n]
    exact coordinateSecond_bind_le _ _ _
  have hb (i : Spin) : BddBelow (Set.range (fun n => coordinateSecond (law n) i)) :=
    ⟨0, by rintro _ ⟨n,rfl⟩; exact coordinateSecond_nonneg _ _⟩
  have ht (i : Spin) := tendsto_atTop_ciInf (ha i) (hb i)
  let Pn := fun n => messageCoupling (law n) (k n)
  obtain ⟨P,_,φ,hφ,hlim⟩ := isCompact_univ.tendsto_subseq (fun n => Set.mem_univ (Pn n))
  have hzero (i : Spin) : ∫ mm, squareJump i mm ∂(P : Measure (Message × Message)) = 0 := by
    have hdiff : Tendsto (fun n => coordinateSecond (law n) i - coordinateSecond (law (n+1)) i)
        atTop (𝓝 0) := by
      convert (ht i).sub ((ht i).comp (tendsto_add_atTop_nat 1)) using 1 <;> simp
    have hint := (ProbabilityMeasure.continuous_integral_continuousMap (squareJump i)).continuousAt.tendsto.comp hlim
    have hn : (fun n => ∫ mm, squareJump i mm ∂(Pn (φ n) : Measure (Message × Message))) =
        (fun n => coordinateSecond (law (φ n)) i - coordinateSecond (law (φ n+1)) i) := by
      funext n
      dsimp [Pn]
      rw [integral_squareJump, ← he]
    simp only [Function.comp_def] at hint
    rw [hn] at hint
    exact tendsto_nhds_unique hint (hdiff.comp hφ.tendsto_atTop)
  have hdiag : ∀ᵐ mm ∂(P : Measure (Message × Message)), mm.1 = mm.2 := by
    have hi (i : Spin) : ∀ᵐ mm ∂(P : Measure (Message × Message)), squareJump i mm = 0 :=
      (integral_eq_zero_iff_of_nonneg (squareJump_nonneg i)
        ((squareJump i).continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))).mp (hzero i)
    filter_upwards [ae_all_iff.mpr hi] with mm hmm
    apply Subtype.ext
    funext i
    have h := hmm i
    change (mm.1 i-mm.2 i)^2 = 0 at h
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp h)
  have hmaps : P.map Prod.snd = P.map Prod.fst := by
    apply Subtype.ext
    exact Measure.map_congr (hdiag.mono (fun mm hm => hm.symm))
  refine ⟨P.map Prod.fst, φ, hφ, ?_, ?_⟩
  · have hh := (ProbabilityMeasure.continuous_map (continuous_fst : Continuous (@Prod.fst Message Message))).tendsto P |>.comp hlim
    simpa only [Function.comp_def, Pn, messageCoupling_fst] using hh
  · have hh := (ProbabilityMeasure.continuous_map (continuous_snd : Continuous (@Prod.snd Message Message))).tendsto P |>.comp hlim
    simp only [Function.comp_def, Pn, messageCoupling_snd, ← he, hmaps] at hh
    exact hh

end ThreeState

end OAI
