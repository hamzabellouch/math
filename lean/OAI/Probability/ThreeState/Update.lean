import Mathlib
import OAI.Probability.ThreeState.Observation

namespace OAI

/-! Branchwise likelihood updates and their independent product measures. -/

namespace ThreeState
open MeasureTheory
open scoped Classical

noncomputable def edgeMessage (lam : ℝ) (h : Admissible lam) (m : Message) : Message :=
  ⟨fun i => 1+lam*(m i-1), by
    constructor
    · intro i
      have hl := Message.nonneg m i
      have hu := Message.le_three m i
      by_cases hp : 0 ≤ lam
      · nlinarith [h.2]
      · have hn : lam ≤ 0 := le_of_not_ge hp
        nlinarith [h.1]
    · simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib,
        Message.sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      norm_num⟩

lemma continuous_edgeMessage (lam : ℝ) (h : Admissible lam) : Continuous (edgeMessage lam h) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  exact continuous_const.add (continuous_const.mul (((continuous_apply i).comp continuous_subtype_val).sub continuous_const))

lemma channel_decompose (lam : ℝ) (i j : Spin) :
    channel lam i j = (1-lam)/3 + if i=j then lam else 0 := by
  unfold channel
  split_ifs <;> ring

lemma channel_message (lam : ℝ) (m : Message) (i : Spin) :
    ∑ j, channel lam i j * m j = 1+lam*(m i-1) := by
  simp_rw [channel_decompose, add_mul, ite_mul, zero_mul]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Message.sum]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  ring

lemma mass_channelPMF (lam : ℝ) (h : Admissible lam) (i j : Spin) :
    mass (channelPMF lam h i) j = channel lam i j := by
  simp [mass, channelPMF, PMF.ofFintype_apply, ENNReal.toReal_ofReal (channel_nonneg h i j)]

noncomputable def edgeLaw {α : Type*} (law : Spin → PMF α) (lam : ℝ) (h : Admissible lam) : Spin → PMF α :=
  fun i => (channelPMF lam h i).bind law

lemma mass_edgeLaw {α : Type*} (law : Spin → PMF α) (lam : ℝ) (h : Admissible lam) (i : Spin) (y : α) :
    mass (edgeLaw law lam h i) y = mass (marginal law) y * edgeMessage lam h (likelihood law y) i := by
  rw [edgeLaw, mass_bind, tsum_fintype]
  simp_rw [mass_channelPMF, ← weighted_likelihood law y]
  calc
    (∑ j, channel lam i j * (mass (marginal law) y * likelihood law y j)) =
      mass (marginal law) y * (∑ j, channel lam i j * likelihood law y j) := by
        rw [Finset.mul_sum]
        congr 1
        funext j
        ring
    _ = _ := by rw [channel_message]; rfl

noncomputable def sigmaPMF {ι : Type*} {α : ι → Type*} (p : PMF ι) (q : ∀ i, PMF (α i)) : PMF (Sigma α) :=
  p.bind (fun i => (q i).map (Sigma.mk i))

lemma sigmaPMF_apply {ι : Type*} {α : ι → Type*} (p : PMF ι) (q : ∀ i, PMF (α i))
    (i : ι) (a : α i) : sigmaPMF p q ⟨i,a⟩ = p i * q i a := by
  classical
  rw [sigmaPMF, PMF.bind_apply, tsum_eq_single i]
  · simp [PMF.map_apply]
  · intro j hj
    have he (b : α j) : (⟨i,a⟩ : Sigma α) ≠ ⟨j,b⟩ := by
      intro hh
      exact hj (congrArg Sigma.fst hh).symm
    simp [PMF.map_apply, he]

lemma mass_sigmaPMF {ι : Type*} {α : ι → Type*} (p : PMF ι) (q : ∀ i, PMF (α i))
    (i : ι) (a : α i) : mass (sigmaPMF p q) ⟨i,a⟩ = mass p i * mass (q i) a := by
  simp only [mass, sigmaPMF_apply, ENNReal.toReal_mul]

lemma mass_iidVector {α : Type*} (p : PMF α) (n : ℕ) (v : Fin n → α) :
    mass (iidVector p n) v = ∏ j, mass p (v j) := by
  simp only [mass, iidVector_apply, ENNReal.toReal_prod]

 
noncomputable def productReference {α : Type*} (offspring : PMF ℕ) (law : Spin → PMF α) :
    PMF (Σ n : ℕ, Fin n → α) := sigmaPMF offspring (iidVector (marginal law))

noncomputable def composeLaw {α : Type*} (offspring : PMF ℕ) (law : Spin → PMF α)
    (lam : ℝ) (h : Admissible lam) : Spin → PMF (Σ n : ℕ, Fin n → α) :=
  fun i => sigmaPMF offspring (iidVector (edgeLaw law lam h i))

noncomputable def productWeight (lam : ℝ) (h : Admissible lam) {n : ℕ} (m : Fin n → Message) (i : Spin) : ℝ :=
  ∏ j, edgeMessage lam h (m j) i

noncomputable def normalizer (lam : ℝ) (h : Admissible lam) {n : ℕ} (m : Fin n → Message) : ℝ :=
  (∑ i : Spin, productWeight lam h m i)/3

lemma productWeight_nonneg (lam : ℝ) (h : Admissible lam) {n : ℕ} (m : Fin n → Message) (i : Spin) :
    0 ≤ productWeight lam h m i :=
  Finset.prod_nonneg (fun index _ => Message.nonneg (edgeMessage lam h (m index)) i)

lemma normalizer_nonneg (lam : ℝ) (h : Admissible lam) {n : ℕ} (m : Fin n → Message) :
    0 ≤ normalizer lam h m := div_nonneg (Finset.sum_nonneg (fun i _ => productWeight_nonneg _ _ _ _)) (by norm_num)

lemma productWeight_sum (lam : ℝ) (h : Admissible lam) {n : ℕ} (m : Fin n → Message) :
    ∑ i, productWeight lam h m i = 3*normalizer lam h m := by dsimp [normalizer]; ring

noncomputable def combineMessage (lam : ℝ) (h : Admissible lam) {n : ℕ} (m : Fin n → Message) : Message :=
  if hz : normalizer lam h m = 0 then uninformative else
    ⟨fun i => productWeight lam h m i / normalizer lam h m, by
      constructor
      · intro i
        exact div_nonneg (productWeight_nonneg _ _ _ _) (normalizer_nonneg _ _ _)
      · rw [← Finset.sum_div, productWeight_sum]
        field_simp⟩

lemma mass_composeLaw {α : Type*} (offspring : PMF ℕ) (law : Spin → PMF α)
    (lam : ℝ) (h : Admissible lam) (n : ℕ) (v : Fin n → α) (i : Spin) :
    mass (composeLaw offspring law lam h i) ⟨n,v⟩ =
      mass (productReference offspring law) ⟨n,v⟩ * productWeight lam h (fun j => likelihood law (v j)) i := by
  simp only [composeLaw, productReference, mass_sigmaPMF, mass_iidVector, mass_edgeLaw,
    Finset.prod_mul_distrib, productWeight, mul_assoc]

lemma mass_marginal_composeLaw {α : Type*} (offspring : PMF ℕ) (law : Spin → PMF α)
    (lam : ℝ) (h : Admissible lam) (n : ℕ) (v : Fin n → α) :
    mass (marginal (composeLaw offspring law lam h)) ⟨n,v⟩ =
      mass (productReference offspring law) ⟨n,v⟩ * normalizer lam h (fun j => likelihood law (v j)) := by
  rw [mass_marginal]
  simp_rw [mass_composeLaw]
  rw [← Finset.mul_sum]
  simp [normalizer]
  ring

lemma weighted_combineMessage (lam : ℝ) (h : Admissible lam) {n : ℕ}
    (m : Fin n → Message) (i : Spin) :
    normalizer lam h m * combineMessage lam h m i = productWeight lam h m i := by
  by_cases hz : normalizer lam h m = 0
  · have hs := productWeight_sum lam h m
    have hi := Finset.single_le_sum (fun j _ => productWeight_nonneg lam h m j) (Finset.mem_univ i)
    have hn := productWeight_nonneg lam h m i
    simp only [hz, mul_zero] at hs
    have hw : productWeight lam h m i = 0 := le_antisymm (by simpa [hs] using hi) hn
    simp [hz, hw]
  · simp only [combineMessage, dite_eq_right hz]
    field_simp

lemma likelihood_composeLaw {α : Type*} (offspring : PMF ℕ) (law : Spin → PMF α)
    (lam : ℝ) (h : Admissible lam) (n : ℕ) (v : Fin n → α)
    (hm : mass (marginal (composeLaw offspring law lam h)) ⟨n,v⟩ ≠ 0) :
    likelihood (composeLaw offspring law lam h) ⟨n,v⟩ =
      combineMessage lam h (fun j => likelihood law (v j)) := by
  apply Subtype.ext
  funext i
  apply mul_left_cancel₀ hm
  rw [weighted_likelihood, mass_composeLaw, mass_marginal_composeLaw, mul_assoc,
    weighted_combineMessage]

lemma weighted_test_composeLaw {α : Type*} (offspring : PMF ℕ) (law : Spin → PMF α)
    (lam : ℝ) (h : Admissible lam) (f : Message → ℝ) (n : ℕ) (v : Fin n → α) :
    mass (marginal (composeLaw offspring law lam h)) ⟨n,v⟩ *
      f (likelihood (composeLaw offspring law lam h) ⟨n,v⟩) =
    mass (productReference offspring law) ⟨n,v⟩ *
      (normalizer lam h (fun j => likelihood law (v j)) *
        f (combineMessage lam h (fun j => likelihood law (v j)))) := by
  by_cases hm : mass (marginal (composeLaw offspring law lam h)) ⟨n,v⟩ = 0
  · rw [mass_marginal_composeLaw] at hm
    rw [← mul_assoc, ← mass_marginal_composeLaw, mass_marginal_composeLaw, hm]
    simp
  · rw [likelihood_composeLaw offspring law lam h n v hm, mass_marginal_composeLaw, mul_assoc]

lemma hasMean_weighted_compose {α : Type*} (offspring : PMF ℕ) (law : Spin → PMF α)
    (lam : ℝ) (h : Admissible lam) (f : Message → ℝ) (C : ℝ) (hf : ∀ m, |f m| ≤ C) :
    HasMean (productReference offspring law) (fun nv =>
      normalizer lam h (fun j => likelihood law (nv.2 j)) *
        f (combineMessage lam h (fun j => likelihood law (nv.2 j)))) := by
  have hs : Summable (fun nv => mass (marginal (composeLaw offspring law lam h)) nv *
      f (likelihood (composeLaw offspring law lam h) nv)) :=
    hasMean_bounded (marginal (composeLaw offspring law lam h)) C
      (fun nv => hf (likelihood (composeLaw offspring law lam h) nv))
  exact hs.congr (fun ⟨n,v⟩ => weighted_test_composeLaw offspring law lam h f n v)

lemma mean_test_compose {α : Type*} (offspring : PMF ℕ) (law : Spin → PMF α)
    (lam : ℝ) (h : Admissible lam) (f : Message → ℝ) :
    mean (marginal (composeLaw offspring law lam h)) (fun nv => f (likelihood (composeLaw offspring law lam h) nv)) =
    mean (productReference offspring law) (fun nv =>
      normalizer lam h (fun j => likelihood law (nv.2 j)) *
        f (combineMessage lam h (fun j => likelihood law (nv.2 j)))) := by
  apply tsum_congr
  rintro ⟨n,v⟩
  exact weighted_test_composeLaw offspring law lam h f n v

end ThreeState
namespace ThreeState
open MeasureTheory
open scoped Classical

lemma iidVector_outer_pi {α : Type*} (p : PMF α) (n : ℕ) (s : Fin n → Set α) :
    (iidVector p n).toOuterMeasure (Set.univ.pi s) = ∏ j, p.toOuterMeasure (s j) := by
  induction n with
  | zero =>
    simp [iidVector]
    funext i
    exact Fin.elim0 i
  | succ n ih =>
    rw [iidVector, PMF.toOuterMeasure_bind_apply]
    simp only [PMF.toOuterMeasure_map_apply]
    have he (a : α) : Fin.cons a ⁻¹' (Set.univ.pi s) =
        if a ∈ s 0 then Set.univ.pi (fun j : Fin n => s j.succ) else ∅ := by
      ext v
      simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_true_left]
      rw [Fin.forall_fin_succ]
      by_cases ha : a ∈ s 0 <;> simp [ha]
    simp_rw [he]
    have hh (a : α) : p a * (iidVector p n).toOuterMeasure
        (if a ∈ s 0 then Set.univ.pi (fun j : Fin n => s j.succ) else ∅) =
        (s 0).indicator p a * ∏ j : Fin n, p.toOuterMeasure (s j.succ) := by
      by_cases ha : a ∈ s 0 <;> simp [ha, ih]
    simp_rw [hh]
    rw [ENNReal.tsum_mul_right, ← PMF.toOuterMeasure_apply, Fin.prod_univ_succ]

lemma iidVector_toMeasure {α : Type*} [MeasurableSpace α] (p : PMF α) (n : ℕ) :
    (iidVector p n).toMeasure = Measure.pi (fun _ : Fin n => p.toMeasure) := by
  symm
  apply Measure.pi_eq
  intro s hs
  rw [PMF.toMeasure_apply_eq_toOuterMeasure_apply _ (MeasurableSet.univ_pi hs), iidVector_outer_pi]
  congr 1
  funext j
  exact (PMF.toMeasure_apply_eq_toOuterMeasure_apply p (hs j)).symm

noncomputable def iidMeasure (Q : ProbabilityMeasure Message) (n : ℕ) :
    ProbabilityMeasure (Fin n → Message) := ProbabilityMeasure.pi (fun _ => Q)

lemma continuous_iidMeasure (n : ℕ) : Continuous (fun Q => iidMeasure Q n) :=
  ProbabilityMeasure.continuous_pi.comp (continuous_pi (fun _ => continuous_id))

lemma likelihoodPMF_iid_toMeasure {α : Type*} (law : Spin → PMF α) (n : ℕ) :
    (iidVector (likelihoodPMF law) n).toMeasure =
      (iidMeasure (likelihoodLaw law) n : Measure (Fin n → Message)) := by
  exact iidVector_toMeasure _ n

lemma integral_iid_likelihood {α : Type*} (law : Spin → PMF α) (n : ℕ)
    (f : C((Fin n → Message),ℝ)) :
    ∫ m, f m ∂(iidMeasure (likelihoodLaw law) n : Measure (Fin n → Message)) =
      mean (iidVector (marginal law) n) (fun v => f (fun j => likelihood law (v j))) := by
  rw [← likelihoodPMF_iid_toMeasure]
  rw [PMF.integral_eq_tsum _ _
    (f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))]
  change mean (iidVector ((marginal law).map (likelihood law)) n) f = _
  rw [← iidVector_map]
  obtain ⟨C,hC⟩ := isCompact_univ.exists_bound_of_continuousOn f.continuous.continuousOn
  exact mean_map_bounded _ _ _ C (fun v => by simpa only [Real.norm_eq_abs] using hC _ (Set.mem_univ _))

end ThreeState

end OAI
