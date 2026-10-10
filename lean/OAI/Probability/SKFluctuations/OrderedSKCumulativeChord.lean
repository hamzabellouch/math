import Mathlib
import OAI.Probability.SKFluctuations.RootedVariancePressure

namespace OAI

/-! Ordered S K Cumulative Chord. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
open MeasureTheory Filter Set
open scoped Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SKFluctuations
open MeasureTheory ProbabilityTheory Hierarchy
open scoped Topology NNReal BigOperators

 

theorem orderedSK_cumulative_chord (n : ℕ) (hn : 0 < n) (as : List PositiveMass)
    (ho : as.Pairwise (fun a b => a.val ≤ b.val)) (hu : ∀ a ∈ as, a.val ≤ 1)
    (b h b' h' : ℕ → ℝ) (hb : Monotone b) (hh : Monotone h)
    (hb' : Monotone b') (hh' : Monotone h')
    (hb0 : 0 ≤ b 0) (hh0 : 0 ≤ h 0) (hb0' : 0 ≤ b' 0) (hh0' : 0 ≤ h' 0)
    (hba : ∀ j, j ≤ as.length → b j ≤ b' j)
    (hzero : ∀ j, j ≤ as.length → b j = b' j → h j = h' j)
    (x : OrderedFeatureIndex n → ℝ) :
    orderedSKPressure n as b' h' x ≤ orderedSKPressure n as b h x+
      (1/4:ℝ)*massStepSum as 0 (fun j => (h j-h' j)^2/(b' j-b j)) := by
  let : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  have hnR : 0 < (n:ℝ) := Nat.cast_pos.mpr hn
  let B : ℕ → ℝ := fun j => (n:ℝ)/2*((h j-h' j)^2/(b' j-b j))
  have hB : ∀ j, j ≤ as.length → ∀ σ τ,
      -B j ≤ featureKernel (orderedFeature n)
        (orderedClock n b' h' j-orderedClock n b h j) σ τ := by
    intro j hj σ τ
    have hdiff (i : OrderedFeatureIndex n) :
        (orderedClock n b' h' j-orderedClock n b h j) i =
          Sum.elim (fun _ => h' j-h j) (fun _ => b' j-b j) i := by
      cases i <;> rfl
    simp only [featureKernel,hdiff,orderedFeature_single]
    rw [orderedCovariance n hn σ τ]
    by_cases hz : b j = b' j
    · have hhj := hzero j hj hz
      simp [B,← hz,← hhj]
    · have ha : 0 < b' j-b j := sub_pos.mpr (lt_of_le_of_ne (hba j hj) hz)
      have hs : -((h j-h' j)^2/(2*(b' j-b j))) ≤
          (b' j-b j)/2*(orderedOverlap n σ τ)^2-(h j-h' j)*orderedOverlap n σ τ := by
        rw [← neg_div,div_le_iff₀ (by positivity)]
        nlinarith [sq_nonneg ((b' j-b j)*orderedOverlap n σ τ-(h j-h' j))]
      have hs' := mul_le_mul_of_nonneg_left hs hnR.le
      dsimp only [B]
      convert hs' using 1
      · simp only [div_eq_mul_inv,mul_inv_rev]
        ring
      · ring
  have hp := disorderPressure_chord (uniformWeight_pos n) (orderedFeature n)
    (fun i => (orderedAmplitude n i)^2) (orderedFeature_square n) as ho hu 0
    (orderedClock n b h) (orderedClock n b' h')
    (fun i => by cases i with | inl i => exact hh | inr i => exact hb)
    (fun i => by cases i with | inl i => exact hh' | inr i => exact hb')
    (fun i => by cases i with | inl i => exact hh0 | inr i => exact hb0)
    (fun i => by cases i with | inl i => exact hh0' | inr i => exact hb0') B hB x
  have hcost : massStepSum as 0 B = (n:ℝ)/2*
      massStepSum as 0 (fun j => (h j-h' j)^2/(b' j-b j)) :=
    massStepSum_const_mul as _ 0 ((n:ℝ)/2)
  rw [hcost] at hp
  have hd : (disorderPressure (uniformWeight n) (orderedFeature n)
      (fun i => (orderedAmplitude n i)^2) as 0 (orderedClock n b' h') x-
      disorderPressure (uniformWeight n) (orderedFeature n)
      (fun i => (orderedAmplitude n i)^2) as 0 (orderedClock n b h) x)/(n:ℝ) ≤
        (1/4:ℝ)*massStepSum as 0 (fun j => (h j-h' j)^2/(b' j-b j)) := by
    apply (div_le_iff₀ hnR).mpr
    nlinarith
  unfold orderedSKPressure
  rw [sub_div] at hd
  linarith

end SKFluctuations

namespace SKFluctuations.Hierarchy
open scoped BigOperators

theorem massStepSum_sub (as : List PositiveMass) (C D : ℕ → ℝ) (a : ℝ) :
    massStepSum as a (fun j => C j-D j) = massStepSum as a C-massStepSum as a D := by
  induction as generalizing a C D with
  | nil => change (1-a)*(C 0-D 0) = _; simp only [massStepSum]; ring
  | cons b bs ih =>
    change (b.val-a)*(C 0-D 0)+massStepSum bs b.val (fun j => C (j+1)-D (j+1)) = _
    rw [ih]
    change _ = ((b.val-a)*C 0+massStepSum bs b.val (fun j => C (j+1)))-
      ((b.val-a)*D 0+massStepSum bs b.val (fun j => D (j+1)))
    ring

end SKFluctuations.Hierarchy

namespace SKFluctuations
open MeasureTheory ProbabilityTheory Hierarchy
open scoped Topology NNReal BigOperators

 

noncomputable def finiteCompensatedPressure (n : ℕ) (as : List PositiveMass)
    (b h e r : ℕ → ℝ) (x : OrderedFeatureIndex n → ℝ) : ℝ :=
  orderedSKPressure n as (fun j => b j-e j) (fun j => h j+e j*r j) x+
    (1/4:ℝ)*massStepSum as 0 (fun j => e j*(r j)^2)

 

theorem finiteCompensatedPressure_mono (n : ℕ) (hn : 0 < n) (as : List PositiveMass)
    (ho : as.Pairwise (fun a b => a.val ≤ b.val)) (hu : ∀ a ∈ as, a.val ≤ 1)
    (b h e e' r : ℕ → ℝ) (he : ∀ j, j ≤ as.length → e j ≤ e' j)
    (hb : Monotone (fun j => b j-e j)) (hh : Monotone (fun j => h j+e j*r j))
    (hb' : Monotone (fun j => b j-e' j)) (hh' : Monotone (fun j => h j+e' j*r j))
    (hb0 : 0 ≤ b 0-e 0) (hh0 : 0 ≤ h 0+e 0*r 0)
    (hb0' : 0 ≤ b 0-e' 0) (hh0' : 0 ≤ h 0+e' 0*r 0)
    (x : OrderedFeatureIndex n → ℝ) :
    finiteCompensatedPressure n as b h e r x ≤ finiteCompensatedPressure n as b h e' r x := by
  have hc := orderedSK_cumulative_chord n hn as ho hu
    (fun j => b j-e' j) (fun j => h j+e' j*r j)
    (fun j => b j-e j) (fun j => h j+e j*r j)
    hb' hh' hb hh hb0' hh0' hb0 hh0
    (fun j hj => sub_le_sub_left (he j hj) _) (fun j _ hz => by congr 1; congr 1; linarith) x
  have hq (j : ℕ) :
      (h j+e' j*r j-(h j+e j*r j))^2/(b j-e j-(b j-e' j)) = (e' j-e j)*(r j)^2 := by
    by_cases hz : e' j = e j
    · simp [hz]
    · have hx : e' j-e j ≠ 0 := sub_ne_zero.mpr hz
      rw [show b j-e j-(b j-e' j) = e' j-e j by ring]
      apply (div_eq_iff hx).mpr
      ring
  simp_rw [hq] at hc
  have hpen : massStepSum as 0 (fun j => (e' j-e j)*(r j)^2) =
      massStepSum as 0 (fun j => e' j*(r j)^2)-massStepSum as 0 (fun j => e j*(r j)^2) := by
    simp_rw [sub_mul]
    exact massStepSum_sub _ _ _ _
  rw [hpen] at hc
  unfold finiteCompensatedPressure
  linarith

 
theorem finiteCompensatedPressure_lower (n : ℕ) (hn : 0 < n) (as : List PositiveMass)
    (ho : as.Pairwise (fun a b => a.val ≤ b.val)) (hu : ∀ a ∈ as, a.val ≤ 1)
    (b h e r : ℕ → ℝ) (he : ∀ j, j ≤ as.length → 0 ≤ e j)
    (hb : Monotone b) (hh : Monotone h)
    (hb' : Monotone (fun j => b j-e j)) (hh' : Monotone (fun j => h j+e j*r j))
    (hb0 : 0 ≤ b 0) (hh0 : 0 ≤ h 0)
    (hb0' : 0 ≤ b 0-e 0) (hh0' : 0 ≤ h 0+e 0*r 0)
    (x : OrderedFeatureIndex n → ℝ) :
    orderedSKPressure n as b h x ≤ finiteCompensatedPressure n as b h e r x := by
  have hc := finiteCompensatedPressure_mono n hn as ho hu b h (fun _ => 0) e r he
    (by simpa using hb) (by simpa using hh) hb' hh'
    (by simpa using hb0) (by simpa using hh0) hb0' hh0' x
  have hz : massStepSum as 0 (fun _ => (0:ℝ)) = 0 := by
    have hx := massStepSum_const_mul as (fun _ => (0:ℝ)) 0 0
    simpa using hx
  simpa [finiteCompensatedPressure,hz] using hc

end SKFluctuations

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
variable {ι S : Type*} [Fintype ι] [Fintype S] [Nonempty S]

 

theorem hierarchyPairMean_square {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (K : S → S → ℝ) (steps : List (GaussianStep ι))
    {a : ℝ} (ha : OrderedSteps a steps) (x : ι → ℝ) :
    (hierarchyPairMean w φ K steps x)^2 ≤
      hierarchyPairMean w φ (fun σ τ => (K σ τ)^2) steps x := by
  let c := hierarchyPairMean w φ K steps x
  have hp := hierarchyPairMean_mono hw φ
    (K := fun _ _ => 0) (L := fun σ τ => (K σ τ-c)^2)
    (fun σ τ => sq_nonneg _) steps ha x
  rw [hierarchyPairMean_const hw φ steps ha] at hp
  have he : (fun σ τ => (K σ τ-c)^2) =
      fun σ τ => 1*(1*(K σ τ)^2+(-2*c)*K σ τ)+1*c^2 := by funext σ τ; ring
  rw [he,hierarchyPairMean_linear,hierarchyPairMean_linear,
    hierarchyPairMean_const hw φ steps ha] at hp
  dsimp only [c] at hp
  nlinarith

 

noncomputable def levelPairMean (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (K : S → S → ℝ) : List (GaussianStep ι) → ℕ → (ι → ℝ) → ℝ
  | steps,0 => hierarchyPairMean w φ K steps
  | [],_+1 => hierarchyPairMean w φ K []
  | (m,q)::steps,j+1 => shiftedMean (Measure.pi fun i => gaussianReal 0 (q i)) m
      (gaussianHierarchy w φ steps) (levelPairMean w φ K steps j)

theorem levelPairMean_smooth {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (K : S → S → ℝ) (steps : List (GaussianStep ι))
    {a : ℝ} (ha : OrderedSteps a steps) (j r : ℕ) :
    BddSmooth r (levelPairMean w φ K steps j) := by
  induction steps generalizing a j with
  | nil => cases j <;> exact hierarchyPairMean_smooth hw φ K [] ha r
  | cons st steps ih =>
    cases j with
    | zero => exact hierarchyPairMean_smooth hw φ K _ ha r
    | succ j =>
        exact (ih ha.2.2.2 j).shiftedMean
          (gaussianHierarchy_regular hw φ steps ha.2.2.2 r)
          (gaussianHierarchy_integrable hw φ steps ha.2.2.2 st.1 st.2)

theorem levelPairMean_const {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (steps : List (GaussianStep ι))
    {a : ℝ} (ha : OrderedSteps a steps) (j : ℕ) (c : ℝ) (x : ι → ℝ) :
    levelPairMean w φ (fun _ _ => c) steps j x = c := by
  induction steps generalizing a j x with
  | nil => cases j <;> exact hierarchyPairMean_const hw φ [] ha c x
  | cons st steps ih =>
    cases j with
    | zero => exact hierarchyPairMean_const hw φ _ ha c x
    | succ j =>
      change shiftedMean _ st.1 _ (levelPairMean w φ (fun _ _ => c) steps j) x = c
      rw [funext (ih ha.2.2.2 j)]
      exact shiftedMean_const c (gaussianHierarchy_integrable hw φ steps ha.2.2.2 st.1 st.2 x)

theorem levelPairMean_mono {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) {K L : S → S → ℝ}
    (hKL : ∀ σ τ, K σ τ ≤ L σ τ) (steps : List (GaussianStep ι))
    {a : ℝ} (ha : OrderedSteps a steps) (j : ℕ) (x : ι → ℝ) :
    levelPairMean w φ K steps j x ≤ levelPairMean w φ L steps j x := by
  induction steps generalizing a j x with
  | nil => cases j <;> exact hierarchyPairMean_mono hw φ hKL [] ha x
  | cons st steps ih =>
    cases j with
    | zero => exact hierarchyPairMean_mono hw φ hKL _ ha x
    | succ j =>
        exact shiftedMean_mono (levelPairMean_smooth hw φ K steps ha.2.2.2 j 0)
          (levelPairMean_smooth hw φ L steps ha.2.2.2 j 0) (ih ha.2.2.2 j)
          (gaussianHierarchy_integrable hw φ steps ha.2.2.2 st.1 st.2 x)

theorem levelPairMean_square {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (K : S → S → ℝ) (steps : List (GaussianStep ι))
    {a : ℝ} (ha : OrderedSteps a steps) (j : ℕ) (x : ι → ℝ) :
    (levelPairMean w φ K steps j x)^2 ≤
      levelPairMean w φ (fun σ τ => (K σ τ)^2) steps j x := by
  induction steps generalizing a j x with
  | nil => cases j <;> exact hierarchyPairMean_square hw φ K [] ha x
  | cons st steps ih =>
    cases j with
    | zero => exact hierarchyPairMean_square hw φ K _ ha x
    | succ j =>
      have hi := gaussianHierarchy_integrable hw φ steps ha.2.2.2 st.1 st.2 x
      have hA := levelPairMean_smooth hw φ K steps ha.2.2.2 j 0
      have h₁ := shiftedMean_square_sub_nonneg
        (gaussianHierarchy_regular hw φ steps ha.2.2.2 0).1.choose_spec.continuous hA hi
      have h₂ := shiftedMean_mono (hA.mul hA)
        (levelPairMean_smooth hw φ (fun σ τ => (K σ τ)^2) steps ha.2.2.2 j 0)
        (fun y => by simpa only [pow_two] using ih ha.2.2.2 j y) hi
      simp only [← pow_two] at h₂
      exact (sub_nonneg.mp h₁).trans h₂

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
variable {ι S : Type*} [Fintype ι] [Fintype S] [Nonempty S]

 

noncomputable def rootLevelPairMean (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (q : ι → ℝ≥0) (K : S → S → ℝ) (steps : List (GaussianStep ι)) (j : ℕ) : ℝ :=
  zeroContinuation (Measure.pi fun i => gaussianReal 0 (q i)) (levelPairMean w φ K steps j) 0

theorem rootLevelPairMean_mono {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (q : ι → ℝ≥0) {K L : S → S → ℝ}
    (hKL : ∀ σ τ, K σ τ ≤ L σ τ) (steps : List (GaussianStep ι))
    {a : ℝ} (ha : OrderedSteps a steps) (j : ℕ) :
    rootLevelPairMean w φ q K steps j ≤ rootLevelPairMean w φ q L steps j := by
  apply integral_mono ((levelPairMean_smooth hw φ K steps ha j 0).integrable_zero_shift 0)
    ((levelPairMean_smooth hw φ L steps ha j 0).integrable_zero_shift 0)
  intro y
  exact levelPairMean_mono hw φ hKL steps ha j _

theorem rootLevelPairMean_const {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (q : ι → ℝ≥0) (steps : List (GaussianStep ι))
    {a : ℝ} (ha : OrderedSteps a steps) (j : ℕ) (c : ℝ) :
    rootLevelPairMean w φ q (fun _ _ => c) steps j = c := by
  unfold rootLevelPairMean zeroContinuation
  simp_rw [levelPairMean_const hw φ steps ha]
  simp

theorem rootLevelPairMean_square {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (q : ι → ℝ≥0) (K : S → S → ℝ)
    (steps : List (GaussianStep ι)) {a : ℝ} (ha : OrderedSteps a steps) (j : ℕ) :
    (rootLevelPairMean w φ q K steps j)^2 ≤
      rootLevelPairMean w φ q (fun σ τ => (K σ τ)^2) steps j := by
  let ν := Measure.pi fun i => gaussianReal 0 (q i)
  have hi : Integrable (fun _ : ι → ℝ => Real.exp ((0:ℝ)*0)) ν := by simp
  have hA := levelPairMean_smooth hw φ K steps ha j 0
  have h₁ := shiftedMean_square_sub_nonneg (ν := ν) (x := 0)
    (F := fun _ => (0:ℝ)) continuous_const hA hi
  have h₂ := integral_mono ((hA.mul hA).integrable_zero_shift (ν := ν) 0)
    ((levelPairMean_smooth hw φ (fun σ τ => (K σ τ)^2) steps ha j 0).integrable_zero_shift (ν := ν) 0)
    (fun y => by simpa only [pow_two] using levelPairMean_square hw φ K steps ha j (0+y))
  rw [shiftedMean_zero,shiftedMean_zero] at h₁
  change (zeroContinuation ν (levelPairMean w φ K steps j) 0)^2 ≤
    zeroContinuation ν (levelPairMean w φ (fun σ τ => (K σ τ)^2) steps j) 0
  exact (sub_nonneg.mp h₁).trans (by simpa only [pow_two,zeroContinuation] using h₂)

omit [Nonempty S] in
theorem hierarchyPairMean_sum {κ : Type*} [Fintype κ] (w : S → ℝ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (K : κ → S → S → ℝ)
    (steps : List (GaussianStep ι)) (x : ι → ℝ) :
    hierarchyPairMean w φ (fun σ τ => ∑ i, K i σ τ) steps x =
      ∑ i, hierarchyPairMean w φ (K i) steps x := by
  unfold hierarchyPairMean
  simp only [Finset.mul_sum]
  simp_rw [Finset.sum_comm (s := (Finset.univ : Finset S)) (t := (Finset.univ : Finset κ))]

omit [Nonempty S] in
theorem hierarchyPairMean_const_mul (w : S → ℝ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (K : S → S → ℝ)
    (steps : List (GaussianStep ι)) (c : ℝ) (x : ι → ℝ) :
    hierarchyPairMean w φ (fun σ τ => c*K σ τ) steps x =
      c*hierarchyPairMean w φ K steps x := by
  unfold hierarchyPairMean
  simp_rw [mul_left_comm _ c,← Finset.mul_sum]

end SKFluctuations.Hierarchy

namespace SKFluctuations
open MeasureTheory ProbabilityTheory Hierarchy
open scoped NNReal Topology BigOperators

 theorem orderedOverlap_abs_le_one (n : ℕ) (σ τ : Spin n) : |orderedOverlap n σ τ| ≤ 1 := by
  have hs (b : Bool) : |spinValue b| = 1 := by cases b <;> norm_num [spinValue]
  by_cases hn : n = 0
  · subst n; simp [orderedOverlap]
  have hnR : 0 < (n:ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  unfold orderedOverlap
  rw [abs_div,abs_of_pos hnR]
  apply (div_le_one hnR).mpr
  calc
    _ ≤ ∑ i, |spinValue (σ i)*spinValue (τ i)| := Finset.abs_sum_le_sum_abs _ _
    _ = (n:ℝ) := by simp only [abs_mul,hs,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one]

 theorem hierarchyPairMean_overlap_nonneg {ι : Type*} [Fintype ι] (n : ℕ)
    {w : Spin n → ℝ} (hw : ∀ σ, 0 < w σ) (φ : Spin n → (ι → ℝ) →L[ℝ] ℝ)
    (steps : List (GaussianStep ι)) {a : ℝ} (ha : OrderedSteps a steps) (x : ι → ℝ) :
    0 ≤ hierarchyPairMean w φ (orderedOverlap n) steps x := by
  have he : orderedOverlap n = fun σ τ => (1/(n:ℝ))*∑ i, spinValue (σ i)*spinValue (τ i) := by
    funext σ τ
    unfold orderedOverlap
    ring
  rw [he,hierarchyPairMean_const_mul,hierarchyPairMean_sum]
  simp_rw [hierarchyPairMean_product hw φ _ _ steps ha]
  apply mul_nonneg (by positivity)
  exact Finset.sum_nonneg fun i _ => mul_self_nonneg _

 theorem levelPairMean_overlap_nonneg {ι : Type*} [Fintype ι] (n : ℕ)
    {w : Spin n → ℝ} (hw : ∀ σ, 0 < w σ) (φ : Spin n → (ι → ℝ) →L[ℝ] ℝ)
    (steps : List (GaussianStep ι)) {a : ℝ} (ha : OrderedSteps a steps) (j : ℕ) (x : ι → ℝ) :
    0 ≤ levelPairMean w φ (orderedOverlap n) steps j x := by
  induction steps generalizing a j x with
  | nil => cases j <;> exact hierarchyPairMean_overlap_nonneg n hw φ [] ha x
  | cons st steps ih =>
    cases j with
    | zero => exact hierarchyPairMean_overlap_nonneg n hw φ _ ha x
    | succ j =>
      exact shiftedMean_nonneg (ih ha.2.2.2 j)
        (gaussianHierarchy_integrable hw φ steps ha.2.2.2 st.1 st.2 x)

 

theorem rootLevelPairMean_SK_bounds {ι : Type*} [Fintype ι] (n : ℕ)
    {w : Spin n → ℝ} (hw : ∀ σ, 0 < w σ) (φ : Spin n → (ι → ℝ) →L[ℝ] ℝ)
    (q : ι → ℝ≥0) (steps : List (GaussianStep ι)) {a : ℝ} (ha : OrderedSteps a steps) (j : ℕ) :
    let S := rootLevelPairMean w φ q (orderedOverlap n) steps j
    let B := rootLevelPairMean w φ q (fun σ τ => (orderedOverlap n σ τ)^2) steps j
    0 ≤ S ∧ S ≤ 1 ∧ S^2 ≤ B ∧ B ≤ 1 := by
  dsimp only
  refine ⟨?_,?_,rootLevelPairMean_square hw φ q _ steps ha j,?_⟩
  · exact integral_nonneg fun y => levelPairMean_overlap_nonneg n hw φ steps ha j _
  · have h := rootLevelPairMean_mono hw φ q
      (fun σ τ => (le_abs_self _).trans (orderedOverlap_abs_le_one n σ τ)) steps ha j
    rwa [rootLevelPairMean_const hw φ q steps ha j] at h
  · have h := rootLevelPairMean_mono hw φ q
      (K := fun σ τ => (orderedOverlap n σ τ)^2) (L := fun _ _ => 1)
      (fun σ τ => by nlinarith [(abs_le.mp (orderedOverlap_abs_le_one n σ τ)).1,
        (abs_le.mp (orderedOverlap_abs_le_one n σ τ)).2]) steps ha j
    rw [rootLevelPairMean_const hw φ q steps ha j] at h
    exact h

end SKFluctuations

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators

section Linear
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] {ν : Measure E} [IsProbabilityMeasure ν]

omit [MeasurableSpace E] [BorelSpace E] in
theorem massStepSum_smooth (as : List PositiveMass) (a : ℝ) (A : ℕ → E → ℝ)
    (r : ℕ) (hA : ∀ j, BddSmooth r (A j)) :
    BddSmooth r (fun x => massStepSum as a (fun j => A j x)) := by
  induction as generalizing a A with
  | nil => exact (hA 0).const_mul (1-a)
  | cons b as ih =>
    exact ((hA 0).const_mul (b.val-a)).add
      (ih b.val (fun j => A (j+1)) (fun j => hA (j+1)))

omit [IsProbabilityMeasure ν] in
theorem shiftedMean_massStepSum {F : E → ℝ} {m a : ℝ}
    (as : List PositiveMass) (A : ℕ → E → ℝ) (hA : ∀ j, BddSmooth 0 (A j))
    (x : E) (hi : Integrable (fun z => Real.exp (m*F (x+z))) ν) :
    shiftedMean ν m F (fun y => massStepSum as a (fun j => A j y)) x =
      massStepSum as a (fun j => shiftedMean ν m F (A j) x) := by
  induction as generalizing a A with
  | nil => exact shiftedMean_const_mul (1-a) x
  | cons b as ih =>
    change shiftedMean ν m F (fun y => (b.val-a)*A 0 y+
      massStepSum as b.val (fun j => A (j+1) y)) x = _
    rw [shiftedMean_add ((hA 0).const_mul _) (massStepSum_smooth _ _ _ 0 (fun j => hA (j+1))) hi,
      shiftedMean_const_mul,ih _ (fun j => hA (j+1))]
    rfl

theorem zeroContinuation_massStepSum (as : List PositiveMass) (a : ℝ)
    (A : ℕ → E → ℝ) (hA : ∀ j, BddSmooth 0 (A j)) (x : E) :
    zeroContinuation ν (fun y => massStepSum as a (fun j => A j y)) x =
      massStepSum as a (fun j => zeroContinuation ν (A j) x) := by
  have hi : Integrable (fun _ : E => Real.exp ((0:ℝ)*0)) ν := by simp
  have h := shiftedMean_massStepSum (ν := ν) (m := 0) (F := fun _ => 0) (a := a) as A hA x hi
  simpa only [shiftedMean_zero] using h

end Linear
variable {ι S : Type*} [Fintype ι] [Fintype S] [Nonempty S]

 

noncomputable def clockPairReward (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ) :
    (ℕ → S → S → ℝ) → List PositiveMass → ℝ → (ℕ → ι → ℝ≥0) → (ι → ℝ) → ℝ
  | K,[],a,_ => fun x => (1-a)*hierarchyPairMean w φ (K 0) [] x
  | K,b::as,a,q => fun x => (b.val-a)*hierarchyPairMean w φ (K 0) (clockSteps (b::as) q) x+
      shiftedMean (Measure.pi fun i => gaussianReal 0 (q 0 i)) b.val
        (gaussianHierarchy w φ (clockSteps as (fun j => q (j+1))))
        (clockPairReward w φ (fun j => K (j+1)) as b.val (fun j => q (j+1))) x

theorem clockPairReward_eq_massStepSum {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (K : ℕ → S → S → ℝ)
    (as : List PositiveMass) {a : ℝ} (ha : MassOrdered a as)
    (q : ℕ → ι → ℝ≥0) (x : ι → ℝ) :
    clockPairReward w φ K as a q x =
      massStepSum as a (fun j => levelPairMean w φ (K j) (clockSteps as q) j x) := by
  induction as generalizing a K q x with
  | nil => rfl
  | cons b as ih =>
    change (b.val-a)*hierarchyPairMean w φ (K 0) (clockSteps (b::as) q) x+_ = _
    rw [funext (ih _ ha.2.2 (fun j => q (j+1)))]
    rw [shiftedMean_massStepSum as _
      (fun j => levelPairMean_smooth hw φ (K (j+1)) _ (clockSteps_ordered ha.2.2 _) j 0) x
      (gaussianHierarchy_integrable hw φ _ (clockSteps_ordered ha.2.2 _) b.val (q 0) x)]
    rfl

theorem clockPairReward_smooth {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (K : ℕ → S → S → ℝ)
    (as : List PositiveMass) {a : ℝ} (ha : MassOrdered a as)
    (q : ℕ → ι → ℝ≥0) (r : ℕ) :
    BddSmooth r (clockPairReward w φ K as a q) := by
  rw [funext (clockPairReward_eq_massStepSum hw φ K as ha q)]
  exact massStepSum_smooth as a _ r (fun j => levelPairMean_smooth hw φ (K j) _ (clockSteps_ordered ha q) j r)

theorem zero_clockPairReward_eq_massStepSum {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (K : ℕ → S → S → ℝ)
    (as : List PositiveMass) {a : ℝ} (ha : MassOrdered a as)
    (q : ℕ → ι → ℝ≥0) (q₀ : ι → ℝ≥0) :
    zeroContinuation (Measure.pi fun i => gaussianReal 0 (q₀ i))
      (clockPairReward w φ K as a q) 0 =
      massStepSum as a (fun j => rootLevelPairMean w φ q₀ (K j) (clockSteps as q) j) := by
  rw [funext (clockPairReward_eq_massStepSum hw φ K as ha q)]
  exact zeroContinuation_massStepSum as a _
    (fun j => levelPairMean_smooth hw φ (K j) _ (clockSteps_ordered ha q) j 0) 0

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
variable {ι S : Type*} [Fintype ι] [DecidableEq ι] [Fintype S] [Nonempty S]

 
noncomputable def interpolatedIncrements (q r : ℕ → ι → ℝ) (t : ℝ) (j : ℕ) (i : ι) : ℝ≥0 :=
  Real.toNNReal (q (j+1) i-q j i+t*((r (j+1) i-q (j+1) i)-(r j i-q j i)))

omit [Fintype ι] [DecidableEq ι] in
theorem affineSteps_signedClock_eq (as : List PositiveMass) (q r : ℕ → ι → ℝ) (t : ℝ) :
    affineSteps (signedClockSteps as q r) t = clockSteps as (interpolatedIncrements q r t) := by
  induction as generalizing q r with
  | nil => rfl
  | cons a as ih =>
    simp only [signedClockSteps,affineSteps_cons,clockSteps,Pi.sub_apply,ih]
    rfl

omit [Nonempty S] in
theorem pathKernelPenalty_signedClock_eq (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (as : List PositiveMass) (q r : ℕ → ι → ℝ) (t a : ℝ) :
    pathKernelPenalty w φ (featureKernel φ (r 0-q 0)) a (signedClockSteps as q r) t =
      clockPairReward w φ (fun j => featureKernel φ (r j-q j)) as a (interpolatedIncrements q r t) := by
  induction as generalizing q r a with
  | nil => rfl
  | cons b as ih =>
    funext x
    change (b.val-a)*hierarchyPairMean w φ (featureKernel φ (r 0-q 0))
        (affineSteps (signedClockSteps (b::as) q r) t) x+
      varianceTest b.val
        (gaussianHierarchy w φ (affineSteps (signedClockSteps as (fun j => q (j+1)) (fun j => r (j+1))) t))
        (pathKernelPenalty w φ
          (fun σ τ => featureKernel φ (r 0-q 0) σ τ+
            featureKernel φ ((r 1-q 1)-(r 0-q 0)) σ τ) b.val
          (signedClockSteps as (fun j => q (j+1)) (fun j => r (j+1))) t)
        (fun i => (q 1-q 0) i+t*((r 1-q 1)-(r 0-q 0)) i) x = _
    rw [featureKernel_add_difference,ih (fun j => q (j+1)) (fun j => r (j+1)) b.val,
      affineSteps_signedClock_eq,affineSteps_signedClock_eq]
    rfl

 

theorem root_pathKernelPenalty_eq_massStepSum {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (as : List PositiveMass) (ha : MassOrdered 0 as)
    (q r : ℕ → ι → ℝ) (t : ℝ) :
    zeroContinuation (Measure.pi fun i => gaussianReal 0 (Real.toNNReal (q 0 i+t*(r 0 i-q 0 i))))
      (pathKernelPenalty w φ (featureKernel φ (r 0-q 0)) 0 (signedClockSteps as q r) t) 0 =
      massStepSum as 0 (fun j => rootLevelPairMean w φ
        (fun i => Real.toNNReal (q 0 i+t*(r 0 i-q 0 i)))
        (featureKernel φ (r j-q j)) (affineSteps (signedClockSteps as q r) t) j) := by
  rw [pathKernelPenalty_signedClock_eq,affineSteps_signedClock_eq]
  exact zero_clockPairReward_eq_massStepSum hw φ _ as ha _ _

end SKFluctuations.Hierarchy

namespace SKFluctuations.GaussianCalculus
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators
variable {ι : Type*} [Fintype ι]

 

theorem hasDerivAt_integral_scaledSource {ν : Measure (ι → ℝ)} (hν : ExponentialIncrement ν)
    {F : (ι → ℝ) → ℝ} {G : ι → (ι → ℝ) → ℝ} {C : ℝ≥0}
    (hF : LipschitzWith C F) (hG : ∀ i, Continuous (G i))
    (hdF : ∀ x v t, HasDerivAt (fun s : ℝ => F (x+s • v))
      (∑ i, v i*G i (x+t • v)) t)
    {a a' : ℝ → (ι → ℝ)} {l r B t : ℝ} (ht : t ∈ Ioo l r)
    (ha : ∀ s ∈ Ioo l r, HasDerivAt a (a' s) s)
    (hB : ∀ s ∈ Ioo l r, ‖a' s‖ ≤ B) (x : ι → ℝ) :
    HasDerivAt (fun s => ∫ z, F (x+a s*z) ∂ν)
      (∫ z, ∑ i, (a' t*z) i*G i (x+a t*z) ∂ν) t := by
  have hd (s) (hs : s ∈ Ioo l r) (z : ι → ℝ) :
      HasDerivAt (fun u => F (x+a u*z)) (∑ i, (a' s*z) i*G i (x+a s*z)) s := by
    apply LipschitzWith.hasDerivAt_curve hF (HasDerivAt.const_add x ((ha s hs).mul_const z))
    simpa only [zero_smul,add_zero] using hdF (x+a s*z) (a' s*z) 0
  have hb (s) (hs : s ∈ Ioo l r) (z : ι → ℝ) :
      |∑ i, (a' s*z) i*G i (x+a s*z)| ≤ (C:ℝ)*B*‖z‖ := by
    have hl : HasLineDerivAt ℝ F (∑ i, (a' s*z) i*G i (x+a s*z)) (x+a s*z) (a' s*z) := by
      simpa only [HasLineDerivAt,zero_smul,add_zero] using hdF (x+a s*z) (a' s*z) 0
    have hh := norm_lineDeriv_le_of_lipschitz ℝ (x₀ := x+a s*z) (v := a' s*z) hF
    rw [hl.lineDeriv,Real.norm_eq_abs] at hh
    exact hh.trans ((mul_le_mul_of_nonneg_left ((norm_mul_le _ _).trans
      (mul_le_mul_of_nonneg_right (hB s hs) (norm_nonneg z))) C.coe_nonneg).trans_eq (by ring))
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (s := Ioo l r) (bound := fun z => (C:ℝ)*B*‖z‖)
    (Ioo_mem_nhds ht.1 ht.2) _ ((ExpNormBounded.lipschitz hF).diagonal_integrable hν x (a t)) _ _
    (hν.integrable_norm.const_mul ((C:ℝ)*B)) _).2
  · exact Eventually.of_forall fun _ =>
      (hF.continuous.comp (continuous_const.add (continuous_const.mul continuous_id))).aestronglyMeasurable
  · exact (continuous_finsetSum _ fun i _ =>
      ((continuous_apply i).const_mul (a' t i)).mul
        ((hG i).comp (continuous_const.add (continuous_const.mul continuous_id)))).aestronglyMeasurable
  · exact Eventually.of_forall fun z s hs => by
      simpa only [Real.norm_eq_abs] using hb s hs z
  · exact Eventually.of_forall fun z s hs => hd s hs z

 
theorem hasDerivAt_signed_zeroContinuation {n : ℕ}
    {F : (Fin (n+1) → ℝ) → ℝ} {G H : Fin (n+1) → (Fin (n+1) → ℝ) → ℝ} {C : ℝ≥0}
    (hF : LipschitzWith C F) (hG : ∀ i, BddSmooth 0 (G i)) (hH : ∀ i, BddSmooth 0 (H i))
    (hd : ∀ x v t, HasDerivAt (fun s : ℝ => F (x+s • v))
      (∑ i, v i*G i (x+t • v)) t)
    (hd₁ : ∀ i x t, HasDerivAt (fun s : ℝ => G i (x+s • Pi.single i 1))
      (H i (x+t • Pi.single i 1)) t)
    (q d : Fin (n+1) → ℝ) {t : ℝ} (ht : ∀ i, 0 < q i+t*d i) (x : Fin (n+1) → ℝ) :
    HasDerivAt (fun s => zeroContinuation (Measure.pi fun i => gaussianReal 0
        (Real.toNNReal (q i+s*d i))) F x)
      (∑ i, (d i/2)*zeroContinuation (Measure.pi fun i => gaussianReal 0
        (Real.toNNReal (q i+t*d i))) (H i) x) t := by
  let a := fun s i => Real.sqrt (q i+s*d i)
  let a' := fun s i => d i/(2*Real.sqrt (q i+s*d i))
  let ν := Measure.pi (fun _ : Fin (n+1) => gaussianReal 0 1)
  have hν : ExponentialIncrement ν := exponentialIncrement_gaussian (fun _ => 1)
  have ha' : ContinuousAt a' t := continuousAt_pi.mpr fun i =>
    continuousAt_const.div (continuousAt_const.mul
      (continuousAt_const.add (continuousAt_id.mul continuousAt_const)).sqrt)
      (mul_ne_zero (by norm_num) (Real.sqrt_ne_zero'.mpr (ht i)))
  have hp : ∀ᶠ s in 𝓝 t, ∀ i, 0 < q i+s*d i := by
    rw [eventually_all]
    intro i
    exact (continuousAt_const.add (continuousAt_id.mul continuousAt_const)).eventually
      (eventually_gt_nhds (ht i))
  have hB : ∀ᶠ s in 𝓝 t, ‖a' s‖ ≤ ‖a' t‖+1 :=
    (ha'.norm.eventually (eventually_lt_nhds (lt_add_one _))).mono fun _ h => h.le
  obtain ⟨l,r,htr,hlr⟩ := (hp.and hB).exists_Ioo_subset
  have haD (s) (hs : s ∈ Ioo l r) : HasDerivAt a (a' s) s := by
    apply hasDerivAt_pi.mpr
    intro i
    simpa only [a,a',id_eq,one_mul] using
      (((hasDerivAt_id s).mul_const (d i)).const_add (q i)).sqrt ((hlr hs).1 i).ne'
  have hh := hasDerivAt_integral_scaledSource hν hF (fun i => (hG i).continuous)
    hd htr haD (fun s hs => (hlr hs).2) x
  have hs (i : Fin (n+1)) : (∫ z, z i*G i (x+a t*z) ∂ν) =
      a t i*∫ z, H i (x+a t*z) ∂ν :=
    standardGaussianVector_diagonal_stein i (ExpNormBounded.bddSmooth (hG i))
      (ExpNormBounded.bddSmooth (hH i)) (hd₁ i) x (a t)
  have heF (s : ℝ) : zeroContinuation (Measure.pi fun i => gaussianReal 0
      (Real.toNNReal (q i+s*d i))) F x = ∫ z, F (x+a s*z) ∂ν := by
    simpa only [zeroContinuation,a,ν,sqrt_coe_toNNReal,Pi.mul_def] using
      (integral_diagonalGaussian (fun i => Real.toNNReal (q i+s*d i))
        (f := fun z => F (x+z)) (hF.continuous.comp (continuous_const.add continuous_id))).symm
  have heH (i : Fin (n+1)) : zeroContinuation (Measure.pi fun i => gaussianReal 0
      (Real.toNNReal (q i+t*d i))) (H i) x = ∫ z, H i (x+a t*z) ∂ν := by
    simpa only [zeroContinuation,a,ν,sqrt_coe_toNNReal,Pi.mul_def] using
      (integral_diagonalGaussian (fun i => Real.toNNReal (q i+t*d i))
        (f := fun z => H i (x+z)) ((hH i).continuous.comp (continuous_const.add continuous_id))).symm
  simp_rw [heF,heH]
  apply hh.congr_deriv
  rw [integral_finsetSum _ (fun i _ => (by
    simpa only [Pi.mul_apply,mul_assoc] using
      ((ExpNormBounded.bddSmooth (hG i)).diagonal_coord_integrable (fun _ => 1) x (a t) i).const_mul (a' t i)))]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.mul_apply]
  rw [show (fun z => a' t i*z i*G i (x+a t*z)) =
      (fun z => a' t i*(z i*G i (x+a t*z))) by funext z; ring,
    integral_const_mul,hs,← mul_assoc]
  congr 1
  dsimp [a,a']
  rw [div_mul_eq_mul_div, mul_div_mul_right _ _ (Real.sqrt_ne_zero'.mpr (ht i))]

end SKFluctuations.GaussianCalculus

end

end OAI
