import Mathlib
import OAI.Combinatorics.MatchingCount.Algorithm.GuardProbability

namespace OAI

namespace MatchingFPRAS.FiniteTrial
open Transport Enlargement Variation Adaptive Amplification Finset
open scoped Classical

variable {G : GraphInput} [Nontrivial (Fin G.n)]
attribute [local instance] NumberedHierarchy.labelOrder sym2Order bagEdgeOrder bagEdgeFintype
attribute [local instance] UnitRefresh.Computable.allowedDec prodOrder sumOrder
noncomputable local instance (w : Fin G.n → Fin G.n → ℚ) (K : ℕ) :
    DecidableEq (SourceLabel (fun x y=>(w x y:ℝ)) K) := Classical.decEq _
noncomputable local instance (w : Fin G.n → Fin G.n → ℚ) (K : ℕ) :
    Fintype (BagEdge (sourceBags (fun x y=>(w x y:ℝ)) K)) := Fintype.ofFinite _
noncomputable local instance (w : Fin G.n → Fin G.n → ℚ) (K : ℕ) :
    Fintype (SourceMarked (fun x y=>(w x y:ℝ)) K) := Fintype.ofFinite _

noncomputable def guardBits (p : Trial.Parameters G) : ℕ := 16*oneBits p
noncomputable def ScaleState.drawGuard (p : Trial.Parameters G) (s : ScaleState G p.K) :
    (Fin (guardBits p) → Bool) → GuardSamples p s :=
  (fun b i=>s.drawOne p le_rfl (b i)) ∘ matrixBitsEquiv 16 (oneBits p)
lemma ScaleState.drawGuard_law (p : Trial.Parameters G) (s : ScaleState G p.K) :
    imageLaw (s.drawGuard p)=(guardLaw p s).mass := by
  unfold ScaleState.drawGuard
  erw [imageLaw_comp_equiv,imageLaw_componentwise]
  rw [ScaleState.drawOne_law]
  rfl
lemma ScaleState.drawGuard_no_certificate (p : Trial.Parameters G) (s : ScaleState G p.K)
    (hZ : Z G = 0) (b : Fin (guardBits p) → Bool) : ¬guardPass p s (s.drawGuard p b) := by
  dsimp only [guardBits] at b
  dsimp only [guardPass, ScaleState.drawGuard, guardBits, Function.comp_apply]
  simp only [s.drawOne_certificate_zero p le_rfl hZ, lt_self_iff_false, exists_const, not_false_eq_true]

noncomputable def guardedBits (p : Trial.Parameters G) : ℕ := p.K*stageBits p+guardBits p
noncomputable def drawGuarded (p : Trial.Parameters G) :
    (Fin (guardedBits p) → Bool) → GuardedTrial p :=
  fun b =>
    let c := pairBitsEquiv (p.K*stageBits p) (guardBits p) b
    let x := drawLayer p p.K le_rfl c.1
    ⟨x,((layers p p.K le_rfl).state x).drawGuard p c.2⟩
lemma drawGuarded_law (p : Trial.Parameters G) : imageLaw (drawGuarded p)=(guardedLaw p).mass := by
  change imageLaw ((fun c : (Fin (p.K*stageBits p) → Bool) × (Fin (guardBits p) → Bool) =>
    (⟨drawLayer p p.K le_rfl c.1,
      ((layers p p.K le_rfl).state (drawLayer p p.K le_rfl c.1)).drawGuard p c.2⟩ : GuardedTrial p)) ∘
    pairBitsEquiv (p.K*stageBits p) (guardBits p)) = _
  erw [imageLaw_comp_equiv]
  change imageLaw _ = sigmaLift (layers p p.K le_rfl).law.mass (fun x=>(guardLaw p ((layers p p.K le_rfl).state x)).mass)
  rw [imageLaw_sigma_pair (drawLayer p p.K le_rfl) (fun x=>((layers p p.K le_rfl).state x).drawGuard p)]
  simp_rw [ScaleState.drawGuard_law]
  rw [drawLayer_law]
noncomputable def guardedBitOutput (p : Trial.Parameters G) : (Fin (guardedBits p) → Bool) → ℚ :=
  guardedOutput p ∘ drawGuarded p
lemma guardedBitOutput_nonneg (p : Trial.Parameters G) (b : Fin (guardedBits p) → Bool) :
    0≤guardedBitOutput p b := guardedOutput_nonneg p _
theorem guardedBitOutput_zero (p : Trial.Parameters G) (hZ : Z G=0) (b : Fin (guardedBits p) → Bool) :
    guardedBitOutput p b=0 := by
  unfold guardedBitOutput drawGuarded
  simp only [Function.comp_apply, guardedOutput]
  exact ite_eq_right (ScaleState.drawGuard_no_certificate p _ hZ _)

noncomputable def guardedAmplifiedBits (p : Trial.Parameters G) (δ : ℚ) : ℕ :=
  (2*halfRepetitions δ+1)*guardedBits p
noncomputable def drawGuardedTrials (p : Trial.Parameters G) (δ : ℚ) :
    (Fin (guardedAmplifiedBits p δ) → Bool) → Fin (2*halfRepetitions δ+1) → GuardedTrial p :=
  (fun bits i=>drawGuarded p (bits i)) ∘ matrixBitsEquiv (2*halfRepetitions δ+1) (guardedBits p)
lemma drawGuardedTrials_law (p : Trial.Parameters G) (δ : ℚ) :
    imageLaw (drawGuardedTrials p δ)=((guardedLaw p).iid (2*halfRepetitions δ+1)).mass := by
  unfold drawGuardedTrials
  erw [imageLaw_comp_equiv,imageLaw_componentwise]
  rw [drawGuarded_law]
  rfl
noncomputable def guardedAmplifiedOutput (p : Trial.Parameters G) (δ : ℚ)
    (x : Fin (2*halfRepetitions δ+1) → GuardedTrial p) : ℚ := median (fun i=>guardedOutput p (x i))
noncomputable def guardedAmplifiedBitOutput (p : Trial.Parameters G) (δ : ℚ) :
    (Fin (guardedAmplifiedBits p δ) → Bool) → ℚ := guardedAmplifiedOutput p δ ∘ drawGuardedTrials p δ
lemma guardedAmplifiedBitOutput_nonneg (p : Trial.Parameters G) (δ : ℚ)
    (b : Fin (guardedAmplifiedBits p δ) → Bool) : 0≤guardedAmplifiedBitOutput p δ b :=
  median_nonneg _ (fun _=>guardedOutput_nonneg p _)

omit [Nontrivial (Fin G.n)] in
lemma median_eq_of_constant {k : ℕ} (x : Fin (2*k+1) → ℚ) (a : ℚ) (hx : ∀ i,x i=a) : median x=a := by
  unfold median sortedValue
  have hp := List.mergeSort_perm (List.ofFn x) (· ≤ ·)
  have hm : (sortedList x)[k]'(by rw [sortedList_length]; omega) ∈ List.ofFn x :=
    hp.mem_iff.mp (List.getElem_mem _)
  obtain ⟨i,hi⟩ := List.mem_ofFn.mp hm
  rw [←hi, hx]

theorem guardedAmplifiedBitOutput_zero (p : Trial.Parameters G) (hZ : Z G=0) (δ : ℚ)
    (b : Fin (guardedAmplifiedBits p δ) → Bool) : guardedAmplifiedBitOutput p δ b=0 := by
  apply median_eq_of_constant
  intro i
  exact guardedBitOutput_zero p hZ _

noncomputable def guardedAccurateBits (p : Trial.Parameters G) (δ : ℚ) : Finset (Fin (guardedAmplifiedBits p δ) → Bool) :=
  univ.filter fun b=>Accurate p (guardedAmplifiedBitOutput p δ b)
theorem guardedAmplifiedBitOutput_success (p : Trial.Parameters G) (hZ : 0<Z G) (δ : ℚ) (hδ : 0<δ) :
    ((guardedAccurateBits p δ).card:ℚ)/(2:ℚ)^(guardedAmplifiedBits p δ)≥1-δ := by
  have hf := median_delta (guardedLaw p) (guardedOutput p) ((1-p.epsilon)*(Z G:ℚ))
    ((1+p.epsilon)*(Z G:ℚ)) (guarded_trial_failure p hZ) δ hδ
  have hc:=event_complement ((guardedLaw p).iid (2*halfRepetitions δ+1)).mass
    (fun x=>Accurate p (guardedAmplifiedOutput p δ x))
  rw [Law.total] at hc
  have hh : 1-(δ:ℝ) ≤ event ((guardedLaw p).iid (2*halfRepetitions δ+1)).mass
      (fun x=>Accurate p (guardedAmplifiedOutput p δ x)) := by
    change event _ (fun x=>¬Accurate p (guardedAmplifiedOutput p δ x))≤(δ:ℝ) at hf
    linarith only [hc,hf]
  rw [←drawGuardedTrials_law,event_imageLaw] at hh
  have he : Fintype.card (Fin (guardedAmplifiedBits p δ) → Bool)=2^(guardedAmplifiedBits p δ) := by simp
  rw [he] at hh
  change 1-(δ:ℝ) ≤ ((guardedAccurateBits p δ).card:ℝ)/(2^(guardedAmplifiedBits p δ):ℕ) at hh
  have hr : ((1-δ:ℚ):ℝ) ≤ (((((guardedAccurateBits p δ).card:ℚ)/(2:ℚ)^(guardedAmplifiedBits p δ)):ℚ):ℝ) := by
    push_cast
    simpa only [Nat.cast_pow,Nat.cast_ofNat] using hh
  exact Rat.cast_le.mp hr

end MatchingFPRAS.FiniteTrial

end OAI
