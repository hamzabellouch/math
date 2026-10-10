import OAI.Probability.TraceReconstruction.LayoutRates

namespace OAI

/-!
# ErrorRates

Realization of block caps, sparse scales, sharp and smoothing budgets, tree tails, fit errors, and uniform polynomial/exponential bounds.
-/

open scoped ENNReal
noncomputable section

open Filter
open scoped Topology


noncomputable section
namespace TraceReconstruction
open scoped Classical

theorem sourceWindowSize_le (N : ℝ) (b j : ℕ) (ε : ℝ) (hN : 0 ≤ N) :
    (sourceWindowSize N b ε j:ℝ) ≤ N^(scaleKappa b (j+1) ε) := by
  have hh := Nat.floor_le (div_nonneg (Real.rpow_nonneg hN (scaleKappa b (j+1) ε)) (by norm_num : (0:ℝ) ≤ 4))
  unfold sourceWindowSize
  push_cast
  linarith only [hh]

-- We use only positive target scales below.
theorem SourceArithmeticBounds.scheduled_trials {C N F ε : ℝ} {s b ell k : ℕ}
    (H : SourceArithmeticBounds C N F ε s b ell k) (hN : 0 < N) (hC : 0 < C) (hF : 0 < F)
    (j : ℕ) (hj : j+1 < b) :
    N^(scaleKappa b (j+2) ε+ε)/(4800*(C^(2*b)*F)) ≤
      (sourceScheduledTrials (sourceBlockWindows N b ε) (sourceArithmeticTrials C N b ε ell k) (j+1):ℝ) := by
  let T := sourceBlockWindows N b ε
  let n := sourceArithmeticTrials C N b ε ell k
  have htbig := (H.windows (j+1) hj).1
  have hsize : (T (j+1):ℝ) ≤ N^(scaleKappa b (j+2) ε) := by
    dsimp [T]
    rw [sourceBlockWindows,ite_eq_left hj]
    have hh := Nat.floor_le (div_nonneg (Real.rpow_nonneg hN.le (scaleKappa b (j+2) ε)) (by norm_num : (0:ℝ) ≤ 4))
    simp only [sourceWindowSize,Nat.cast_mul,Nat.cast_ofNat]
    linarith only [hh]
  have hx : 8 ≤ N^(scaleKappa b (j+2) ε) := by
    have hh : (24:ℝ) ≤ T (j+1) := by exact_mod_cast htbig
    linarith only [hh,hsize]
  have hlo := (sourceWindowSize_bounds (b:=b) (j:=j+1) hx).1
  have hn := (H.trials j (by omega)).1
  have hdvd : 4 ∣ T (j+1) := by
    dsimp [T]
    rw [sourceBlockWindows,ite_eq_left hj,sourceWindowSize]
    exact dvd_mul_right _ _
  have htlo : N^(scaleKappa b (j+2) ε)/8 ≤ ((T (j+1)/4:ℕ):ℝ) := by
    rw [Nat.cast_div hdvd (by norm_num : (4:ℝ)≠0)]
    have hh : (sourceWindowSize N b ε (j+1):ℝ)=(T (j+1):ℝ) := by simp [T,sourceBlockWindows,hj]
    rw [hh] at hlo
    linarith only [hlo]
  rw [sourceScheduledTrials,Nat.cast_mul,Real.rpow_add hN]
  calc
    _ = (N^(scaleKappa b (j+2) ε)/8)*(N^ε/(600*(C^(2*b)*F))) := by ring
    _ ≤ _ := mul_le_mul htlo hn (by positivity) (by positivity)

theorem SourceArithmeticBounds.binomial_caps {C N F ε ω : ℝ} {s b ell k : ℕ}
    (H : SourceArithmeticBounds C N F ε s b ell k) (hN : 0 < N)
    (hC : 1 ≤ C) (hF : 1 ≤ F) (hω : 0 < ω) :
    (∀j<b,hiddenBinomialCap (sourceArithmeticTrials C N b ε ell k j) ω ≤
       (200*(C^(2*b)*F)/ω)*N^(-ε/2)) ∧
    (∀j,j+1<b →hiddenBinomialCap
      (sourceScheduledTrials (sourceBlockWindows N b ε) (sourceArithmeticTrials C N b ε ell k) (j+1)) ω ≤
        (200*(C^(2*b)*F)/ω)*N^(-(scaleKappa b (j+2) ε+ε)/2)) := by
  let G := C^(2*b)*F
  have hG : 1 ≤ G := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hC) hF
  have hcoef : 4*(4800*G) ≤ (200*G/ω)^2*ω^2 := by
    have hident : (200*G/ω)^2*ω^2=40000*G^2 := by field_simp; ring
    rw [hident]
    nlinarith only [hG,sq_nonneg (G-1)]
  constructor
  · intro j hj
    apply hiddenBinomialCap_rpow hN (by positivity : 0 < 600*G) (by positivity) (H.trials j hj).1
    dsimp [G] at *
    have hnon : 0 ≤ C^(2*b)*F := by positivity
    linarith only [hcoef,hnon]
  · intro j hj
    exact hiddenBinomialCap_rpow hN (by positivity : 0 < 4800*G) (by positivity)
      (H.scheduled_trials hN (by linarith only [hC]) (by linarith only [hF]) j hj) hcoef

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical

theorem sourceSparseCount_scale (N : ℝ) (b s : ℕ) (ε : ℝ) (hN : 0 < N) :
    (sourceSparseCount (sourceBlockWindows N b ε) s (b-1):ℝ) ≤
      ((2^s:ℕ):ℝ)*N^(sourceInteriorExponent b ε) := by
  unfold sourceSparseCount sourceInteriorExponent
  push_cast
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [Real.rpow_sum_of_pos hN]
  apply Finset.prod_le_prod₀
  · intro j _
    positivity
  · intro j hj
    have hj' := Finset.mem_range.mp hj
    rw [sourceBlockWindows,ite_eq_left (by omega)]
    exact sourceWindowSize_le N b (j+1) ε hN.le

theorem sourceLeafCount_succ (T : ℕ → ℕ) (j : ℕ) :
    SourceLeafCount T (j+1)=T j*SourceLeafCount T j := by
  exact (Fintype.card_prod (α:=Fin (T j)) (β:=WindowLeaf T j)).trans (by rw [Fintype.card_fin])

theorem sourceLeafCount_le_length {P T : ℕ → ℕ} {ell b : ℕ} (hell : 1 ≤ ell)
    (hPT : ∀j<b,T j ≤ P j) : SourceLeafCount T b ≤ sourceBlockLength P ell b := by
  induction b with
  | zero =>
    change Fintype.card (Fin 1) ≤ ell
    simpa using hell
  | succ b ih =>
    rw [sourceLeafCount_succ,sourceBlockLength]
    exact Nat.mul_le_mul (hPT b (by omega)) (ih (fun j hj=>hPT j (by omega)))

theorem sourceArithmeticLength_eq_block (C N : ℝ) (b : ℕ) (ε : ℝ) (ell k j : ℕ) :
    sourceArithmeticLength C N b ε ell k j=
      sourceBlockLength (sourceArithmeticP C N b ε ell k) ell j := by
  induction j with
  | zero => rfl
  | succ j ih => rw [sourceArithmeticLength_step,sourceBlockLength,ih,mul_comm]

theorem SourceArithmeticBounds.leaf_bound {C N F ε : ℝ} {s b ell k : ℕ}
    (H : SourceArithmeticBounds C N F ε s b ell k) (hN : 0 < N) :
    (SourceLeafCount (sourceBlockWindows N b ε) b:ℝ) ≤ N := by
  have hell : 1 ≤ ell := by
    have hh := (H.lengths 0 (Nat.zero_le _)).1
    rw [show sourceArithmeticLength C N b ε ell k 0=ell by rfl] at hh
    have hp : 0 < N^(scaleA b 0 ε)/2 := by positivity
    have he : (0:ℝ)<ell := hp.trans_le hh
    have he' : 0<ell := by exact_mod_cast he
    omega
  have hh := sourceLeafCount_le_length (P:=sourceArithmeticP C N b ε ell k) hell
    (fun j hj=>Nat.le_trans (by omega : sourceBlockWindows N b ε j ≤ 2*sourceBlockWindows N b ε j)
      (H.windows j hj).2.2.1)
  have hh' : (SourceLeafCount (sourceBlockWindows N b ε) b:ℝ) ≤
      sourceArithmeticLength C N b ε ell k b := by
    rw [sourceArithmeticLength_eq_block]
    exact_mod_cast hh
  apply hh'.trans
  simpa only [scaleA_top,Real.rpow_one] using (H.lengths b le_rfl).2

/-- Full sparse degree, with the excluded bottom window and the exact
 source gap. This is the high-degree geometric gain, before constants. -/
theorem source_sparse_weight_bound (N ε d W w : ℝ) (b s : ℕ) (hN : 0 < N) (hW : 0 ≤ W)
    (hw : w^2 ≤ W*N^(-scaleA b 0 ε*d)) :
    w^2*(sourceSparseCount (sourceBlockWindows N b ε) s (b-1):ℝ) ≤
      W*((2^s:ℕ):ℝ)*N^(-(scaleA b 0 ε*d-sourceInteriorExponent b ε)) := by
  have hr : N^(-scaleA b 0 ε*d)*N^(sourceInteriorExponent b ε)=
      N^(-(scaleA b 0 ε*d-sourceInteriorExponent b ε)) := by
    rw [←Real.rpow_add hN]
    congr 1
    ring
  calc
    _ ≤ (W*N^(-scaleA b 0 ε*d))*(((2^s:ℕ):ℝ)*N^(sourceInteriorExponent b ε)) :=
      mul_le_mul hw (sourceSparseCount_scale N b s ε hN) (by positivity) (by positivity)
    _ = (W*((2^s:ℕ):ℝ))*(N^(-scaleA b 0 ε*d)*N^(sourceInteriorExponent b ε)) := by ring
    _ = _ := by rw [hr]

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical

def sourceBadRoleFactor (b R : ℕ) : ℝ :=
  ∑r∈Finset.range R,4*((3^((b+1)*r):ℕ):ℝ)^2

def sourceForcedRoleFactor (b R : ℕ) : ℝ :=
  ∑r∈Finset.range R,4*((3^((b+1)*r):ℕ):ℝ)*(OccupiedParityTree.shapeRoleConstant r (b+1):ℝ)

/-- Explicit finite sharp energy bound. The two undesirable pattern classes
 are suppressed by eta and a, and the genuine binary forced skeleton pays
 its full source exponent. The high tail uses the sparse, not dense count. -/
theorem source_sharp_numeric (T n : ℕ→ℕ) (s b R : ℕ) (ω η a w N ε d K W Q gap : ℝ)
    (hN : 1 ≤ N) (hK : 0 ≤ K) (hW : 0 ≤ W) (_hQ : 0 ≤ Q)
    (hleaves : (SourceLeafCount T (b+1):ℝ) ≤ N) (hwone : w^2 ≤ 1)
    (hw : w^2 ≤ W*N^(-scaleA (b+1) 0 ε*d))
    (hsmall : w^2*((2^s:ℕ):ℝ)*(sourceSparseCount T s b:ℝ) ≤ 1)
    (hhalf : w^2*(sourceSparseCount T s b:ℝ) ≤ 1/2)
    (hsparse : w^2*(sourceSparseCount T s b:ℝ) ≤ Q*N^(-gap))
    (hn : ∀j≤b,hiddenBinomialCap (n j) ω ≤ K*N^(-ε/2))
    (hg : ∀j<b,hiddenBinomialCap (sourceScheduledTrials T n (j+1)) ω ≤
      K*N^(-(scaleKappa (b+1) (j+2) ε+ε)/2)) :
    sourceSharpEnergyBudget T n s b R ω η a w ≤
      sourceBadRoleFactor b R*N^R*(η^2+a^2)+
      sourceForcedRoleFactor b R*W^(2^(b+1))*sourceSkeletonPrefactor s b K*N^(-forcedDecay (b+1) ε d)+
      8*Q^R*N^(-gap*(R:ℝ)) := by
  have hN0 : 0 < N := by linarith only [hN]
  let A := W^(2^(b+1))*sourceSkeletonPrefactor s b K*N^(-forcedDecay (b+1) ε d)
  have hA : 0 ≤ A := by dsimp [A]; positivity [sourceSkeletonPrefactor_nonneg s b hK]
  have hlow (r : ℕ) (hr : r∈Finset.range R) :
      w^(2*r)*(if r=0 then 0 else sourceSharpDegreeBudget T n s b r ω η a) ≤
        4*((3^((b+1)*r):ℕ):ℝ)^2*N^R*(η^2+a^2)+
          (4*((3^((b+1)*r):ℕ):ℝ)*(OccupiedParityTree.shapeRoleConstant r (b+1):ℝ))*A := by
    have hr' : r ≤ R := (Finset.mem_range.mp hr).le
    have hw0 : 0 ≤ w^(2*r) := by rw [pow_mul]; exact pow_nonneg (sq_nonneg w) r
    have hw1 : w^(2*r) ≤ 1 := by rw [pow_mul]; exact pow_le_one₀ (sq_nonneg w) hwone
    have hc : ((SourceLeafCount T (b+1)).choose r:ℝ) ≤ N^R := by
      have hh : ((SourceLeafCount T (b+1)).choose r:ℝ) ≤ (SourceLeafCount T (b+1):ℝ)^r := by
        exact_mod_cast Nat.choose_le_pow (SourceLeafCount T (b+1)) r
      exact hh.trans ((pow_le_pow_left₀ (by positivity) hleaves r).trans (pow_le_pow_right₀ hN hr'))
    have hbad : w^(2*r)*(((SourceLeafCount T (b+1)).choose r:ℝ)) ≤ N^R := by
      apply (mul_le_mul hw1 hc (by positivity) (by norm_num : (0:ℝ) ≤ 1)).trans_eq
      exact one_mul _
    by_cases hr0 : r=0
    · rw [ite_eq_left hr0,mul_zero]
      positivity
    rw [ite_eq_right hr0,sourceSharpDegreeBudget,mul_add]
    have hB : w^(2*r)*(4*((3^((b+1)*r):ℕ):ℝ)*
        (((SourceLeafCount T (b+1)).choose r:ℝ)*((3^((b+1)*r):ℕ):ℝ)*(η^2+a^2))) ≤
        4*((3^((b+1)*r):ℕ):ℝ)^2*N^R*(η^2+a^2) := by
      have hh := mul_le_mul_of_nonneg_right hbad
        (show 0 ≤ 4*((3^((b+1)*r):ℕ):ℝ)^2*(η^2+a^2) by positivity)
      nlinarith only [hh]
    rw [mul_add]
    apply add_le_add hB
    by_cases hrf : 2^(b+1) ≤ r
    · rw [ite_eq_left hrf]
      have hh := mul_le_mul_of_nonneg_left
        (source_forced_degree_decay T n s b r ω N ε d K W w hN0 hK hW hrf hsmall hw hn hg)
        (show 0 ≤ 4*((3^((b+1)*r):ℕ):ℝ) by positivity)
      dsimp [A]
      nlinarith only [hh]
    · rw [ite_eq_right hrf,mul_zero,mul_zero]
      positivity
  have hsum := Finset.sum_le_sum hlow
  rw [Finset.sum_add_distrib] at hsum
  have hbadSum : (∑r∈Finset.range R,4*((3^((b+1)*r):ℕ):ℝ)^2*N^R*(η^2+a^2))=
      sourceBadRoleFactor b R*N^R*(η^2+a^2) := by simp only [sourceBadRoleFactor,Finset.sum_mul]
  have hforceSum : (∑r∈Finset.range R,(4*((3^((b+1)*r):ℕ):ℝ)*(OccupiedParityTree.shapeRoleConstant r (b+1):ℝ))*A)=
      sourceForcedRoleFactor b R*W^(2^(b+1))*sourceSkeletonPrefactor s b K*N^(-forcedDecay (b+1) ε d) := by
    rw [←Finset.sum_mul]
    dsimp [sourceForcedRoleFactor,A]
    ring
  rw [hbadSum,hforceSum] at hsum
  apply add_le_add hsum
  have hx : 0 ≤ w^2*(sourceSparseCount T s b:ℝ) := by positivity
  have htail : 4*(w^2*(sourceSparseCount T s b:ℝ))^R/(1-w^2*(sourceSparseCount T s b:ℝ)) ≤
      8*(w^2*(sourceSparseCount T s b:ℝ))^R := by
    apply (div_le_iff₀ (by linarith only [hhalf])).mpr
    have hh := mul_le_mul_of_nonneg_right hhalf (pow_nonneg hx R)
    nlinarith only [hh]
  apply htail.trans
  have hrp : (N^(-gap))^R=N^(-gap*(R:ℝ)) := by rw [←Real.rpow_natCast,←Real.rpow_mul hN0.le]
  have hh := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hx hsparse R) (by norm_num : (0:ℝ)≤8)
  simpa only [mul_pow,hrp,mul_assoc] using hh

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical

def sourceSmoothingPrefactor (s : ℕ) (K : ℝ) : ℝ :=
  (2:ℝ)^(s*s+s)*(((s:ℝ)+1)*K)^(s+1)

theorem hiddenSmoothingBound_scale {N e K ω : ℝ} {m s : ℕ}
    (hN : 0 < N) (hK : 0 ≤ K)
    (hm : hiddenBinomialCap m ω ≤ K*N^(-e/2)) :
    hiddenSmoothingBound m s ω ≤ sourceSmoothingPrefactor s K*N^(-((s:ℝ)+1)*e/2) := by
  have hs : 1 ≤ (s:ℝ)+1 := by linarith [Nat.cast_nonneg s (α:=ℝ)]
  have hs0 : 0 ≤ (s:ℝ)+1 := by positivity
  have heq : 4*((s:ℝ)+1)/((m:ℝ)*ω^2+2)=((s:ℝ)+1)*(4/((m:ℝ)*ω^2+2)) := by ring
  have hh : Real.sqrt (4*((s:ℝ)+1)/((m:ℝ)*ω^2+2)) ≤ ((s:ℝ)+1)*K*N^(-e/2) := by
    rw [heq,Real.sqrt_mul hs0]
    have hsq : Real.sqrt ((s:ℝ)+1) ≤ (s:ℝ)+1 := by
      apply (Real.sqrt_le_iff).mpr
      exact ⟨hs0,by nlinarith only [hs,sq_nonneg ((s:ℝ))]⟩
    have h := mul_le_mul hsq hm (Real.sqrt_nonneg _) hs0
    simpa only [hiddenBinomialCap,mul_assoc] using h
  have hleft := mul_le_mul
    (pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left hh (by norm_num : (0:ℝ)≤2)) s)
    hh (Real.sqrt_nonneg _) (by positivity)
  apply (mul_le_mul_of_nonneg_left hleft (by positivity : (0:ℝ)≤2^(s*s))).trans_eq
  have hr : (N^(-e/2))^(s+1)=N^(-((s:ℝ)+1)*e/2) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hN.le]
    push_cast
    congr 1
    ring
  dsimp [sourceSmoothingPrefactor]
  rw [pow_add,pow_succ (((s:ℝ)+1)*K)]
  simp only [mul_pow]
  have he : (N^(-e/2))^s*N^(-e/2)=N^(-((s:ℝ)+1)*e/2) := by rw [←pow_succ,hr]
  calc
    _ = (2:ℝ)^(s*s)*2^s*((s:ℝ)+1)^s*K^s*(((s:ℝ)+1)*K)*
      ((N^(-e/2))^s*N^(-e/2)) := by ring
    _ = _ := by rw [he]; ring

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical

theorem sourceLeafCount_positive {T : ℕ → ℕ} {b : ℕ} (hT : ∀j<b,1 ≤ T j) :
    1 ≤ SourceLeafCount T b := by
  induction b with
  | zero => change 1 ≤ Fintype.card (Fin 1); simp
  | succ b ih =>
    rw [sourceLeafCount_succ]
    exact one_le_mul_of_one_le_of_one_le (hT b (by omega)) (ih (fun j hj=>hT j (by omega)))

theorem sourceFitTail_simple {T n : ℕ → ℕ} {b : ℕ} {v : ℝ}
    (hT : ∀j<b,1 ≤ T j)
    (hv : ∀j,j+1<b → v ≤ 2*((T j:ℝ)/8)^2/(((T (j+1):ℝ)+1)*(n j:ℝ))) :
    sourceFitTail T n b ≤ 2*(b:ℝ)*(SourceLeafCount T b:ℝ)*Real.exp (-v) := by
  induction b using Nat.twoStepInduction with
  | zero => simp [sourceFitTail]
  | one => simp only [sourceFitTail]; positivity
  | more b _ ih =>
    have hi := ih (fun j hj=>hT j (by omega)) (fun j hj=>hv j (by omega))
    have hleaf : (1:ℝ) ≤ SourceLeafCount T (b+1) := by
      exact_mod_cast sourceLeafCount_positive (fun j hj=>hT j (show j<b+2 by omega))
    have he := Real.exp_le_exp.mpr (neg_le_neg (hv b (by omega)))
    rw [sourceFitTail,sourceLeafCount_succ,Nat.cast_mul]
    have hmul := mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_left he (by norm_num : (0:ℝ)≤2)) hi)
      (show 0 ≤ (T (b+1):ℝ) by positivity)
    have hlast := mul_le_mul_of_nonneg_left hleaf (show 0 ≤ (T (b+1):ℝ)*Real.exp (-v) by positivity)
    push_cast at hmul ⊢
    have hex : -(2*((T b:ℝ)/8)^2/(((T (b+1):ℝ)+1)*(n b:ℝ))) =
        -2*((T b:ℝ)/8)^2/(((T (b+1):ℝ)+1)*(n b:ℝ)) := by ring
    rw [hex] at hmul
    nlinarith only [hmul,hlast]

theorem windowCollection_card_bound {T : ℕ → ℕ} {b : ℕ} (hT : ∀j<b,1 ≤ T j) :
    Fintype.card (WindowCollection T b) ≤ 2*b*SourceLeafCount T b := by
  induction b with
  | zero => change Fintype.card PEmpty ≤ _; simp
  | succ b ih =>
    have hi := ih (fun j hj=>hT j (by omega))
    have hp := sourceLeafCount_positive (b:=b) (fun j hj=>hT j (show j<b+1 by omega))
    have ht := hT b (by omega)
    have hc : Fintype.card (WindowCollection T (b+1))=2+T b*Fintype.card (WindowCollection T b) := by
      change Fintype.card (Bool ⊕ (Fin (T b) × WindowCollection T b))=_
      simp only [Fintype.card_sum,Fintype.card_bool,Fintype.card_prod,Fintype.card_fin]
    rw [hc,sourceLeafCount_succ]
    have hm := Nat.mul_le_mul_left (T b) hi
    have hh : 1 ≤ T b*SourceLeafCount T b := one_le_mul_of_one_le_of_one_le ht hp
    nlinarith only [hm,hh]

theorem collectionCount_lower {T n g : ℕ→ℕ} {b : ℕ} {M : ℝ}
    (hn : ∀j<b,M ≤ (n j:ℝ)) (hg : ∀j<b,g j=0 ∨ M ≤ (g j:ℝ))
    (v : WindowCollection T b) :
    collectionCount T n g b v=0 ∨ M ≤ (collectionCount T n g b v:ℝ) := by
  induction b with
  | zero => exact PEmpty.elim v
  | succ b ih =>
    rcases v with a | ⟨u,v⟩
    · cases a
      · exact Or.inr (hn b (by omega))
      · exact hg b (by omega)
    · exact ih (fun j hj=>hn j (by omega)) (fun j hj=>hg j (by omega)) v

theorem sourceEffectiveHiddenTail_simple {T n : ℕ→ℕ} {b : ℕ} {M ω : ℝ}
    (hT : ∀j<b,1 ≤ T j) (hn : ∀j<b,M ≤ (n j:ℝ))
    (hg : ∀j<b,sourceScheduledTrials T n j=0 ∨ M ≤ (sourceScheduledTrials T n j:ℝ)) :
    sourceEffectiveHiddenTail T n b ω ≤ 2*(b:ℝ)*(SourceLeafCount T b:ℝ)*Real.exp (-M*ω^4/16) := by
  unfold sourceEffectiveHiddenTail
  have hh (v : WindowCollection T b) :
      (if collectionCount T n (sourceScheduledTrials T n) b v=0 then 0 else
        Real.exp (-(collectionCount T n (sourceScheduledTrials T n) b v:ℝ)*ω^4/16)) ≤ Real.exp (-M*ω^4/16) := by
    rcases collectionCount_lower hn hg v with hz | hm
    · rw [ite_eq_left hz]; positivity
    · split_ifs
      · positivity
      · apply Real.exp_le_exp.mpr
        have hh := mul_le_mul_of_nonneg_right hm (pow_nonneg (sq_nonneg ω) 2)
        nlinarith only [hh]
  apply (Finset.sum_le_sum (fun v _=>hh v)).trans
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
  exact_mod_cast windowCollection_card_bound hT

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical

/-- The literal centering fluctuation has the source epsilon exponent.
 This does not treat nested window starts as independent. -/
theorem SourceArithmeticBounds.fit_exponent {C N F ε : ℝ} {s b ell k j : ℕ}
    (H : SourceArithmeticBounds C N F ε s b ell k) (hC : 0<C) (hF : 0<F) (hN : 1 ≤ N) (he : 0 ≤ ε)
    (hκ : ∀v<b,3*ε ≤ scaleKappa b (v+1) ε) (hj : j+1<b) :
    N^ε/512 ≤ 2*((sourceBlockWindows N b ε j:ℝ)/8)^2 /
      (((sourceBlockWindows N b ε (j+1):ℝ)+1)*(sourceArithmeticTrials C N b ε ell k j:ℝ)) := by
  have hN0 : 0<N := by linarith only [hN]
  have hpresent := (H.windows j (by omega)).1
  have hwin : 24 ≤ sourceWindowSize N b ε j := by
    simpa only [sourceBlockWindows,ite_eq_left (by omega : j<b)] using hpresent
  have hlarge : 8 ≤ N^(scaleKappa b (j+1) ε) := by
    have hh : (24:ℝ) ≤ sourceWindowSize N b ε j := by exact_mod_cast hwin
    exact (by norm_num : (8:ℝ)≤24).trans (hh.trans (sourceWindowSize_le N b j ε hN0.le))
  have hl : N^(scaleKappa b (j+1) ε)/2 ≤ (sourceBlockWindows N b ε j:ℝ) := by
    simpa only [sourceBlockWindows,ite_eq_left (by omega : j<b)] using (sourceWindowSize_bounds hlarge).1
  have hu : (sourceBlockWindows N b ε (j+1):ℝ)+1 ≤ 2*N^(scaleKappa b (j+2) ε) := by
    have hh := sourceWindowSize_le N b (j+1) ε hN0.le
    have he' : 0 ≤ scaleKappa b (j+2) ε := by linarith only [hκ (j+1) hj,he]
    have ho := Real.one_le_rpow hN he'
    simpa only [sourceBlockWindows,ite_eq_left hj] using (show (sourceWindowSize N b ε (j+1):ℝ)+1 ≤ 2*N^(scaleKappa b (j+2) ε) by linarith only [hh,ho])
  have htr := (H.trials j (by omega)).2
  have hd : ((sourceBlockWindows N b ε (j+1):ℝ)+1)*sourceArithmeticTrials C N b ε ell k j ≤
      4*N^(scaleKappa b (j+2) ε)*N^ε := by
    have hh := mul_le_mul hu htr (by positivity) (by positivity)
    nlinarith only [hh]
  have htrial : 0 < (sourceArithmeticTrials C N b ε ell k j:ℝ) :=
    (show 0 < N^ε/(600*(C^(2*b)*F)) by positivity).trans_le (H.trials j (by omega)).1
  have hdpos : 0 < ((sourceBlockWindows N b ε (j+1):ℝ)+1)*sourceArithmeticTrials C N b ε ell k j := by positivity
  apply (le_div_iff₀ hdpos).mpr
  have hmul := mul_le_mul_of_nonneg_left hd (show 0 ≤ N^ε/512 by positivity)
  have hsquare := pow_le_pow_left₀ (show 0 ≤ N^(scaleKappa b (j+1) ε)/2 by positivity) hl 2
  have hpow : N^ε*N^(scaleKappa b (j+2) ε)*N^ε=(N^(scaleKappa b (j+1) ε))^2 := by
    rw [←Real.rpow_add hN0,←Real.rpow_add hN0,←Real.rpow_natCast,←Real.rpow_mul hN0.le]
    norm_num only [Nat.cast_ofNat]
    congr 1
    have hx := scaleKappa_step b (j+1) ε (by omega)
    linarith only [hx]
  nlinarith only [hmul,hsquare,hpow]

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open Filter
open scoped Topology Classical

/-- A convenience for the manuscript's fixed-B polynomial losses. This
 predicate is only used to prove bounds on the literal finite constants. -/
def SourcePolyUpper (f : ℕ→ℝ) : Prop :=
  ∃ C : ℝ,0 ≤ C ∧ ∃ h : ℕ,∀D,f D ≤ C*((D:ℝ)+1)^h

theorem SourcePolyUpper.const (c : ℝ) : SourcePolyUpper (fun _=>c) := by
  refine ⟨|c|,abs_nonneg _,0,?_⟩
  intro D
  simpa using le_abs_self c

theorem SourcePolyUpper.depth : SourcePolyUpper (fun D=>(D:ℝ)+1) := by
  exact ⟨1,zero_le_one,1,by simp⟩

theorem SourcePolyUpper.mono {f g : ℕ→ℝ} (hg : SourcePolyUpper g) (hf : ∀D,f D ≤ g D) :
    SourcePolyUpper f := by
  obtain ⟨C,hC,h,H⟩ := hg
  exact ⟨C,hC,h,fun D=>(hf D).trans (H D)⟩

theorem SourcePolyUpper.add {f g : ℕ→ℝ} (hf : SourcePolyUpper f) (hg : SourcePolyUpper g) :
    SourcePolyUpper (fun D=>f D+g D) := by
  obtain ⟨C,hC,h,H⟩ := hf
  obtain ⟨K,hK,k,G⟩ := hg
  refine ⟨C+K,add_nonneg hC hK,h+k,?_⟩
  intro D
  have hd : 1 ≤ (D:ℝ)+1 := by linarith [Nat.cast_nonneg D (α:=ℝ)]
  have hh := (H D).trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hd (by omega : h ≤ h+k)) hC)
  have hk := (G D).trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hd (by omega : k ≤ h+k)) hK)
  nlinarith only [hh,hk]

theorem SourcePolyUpper.mul {f g : ℕ→ℝ} (hf : SourcePolyUpper f) (hg : SourcePolyUpper g)
    (hf0 : ∀D,0 ≤ f D) (hg0 : ∀D,0 ≤ g D) : SourcePolyUpper (fun D=>f D*g D) := by
  obtain ⟨C,hC,h,H⟩ := hf
  obtain ⟨K,hK,k,G⟩ := hg
  refine ⟨C*K,mul_nonneg hC hK,h+k,?_⟩
  intro D
  calc
    f D*g D ≤ (C*((D:ℝ)+1)^h)*(K*((D:ℝ)+1)^k) :=
      mul_le_mul (H D) (G D) (hg0 D) ((hf0 D).trans (H D))
    _ = _ := by rw [pow_add]; ring

theorem SourcePolyUpper.pow {f : ℕ→ℝ} (hf : SourcePolyUpper f) (hf0 : ∀D,0 ≤ f D) (r : ℕ) :
    SourcePolyUpper (fun D=>(f D)^r) := by
  obtain ⟨C,hC,h,H⟩ := hf
  refine ⟨C^r,pow_nonneg hC _,h*r,?_⟩
  intro D
  simpa only [mul_pow,pow_mul] using pow_le_pow_left₀ (hf0 D) (H D) r

theorem sourceEpsilon_inverse_poly (B : ℕ) :
    SourcePolyUpper (fun D=>(sourceEpsilon B D)⁻¹) := by
  refine ⟨(2:ℝ)^(4*B+100),by positivity,1,?_⟩
  intro D
  simp only [sourceEpsilon,one_div,inv_inv,pow_one]
  exact le_rfl

theorem totalScoreExponent_poly (B : ℕ) (hB : 2 ≤ B) :
    SourcePolyUpper (totalScoreExponent B) := by
  apply (SourcePolyUpper.const 3 |>.add
    (SourcePolyUpper.depth.mul (SourcePolyUpper.const (B:ℝ)) (fun D=>by positivity) (fun _=>by positivity))).mono
  intro D
  have hh := (totalScoreExponent_bounds B D hB).2
  nlinarith only [hh,Nat.cast_nonneg B (α:=ℝ)]

theorem SourcePolyUpper.ceil {f : ℕ→ℝ} (hf : SourcePolyUpper f) (hf0 : ∀D,0 ≤ f D) :
    SourcePolyUpper (fun D=>(⌈f D⌉₊:ℝ)) := by
  apply (hf.add (SourcePolyUpper.const 1)).mono
  intro D
  exact (Nat.ceil_lt_add_one (hf0 D)).le

theorem sourceCancellationOrder_poly (B : ℕ) (hB : 2 ≤ B) :
    SourcePolyUpper (fun D=>(sourceCancellationOrder B D:ℝ)) := by
  let f := fun D=>totalScoreExponent B D+(sourceDegreeCutoff B:ℝ)+B+10
  have hf : SourcePolyUpper f := (((totalScoreExponent_poly B hB).add
    (SourcePolyUpper.const (sourceDegreeCutoff B:ℝ))).add (SourcePolyUpper.const (B:ℝ))).add
      (SourcePolyUpper.const 10)
  have hf0 (D) : 0 ≤ f D := by
    have hd := (totalScoreExponent_bounds B D hB).1
    have hr : 0 ≤ (sourceDegreeCutoff B:ℝ) := Nat.cast_nonneg _
    dsimp [f]
    linarith only [hd,hr,Nat.cast_nonneg B (α:=ℝ)]
  have hh := ((SourcePolyUpper.const 100).mul hf (fun _=>by norm_num) hf0).mul
    (sourceEpsilon_inverse_poly B) (fun D=>mul_nonneg (by norm_num) (hf0 D))
      (fun D=>(inv_pos.mpr (sourceEpsilon_pos B D)).le)
  have hc := hh.ceil (fun D=>mul_nonneg (mul_nonneg (by norm_num) (hf0 D))
    (inv_pos.mpr (sourceEpsilon_pos B D)).le)
  simpa only [sourceCancellationOrder,f,div_eq_mul_inv] using hc

theorem sourceCancellationOrder_large (B D : ℕ) :
    100*(totalScoreExponent B D+(sourceDegreeCutoff B:ℝ)+B+10) ≤
      (sourceCancellationOrder B D:ℝ)*sourceEpsilon B D := by
  exact (div_le_iff₀ (sourceEpsilon_pos B D)).mp (Nat.le_ceil _)

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open Filter
open scoped Topology Classical

/-- Literal finite-block factors are subpower uniformly over the joint
 deletion regime when their logarithms grow polynomially in the depth. -/
def SourceExpUpper (f : ℕ→ℝ→ℝ) : Prop :=
  ∃ C : ℝ,0 ≤ C ∧ ∃ h : ℕ,∀D q,q∈Set.Ioc 0 (1/2:ℝ) →
    f D q ≤ Real.exp (C*((D:ℝ)+1)^h*q^(-3:ℤ))

theorem SourcePolyUpper.expUpper {f : ℕ→ℝ} (hf : SourcePolyUpper f) :
    SourceExpUpper (fun D _=>f D) := by
  obtain ⟨C,hC,h,H⟩ := hf
  refine ⟨C,hC,h,?_⟩
  intro D q hq
  have hΛ := deletion_inverse_cube_ge_one ⟨hq.1,by linarith only [hq.2]⟩
  have hmul := mul_le_mul_of_nonneg_left hΛ (show 0 ≤ C*((D:ℝ)+1)^h by positivity)
  exact (H D).trans ((by linarith only [hmul] : C*((D:ℝ)+1)^h ≤ C*((D:ℝ)+1)^h*q^(-3:ℤ)+1).trans
    (Real.add_one_le_exp _))

theorem SourceExpUpper.const (c : ℝ) : SourceExpUpper (fun _ _=>c) :=
  (SourcePolyUpper.const c).expUpper

theorem SourceExpUpper.mono {f g : ℕ→ℝ→ℝ} (hg : SourceExpUpper g)
    (hf : ∀D q,q∈Set.Ioc 0 (1/2:ℝ) → f D q ≤ g D q) : SourceExpUpper f := by
  obtain ⟨C,hC,h,H⟩ := hg
  exact ⟨C,hC,h,fun D q hq=>(hf D q hq).trans (H D q hq)⟩

theorem SourceExpUpper.mul {f g : ℕ→ℝ→ℝ} (hf : SourceExpUpper f) (hg : SourceExpUpper g)
    (hf0 : ∀D q,q∈Set.Ioc 0 (1/2:ℝ) → 0 ≤ f D q)
    (hg0 : ∀D q,q∈Set.Ioc 0 (1/2:ℝ) → 0 ≤ g D q) :
    SourceExpUpper (fun D q=>f D q*g D q) := by
  obtain ⟨C,hC,h,H⟩ := hf
  obtain ⟨K,hK,k,G⟩ := hg
  refine ⟨C+K,add_nonneg hC hK,h+k,?_⟩
  intro D q hq
  have hΛ : 0 ≤ q^(-3:ℤ) := (zpow_pos hq.1 _).le
  have hd : 1 ≤ (D:ℝ)+1 := by linarith [Nat.cast_nonneg D (α:=ℝ)]
  have hh := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hd (by omega : h≤h+k)) hC) hΛ
  have hk := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hd (by omega : k≤h+k)) hK) hΛ
  calc
    _ ≤ Real.exp (C*((D:ℝ)+1)^h*q^(-3:ℤ))*Real.exp (K*((D:ℝ)+1)^k*q^(-3:ℤ)) :=
      mul_le_mul (H D q hq) (G D q hq) (hg0 D q hq) ((hf0 D q hq).trans (H D q hq))
    _ ≤ _ := by rw [←Real.exp_add]; apply Real.exp_le_exp.mpr; nlinarith only [hh,hk]

theorem SourceExpUpper.pow_variably {f : ℕ→ℝ→ℝ} {r : ℕ→ℕ} (hf : SourceExpUpper f)
    (hf0 : ∀D q,q∈Set.Ioc 0 (1/2:ℝ) → 0 ≤ f D q)
    (hr : SourcePolyUpper (fun D=>(r D:ℝ))) : SourceExpUpper (fun D q=>(f D q)^(r D)) := by
  obtain ⟨C,hC,h,H⟩ := hf
  obtain ⟨K,hK,k,G⟩ := hr
  refine ⟨C*K,mul_nonneg hC hK,h+k,?_⟩
  intro D q hq
  have hΛ : 0≤q^(-3:ℤ) := (zpow_pos hq.1 _).le
  have hh := mul_le_mul_of_nonneg_right (G D) (show 0≤C*((D:ℝ)+1)^h*q^(-3:ℤ) by positivity)
  calc
    _ ≤ (Real.exp (C*((D:ℝ)+1)^h*q^(-3:ℤ)))^(r D) := pow_le_pow_left₀ (hf0 D q hq) (H D q hq) _
    _ = Real.exp ((r D:ℝ)*(C*((D:ℝ)+1)^h*q^(-3:ℤ))) := (Real.exp_nat_mul _ _).symm
    _ ≤ _ := by apply Real.exp_le_exp.mpr; rw [pow_add]; nlinarith only [hh]

theorem SourceExpUpper.pow {f : ℕ→ℝ→ℝ} (hf : SourceExpUpper f)
    (hf0 : ∀D q,q∈Set.Ioc 0 (1/2:ℝ) → 0 ≤ f D q) (r : ℕ) :
    SourceExpUpper (fun D q=>(f D q)^r) :=
  hf.pow_variably hf0 (SourcePolyUpper.const (r:ℝ))

theorem sourceOverlapConstant_expUpper : SourceExpUpper (fun _ q=>sourceOverlapConstant q) := by
  refine ⟨sourceChannelLogConstant,sourceChannelLogConstant_pos.le,0,?_⟩
  intro D q hq
  simp only [pow_zero,mul_one]
  apply (Real.log_le_iff_le_exp (sourceOverlapConstant_pos hq.1)).mp
  exact sourceOverlapConstant_log_bound ⟨hq.1,by linarith only [hq.2]⟩

theorem initialOverlapLower_inverse_expUpper : SourceExpUpper (fun _ q=>(initialOverlapLower q)⁻¹) := by
  refine ⟨1536+(32+3*primitivePeriodConstant),by unfold primitivePeriodConstant; positivity,0,?_⟩
  intro D q hq
  have hp := initialOverlapLower_pos q
  have hΛ := deletion_inverse_cube_ge_one ⟨hq.1,by linarith only [hq.2]⟩
  rw [←Real.log_le_iff_le_exp (inv_pos.mpr hp),Real.log_inv,initialOverlapLower,
    Real.log_div (Real.exp_pos _).ne' (by norm_num),Real.log_exp]
  simp only [pow_zero,mul_one,zpow_neg,zpow_ofNat] at hΛ ⊢
  have hh := Real.log_le_self (by norm_num : (0:ℝ)≤1536)
  have hmul := mul_le_mul_of_nonneg_left hΛ (by norm_num : (0:ℝ)≤1536)
  simp only [div_eq_mul_inv] at *
  nlinarith only [hh,hmul]

/-- All indices are inside the same physical n,q instance. -/
theorem SourceExpUpper.uniform (f : ℕ→ℝ→ℝ) (hf : SourceExpUpper f)
    (B : ℕ) (ζ δ : ℝ) (hB : 2 ≤ B) (hζ : ζ∈Set.Ioo 0 1) (hδ : 0<δ)
    {n q : ℕ→ℝ} (hn : Tendsto n atTop atTop) (hq : ∀t,q t∈Set.Ioc 0 (1/2:ℝ))
    (hH : Tendsto (fun t=>(q t)^3*Real.log (n t)) atTop atTop) :
    ∀ᶠt in atTop,∀i,f (sourceDepth B ζ ((q t)^3*Real.log (n t))) (q t) ≤
      (sourceTargetScale B (sourceDepth B ζ ((q t)^3*Real.log (n t))) (n t) i)^(
        δ*sourceEpsilon B (sourceDepth B ζ ((q t)^3*Real.log (n t)))) := by
  obtain ⟨C,hC,h,H⟩ := hf
  have hrel (t) : Real.log (n t)=(q t)^(-3:ℤ)*((q t)^3*Real.log (n t)) := by
    rw [zpow_neg,zpow_ofNat]
    field_simp [(hq t).1.ne']
  filter_upwards [source_uniform_exp_absorption B h ζ C δ hB hζ hC hδ hn hH
    (fun t=>zpow_pos (hq t).1 _) hrel] with t ht i
  exact (H _ _ (hq t)).trans (ht i)

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open Filter
open scoped Topology Classical

def sourceMomentEnvelope (B D : ℕ) : ℝ :=
  ((10^8:ℝ)*2^(10*B)*((B:ℝ)+4)*2+1)*((D:ℝ)+1)*2^(B*D)

def sourceCapEnvelope (B D : ℕ) (q : ℝ) : ℝ :=
  200*(sourceOverlapConstant q)^(2*B*(D+1)+2)*(initialOverlapLower q)⁻¹

def sourceWeightEnvelope (B D : ℕ) : ℝ := 144*(sourceMomentEnvelope B D)^2

theorem sourceMomentEnvelope_pos (B D : ℕ) : 0 < sourceMomentEnvelope B D := by
  unfold sourceMomentEnvelope
  positivity

theorem sourceCapEnvelope_pos (B D : ℕ) {q : ℝ} (hq : 0<q) : 0 < sourceCapEnvelope B D q := by
  unfold sourceCapEnvelope
  positivity [sourceOverlapConstant_pos hq,initialOverlapLower_pos q]

theorem sourceMomentEnvelope_expUpper (B : ℕ) : SourceExpUpper (fun D _=>sourceMomentEnvelope B D) := by
  have hr : SourcePolyUpper (fun D=>((B*D:ℕ):ℝ)) := by
    apply ((SourcePolyUpper.const (B:ℝ)).mul SourcePolyUpper.depth (fun _=>by positivity) (fun _=>by positivity)).mono
    intro D
    push_cast
    nlinarith only [Nat.cast_nonneg B (α:=ℝ)]
  have hpow := (SourceExpUpper.const 2).pow_variably (fun _ _ _=>by norm_num) hr
  have hp := ((SourcePolyUpper.const ((10^8:ℝ)*2^(10*B)*((B:ℝ)+4)*2+1)).mul
    SourcePolyUpper.depth (fun _=>by positivity) (fun _=>by positivity)).expUpper
  exact hp.mul hpow (fun _ _ _=>by positivity) (fun _ _ _=>by positivity)

theorem sourceCapEnvelope_expUpper (B : ℕ) : SourceExpUpper (sourceCapEnvelope B) := by
  have hr : SourcePolyUpper (fun D=>((2*B*(D+1)+2:ℕ):ℝ)) := by
    have hp := ((SourcePolyUpper.const ((2*B:ℕ):ℝ)).mul SourcePolyUpper.depth
      (fun _=>by positivity) (fun _=>by positivity)).add (SourcePolyUpper.const 2)
    simpa only [Nat.cast_mul,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat] using hp
  have hc := sourceOverlapConstant_expUpper.pow_variably (fun _ q hq=>(sourceOverlapConstant_pos hq.1).le) hr
  exact ((SourceExpUpper.const 200).mul hc (fun _ _ _=>by norm_num)
    (fun _ q hq=>pow_nonneg (sourceOverlapConstant_pos hq.1).le _)).mul initialOverlapLower_inverse_expUpper
    (fun _ q hq=>by positivity [sourceOverlapConstant_pos hq.1])
    (fun _ q _=>(inv_pos.mpr (initialOverlapLower_pos q)).le)

theorem sourceWeightEnvelope_expUpper (B : ℕ) : SourceExpUpper (fun D _=>sourceWeightEnvelope B D) := by
  exact (SourceExpUpper.const 144).mul
    ((sourceMomentEnvelope_expUpper B).pow (fun D _ _=>(sourceMomentEnvelope_pos B D).le) 2)
    (fun _ _ _=>by norm_num) (fun _ _ _=>sq_nonneg _)

theorem sourceMotif_expUpper (B : ℕ) (hB : 2 ≤ B) :
    SourceExpUpper (fun D _=>(2:ℝ)^(sourceCancellationOrder B D)) :=
  (SourceExpUpper.const 2).pow_variably (fun _ _ _=>by norm_num) (sourceCancellationOrder_poly B hB)

theorem sourceSmoothingPrefactor_expUpper (B : ℕ) (hB : 2 ≤ B) :
    SourceExpUpper (fun D q=>sourceSmoothingPrefactor (sourceCancellationOrder B D) (sourceCapEnvelope B D q)) := by
  let s := sourceCancellationOrder B
  have hs := sourceCancellationOrder_poly B hB
  have hs0 (D) : 0 ≤ (s D:ℝ) := Nat.cast_nonneg _
  have hp : SourcePolyUpper (fun D=>((s D*s D+s D:ℕ):ℝ)) := by
    simpa only [Nat.cast_add,Nat.cast_mul] using (hs.mul hs hs0 hs0).add hs
  have ht : SourcePolyUpper (fun D=>((s D+1:ℕ):ℝ)) := by
    simpa only [Nat.cast_add,Nat.cast_one] using hs.add (SourcePolyUpper.const 1)
  have hone := (SourceExpUpper.const 2).pow_variably (fun _ _ _=>by norm_num) hp
  have htwo := ((ht.expUpper).mul (sourceCapEnvelope_expUpper B)
    (fun _ _ _=>Nat.cast_nonneg _) (fun D _ hq=>(sourceCapEnvelope_pos B D hq.1).le)).pow_variably
      (fun D q hq=>mul_nonneg (Nat.cast_nonneg _) (sourceCapEnvelope_pos B D hq.1).le) ht
  have H := hone.mul htwo (fun _ _ _=>by positivity)
    (fun D q hq=>pow_nonneg (mul_nonneg (Nat.cast_nonneg _) (sourceCapEnvelope_pos B D hq.1).le) _)
  simpa only [sourceSmoothingPrefactor,s,Nat.cast_add,Nat.cast_one] using H

theorem sourceSkeletonPrefactor_expUpper (B b : ℕ) (hB : 2 ≤ B) :
    SourceExpUpper (fun D q=>sourceSkeletonPrefactor (sourceCancellationOrder B D) b (sourceCapEnvelope B D q)) := by
  have hL := sourceMotif_expUpper B hB
  have hK := sourceCapEnvelope_expUpper B
  have hA := ((SourceExpUpper.const 2).mul (hL.pow (fun _ _ _=>by positivity) 3)
    (fun _ _ _=>by norm_num) (fun _ _ _=>by positivity)).mul hK
      (fun _ _ _=>by positivity) (fun D _ hq=>(sourceCapEnvelope_pos B D hq.1).le)
  have hF := ((SourceExpUpper.const 4).mul (hL.pow (fun _ _ _=>by positivity) 6)
    (fun _ _ _=>by norm_num) (fun _ _ _=>by positivity)).mul
      (hK.pow (fun D _ hq=>(sourceCapEnvelope_pos B D hq.1).le) 2)
      (fun _ _ _=>by positivity) (fun _ _ _=>sq_nonneg _)
  have H := hA.mul (hF.pow (fun _ _ _=>by positivity) (2^b-1))
    (fun D q hq=>by positivity [sourceCapEnvelope_pos B D hq.1]) (fun _ _ _=>by positivity)
  simpa only [sourceSkeletonPrefactor,binaryTreeBudget_const,Nat.cast_pow,Nat.cast_ofNat] using H

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical

theorem SourceArithmeticBounds.fit_tail {C N F ε : ℝ} {s b ell k : ℕ}
    (H : SourceArithmeticBounds C N F ε s b ell k) (hC : 0<C) (hF : 0<F)
    (hN : 1≤N) (he : 0≤ε) (hκ : ∀v<b,3*ε ≤ scaleKappa b (v+1) ε) :
    sourceFitTail (sourceBlockWindows N b ε) (sourceArithmeticTrials C N b ε ell k) b ≤
      2*(b:ℝ)*N*Real.exp (-(N^ε/512)) := by
  have hN0 : 0<N := by linarith only [hN]
  apply (sourceFitTail_simple (fun j hj=>(by omega : 1≤24).trans (H.windows j hj).1)
    (fun j hj=>H.fit_exponent hC hF hN he hκ hj)).trans
  have hh := mul_le_mul_of_nonneg_left (H.leaf_bound hN0) (show 0≤2*(b:ℝ) by positivity)
  exact mul_le_mul_of_nonneg_right hh (Real.exp_pos _).le

theorem SourceArithmeticBounds.metadata_tail {C N F ε ω : ℝ} {s b ell k : ℕ}
    (H : SourceArithmeticBounds C N F ε s b ell k) (hN : 0<N) :
    sourceEffectiveHiddenTail (sourceBlockWindows N b ε) (sourceArithmeticTrials C N b ε ell k) b ω ≤
      2*(b:ℝ)*N*Real.exp (-(N^ε/(600*(C^(2*b)*F)))*ω^4/16) := by
  apply (sourceEffectiveHiddenTail_simple (fun j hj=>(by omega : 1≤24).trans (H.windows j hj).1)
    (fun j hj=>(H.trials j hj).1) ?_).trans
  · exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (H.leaf_bound hN) (show 0≤2*(b:ℝ) by positivity)) (Real.exp_pos _).le
  · intro j hj
    cases j with
    | zero => exact Or.inl rfl
    | succ j =>
      right
      rw [sourceScheduledTrials,Nat.cast_mul]
      have ht := (H.windows (j+1) hj).1
      have hd : 1 ≤ sourceBlockWindows N b ε (j+1)/4 := by omega
      have hd' : (1:ℝ) ≤ (sourceBlockWindows N b ε (j+1)/4:ℕ) := by exact_mod_cast hd
      exact (H.trials j (by omega)).1.trans
        (le_mul_of_one_le_left (Nat.cast_nonneg _) hd')

/-- Quantitative clipping without any default-limit increase or limiting
 interchange: the power is the finite even moment actually used by the oracle. -/
theorem source_clipping_moment_power (T : ℕ→ℕ) (s b k : ℕ) (N gap L : ℝ)
    (hN : 0<N)
    (hhalf : ((6*(2*k:ℕ):ℝ)*L)^2*sourceSparseCount T s b ≤ 1/2)
    (hscale : ((6*(2*k:ℕ):ℝ)*L)^2*sourceSparseCount T s b ≤ N^(-gap/2)/8) :
    Real.sqrt (6*(4*sourceCenteredBudget T s b k L)^k) ≤ 3*N^(-gap*(k:ℝ)/4) := by
  let x := ((6*(2*k:ℕ):ℝ)*L)^2*sourceSparseCount T s b
  have hx : 0≤x := by dsimp [x]; positivity
  have hden : 0<1-x := by dsimp [x]; linarith only [hhalf]
  have hc : 4*sourceCenteredBudget T s b k L ≤ N^(-gap/2) := by
    have hh : x/(1-x) ≤ 2*x := by
      apply (div_le_iff₀ hden).mpr
      have hxhalf : x≤1/2 := hhalf
      nlinarith only [mul_le_mul_of_nonneg_left hxhalf hx]
    change 4*(x/(1-x)) ≤ _
    nlinarith only [hh,hscale]
  have hc0 : 0 ≤ 4*sourceCenteredBudget T s b k L :=
    mul_nonneg (by norm_num) (sourceCenteredBudget_nonneg T s b k L (by linarith only [hhalf]))
  have hh := pow_le_pow_left₀ hc0 hc k
  have hr : (N^(-gap/2))^k=(N^(-gap*(k:ℝ)/4))^2 := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hN.le,←Real.rpow_natCast,←Real.rpow_mul hN.le]
    norm_num only [Nat.cast_ofNat]
    congr 1
    ring
  rw [hr] at hh
  apply (Real.sqrt_le_left (by positivity : 0≤3*N^(-gap*(k:ℝ)/4))).mpr
  nlinarith only [hh,sq_nonneg (N^(-gap*(k:ℝ)/4))]

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open Filter
open scoped Topology Classical

theorem SourceExpUpper.add {f g : ℕ→ℝ→ℝ} (hf : SourceExpUpper f) (hg : SourceExpUpper g) :
    SourceExpUpper (fun D q=>f D q+g D q) := by
  obtain ⟨C,hC,h,H⟩ := hf
  obtain ⟨K,hK,k,G⟩ := hg
  refine ⟨C+K+1,by positivity,h+k,?_⟩
  intro D q hq
  have hΛ := deletion_inverse_cube_ge_one ⟨hq.1,by linarith only [hq.2]⟩
  have hd : 1≤(D:ℝ)+1 := by linarith [Nat.cast_nonneg D (α:=ℝ)]
  have hh := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hd (by omega : h≤h+k)) hC) (by linarith only [hΛ] : 0≤q^(-3:ℤ))
  have hk := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hd (by omega : k≤h+k)) hK) (by linarith only [hΛ] : 0≤q^(-3:ℤ))
  have hz : 1≤((D:ℝ)+1)^(h+k)*q^(-3:ℤ) := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hd) hΛ
  have hc0 : 0≤C*((D:ℝ)+1)^(h+k)*q^(-3:ℤ) := by positivity
  have hk0 : 0≤K*((D:ℝ)+1)^(h+k)*q^(-3:ℤ) := by positivity
  have he1 : f D q ≤ Real.exp ((C+K)*((D:ℝ)+1)^(h+k)*q^(-3:ℤ)) :=
    (H D q hq).trans (Real.exp_le_exp.mpr (by nlinarith only [hh,hk0]))
  have he2 : g D q ≤ Real.exp ((C+K)*((D:ℝ)+1)^(h+k)*q^(-3:ℤ)) :=
    (G D q hq).trans (Real.exp_le_exp.mpr (by nlinarith only [hk,hc0]))
  have he := Real.add_one_le_exp (((D:ℝ)+1)^(h+k)*q^(-3:ℤ))
  have he' := mul_le_mul_of_nonneg_left (show 2≤Real.exp (((D:ℝ)+1)^(h+k)*q^(-3:ℤ)) by linarith only [he,hz])
    (Real.exp_pos ((C+K)*((D:ℝ)+1)^(h+k)*q^(-3:ℤ))).le
  rw [←Real.exp_add] at he'
  convert (show f D q+g D q ≤ Real.exp ((C+K)*((D:ℝ)+1)^(h+k)*q^(-3:ℤ)+((D:ℝ)+1)^(h+k)*q^(-3:ℤ)) by linarith only [he1,he2,he']) using 1
  congr 1
  ring

def sourceScaleInverseEnvelope (B D : ℕ) : ℝ := 2*(2:ℝ)^(B*D)

theorem sourceScaleInverseEnvelope_expUpper (B : ℕ) : SourceExpUpper (fun D _=>sourceScaleInverseEnvelope B D) := by
  have hr : SourcePolyUpper (fun D=>((B*D:ℕ):ℝ)) := by
    apply ((SourcePolyUpper.const (B:ℝ)).mul SourcePolyUpper.depth (fun _=>by positivity) (fun _=>by positivity)).mono
    intro D
    push_cast
    nlinarith only [Nat.cast_nonneg B (α:=ℝ)]
  exact (SourceExpUpper.const 2).mul ((SourceExpUpper.const 2).pow_variably (fun _ _ _=>by norm_num) hr)
    (fun _ _ _=>by norm_num) (fun _ _ _=>by positivity)

theorem source_log_scale_lower (B D i : ℕ) {n : ℝ} (hB : 2≤B) (hn : 1<n) :
    Real.log n ≤ sourceScaleInverseEnvelope B D*Real.log (sourceTargetScale B D n i) := by
  have hh := mul_le_mul_of_nonneg_right (sourceScaleProduct_lower B D i hB) (Real.log_pos hn).le
  rw [sourceTargetScale,Real.log_rpow (by linarith only [hn] : 0<n)]
  dsimp [sourceScaleInverseEnvelope]
  have hp : 0<(2:ℝ)*2^(B*D) := by positivity
  have H := mul_le_mul_of_nonneg_left hh hp.le
  field_simp at H
  nlinarith only [H]

theorem SourceExpUpper.uniform_log {f : ℕ→ℝ→ℝ} (hf : SourceExpUpper f)
    (hf0 : ∀D q,q∈Set.Ioc 0 (1/2:ℝ) → 0≤f D q)
    (B : ℕ) (ζ δ : ℝ) (hB : 2≤B) (hζ : ζ∈Set.Ioo 0 1) (hδ : 0<δ)
    {n q : ℕ→ℝ} (hn : Tendsto n atTop atTop) (hq : ∀t,q t∈Set.Ioc 0 (1/2:ℝ))
    (hH : Tendsto (fun t=>(q t)^3*Real.log (n t)) atTop atTop) :
    ∀ᶠt in atTop,∀i,f (sourceDepth B ζ ((q t)^3*Real.log (n t))) (q t)*Real.log (n t) ≤
      (sourceTargetScale B (sourceDepth B ζ ((q t)^3*Real.log (n t))) (n t) i)^
        (δ*sourceEpsilon B (sourceDepth B ζ ((q t)^3*Real.log (n t)))) := by
  let g := fun D q=>f D q*sourceScaleInverseEnvelope B D*(2/δ)*(sourceEpsilon B D)⁻¹
  have hg : SourceExpUpper g :=
    ((hf.mul (sourceScaleInverseEnvelope_expUpper B) hf0 (fun _ _ _=>by unfold sourceScaleInverseEnvelope; positivity)).mul
      (SourceExpUpper.const (2/δ)) (fun D q hq=>by unfold sourceScaleInverseEnvelope; positivity [hf0 D q hq]) (fun _ _ _=>by positivity)).mul
        (sourceEpsilon_inverse_poly B).expUpper (fun D q hq=>by unfold sourceScaleInverseEnvelope; positivity [hf0 D q hq])
          (fun D _ _=>(inv_pos.mpr (sourceEpsilon_pos B D)).le)
  have hu := SourceExpUpper.uniform g hg B ζ (δ/2) hB hζ (by positivity) hn hq hH
  filter_upwards [hu,hn.eventually_gt_atTop 1] with t ht hnt
  intro i
  let D := sourceDepth B ζ ((q t)^3*Real.log (n t))
  let N := sourceTargetScale B D (n t) i
  let ε := sourceEpsilon B D
  have he : 0<ε := sourceEpsilon_pos B D
  have hN : 0<N := Real.rpow_pos_of_pos (by linarith only [hnt]) _
  have hl := source_log_scale_lower B D i hB hnt
  have hb := Real.log_le_rpow_div hN.le (show 0<δ*ε/2 by positivity)
  have hmul := mul_le_mul_of_nonneg_left hb
    (show 0≤f D (q t)*sourceScaleInverseEnvelope B D by unfold sourceScaleInverseEnvelope; positivity [hf0 D _ (hq t)])
  have hg' := mul_le_mul_of_nonneg_right (ht i) (Real.rpow_pos_of_pos hN (δ*ε/2)).le
  have hr : N^((δ/2)*ε)*N^(δ*ε/2)=N^(δ*ε) := by rw [←Real.rpow_add hN]; congr 1; ring
  change g D (q t)*N^(δ*ε/2) ≤ N^((δ/2)*ε)*N^(δ*ε/2) at hg'
  rw [hr] at hg'
  have heq : f D (q t)*sourceScaleInverseEnvelope B D*(N^(δ*ε/2)/(δ*ε/2))=g D (q t)*N^(δ*ε/2) := by
    dsimp [g,ε]
    field_simp
  have hfirst := mul_le_mul_of_nonneg_left hl (hf0 D (q t) (hq t))
  change f D (q t)*Real.log (n t) ≤ N^(δ*ε)
  rw [heq] at hmul
  nlinarith only [hfirst,hmul,hg']

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open Filter
open scoped Topology Classical

/-- Uniform exponential domination at every working scale, with the
 full depth and the varying known deletion probability retained. -/
theorem SourceExpUpper.uniform_tail {f g h : ℕ→ℝ→ℝ}
    (hf : SourceExpUpper f) (hg : SourceExpUpper g) (hh : SourceExpUpper h)
    (hf0 : ∀D q,q∈Set.Ioc 0 (1/2:ℝ) → 0<f D q)
    (_hg0 : ∀D q,q∈Set.Ioc 0 (1/2:ℝ) → 0≤g D q)
    (hh0 : ∀D q,q∈Set.Ioc 0 (1/2:ℝ) → 0≤h D q)
    (B : ℕ) (ζ : ℝ) (hB : 2≤B) (hζ : ζ∈Set.Ioo 0 1)
    {n q : ℕ→ℝ} (hn : Tendsto n atTop atTop) (hq : ∀t,q t∈Set.Ioc 0 (1/2:ℝ))
    (hH : Tendsto (fun t=>(q t)^3*Real.log (n t)) atTop atTop) :
    ∀ᶠt in atTop,∀i,
      g (sourceDepth B ζ ((q t)^3*Real.log (n t))) (q t)*
        Real.exp (-(sourceTargetScale B (sourceDepth B ζ ((q t)^3*Real.log (n t))) (n t) i)^
          (sourceEpsilon B (sourceDepth B ζ ((q t)^3*Real.log (n t))))/
          f (sourceDepth B ζ ((q t)^3*Real.log (n t))) (q t)) ≤
      (n t)^(-(h (sourceDepth B ζ ((q t)^3*Real.log (n t))) (q t))) := by
  have hfu := SourceExpUpper.uniform f hf B ζ (1/4) hB hζ (by norm_num) hn hq hH
  have hgu := SourceExpUpper.uniform g hg B ζ (1/4) hB hζ (by norm_num) hn hq hH
  have hhu := hh.uniform_log hh0 B ζ (1/4) hB hζ (by norm_num) hn hq hH
  have hcu := SourceExpUpper.uniform _ (SourceExpUpper.const 2) B ζ (1/4) hB hζ (by norm_num) hn hq hH
  filter_upwards [hfu,hgu,hhu,hcu,hn.eventually_gt_atTop 1] with t hft hgt hht hct hnt
  intro i
  let D := sourceDepth B ζ ((q t)^3*Real.log (n t))
  let N := sourceTargetScale B D (n t) i
  let ε := sourceEpsilon B D
  let X := N^((1/4)*ε)
  have hN : 0<N := Real.rpow_pos_of_pos (by linarith only [hnt]) _
  have hx : 0<X := Real.rpow_pos_of_pos hN _
  have hfD := hf0 D (q t) (hq t)
  have hfX : f D (q t)≤X := hft i
  have hgX : g D (q t)≤X := hgt i
  have hhX : h D (q t)*Real.log (n t)≤X := hht i
  have hX2 : 2≤X := hct i
  have hpow : N^ε=X^4 := by
    dsimp [X]
    rw [←Real.rpow_natCast,←Real.rpow_mul hN.le]
    norm_num only [Nat.cast_ofNat]
    congr 1
    ring
  have hsize : 2*X*f D (q t) ≤ X^4 := by
    have h1 := mul_le_mul_of_nonneg_left hfX (show 0≤2*X by positivity)
    have h2 : 2*X^2 ≤ X^4 := by nlinarith only [hX2,sq_nonneg (X^2-2),sq_nonneg (X-2)]
    nlinarith only [h1,h2]
  have hden : 2*X ≤ N^ε/f D (q t) := (le_div_iff₀ hfD).mpr (by rw [hpow]; exact hsize)
  have hexp : Real.exp (g D (q t)-N^ε/f D (q t)) ≤ (n t)^(-h D (q t)) := by
    rw [Real.rpow_def_of_pos (by linarith only [hnt] : 0<n t)]
    exact Real.exp_le_exp.mpr (by nlinarith only [hden,hgX,hhX])
  apply le_trans _ hexp
  rw [Real.exp_sub]
  have he := mul_le_mul_of_nonneg_right
    (show g D (q t) ≤ Real.exp (g D (q t)) by linarith only [Real.add_one_le_exp (g D (q t))])
    (Real.exp_pos (-N^ε/f D (q t))).le
  have hnexp : -N^ε/f D (q t) = -(N^ε/f D (q t)) := by ring
  rw [hnexp, Real.exp_neg] at he
  change g D (q t)*Real.exp (-N^ε/f D (q t)) ≤ _
  rw [hnexp, Real.exp_neg]
  simpa only [div_eq_mul_inv] using he

end TraceReconstruction

end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
