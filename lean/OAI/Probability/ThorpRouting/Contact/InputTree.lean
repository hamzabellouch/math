import Mathlib
import OAI.Probability.ThorpRouting.Contact.HeightDecay

namespace OAI

namespace ThorpNine.Contact

namespace Thorp

lemma centralDistance_exceptional (L r : ℕ) (C D : Card r → Equiv.Perm (Card L))
    (E : Finset (Card r)) (h : ∀ u ∉ E, C u = D u) :
    centralDistance L r C D ≤ E.card*2^L := by
  classical
  calc
    _ ≤ ∑ u : Card r, if u ∈ E then 2^L else 0 := by
      apply Finset.sum_le_sum
      intro u _
      split_ifs with hu
      · simpa only [card_positions] using permDistance_le (C u) (D u)
      · rw [h u hu,permDistance_refl]
    _ = _ := by simp


inductive InputTree : ℕ → Type
  | tip {d : ℕ} (p : Equiv.Perm (Card d)) : InputTree d
  | node {d : ℕ} (ξ : Card d → Bool) (T : Bool → InputTree d) : InputTree (d+1)

def InputTree.perm : {d : ℕ} → InputTree d → Equiv.Perm (Card d)
  | _, .tip p => p
  | _, .node ξ T => pairSwitch ξ * childLift (fun b => (T b).perm)

noncomputable def InputTree.levelCost (t : ℕ) : {d : ℕ} → InputTree d →
    {ι : Type*} → [Fintype ι] → (ι ↪ Card d) → (SwitchIndex d → Bool) → ℕ
  | _, .tip _, _, _, _, _ => 0
  | d+1, .node ξ T, _, _, e, Y =>
    let x := e.trans (headTailEquiv d).toEmbedding
    let c := PairRouting.colors x ξ
    let hc := PairRouting.colors_compatible x ξ
    let σ := coinStepEquiv d Y
    if t = d+1 then PairRouting.alternatingCycles (PairRouting.switchedEmbedding x ξ)
      (fun b => if b then butterflyPerm d (decodeButterfly d σ.1.2) * (T true).perm⁻¹
        else butterflyPerm d (decodeButterfly d σ.1.1) * (T false).perm⁻¹)
    else (T false).levelCost t (PairRouting.childEmbedding x c hc false) σ.1.1 +
      (T true).levelCost t (PairRouting.childEmbedding x c hc true) σ.1.2

lemma InputTree.levelCost_node (t d : ℕ) (ξ : Card d → Bool) (T : Bool → InputTree d)
    {ι : Type*} [Fintype ι] (e : ι ↪ Card (d+1))
    (Y : (SwitchIndex d → Bool) × (SwitchIndex d → Bool)) (η : Card d → Bool) :
    (InputTree.node ξ T).levelCost t e ((coinStepEquiv d).symm (Y,η)) =
      let x := e.trans (headTailEquiv d).toEmbedding
      let c := PairRouting.colors x ξ
      let hc := PairRouting.colors_compatible x ξ
      if t = d+1 then PairRouting.alternatingCycles (PairRouting.switchedEmbedding x ξ)
        (fun b => if b then butterflyPerm d (decodeButterfly d Y.2) * (T true).perm⁻¹
          else butterflyPerm d (decodeButterfly d Y.1) * (T false).perm⁻¹)
      else (T false).levelCost t (PairRouting.childEmbedding x c hc false) Y.1 +
        (T true).levelCost t (PairRouting.childEmbedding x c hc true) Y.2 := by
  rw [InputTree.levelCost]
  rfl

lemma InputTree.levelCost_gt (t d : ℕ) (T : InputTree d) (ht : d < t)
    {ι : Type*} [Fintype ι] (e : ι ↪ Card d) (Y : SwitchIndex d → Bool) :
    T.levelCost t e Y = 0 := by
  induction T generalizing ι with
  | tip p => rfl
  | @node d ξ T ih =>
    rw [InputTree.levelCost,ite_eq_right (by omega : t ≠ d+1),ih false (by omega),ih true (by omega)]

lemma InputTree.levelCost_adapted (t d : ℕ) (T : InputTree d)
    {ι : Type*} [Fintype ι] (e : ι ↪ Card d) :
    LayerAdapted d (t-1) (fun Y => T.levelCost t e Y) := by
  induction T generalizing ι with
  | tip p => intro Y Y' _; rfl
  | @node d ξ T ih =>
    intro Y Y' h
    dsimp only
    conv_lhs => rw [←(coinStepEquiv d).symm_apply_apply Y]
    conv_rhs => rw [←(coinStepEquiv d).symm_apply_apply Y']
    rw [InputTree.levelCost_node t d ξ T e ((coinStepEquiv d Y).1) ((coinStepEquiv d Y).2),
      InputTree.levelCost_node t d ξ T e ((coinStepEquiv d Y').1) ((coinStepEquiv d Y').2)]
    by_cases ht : t = d+1
    · subst t
      rw [ite_eq_left rfl,ite_eq_left rfl]
      have he₀ : (coinStepEquiv d Y).1.1 = (coinStepEquiv d Y').1.1 := by
        funext i
        exact h (Sum.inr (false,i)) (by simpa only [switchHeight,Nat.add_sub_cancel] using switchHeight_le d i)
      have he₁ : (coinStepEquiv d Y).1.2 = (coinStepEquiv d Y').1.2 := by
        funext i
        exact h (Sum.inr (true,i)) (by simpa only [switchHeight,Nat.add_sub_cancel] using switchHeight_le d i)
      rw [he₀,he₁]
    · rw [ite_eq_right ht,ite_eq_right ht]
      congr 1
      · apply ih false
        intro i hi
        exact h (Sum.inr (false,i)) hi
      · apply ih true
        intro i hi
        exact h (Sum.inr (true,i)) hi

theorem InputTree.level_partial_mgf (r s u : ℕ) (hu : u < r)
    (T : InputTree (s+r)) {ι : Type*} [Fintype ι] (e : ι ↪ Card (s+r))
    (lo : Card r × SwitchIndex s → Bool) (J : ℕ) (hJ : 0 < J) (q : ℝ) (hq : 1 ≤ q) :
    finiteMean (fun hi : Card s × SwitchIndex r → Bool =>
      q^(T.levelCost (s+u+1) e (assembleBits r s lo hi))) ≤
      Real.exp (Fintype.card ι * cycleCoefficient u J q) := by
  classical
  induction r generalizing u ι with
  | zero => omega
  | succ r ih =>
    simp only [Nat.add_succ] at *
    cases T with
    | tip p =>
      simp only [InputTree.levelCost,pow_zero,finiteMean_const]
      exact Real.one_le_exp (mul_nonneg (Nat.cast_nonneg _) (cycleCoefficient_nonneg u J q hq))
    | node ξ T =>
      let x := e.trans (headTailEquiv (s+r)).toEmbedding
      let c := PairRouting.colors x ξ
      let hc := PairRouting.colors_compatible x ξ
      let e₀ := PairRouting.childEmbedding x c hc false
      let e₁ := PairRouting.childEmbedding x c hc true
      let e' := PairRouting.switchedEmbedding x ξ
      let lo₀ : Card r × SwitchIndex s → Bool := fun j => lo (Fin.cons false j.1,j.2)
      let lo₁ : Card r × SwitchIndex s → Bool := fun j => lo (Fin.cons true j.1,j.2)
      let Y₀ := fun hi : Card s × SwitchIndex r → Bool => assembleBits r s lo₀ hi
      let Y₁ := fun hi : Card s × SwitchIndex r → Bool => assembleBits r s lo₁ hi
      let N := fun hi : (Card s × SwitchIndex r → Bool) × (Card s × SwitchIndex r → Bool) =>
        PairRouting.alternatingCycles e' (fun b =>
          if b then butterflyPerm (s+r) (decodeButterfly (s+r) (Y₁ hi.2)) * (T true).perm⁻¹
          else butterflyPerm (s+r) (decodeButterfly (s+r) (Y₀ hi.1)) * (T false).perm⁻¹)
      let L₀ := fun hi : Card s × SwitchIndex r → Bool =>
        (T false).levelCost (s+u+1) e₀ (Y₀ hi)
      let L₁ := fun hi : Card s × SwitchIndex r → Bool =>
        (T true).levelCost (s+u+1) e₁ (Y₁ hi)
      have hs (hi : (Card s × SwitchIndex r → Bool) × (Card s × SwitchIndex r → Bool))
          (η : Card s × Card r → Bool) :
          (InputTree.node ξ T).levelCost (s+u+1) e
            (assembleBits (r+1) s lo ((highStepEquiv r s).symm (hi,η))) =
            if u = r then N hi else L₀ hi.1 + L₁ hi.2 := by
        rw [assembleBits_step]
        rw [InputTree.levelCost_node (s+u+1) (s+r) ξ T e (Y₀ hi.1,Y₁ hi.2) (fun y => η (((cardSplit r s) y).2,((cardSplit r s) y).1))]
        simp only [Nat.add_right_cancel_iff,Nat.add_left_cancel_iff]
        rfl
      rw [finiteMean_equiv (highStepEquiv r s),finiteMean_prod]
      simp_rw [hs,finiteMean_const]
      by_cases hur : u = r
      · subst u
        simp only [ite_true]
        rw [finiteMean_prod,finiteMean_comm]
        calc
          _ ≤ finiteMean (fun _hi : Card s × SwitchIndex r → Bool =>
            Real.exp (Fintype.card ι * cycleCoefficient r J q)) := by
            apply finiteMean_mono
            intro hi
            have hn := node_partial_mgf r s e' (T false).perm (T true).perm
              (butterflyPerm (s+r) (decodeButterfly (s+r) (Y₁ hi))) lo₀ J hJ q hq
            exact hn
          _ = _ := finiteMean_const _
      · simp only [ite_eq_right hur,pow_add]
        rw [finiteMean_prod_mul (fun hi => q ^ L₀ hi) (fun hi => q ^ L₁ hi)]
        have hu' : u < r := by omega
        have h₀ := ih u hu' (T false) e₀ lo₀
        have h₁ := ih u hu' (T true) e₁ lo₁
        have hp := mul_le_mul h₀ h₁ (finiteMean_nonneg (fun _ => pow_nonneg (by linarith) _))
          (Real.exp_nonneg _)
        refine hp.trans_eq ?_
        rw [←Real.exp_add]
        congr 1
        have hcount := PairRouting.color_card_add c
        have hcount' : (Fintype.card {i : ι // c i = false} : ℝ) +
            Fintype.card {i : ι // c i = true} = Fintype.card ι := by exact_mod_cast hcount
        change (Fintype.card {i : ι // c i = false} : ℝ) * cycleCoefficient u J q +
            Fintype.card {i : ι // c i = true} * cycleCoefficient u J q = _
        rw [←add_mul,hcount']


noncomputable def InputTree.slabCost (l d : ℕ) (T : InputTree d) {ι : Type*} [Fintype ι]
    (e : ι ↪ Card d) (Y : SwitchIndex d → Bool) : ℕ :=
  ∑ i : Fin l, T.levelCost (l+i.1+1) e Y

lemma InputTree.slabCost_adapted (l d : ℕ) (T : InputTree d) {ι : Type*} [Fintype ι]
    (e : ι ↪ Card d) :
    LayerAdapted d (2*l) (fun Y => InputTree.slabCost l d T e Y) := by
  apply layerAdapted_sum
  intro i _
  exact layerAdapted_mono (InputTree.levelCost_adapted (l+i.1+1) d T e) (by omega)

theorem InputTree.slab_partial_mgf (r s l : ℕ) (hl : 0 < l) (hs : 2*s ≤ l) (T : InputTree (s+r))
    {ι : Type*} [Fintype ι] (e : ι ↪ Card (s+r))
    (lo : Card r × SwitchIndex s → Bool) (q : ℝ) (hq : 1 ≤ q)
    (hlog : Real.log q ≤ 1/250) :
    finiteMean (fun hi : Card s × SwitchIndex r → Bool =>
      q^(InputTree.slabCost l (s+r) T e (assembleBits r s lo hi))) ≤
      Real.exp (Fintype.card ι * (68*Real.exp (-(l:ℝ)/64))) := by
  classical
  let : NeZero l := ⟨ne_of_gt hl⟩
  have hqp : 0 < q := lt_of_lt_of_le (by norm_num) hq
  calc
    _ ≤ finiteMean (fun hi : Card s × SwitchIndex r → Bool =>
      finiteMean (fun i : Fin l => q^(l*T.levelCost (l+i.1+1) e
        (assembleBits r s lo hi)))) := by
      apply finiteMean_mono
      intro hi
      simpa only [InputTree.slabCost,Fintype.card_fin] using
        pow_sum_le_mean_powers (fun i : Fin l => T.levelCost (l+i.1+1) e
          (assembleBits r s lo hi)) q hqp
    _ = finiteMean (fun i : Fin l => finiteMean (fun hi : Card s × SwitchIndex r → Bool =>
      q^(l*T.levelCost (l+i.1+1) e (assembleBits r s lo hi)))) := finiteMean_comm _
    _ ≤ finiteMean (fun _i : Fin l =>
      Real.exp (Fintype.card ι * (68*Real.exp (-(l:ℝ)/64)))) := by
      apply finiteMean_mono
      intro i
      by_cases ht : l+i.1+1 ≤ s+r
      · have hs' : s ≤ l+i.1 := by omega
        have he : l+i.1+1 = s+(l+i.1-s)+1 := by omega
        have hu : l+i.1-s < r := by omega
        have hm := InputTree.level_partial_mgf r s (l+i.1-s) hu T e lo
          ⌈Real.exp ((l:ℝ)/32)⌉₊ (cycleCutoff_pos l) (q^l) (one_le_pow₀ hq)
        have hc := cycleCoefficient_decay l (l+i.1-s) (by
          rw [Nat.cast_sub hs',Nat.cast_add]
          have hsr : (2:ℝ)*s ≤ l := by exact_mod_cast hs
          have hi : (0:ℝ) ≤ i.1 := Nat.cast_nonneg _
          linarith) (q^l) (one_le_pow₀ hq) (by
            rw [Real.log_pow]
            nlinarith [mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg l)])
        simp_rw [he,pow_mul]
        exact hm.trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hc (Nat.cast_nonneg _)))
      · have hz := InputTree.levelCost_gt (l+i.1+1) (s+r) T (by omega) e
        simp only [hz,Nat.mul_zero,pow_zero,finiteMean_const]
        exact Real.one_le_exp_iff.mpr (by positivity)
    _ = _ := finiteMean_const _


def boundaryTree (L : ℕ) : (r : ℕ) → (Card r → Equiv.Perm (Card L)) →
    (SwitchIndex (L+r) → Bool) → InputTree (L+r)
  | 0, U, _ => .tip (U (fun j => Fin.elim0 j))
  | r+1, U, X => .node (coinStepEquiv (L+r) X).2 (fun b =>
      boundaryTree L r (fun u => U (Fin.cons b u))
        (if b then (coinStepEquiv (L+r) X).1.2 else (coinStepEquiv (L+r) X).1.1))

def boundaryOutput (L : ℕ) : (r : ℕ) → (SwitchIndex (L+r) → Bool) →
    Card r → Equiv.Perm (Card L)
  | 0, Y, _ => butterflyPerm L (decodeButterfly L Y)
  | r+1, Y, u => boundaryOutput L r
      (if u 0 then (coinStepEquiv (L+r) Y).1.2 else (coinStepEquiv (L+r) Y).1.1) (Fin.tail u)

lemma boundaryOutput_adapted (L r : ℕ) :
    LayerAdapted (L+r) L (boundaryOutput L r) := by
  induction r with
  | zero =>
    intro Y Y' h
    have he : Y = Y' := funext (fun i => h i (by simpa only [Nat.add_zero] using switchHeight_le L i))
    rw [he]
  | succ r ih =>
    intro Y Y' h
    funext u
    dsimp only [boundaryOutput]
    cases hb : u 0 <;> simp only [Bool.false_eq_true,↓reduceIte]
    · exact congrFun (ih _ _ (fun i hi => h (Sum.inr (false,i)) hi)) (Fin.tail u)
    · exact congrFun (ih _ _ (fun i hi => h (Sum.inr (true,i)) hi)) (Fin.tail u)

noncomputable def modifiedBoundary (L r : ℕ) (E : Finset (Card r))
    (U : Card r → Equiv.Perm (Card L)) (Y : SwitchIndex (L+r) → Bool) :
    Card r → Equiv.Perm (Card L) := fun u => if u ∈ E then boundaryOutput L r Y u else U u

lemma modifiedBoundary_adapted (L r : ℕ) (E : Finset (Card r))
    (U : Card r → Equiv.Perm (Card L)) :
    LayerAdapted (L+r) L (modifiedBoundary L r E U) := by
  intro Y Y' h
  unfold modifiedBoundary
  rw [boundaryOutput_adapted L r Y Y' h]

lemma permDistance_boundaryTree (L r : ℕ) (U V : Card r → Equiv.Perm (Card L))
    (X : SwitchIndex (L+r) → Bool) :
    permDistance (boundaryTree L r U X).perm (boundaryTree L r V X).perm =
      centralDistance L r U V := by
  induction r with
  | zero =>
    simp only [boundaryTree,InputTree.perm,centralDistance,Fintype.sum_unique]
    congr 1
  | succ r ih =>
    simp only [boundaryTree,InputTree.perm,permDistance_mul_left]
    rw [permDistance_childLift,centralDistance_step,ih,ih]

lemma boundaryTree_levelCost_perturb (t L r : ℕ) (U V : Card r → Equiv.Perm (Card L))
    (X : SwitchIndex (L+r) → Bool) {ι : Type*} [Fintype ι]
    (e : ι ↪ Card (L+r)) (Y : SwitchIndex (L+r) → Bool) :
    (boundaryTree L r U X).levelCost t e Y ≤
      (boundaryTree L r V X).levelCost t e Y + centralDistance L r U V := by
  induction r generalizing ι with
  | zero => simp only [boundaryTree,InputTree.levelCost,Nat.zero_add,Nat.zero_le]
  | succ r ih =>
    rw [boundaryTree,boundaryTree,InputTree.levelCost,InputTree.levelCost]
    by_cases ht : t = L+r+1
    · simp only [ite_eq_left ht]
      have hh := alternatingCycles_distance_le
        (PairRouting.switchedEmbedding (e.trans (headTailEquiv (L+r)).toEmbedding)
          (coinStepEquiv (L+r) X).2)
        (fun b => if b then butterflyPerm (L+r) (decodeButterfly (L+r) (coinStepEquiv (L+r) Y).1.2) *
            (boundaryTree L r (fun u => U (Fin.cons true u)) (coinStepEquiv (L+r) X).1.2).perm⁻¹
          else butterflyPerm (L+r) (decodeButterfly (L+r) (coinStepEquiv (L+r) Y).1.1) *
            (boundaryTree L r (fun u => U (Fin.cons false u)) (coinStepEquiv (L+r) X).1.1).perm⁻¹)
        (fun b => if b then butterflyPerm (L+r) (decodeButterfly (L+r) (coinStepEquiv (L+r) Y).1.2) *
            (boundaryTree L r (fun u => V (Fin.cons true u)) (coinStepEquiv (L+r) X).1.2).perm⁻¹
          else butterflyPerm (L+r) (decodeButterfly (L+r) (coinStepEquiv (L+r) Y).1.1) *
            (boundaryTree L r (fun u => V (Fin.cons false u)) (coinStepEquiv (L+r) X).1.1).perm⁻¹)
      simpa only [Bool.false_eq_true,↓reduceIte,permDistance_mul_left,permDistance_inv,
        permDistance_boundaryTree,←centralDistance_step] using hh
    · simp only [ite_eq_right ht,Bool.false_eq_true,↓reduceIte]
      rw [centralDistance_step]
      have h₀ := ih (fun u => U (Fin.cons false u)) (fun u => V (Fin.cons false u))
        (coinStepEquiv (L+r) X).1.1
        (PairRouting.childEmbedding (e.trans (headTailEquiv (L+r)).toEmbedding)
          (PairRouting.colors (e.trans (headTailEquiv (L+r)).toEmbedding) (coinStepEquiv (L+r) X).2)
          (PairRouting.colors_compatible _ _) false) (coinStepEquiv (L+r) Y).1.1
      have h₁ := ih (fun u => U (Fin.cons true u)) (fun u => V (Fin.cons true u))
        (coinStepEquiv (L+r) X).1.2
        (PairRouting.childEmbedding (e.trans (headTailEquiv (L+r)).toEmbedding)
          (PairRouting.colors (e.trans (headTailEquiv (L+r)).toEmbedding) (coinStepEquiv (L+r) X).2)
          (PairRouting.colors_compatible _ _) true) (coinStepEquiv (L+r) Y).1.2
      omega

lemma boundaryTree_slabCost_perturb (l L r : ℕ) (U V : Card r → Equiv.Perm (Card L))
    (X : SwitchIndex (L+r) → Bool) {ι : Type*} [Fintype ι]
    (e : ι ↪ Card (L+r)) (Y : SwitchIndex (L+r) → Bool) :
    InputTree.slabCost l (L+r) (boundaryTree L r U X) e Y ≤
      InputTree.slabCost l (L+r) (boundaryTree L r V X) e Y + l*centralDistance L r U V := by
  have hh := Finset.sum_le_sum (fun (i : Fin l) (_ : i ∈ Finset.univ) =>
    boundaryTree_levelCost_perturb (l+i.val+1) L r U V X e Y)
  simpa only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
    nsmul_eq_mul,Nat.cast_id,InputTree.slabCost] using hh

lemma modifiedBoundary_distance_le (L r : ℕ) (E : Finset (Card r))
    (U : Card r → Equiv.Perm (Card L)) (Y : SwitchIndex (L+r) → Bool) :
    centralDistance L r (modifiedBoundary L r E U Y) U ≤ E.card*2^L := by
  apply centralDistance_exceptional
  intro u hu
  exact ite_eq_right hu


lemma InputTree.slabCost_gt (l d : ℕ) (T : InputTree d) (hd : d ≤ l)
    {ι : Type*} [Fintype ι] (e : ι ↪ Card d) (Y : SwitchIndex d → Bool) :
    InputTree.slabCost l d T e Y = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  exact InputTree.levelCost_gt _ _ T (by omega) _ _

lemma InputTree.random_slab_adapted_mul_le (d s l : ℕ) (hsd : s ≤ d) (hl : 0 < l)
    (hs : 2*s ≤ l) (T : (SwitchIndex d → Bool) → InputTree d)
    (hT : LayerAdapted d s T) {ι : Type*} [Fintype ι] (e : ι ↪ Card d)
    (F : (SwitchIndex d → Bool) → ℝ) (hF : ∀ Y, 0 ≤ F Y) (hA : LayerAdapted d s F)
    (q : ℝ) (hq : 1 ≤ q) (hlog : Real.log q ≤ 1/250) :
    finiteMean (fun Y => F Y*q^(InputTree.slabCost l d (T Y) e Y)) ≤
      finiteMean F * Real.exp (Fintype.card ι * (68*Real.exp (-(l:ℝ)/64))) := by
  obtain ⟨r,rfl⟩ := Nat.exists_eq_add_of_le hsd
  apply adapted_mul_mean_le r s F _ hF hA
  intro lo
  let hi₀ : Card s × SwitchIndex r → Bool := fun _ => false
  have he (hi : Card s × SwitchIndex r → Bool) :
      T (assembleBits r s lo hi) = T (assembleBits r s lo hi₀) :=
    hT _ _ (assembleBits_agree r s lo hi hi₀)
  simp_rw [he]
  exact InputTree.slab_partial_mgf r s l hl hs _ e lo q hq hlog

lemma InputTree.slab_mgf (l d : ℕ) (hl : 0 < l) (T : InputTree d)
    {ι : Type*} [Fintype ι] (e : ι ↪ Card d) (q : ℝ) (hq : 1 ≤ q)
    (hlog : Real.log q ≤ 1/250) :
    finiteMean (fun Y => q^(InputTree.slabCost l d T e Y)) ≤
      Real.exp (Fintype.card ι * (68*Real.exp (-(l:ℝ)/64))) := by
  have hh := InputTree.random_slab_adapted_mul_le d 0 l (Nat.zero_le _) hl (Nat.zero_le _)
    (fun _ => T) (fun _ _ _ => rfl) e (fun _ => 1) (fun _ => by norm_num)
    (fun _ _ _ => rfl) q hq hlog
  simpa only [one_mul,finiteMean_const] using hh

noncomputable def InputTree.familyCost (L n d : ℕ)
    (T : (SwitchIndex d → Bool) → InputTree d) {ι : Type*} [Fintype ι]
    (e : ι ↪ Card d) (Y : SwitchIndex d → Bool) : ℕ :=
  ∑ j ∈ Finset.range n, InputTree.slabCost (L*4^j) d (T Y) e Y

lemma InputTree.random_slabCost_adapted (l d s : ℕ) (T : (SwitchIndex d → Bool) → InputTree d)
    (hT : LayerAdapted d s T) {ι : Type*} [Fintype ι] (e : ι ↪ Card d) :
    LayerAdapted d (max s (2*l)) (fun Y => InputTree.slabCost l d (T Y) e Y) := by
  intro Y Y' h
  dsimp only
  rw [hT _ _ (agreeThrough_mono (le_max_left _ _) h)]
  exact InputTree.slabCost_adapted l d (T Y') e Y Y'
    (agreeThrough_mono (le_max_right _ _) h)

lemma InputTree.familyCost_adapted (L n d s : ℕ) (T : (SwitchIndex d → Bool) → InputTree d)
    (hT : LayerAdapted d s T) {ι : Type*} [Fintype ι] (e : ι ↪ Card d) :
    LayerAdapted d (max s (familyEnd L n)) (fun Y => InputTree.familyCost L n d T e Y) := by
  apply layerAdapted_sum
  intro j hj
  exact layerAdapted_mono (InputTree.random_slabCost_adapted (L*4^j) d s T hT e)
    (max_le_max_left s (familyEnd_ge L n j (Finset.mem_range.mp hj)))

theorem InputTree.family_mgf_first (L n d s : ℕ) (hL : 0 < L) (hs : s ≤ L)
    (T : (SwitchIndex d → Bool) → InputTree d) (hT : LayerAdapted d s T)
    {ι : Type*} [Fintype ι] (e : ι ↪ Card d) (q : ℝ) (hq : 1 ≤ q)
    (hlog : Real.log q ≤ 1/250) (p : ℝ) (hp : 0 ≤ p)
    (hfirst : finiteMean (fun Y => q^(InputTree.slabCost L d (T Y) e Y)) ≤
      Real.exp (p+Fintype.card ι*(68*Real.exp (-(L:ℝ)/64)))) :
    finiteMean (fun Y => q^(InputTree.familyCost L n d T e Y)) ≤
      Real.exp (p+Fintype.card ι*(68*∑ j ∈ Finset.range n,
        Real.exp (-((L*4^j:ℕ):ℝ)/64))) := by
  induction n with
  | zero =>
    simp only [InputTree.familyCost,Finset.range_zero,Finset.sum_empty,pow_zero,
      finiteMean_const,mul_zero,add_zero]
    exact Real.one_le_exp hp
  | succ n ih =>
    by_cases hn : n = 0
    · subst n
      simpa only [InputTree.familyCost,Nat.zero_add,Finset.sum_range_one,pow_zero,mul_one] using hfirst
    · let l := L*4^n
      have hl : 0 < l := Nat.mul_pos hL (pow_pos (by decide) _)
      have hsl : 2*familyEnd L n ≤ l := familyEnd_two L n
      have hs' : s ≤ familyEnd L n := by
        have hh := familyEnd_ge L n 0 (Nat.pos_of_ne_zero hn)
        simp only [pow_zero,mul_one] at hh
        omega
      have hc : ∀ Y, InputTree.familyCost L (n+1) d T e Y =
          InputTree.familyCost L n d T e Y+InputTree.slabCost l d (T Y) e Y := by
        intro Y
        exact Finset.sum_range_succ _ _
      have hm : finiteMean (fun Y => q^(InputTree.familyCost L (n+1) d T e Y)) ≤
          finiteMean (fun Y => q^(InputTree.familyCost L n d T e Y)) *
            Real.exp (Fintype.card ι*(68*Real.exp (-(l:ℝ)/64))) := by
        by_cases hld : l ≤ d
        · simp_rw [hc,pow_add]
          apply InputTree.random_slab_adapted_mul_le d (familyEnd L n) l (by omega) hl hsl T
            (layerAdapted_mono hT hs') e _ (fun _ => pow_nonneg (by linarith) _)
          · apply layerAdapted_comp
            exact layerAdapted_mono (InputTree.familyCost_adapted L n d s T hT e) (max_le hs' le_rfl)
          · exact hq
          · exact hlog
        · simp_rw [hc,InputTree.slabCost_gt l d _ (by omega),Nat.add_zero]
          exact le_mul_of_one_le_right
            (finiteMean_nonneg (fun _ => pow_nonneg (by linarith) _))
            (Real.one_le_exp_iff.mpr (by positivity))
      refine (hm.trans (mul_le_mul_of_nonneg_right ih (Real.exp_nonneg _))).trans_eq ?_
      rw [←Real.exp_add,Finset.sum_range_succ]
      congr 1
      dsimp only [l]
      ring

lemma InputTree.family_mgf_first_decay (L n d s : ℕ) (hL : 0 < L) (hs : s ≤ L)
    (T : (SwitchIndex d → Bool) → InputTree d) (hT : LayerAdapted d s T)
    {ι : Type*} [Fintype ι] (e : ι ↪ Card d) (q : ℝ) (hq : 1 ≤ q)
    (hlog : Real.log q ≤ 1/250) (p : ℝ) (hp : 0 ≤ p)
    (hfirst : finiteMean (fun Y => q^(InputTree.slabCost L d (T Y) e Y)) ≤
      Real.exp (p+Fintype.card ι*(68*Real.exp (-(L:ℝ)/64)))) :
    finiteMean (fun Y => q^(InputTree.familyCost L n d T e Y)) ≤
      Real.exp (p+Fintype.card ι*heightDecay L) := by
  apply (InputTree.family_mgf_first L n d s hL hs T hT e q hq hlog p hp hfirst).trans
  apply Real.exp_le_exp.mpr
  apply add_le_add_right
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  have hh := mul_le_mul_of_nonneg_left (sum_family_decay L n hL) (by norm_num : (0:ℝ)≤68)
  simpa only [heightDecay,mul_div_assoc] using hh


noncomputable def modifiedInputTree (L r : ℕ) (E : Finset (Card r))
    (U : Card r → Equiv.Perm (Card L)) (X Y : SwitchIndex (L+r) → Bool) : InputTree (L+r) :=
  boundaryTree L r (modifiedBoundary L r E U Y) X

lemma modifiedInputTree_adapted (L r : ℕ) (E : Finset (Card r))
    (U : Card r → Equiv.Perm (Card L)) (X : SwitchIndex (L+r) → Bool) :
    LayerAdapted (L+r) L (modifiedInputTree L r E U X) := by
  intro Y Y' h
  unfold modifiedInputTree
  rw [modifiedBoundary_adapted L r E U Y Y' h]

lemma modified_slab_mgf (l L r : ℕ) (hl : 0 < l) (E : Finset (Card r))
    (U : Card r → Equiv.Perm (Card L)) (X : SwitchIndex (L+r) → Bool)
    {ι : Type*} [Fintype ι] (e : ι ↪ Card (L+r)) (q : ℝ) (hq : 1 ≤ q)
    (hlog : Real.log q ≤ 1/250) :
    finiteMean (fun Y => q^(InputTree.slabCost l (L+r) (modifiedInputTree L r E U X Y) e Y)) ≤
      Real.exp (((l*E.card*2^L:ℕ):ℝ)*Real.log q+
        Fintype.card ι*(68*Real.exp (-(l:ℝ)/64))) := by
  have hqp : 0 < q := by linarith
  have hpoint (Y : SwitchIndex (L+r) → Bool) :
      InputTree.slabCost l (L+r) (modifiedInputTree L r E U X Y) e Y ≤
        InputTree.slabCost l (L+r) (boundaryTree L r U X) e Y+l*E.card*2^L := by
    apply (boundaryTree_slabCost_perturb l L r (modifiedBoundary L r E U Y) U X e Y).trans
    apply Nat.add_le_add_left
    simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left l (modifiedBoundary_distance_le L r E U Y)
  calc
    _ ≤ finiteMean (fun Y => q^(InputTree.slabCost l (L+r) (boundaryTree L r U X) e Y+l*E.card*2^L)) :=
      finiteMean_mono (fun Y => pow_le_pow_right₀ hq (hpoint Y))
    _ = finiteMean (fun Y => q^(InputTree.slabCost l (L+r) (boundaryTree L r U X) e Y)) *
        q^(l*E.card*2^L) := by simp_rw [pow_add]; exact finiteMean_mul_const _ _
    _ ≤ Real.exp (Fintype.card ι*(68*Real.exp (-(l:ℝ)/64))) * q^(l*E.card*2^L) :=
      mul_le_mul_of_nonneg_right (InputTree.slab_mgf l (L+r) hl _ e q hq hlog) (pow_nonneg (by linarith) _)
    _ = _ := by
      have he : Real.exp (((l*E.card*2^L:ℕ):ℝ)*Real.log q) = q^(l*E.card*2^L) := by
        rw [Real.exp_nat_mul,Real.exp_log hqp]
      rw [Real.exp_add,he,mul_comm]

lemma modified_family_mgf (l n L r : ℕ) (hl : 0 < l) (hLl : L ≤ l) (E : Finset (Card r))
    (U : Card r → Equiv.Perm (Card L)) (X : SwitchIndex (L+r) → Bool)
    {ι : Type*} [Fintype ι] (e : ι ↪ Card (L+r)) (q : ℝ) (hq : 1 ≤ q)
    (hlog : Real.log q ≤ 1/250) :
    finiteMean (fun Y => q^(InputTree.familyCost l n (L+r) (modifiedInputTree L r E U X) e Y)) ≤
      Real.exp (((l*E.card*2^L:ℕ):ℝ)*Real.log q+Fintype.card ι*heightDecay l) := by
  exact InputTree.family_mgf_first_decay l n (L+r) L hl hLl _
    (modifiedInputTree_adapted L r E U X) e q hq hlog _
    (mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg hq))
    (modified_slab_mgf l L r hl E U X e q hq hlog)

theorem modified_high_mgf (L n r : ℕ) (hL : 0 < L) (E : Finset (Card r))
    (U : Card r → Equiv.Perm (Card L)) (X : SwitchIndex (L+r) → Bool)
    {ι : Type*} [Fintype ι] (e : ι ↪ Card (L+r)) (q : ℝ) (hq : 1 ≤ q)
    (hlog : Real.log q ≤ 1/500) :
    finiteMean (fun Y => q^(InputTree.familyCost L n (L+r) (modifiedInputTree L r E U X) e Y+
      InputTree.familyCost (2*L) n (L+r) (modifiedInputTree L r E U X) e Y)) ≤
      Real.exp (Fintype.card ι*heightDecay L +
        3*((L*E.card*2^L:ℕ):ℝ)*Real.log q) := by
  have hq2 := one_le_pow₀ (n:=2) hq
  have hlog2 : Real.log (q^2) ≤ 1/250 := by rw [Real.log_pow]; norm_num; linarith
  have h₀ := modified_family_mgf L n L r hL le_rfl E U X e (q^2) hq2 hlog2
  have h₁ := modified_family_mgf (2*L) n L r (by omega) (by omega) E U X e (q^2) hq2 hlog2
  have h₁' : finiteMean (fun Y => (q^2)^(InputTree.familyCost (2*L) n (L+r)
      (modifiedInputTree L r E U X) e Y)) ≤
      Real.exp ((((2*L)*E.card*2^L:ℕ):ℝ)*Real.log (q^2)+Fintype.card ι*heightDecay L) := by
    apply h₁.trans
    apply Real.exp_le_exp.mpr
    exact add_le_add_right (mul_le_mul_of_nonneg_left
      (heightDecay_antitone (show L ≤ 2*L by omega)) (Nat.cast_nonneg _)) _
  have hh := finiteMean_mul_exp_le
    (fun Y => q^(InputTree.familyCost L n (L+r) (modifiedInputTree L r E U X) e Y))
    (fun Y => q^(InputTree.familyCost (2*L) n (L+r) (modifiedInputTree L r E U X) e Y))
    _ _ (by simpa only [pow_right_comm] using h₀) (by simpa only [pow_right_comm] using h₁')
  simp only [←pow_add] at hh
  refine hh.trans_eq ?_
  congr 1
  simp only [Real.log_pow,Nat.cast_mul,Nat.cast_ofNat]
  ring

noncomputable def InputTree.lowCost (H d : ℕ) (T : InputTree d)
    {ι : Type*} [Fintype ι] (e : ι ↪ Card d) (Y : SwitchIndex d → Bool) : ℕ :=
  ∑ i ∈ Finset.range H, T.levelCost (i+1) e Y

lemma InputTree.lowCost_slab (L d : ℕ) (T : InputTree d)
    {ι : Type*} [Fintype ι] (e : ι ↪ Card d) (Y : SwitchIndex d → Bool) :
    InputTree.lowCost L d T e Y+InputTree.slabCost L d T e Y = InputTree.lowCost (2*L) d T e Y := by
  rw [InputTree.lowCost,InputTree.lowCost,show 2*L=L+L by omega,Finset.sum_range_add]
  congr 1
  exact Fin.sum_univ_eq_sum_range (fun i => T.levelCost (L+i+1) e Y) L

lemma InputTree.cost_family (L n d : ℕ) (T : (SwitchIndex d → Bool) → InputTree d)
    {ι : Type*} [Fintype ι] (e : ι ↪ Card d) (Y : SwitchIndex d → Bool) :
    InputTree.lowCost L d (T Y) e Y + InputTree.familyCost L n d T e Y +
      InputTree.familyCost (2*L) n d T e Y = InputTree.lowCost (L*4^n) d (T Y) e Y := by
  induction n with
  | zero => simp only [InputTree.familyCost,Finset.range_zero,Finset.sum_empty,Nat.add_zero,
      pow_zero,mul_one]
  | succ n ih =>
    have he : (2*L)*4^n = 2*(L*4^n) := by ring
    have he' : L*4^(n+1) = 2*(2*(L*4^n)) := by rw [pow_succ]; ring
    simp only [InputTree.familyCost,Finset.sum_range_succ] at ih ⊢
    rw [he,he',←InputTree.lowCost_slab,←InputTree.lowCost_slab,←ih]
    omega

lemma InputTree.lowCost_ge (H d : ℕ) (hd : d ≤ H) (T : InputTree d)
    {ι : Type*} [Fintype ι] (e : ι ↪ Card d) (Y : SwitchIndex d → Bool) :
    InputTree.lowCost H d T e Y = InputTree.lowCost d d T e Y := by
  symm
  apply Finset.sum_subset (Finset.range_mono hd)
  intro i _ hi
  have hi' : d ≤ i := by simpa only [Finset.mem_range,not_lt] using hi
  exact InputTree.levelCost_gt (i+1) d T (by omega) e Y

lemma boundaryTree_levelCost_low (t L r : ℕ) (ht : t ≤ L)
    (U : Card r → Equiv.Perm (Card L)) (X : SwitchIndex (L+r) → Bool)
    {ι : Type*} [Fintype ι] (e : ι ↪ Card (L+r)) (Y : SwitchIndex (L+r) → Bool) :
    (boundaryTree L r U X).levelCost t e Y = 0 := by
  induction r generalizing ι with
  | zero => rfl
  | succ r ih =>
    rw [boundaryTree,InputTree.levelCost,ite_eq_right (by omega : t ≠ L+r+1),ih,ih]

lemma boundaryTree_lowCost_zero (L r : ℕ) (U : Card r → Equiv.Perm (Card L))
    (X : SwitchIndex (L+r) → Bool) {ι : Type*} [Fintype ι]
    (e : ι ↪ Card (L+r)) (Y : SwitchIndex (L+r) → Bool) :
    InputTree.lowCost L (L+r) (boundaryTree L r U X) e Y = 0 := by
  apply Finset.sum_eq_zero
  intro i hi
  exact boundaryTree_levelCost_low (i+1) L r (by simpa only [Finset.mem_range,Nat.lt_iff_add_one_le] using hi) U X e Y

theorem modified_cost_mgf (L r : ℕ) (hL : 0 < L) (E : Finset (Card r))
    (U : Card r → Equiv.Perm (Card L)) (X : SwitchIndex (L+r) → Bool)
    {ι : Type*} [Fintype ι] (e : ι ↪ Card (L+r)) (q : ℝ) (hq : 1 ≤ q)
    (hlog : Real.log q ≤ 1/500) :
    finiteMean (fun Y => q^(InputTree.lowCost (L+r) (L+r) (modifiedInputTree L r E U X Y) e Y)) ≤
      Real.exp (Fintype.card ι*heightDecay L +
        3*((L*E.card*2^L:ℕ):ℝ)*Real.log q) := by
  have hbound : L+r ≤ L*4^(L+r) := by
    have h₀ := pow_four_ge (L+r)
    have h₁ := Nat.mul_le_mul_right (4^(L+r)) hL
    nlinarith
  have he (Y : SwitchIndex (L+r) → Bool) :=
    InputTree.cost_family L (L+r) (L+r) (modifiedInputTree L r E U X) e Y
  have hz (Y : SwitchIndex (L+r) → Bool) :
      InputTree.lowCost L (L+r) (modifiedInputTree L r E U X Y) e Y = 0 :=
    boundaryTree_lowCost_zero L r _ X e Y
  simp only [hz,Nat.zero_add,InputTree.lowCost_ge _ _ hbound] at he
  simp_rw [←he]
  exact modified_high_mgf L (L+r) r hL E U X e q hq hlog


noncomputable def exceptionChild {r : ℕ} (E : Finset (Card (r+1))) (b : Bool) : Finset (Card r) :=
  Finset.univ.filter (fun u => Fin.cons b u ∈ E)

lemma mem_exceptionChild {r : ℕ} (E : Finset (Card (r+1))) (b : Bool) (u : Card r) :
    u ∈ exceptionChild E b ↔ Fin.cons b u ∈ E := by
  classical
  simp only [exceptionChild,Finset.mem_filter,Finset.mem_univ,true_and]

lemma exceptionChild_card_add {r : ℕ} (E : Finset (Card (r+1))) :
    (exceptionChild E false).card+(exceptionChild E true).card = E.card := by
  classical
  have he : (∑ u : Card (r+1), if u ∈ E then 1 else 0) = E.card := by simp
  rw [Fintype.sum_equiv (headTailEquiv r) _
    (fun x : Bool × Card r => if Fin.cons x.1 x.2 ∈ E then 1 else 0)
    (fun x => by change (if x ∈ E then 1 else 0) = (if Fin.cons (x 0) (Fin.tail x) ∈ E then 1 else 0); rw [Fin.cons_self_tail])] at he
  simp only [Fintype.sum_prod_type,Fintype.sum_bool] at he
  simpa only [exceptionChild,Finset.card_filter,add_comm] using he

def seedSplitEquiv (r : ℕ) (A : Type*) : (Card (r+1) → A) ≃ (Card r → A) × (Card r → A) where
  toFun U := (fun u => U (Fin.cons false u),fun u => U (Fin.cons true u))
  invFun U := fun u => if u 0 then U.2 (Fin.tail u) else U.1 (Fin.tail u)
  left_inv U := by
    funext u
    dsimp only
    split_ifs with h
    · rw [←h,Fin.cons_self_tail]
    · have h' : u 0 = false := by cases hh : u 0 <;> simp_all
      rw [←h',Fin.cons_self_tail]
  right_inv U := by simp only [Fin.cons_zero,Fin.tail_cons,Bool.false_eq_true,↓reduceIte]

def seedSandwichShuffle {A B C D E : Type*} :
    (A × B) × ((C × D) × E) ≃ ((A × C) × (B × D)) × E where
  toFun x := (((x.1.1,x.2.1.1),(x.1.2,x.2.1.2)),x.2.2)
  invFun x := ((x.1.1.1,x.1.2.1),((x.1.1.2,x.1.2.2),x.2))
  left_inv _ := rfl
  right_inv _ := rfl

abbrev ModifiedCoins (L r : ℕ) := (Card r → Equiv.Perm (Card L)) × BenesCoins (L+r)

def modifiedStepEquiv (L r : ℕ) : ModifiedCoins L (r+1) ≃
    (ModifiedCoins L r × ModifiedCoins L r) × ((Card (L+r) → Bool) × (Card (L+r) → Bool)) :=
  (Equiv.prodCongr (seedSplitEquiv r (Equiv.Perm (Card L))) (benesStepEquiv (L+r))).trans
    seedSandwichShuffle

noncomputable def modifiedPerm (L r : ℕ) (E : Finset (Card r)) (ω : ModifiedCoins L r) :
    Equiv.Perm (Card (L+r)) :=
  butterflyPerm (L+r) (decodeButterfly (L+r) ω.2.1) *
    (modifiedInputTree L r E ω.1 ω.2.2 ω.2.1).perm⁻¹

noncomputable def modifiedCost (L r : ℕ) (E : Finset (Card r))
    {ι : Type*} [Fintype ι] (e : ι ↪ Card (L+r)) (ω : ModifiedCoins L r) : ℕ :=
  InputTree.lowCost (L+r) (L+r) (modifiedInputTree L r E ω.1 ω.2.2 ω.2.1) e ω.2.1

lemma modifiedBoundary_cons (L r : ℕ) (E : Finset (Card (r+1)))
    (U : Card (r+1) → Equiv.Perm (Card L)) (Y : SwitchIndex (L+r+1) → Bool) (b : Bool) :
    (fun u => modifiedBoundary L (r+1) E U Y (Fin.cons b u)) =
    modifiedBoundary L r (exceptionChild E b) (fun u => U (Fin.cons b u))
      (if b then (coinStepEquiv (L+r) Y).1.2 else (coinStepEquiv (L+r) Y).1.1) := by
  funext u
  simp only [modifiedBoundary,mem_exceptionChild,boundaryOutput,Fin.cons_zero,Fin.tail_cons]

lemma modifiedInputTree_node (L r : ℕ) (E : Finset (Card (r+1)))
    (ω : ModifiedCoins L r × ModifiedCoins L r) (coins : (Card (L+r) → Bool) × (Card (L+r) → Bool)) :
    let z := (modifiedStepEquiv L r).symm (ω,coins)
    modifiedInputTree L (r+1) E z.1 z.2.2 z.2.1 =
      InputTree.node coins.1 (fun b =>
        let w := if b then ω.2 else ω.1
        modifiedInputTree L r (exceptionChild E b) w.1 w.2.2 w.2.1) := by
  dsimp only
  unfold modifiedInputTree
  rw [boundaryTree]
  change InputTree.node coins.1 (fun b => boundaryTree L r _ _) = _
  congr 1
  funext b
  rw [modifiedBoundary_cons]
  cases b <;> rfl

lemma modifiedPerm_step (L r : ℕ) (E : Finset (Card (r+1)))
    (ω : ModifiedCoins L r × ModifiedCoins L r) (coins : (Card (L+r) → Bool) × (Card (L+r) → Bool)) :
    modifiedPerm L (r+1) E ((modifiedStepEquiv L r).symm (ω,coins)) =
      pairSwitch coins.2 * childLift (fun b => modifiedPerm L r (exceptionChild E b)
        (if b then ω.2 else ω.1)) * pairSwitch coins.1 := by
  rw [modifiedPerm,modifiedInputTree_node,InputTree.perm,mul_inv_rev,pairSwitch_inv,childLift_inv]
  change (butterflyPerm (L+r+1) (decodeButterfly (L+r+1)
    ((coinStepEquiv (L+r)).symm ((ω.1.2.1,ω.2.2.1),coins.2)))) * _ = _
  rw [butterflyPerm_step,mul_assoc,←mul_assoc (childLift _),childLift_mul,←mul_assoc]
  congr 2
  apply congrArg childLift
  funext b
  cases b <;> rfl

lemma modifiedPerm_coordinates (L r : ℕ) (E : Finset (Card (r+1)))
    (ω : ModifiedCoins L r × ModifiedCoins L r) (coins : (Card (L+r) → Bool) × (Card (L+r) → Bool))
    (x : Card (L+r+1)) :
    headTailEquiv (L+r) (modifiedPerm L (r+1) E ((modifiedStepEquiv L r).symm (ω,coins)) x) =
      PairRouting.sandwich coins.1 coins.2 (fun b => modifiedPerm L r (exceptionChild E b)
        (if b then ω.2 else ω.1)) (headTailEquiv (L+r) x) := by
  rw [modifiedPerm_step]
  simp only [Equiv.Perm.mul_apply,headTail_switch,headTail_child]
  rfl

lemma InputTree.lowCost_node (d : ℕ) (ξ : Card d → Bool) (T : Bool → InputTree d)
    {ι : Type*} [Fintype ι] (e : ι ↪ Card (d+1)) (Y : (SwitchIndex d → Bool) × (SwitchIndex d → Bool))
    (η : Card d → Bool) :
    InputTree.lowCost (d+1) (d+1) (.node ξ T) e ((coinStepEquiv d).symm (Y,η)) =
      let x := e.trans (headTailEquiv d).toEmbedding
      let c := PairRouting.colors x ξ
      let hc := PairRouting.colors_compatible x ξ
      PairRouting.alternatingCycles (PairRouting.switchedEmbedding x ξ)
        (fun b => if b then butterflyPerm d (decodeButterfly d Y.2) * (T true).perm⁻¹
          else butterflyPerm d (decodeButterfly d Y.1) * (T false).perm⁻¹) +
        InputTree.lowCost d d (T false) (PairRouting.childEmbedding x c hc false) Y.1 +
        InputTree.lowCost d d (T true) (PairRouting.childEmbedding x c hc true) Y.2 := by
  dsimp only
  rw [InputTree.lowCost,Finset.sum_range_succ,InputTree.levelCost_node,ite_eq_left rfl]
  have he : (∑ i ∈ Finset.range d,
      (.node ξ T : InputTree (d+1)).levelCost (i+1) e ((coinStepEquiv d).symm (Y,η))) =
      InputTree.lowCost d d (T false)
        (PairRouting.childEmbedding (e.trans (headTailEquiv d).toEmbedding)
          (PairRouting.colors (e.trans (headTailEquiv d).toEmbedding) ξ) (PairRouting.colors_compatible _ _) false) Y.1 +
      InputTree.lowCost d d (T true)
        (PairRouting.childEmbedding (e.trans (headTailEquiv d).toEmbedding)
          (PairRouting.colors (e.trans (headTailEquiv d).toEmbedding) ξ) (PairRouting.colors_compatible _ _) true) Y.2 := by
    rw [InputTree.lowCost,InputTree.lowCost,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [InputTree.levelCost_node,ite_eq_right (by simp only [Finset.mem_range] at hi; omega : i+1 ≠ d+1)]
  rw [he]
  omega

noncomputable def modifiedAssignmentCost (L r : ℕ) (E : Finset (Card (r+1)))
    {ι : Type*} [Fintype ι] (x : ι ↪ Bool × Card (L+r)) (c : ι → Bool)
    (hc : PairRouting.Compatible x c) (ω : ModifiedCoins L r × ModifiedCoins L r) : ℕ :=
  PairRouting.alternatingCycles (PairRouting.coloredEmbedding x c hc)
    (fun b => modifiedPerm L r (exceptionChild E b) (if b then ω.2 else ω.1)) +
  modifiedCost L r (exceptionChild E false) (PairRouting.childEmbedding x c hc false) ω.1 +
  modifiedCost L r (exceptionChild E true) (PairRouting.childEmbedding x c hc true) ω.2

lemma modifiedCost_step (L r : ℕ) (E : Finset (Card (r+1)))
    {ι : Type*} [Fintype ι] (e : ι ↪ Card (L+r+1))
    (ω : ModifiedCoins L r × ModifiedCoins L r) (coins : (Card (L+r) → Bool) × (Card (L+r) → Bool)) :
    modifiedCost L (r+1) E e ((modifiedStepEquiv L r).symm (ω,coins)) =
      modifiedAssignmentCost L r E (e.trans (headTailEquiv (L+r)).toEmbedding)
        (PairRouting.colors (e.trans (headTailEquiv (L+r)).toEmbedding) coins.1)
        (PairRouting.colors_compatible _ _) ω := by
  rw [modifiedCost,modifiedInputTree_node]
  change InputTree.lowCost (L+r+1) (L+r+1) _ e
    ((coinStepEquiv (L+r)).symm ((ω.1.2.1,ω.2.2.1),coins.2)) = _
  rw [InputTree.lowCost_node]
  unfold modifiedAssignmentCost
  dsimp only
  simp only [Bool.false_eq_true,↓reduceIte]
  rw [PairRouting.switchedEmbedding_eq_colored _ _ (PairRouting.colors_compatible _ _) _ rfl]
  congr 2


namespace PairRouting
variable {ι α : Type*} [Fintype ι] [Fintype α] [DecidableEq α] [DecidableEq ι]

omit [Fintype α] [DecidableEq ι] in
lemma childEmbedding_surjective (x : ι ↪ Bool × α) (hx : Function.Surjective x)
    (c : ι → Bool) (hc : Compatible x c) (b : Bool) :
    Function.Surjective (childEmbedding x c hc b) := by
  intro y
  have hs : Function.Surjective (coloredEmbedding x c hc) :=
    (pairLayer (chosenCoin x c)).surjective.comp hx
  obtain ⟨i,hi⟩ := hs (b,y)
  rw [coloredEmbedding_apply] at hi
  exact ⟨⟨i,congrArg Prod.fst hi⟩,congrArg Prod.snd hi⟩

omit [DecidableEq ι] in
lemma uniformPerm_tuple_upper (e f : ι ↪ α) (he : Function.Surjective e) (p : Equiv.Perm α) :
    finiteMean (fun u : Equiv.Perm α => if ∀ i, (p*u⁻¹) (e i) = f i then (1:ℝ) else 0) ≤
      1/(Fintype.card (Equiv.Perm α):ℝ) := by
  classical
  let M : Equiv.Perm α → Prop := fun u => ∀ i, (p*u⁻¹) (e i) = f i
  have huniq (u v : Equiv.Perm α) (hu : M u) (hv : M v) : u = v := by
    have hh : p*u⁻¹ = p*v⁻¹ := by
      ext x
      obtain ⟨i,rfl⟩ := he x
      exact (hu i).trans (hv i).symm
    exact inv_injective (mul_left_cancel hh)
  unfold finiteMean
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  change (∑ u, if M u then (1:ℝ) else 0) ≤ 1
  by_cases h : ∃ u, M u
  · obtain ⟨u,hu⟩ := h
    rw [Finset.sum_eq_single u]
    · simp only [hu,↓reduceIte,le_refl]
    · intro v _ hv
      exact ite_eq_right (fun hh => hv (huniq v u hh hu))
    · simp
  · push Not at h
    simp only [h,ite_false,Finset.sum_const_zero,zero_le_one]

end PairRouting

noncomputable def centralFactor (L r : ℕ) (E : Finset (Card r)) (a : ℝ) : ℝ :=
  (Nat.factorial (2^L):ℝ)^(-((2:ℝ)^r-E.card)*a)

lemma centralFactor_nonneg (L r : ℕ) (E : Finset (Card r)) (a : ℝ) :
    0 ≤ centralFactor L r E a := Real.rpow_nonneg (Nat.cast_nonneg _) _

lemma centralFactor_step (L r : ℕ) (E : Finset (Card (r+1))) (a : ℝ) :
    centralFactor L (r+1) E a =
      centralFactor L r (exceptionChild E false) a * centralFactor L r (exceptionChild E true) a := by
  unfold centralFactor
  rw [←Real.rpow_add (Nat.cast_pos.mpr (Nat.factorial_pos _))]
  congr 1
  have he : ((exceptionChild E false).card:ℝ)+(exceptionChild E true).card = E.card := by
    exact_mod_cast exceptionChild_card_add E
  rw [pow_succ,←he]
  ring

lemma modifiedPerm_zero (L : ℕ) (E : Finset (Card 0)) (ω : ModifiedCoins L 0) :
    modifiedPerm L 0 E ω =
      if (fun j => Fin.elim0 j : Card 0) ∈ E then 1
      else butterflyPerm L (decodeButterfly L ω.2.1)*(ω.1 (fun j => Fin.elim0 j))⁻¹ := by
  unfold modifiedPerm modifiedInputTree boundaryTree InputTree.perm modifiedBoundary boundaryOutput
  split_ifs
  · exact mul_inv_cancel _
  · rfl

lemma modifiedCost_zero (L : ℕ) (E : Finset (Card 0)) {ι : Type*} [Fintype ι]
    (e : ι ↪ Card L) (ω : ModifiedCoins L 0) : modifiedCost L 0 E e ω = 0 := by
  simp only [modifiedCost,modifiedInputTree,boundaryTree,InputTree.lowCost,
    InputTree.levelCost,Finset.sum_const_zero]

lemma centralFactor_zero (L : ℕ) (E : Finset (Card 0)) (a : ℝ) :
    centralFactor L 0 E a =
      if (fun j => Fin.elim0 j : Card 0) ∈ E then 1 else (Nat.factorial (2^L):ℝ)^(-a) := by
  classical
  let z : Card 0 := fun j => Fin.elim0 j
  have he : (E.card:ℝ) = if z ∈ E then 1 else 0 := by
    by_cases hz : z ∈ E
    · have he : E = {z} := by
        ext u
        rw [Subsingleton.elim u z]
        simp only [hz,Finset.mem_singleton]
      rw [he,ite_eq_left (by simpa only [he] using hz),Finset.card_singleton,Nat.cast_one]
    · have he : E = ∅ := Finset.eq_empty_iff_forall_notMem.mpr (fun u hu => hz (Subsingleton.elim u z ▸ hu))
      rw [he,Finset.card_empty,Nat.cast_zero,ite_eq_right (by simp)]
  unfold centralFactor
  rw [pow_zero,he]
  split_ifs <;> simp

lemma modified_probability_zero_le (L : ℕ) (E : Finset (Card 0))
    {ι : Type*} [Fintype ι] (e f : ι ↪ Card L) (he : Function.Surjective e) :
    PairRouting.tupleProbability (modifiedPerm L 0 E) e f ≤
      if (fun j => Fin.elim0 j : Card 0) ∈ E then 1 else 1/(Nat.factorial (2^L):ℝ) := by
  classical
  rw [PairRouting.tupleProbability,finiteMean_prod,finiteMean_comm]
  let B : ℝ := if (fun j => Fin.elim0 j : Card 0) ∈ E then 1 else 1/(Nat.factorial (2^L):ℝ)
  change _ ≤ B
  calc
    _ ≤ finiteMean (fun _ω : BenesCoins L => B) := by
      apply finiteMean_mono
      intro ω
      simp only [modifiedPerm_zero]
      by_cases h : (fun j => Fin.elim0 j : Card 0) ∈ E
      · simp only [h,↓reduceIte,Equiv.Perm.one_apply,finiteMean_const,B]
        split_ifs <;> norm_num
      · simp only [h,↓reduceIte,B]
        rw [finiteMean_pi_eval (A := fun _ : Card 0 => Equiv.Perm (Card L)) (fun j => Fin.elim0 j) (fun u : Equiv.Perm (Card L) =>
          if ∀ i, (butterflyPerm L (decodeButterfly L ω.1)*u⁻¹) (e i) = f i then (1:ℝ) else 0)]
        convert PairRouting.uniformPerm_tuple_upper e f he (butterflyPerm L (decodeButterfly L ω.1)) using 1
        rw [Fintype.card_perm,card_positions]
    _ = _ := finiteMean_const B

end Thorp

end ThorpNine.Contact

end OAI
