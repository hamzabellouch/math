import Mathlib
import OAI.Combinatorics.MatchingCount.Graphs.Cumulative

namespace OAI

namespace MatchingFPRAS.FiniteChoice

open Finset

lemma tapeIndex_value (k : ℕ) (bits : Fin k → Bool) :
    (tapeIndex k bits).val = ∑ i, (if bits i then 1 else 0)*2^i.val := by
  change (finFunctionFinEquiv (fun i => finTwoEquiv.symm (bits i))).val = _
  rw [finFunctionFinEquiv_apply]
  apply sum_congr rfl; intro i _
  cases bits i <;> simp [finTwoEquiv]

lemma tapeLaw_eq {r : ℕ} (p : Fin r → ℚ) (hs : ∑ i, p i = 1) (k : ℕ) :
    tapeLaw p hs k = outputLaw p hs (pow_pos (by norm_num : 0 < (2:ℕ)) k) := by
  funext i
  have hcard : (univ.filter (fun bits : Fin k → Bool => chooseBits p hs k bits=i)).card =
      (univ.filter (fun J : Fin (2^k) => choose p hs (pow_pos (by norm_num : 0 < (2:ℕ)) k) J=i)).card := by
    calc
      _ = ∑ bits : Fin k → Bool, if chooseBits p hs k bits=i then (1:ℕ) else 0 := by simp
      _ = ∑ J : Fin (2^k), if choose p hs (pow_pos (by norm_num : 0 < (2:ℕ)) k) J=i then (1:ℕ) else 0 :=
        by
          simp only [chooseBits]
          convert (tapeIndex k).sum_comp
            (fun J : Fin (2^k) => if choose p hs (pow_pos (by norm_num : 0 < (2:ℕ)) k) J=i then (1:ℕ) else 0) using 1
          congr 3
      _ = _ := by simp
  simp only [tapeLaw,outputLaw,hcard,Nat.cast_pow,Nat.cast_ofNat]

end MatchingFPRAS.FiniteChoice

namespace MatchingFPRAS.BoundedSimulation

open Finset

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

def runBits {r : ℕ} (z : Ω) (p : ℕ → Ω → Fin r → ℚ)
    (hs : ∀ n s, ∑ i, p n s i = 1) (next : ℕ → Ω → Fin r → Ω) (k : ℕ) :
    (n : ℕ) → (Fin n → Fin k → Bool) → Ω
  | 0, _ => z
  | n+1, bits =>
    let s := runBits z p hs next k n (Fin.init bits)
    next n s (MatchingFPRAS.FiniteChoice.chooseBits (p n s) (hs n s) k (bits (Fin.last n)))

def pointMass (z : Ω) (s : Ω) : ℚ := if z=s then 1 else 0

def uniformLaw {A : Type*} [Fintype A] (f : A → Ω) (s : Ω) : ℚ :=
  (∑ a, if f a=s then (1:ℚ) else 0)/(Fintype.card A:ℚ)




omit [Fintype Ω] in
lemma uniformLaw_equiv [Fintype Ω] {A B : Type*} [Fintype A] [Fintype B] (e : A ≃ B)
    (f : B → Ω) (s : Ω) : uniformLaw (f ∘ e) s=uniformLaw f s := by
  unfold uniformLaw
  rw [Fintype.card_congr e]
  congr 1
  exact e.sum_comp (fun b => if f b=s then (1:ℚ) else 0)

lemma fiber_sum {A : Type*} [Fintype A] (f : A → Ω) (g : Ω → ℚ) :
    (∑ s, (∑ a, if f a=s then (1:ℚ) else 0)*g s) = ∑ a, g (f a) := by
  simp_rw [sum_mul,ite_mul,one_mul,zero_mul]
  rw [sum_comm]
  simp only [sum_ite_eq,mem_univ,ite_true]

lemma uniformLaw_map {A Ψ : Type*} [Fintype A] [Fintype Ψ] [DecidableEq Ψ]
    (f : A → Ω) (g : Ω → Ψ) (t : Ψ) :
    uniformLaw (g ∘ f) t = ∑ s, uniformLaw f s*(if g s=t then 1 else 0) := by
  unfold uniformLaw
  simp only [Function.comp_apply,div_mul_eq_mul_div,← sum_div]
  rw [fiber_sum]

lemma uniformLaw_prod {A B : Type*} [Fintype A] [Fintype B]
    (f : A → Ω) (g : Ω → B → Ω) (t : Ω) :
    uniformLaw (fun ab : A×B => g (f ab.1) ab.2) t =
      ∑ s, uniformLaw f s*uniformLaw (g s) t := by
  unfold uniformLaw
  simp only [Fintype.card_prod,Nat.cast_mul,div_mul_div_comm,← sum_div,Fintype.sum_prod_type]
  rw [fiber_sum]

lemma uniformLaw_chooseBits {r : ℕ} (p : Fin r → ℚ) (hs : ∑ i, p i=1) (k : ℕ) (i : Fin r) :
    uniformLaw (MatchingFPRAS.FiniteChoice.chooseBits p hs k) i =
      MatchingFPRAS.FiniteChoice.outputLaw p hs (pow_pos (by norm_num : 0 < (2:ℕ)) k) i := by
  rw [← MatchingFPRAS.FiniteChoice.tapeLaw_eq]
  simp [uniformLaw,MatchingFPRAS.FiniteChoice.tapeLaw]




lemma uniformLaw_choice_step {r : ℕ} (p : Fin r → ℚ) (hs : ∑ i, p i=1) (k : ℕ)
    (next : Fin r → Ω) (t : Ω) :
    uniformLaw (fun bits => next (MatchingFPRAS.FiniteChoice.chooseBits p hs k bits)) t =
      ∑ i, if next i=t then MatchingFPRAS.FiniteChoice.outputLaw p hs
        (pow_pos (by norm_num : 0 < (2:ℕ)) k) i else 0 := by
  have h := uniformLaw_map (MatchingFPRAS.FiniteChoice.chooseBits p hs k) next t
  simp only [uniformLaw_chooseBits,mul_ite,mul_one,mul_zero] at h
  convert h using 1
  congr 3

lemma runBits_law_succ {r : ℕ} (z : Ω) (p : ℕ → Ω → Fin r → ℚ)
    (hs : ∀ n s, ∑ i, p n s i=1) (next : ℕ → Ω → Fin r → Ω) (k n : ℕ) (t : Ω) :
    uniformLaw (runBits z p hs next k (n+1)) t =
      categoricalStep (uniformLaw (runBits z p hs next k n))
        (fun s => MatchingFPRAS.FiniteChoice.outputLaw (p n s) (hs n s)
          (pow_pos (by norm_num : 0 < (2:ℕ)) k)) (next n) t := by
  let e : ((Fin n → Fin k → Bool) × (Fin k → Bool)) ≃ (Fin (n+1) → Fin k → Bool) :=
    (Equiv.prodComm _ _).trans (Fin.snocEquiv (fun _ => Fin k → Bool))
  have hh := uniformLaw_equiv e (runBits z p hs next k (n+1)) t
  have hc : (runBits z p hs next k (n+1)) ∘ e =
      (fun ab : ((Fin n → Fin k → Bool) × (Fin k → Bool)) =>
        next n (runBits z p hs next k n ab.1)
          (MatchingFPRAS.FiniteChoice.chooseBits (p n (runBits z p hs next k n ab.1))
            (hs n (runBits z p hs next k n ab.1)) k ab.2)) := by
    funext ab
    rcases ab with ⟨pref, last⟩
    change next n (runBits z p hs next k n (Fin.init (Fin.snoc (α := fun _ : Fin (n+1) => Fin k → Bool) pref last)))
      (MatchingFPRAS.FiniteChoice.chooseBits
        (p n (runBits z p hs next k n (Fin.init (Fin.snoc (α := fun _ : Fin (n+1) => Fin k → Bool) pref last))))
        (hs n (runBits z p hs next k n (Fin.init (Fin.snoc (α := fun _ : Fin (n+1) => Fin k → Bool) pref last)))) k
        ((Fin.snoc (α := fun _ : Fin (n+1) => Fin k → Bool) pref last) (Fin.last n))) = _
    simp only [Fin.init_snoc,Fin.snoc_last]
  rw [hc] at hh
  rw [← hh,uniformLaw_prod (runBits z p hs next k n)
    (fun s bits => next n s (MatchingFPRAS.FiniteChoice.chooseBits (p n s) (hs n s) k bits)) t]
  simp only [uniformLaw_choice_step,categoricalStep]

lemma runBits_law {r : ℕ} (z : Ω) (p : ℕ → Ω → Fin r → ℚ)
    (hs : ∀ n s, ∑ i, p n s i=1) (next : ℕ → Ω → Fin r → Ω) (k n : ℕ) :
    uniformLaw (runBits z p hs next k n) = bitRun (pointMass z) p hs next k n := by
  induction n with
  | zero => funext s; by_cases h : z=s <;> simp [runBits,bitRun,uniformLaw,pointMass,h]
  | succ n ih => funext s; rw [runBits_law_succ,ih]; rfl

omit [Fintype Ω] in
lemma pointMass_nonneg [Fintype Ω] (z : Ω) (s : Ω) : 0 ≤ pointMass z s := by
  unfold pointMass; split_ifs <;> norm_num

lemma pointMass_sum (z : Ω) : ∑ s, pointMass z s=1 := by simp [pointMass]

lemma fixed_tape_card (n k : ℕ) : Fintype.card (Fin n → Fin k → Bool)=2^(n*k) := by
  simp only [Fintype.card_fun,Fintype.card_bool,Fintype.card_fin,← pow_mul,Nat.mul_comm k n]




theorem fixed_tape_simulation {r : ℕ} (z : Ω) (p : ℕ → Ω → Fin r → ℚ)
    (hp : ∀ n s i, 0 ≤ p n s i) (hs : ∀ n s, ∑ i, p n s i=1)
    (next : ℕ → Ω → Fin r → Ω) (k n : ℕ) :
    (∑ s, |uniformLaw (runBits z p hs next k n) s-idealRun (pointMass z) p next n s|)/2 ≤
      2*n*r/(2:ℚ)^k := by
  rw [runBits_law]
  exact finite_bit_simulation (pointMass z) (pointMass_nonneg z) (pointMass_sum z) p hp hs next k n

end MatchingFPRAS.BoundedSimulation

namespace MatchingFPRAS.Counting

open Finset

abbrev alpha : ℚ := 1/100000

lemma others_nonempty {n : ℕ} (hn : 2 ≤ n) (i : Fin n) : (univ.erase i).Nonempty := by
  let j : Fin n := ⟨if i.val=0 then 1 else 0, by split_ifs <;> omega⟩
  refine ⟨j,mem_erase.mpr ⟨?_,mem_univ _⟩⟩
  apply Fin.ne_of_val_ne
  dsimp [j]; split_ifs <;> omega

def rowMaximum {n : ℕ} (hn : 2 ≤ n) (G : Fin n → Fin n → ℚ) (v : Fin n → ℚ) (i : Fin n) : ℚ :=
  (univ.erase i).sup' (others_nonempty hn i) (fun j => G i j / v j)

def scaleUpdate {n : ℕ} (hn : 2 ≤ n) (G : Fin n → Fin n → ℚ) (v : Fin n → ℚ) (i : Fin n) : Fin n → ℚ :=
  Function.update v i (rowMaximum hn G v i)

def scalingTrace {n : ℕ} (hn : 2 ≤ n) (G : Fin n → Fin n → ℚ) : ℕ → Fin n → ℚ
  | 0 => fun _ => 2
  | k+1 => if hk : k<n then scaleUpdate hn G (scalingTrace hn G k) ⟨k,hk⟩ else scalingTrace hn G k



open Finset

variable {n : ℕ}

structure ScaleInvariant (G : Fin n → Fin n → ℚ) (v : Fin n → ℚ) : Prop where
  lower : ∀ i, alpha/2 ≤ v i
  upper : ∀ i, v i ≤ 2
  feasible : ∀ i j, i≠j → G i j ≤ v i*v j

lemma ScaleInvariant.pos {G : Fin n → Fin n → ℚ} {v : Fin n → ℚ}
    (hv : ScaleInvariant G v) (i) : 0 < v i := lt_of_lt_of_le (by norm_num [alpha]) (hv.lower i)

lemma rowMaximum_le (hn : 2 ≤ n) (G : Fin n → Fin n → ℚ) (v : Fin n → ℚ)
    (hv : ScaleInvariant G v) (i) : rowMaximum hn G v i ≤ v i := by
  apply Finset.sup'_le
  intro j hj
  exact (div_le_iff₀ (hv.pos j)).mpr (hv.feasible i j (mem_erase.mp hj).1.symm)

lemma ratio_le_rowMaximum (hn : 2 ≤ n) (G : Fin n → Fin n → ℚ) (v : Fin n → ℚ)
    (i j) (hji : j≠i) : G i j/v j ≤ rowMaximum hn G v i :=
  Finset.le_sup' (fun j => G i j/v j) (mem_erase.mpr ⟨hji,mem_univ _⟩)

lemma rowMaximum_lower (hn : 2 ≤ n) (G : Fin n → Fin n → ℚ) (v : Fin n → ℚ)
    (hG : ∀ i j, i≠j → alpha ≤ G i j) (hv : ScaleInvariant G v) (i) :
    alpha/2 ≤ rowMaximum hn G v i := by
  obtain ⟨j,hj⟩ := others_nonempty hn i
  have hji := (mem_erase.mp hj).1
  apply le_trans _ (ratio_le_rowMaximum hn G v i j hji)
  apply (le_div_iff₀ (hv.pos j)).mpr
  have hGi := hG i j hji.symm
  have hvi := hv.upper j
  norm_num [alpha] at *
  linarith

lemma scaleUpdate_le (hn : 2 ≤ n) (G : Fin n → Fin n → ℚ) (v : Fin n → ℚ)
    (hv : ScaleInvariant G v) (i j) : scaleUpdate hn G v i j ≤ v j := by
  by_cases hji : j=i
  · subst j; simpa [scaleUpdate] using rowMaximum_le hn G v hv i
  · simp [scaleUpdate,Function.update_of_ne hji]

lemma scaleUpdate_invariant (hn : 2 ≤ n) (G : Fin n → Fin n → ℚ) (v : Fin n → ℚ)
    (hsym : ∀ i j, G i j=G j i) (hG : ∀ i j, i≠j → alpha ≤ G i j)
    (hv : ScaleInvariant G v) (i) : ScaleInvariant G (scaleUpdate hn G v i) := by
  constructor
  · intro j
    by_cases hji : j=i
    · subst j; simpa [scaleUpdate] using rowMaximum_lower hn G v hG hv i
    · simpa [scaleUpdate,Function.update_of_ne hji] using hv.lower j
  · intro j; exact (scaleUpdate_le hn G v hv i j).trans (hv.upper j)
  · intro a b hab
    by_cases hai : a=i
    · subst a
      have hb := (div_le_iff₀ (hv.pos b)).mp (ratio_le_rowMaximum hn G v i b hab.symm)
      simpa [scaleUpdate,Function.update_of_ne hab.symm] using hb
    · by_cases hbi : b=i
      · subst b
        have ha := (div_le_iff₀ (hv.pos a)).mp (ratio_le_rowMaximum hn G v i a hai)
        simpa [scaleUpdate,Function.update_of_ne hai,hsym i a,mul_comm] using ha
      · simpa [scaleUpdate,Function.update_of_ne hai,Function.update_of_ne hbi] using hv.feasible a b hab

lemma scaleUpdate_tight (hn : 2 ≤ n) (G : Fin n → Fin n → ℚ) (v : Fin n → ℚ)
    (hv : ScaleInvariant G v) (i) :
    ∃ j, j≠i ∧ scaleUpdate hn G v i i*scaleUpdate hn G v i j=G i j := by
  obtain ⟨j,hj,heq⟩ := Finset.exists_mem_eq_sup' (others_nonempty hn i) (fun j => G i j/v j)
  have hji := (mem_erase.mp hj).1
  refine ⟨j,hji,?_⟩
  change rowMaximum hn G v i = G i j/v j at heq
  simp only [scaleUpdate,Function.update_self,Function.update_of_ne hji]
  rw [heq]
  exact div_mul_cancel₀ _ (hv.pos j).ne'

lemma tight_persists (G : Fin n → Fin n → ℚ) (v v' : Fin n → ℚ)
    (hv : ScaleInvariant G v) (hv' : ScaleInvariant G v') (hdown : ∀ i, v' i ≤ v i)
    (i j) (hji : j≠i) (hij : v i*v j=G i j) : v' i*v' j=G i j := by
  apply le_antisymm
  · calc
      _ ≤ v i*v j := mul_le_mul (hdown i) (hdown j) (hv'.pos j).le (hv.pos i).le
      _ = _ := hij
  · exact hv'.feasible i j hji.symm




lemma scalingTrace_invariant (hn : 2 ≤ n) (G : Fin n → Fin n → ℚ)
    (hsym : ∀ i j, G i j=G j i) (hG : ∀ i j, i≠j → alpha ≤ G i j ∧ G i j ≤ 3)
    (k : ℕ) : ScaleInvariant G (scalingTrace hn G k) ∧
      ∀ i, i.val<k → ∃ j, j≠i ∧ scalingTrace hn G k i*scalingTrace hn G k j=G i j := by
  induction k with
  | zero =>
    constructor
    · constructor
      · intro i; norm_num [scalingTrace,alpha]
      · intro i; simp [scalingTrace]
      · intro i j h; have := (hG i j h).2; simp only [scalingTrace]; linarith
    · intro i hi; omega
  | succ k ih =>
    by_cases hk : k<n
    · let i : Fin n := ⟨k,hk⟩
      have hinv := scaleUpdate_invariant hn G (scalingTrace hn G k) hsym (fun i j h => (hG i j h).1) ih.1 i
      have htrace : scalingTrace hn G (k+1)=scaleUpdate hn G (scalingTrace hn G k) i := by
        simp [scalingTrace,hk,i]
      rw [htrace]
      refine ⟨hinv,?_⟩
      intro a ha
      by_cases hak : a.val<k
      · obtain ⟨j,hj,he⟩ := ih.2 a hak
        refine ⟨j,hj,?_⟩
        exact tight_persists G _ _ ih.1 hinv (scaleUpdate_le hn G _ ih.1 i) a j hj he
      · have hai : a=i := Fin.ext (by dsimp [i]; omega)
        subst a
        exact scaleUpdate_tight hn G _ ih.1 i
    · have htrace : scalingTrace hn G (k+1)=scalingTrace hn G k := by simp [scalingTrace,hk]
      rw [htrace]
      refine ⟨ih.1,?_⟩
      intro i _
      exact ih.2 i (by have := i.isLt; omega)



open Finset

theorem one_pass_scaling {n : ℕ} (hn : 2 ≤ n) (G : Fin n → Fin n → ℚ)
    (hsym : ∀ i j, G i j=G j i) (hG : ∀ i j, i≠j → alpha ≤ G i j ∧ G i j ≤ 3) :
    (∀ k i, scalingTrace hn G (k+1) i ≤ scalingTrace hn G k i) ∧
    (∀ i, alpha/2 ≤ scalingTrace hn G n i ∧ scalingTrace hn G n i ≤ 2) ∧
    (∀ i j, i≠j → G i j ≤ scalingTrace hn G n i * scalingTrace hn G n j) ∧
    (∀ i, ∃ j, j≠i ∧ scalingTrace hn G n i * scalingTrace hn G n j=G i j) := by
  have htrace := scalingTrace_invariant hn G hsym hG
  refine ⟨?_,(htrace n).1.lower |> fun h => ?_⟩
  · intro k i
    by_cases hk : k<n
    · change (if h : k<n then scaleUpdate hn G (scalingTrace hn G k) ⟨k,h⟩ else scalingTrace hn G k) i ≤ _
      rw [dite_eq_left hk]
      exact scaleUpdate_le hn G _ (htrace k).1 ⟨k,hk⟩ i
    · simp [scalingTrace,hk]
  · refine ⟨fun i => ⟨h i,(htrace n).1.upper i⟩,(htrace n).1.feasible,?_⟩
    intro i
    exact (htrace n).2 i i.isLt




def rowPeak {n : ℕ} (hn : 2 ≤ n) (g : Fin n → Fin n → ℚ) (i : Fin n) : ℚ :=
  (univ.erase i).sup' (others_nonempty hn i) (g i)

def scaledHoleMatrix {n : ℕ} (g : Fin n → Fin n → ℚ) (v : Fin n → ℚ) (i j : Fin n) : ℚ :=
  g i j/(v i*v j)

def BalancedRows {n : ℕ} (hn : 2 ≤ n) (g : Fin n → Fin n → ℚ) : Prop :=
  ∀ i, (1:ℚ)/4 ≤ rowPeak hn g i ∧ rowPeak hn g i ≤ 1




theorem one_pass_restores_balance {n : ℕ} (hn : 2 ≤ n) (g G : Fin n → Fin n → ℚ)
    (hGsym : ∀ i j, G i j=G j i)
    (hG : ∀ i j, i≠j → alpha ≤ G i j ∧ G i j ≤ 3)
    (hpre : ∀ i, (1:ℚ)/8 ≤ rowPeak hn g i)
    (haccuracy : ∀ i j, i≠j → g i j ≤ G i j ∧ G i j ≤ g i j+2*alpha) :
    (∀ i, (1:ℚ)/16 ≤ scalingTrace hn G n i) ∧
      BalancedRows hn (scaledHoleMatrix g (scalingTrace hn G n)) := by
  let v := scalingTrace hn G n
  have hv := (scalingTrace_invariant hn G hGsym hG n).1
  have hlow (i : Fin n) : (1:ℚ)/16 ≤ v i := by
    obtain ⟨j,hj,heq⟩ := Finset.exists_mem_eq_sup' (others_nonempty hn i) (g i)
    have hji := (mem_erase.mp hj).1
    change rowPeak hn g i=g i j at heq
    have hgij : (1:ℚ)/8 ≤ g i j := by rw [← heq]; exact hpre i
    have hGi := (haccuracy i j hji.symm).1
    have hfeas := hv.feasible i j hji.symm
    have hup := mul_le_mul_of_nonneg_left (hv.upper j) (hv.pos i).le
    dsimp [v]
    linarith
  refine ⟨hlow,?_⟩
  intro i
  constructor
  · obtain ⟨j,hji,heq⟩ := (one_pass_scaling hn G hGsym hG).2.2.2 i
    have hprod : (1:ℚ)/256 ≤ v i*v j := by
      calc
        (1:ℚ)/256 = ((1:ℚ)/16)*((1:ℚ)/16) := by norm_num
        _ ≤ v i*v j := mul_le_mul (hlow i) (hlow j) (by norm_num) (hv.pos i).le
    have hacc := (haccuracy i j hji.symm).2
    have hg : (1:ℚ)/4 ≤ scaledHoleMatrix g v i j := by
      apply (le_div_iff₀ (mul_pos (hv.pos i) (hv.pos j))).mpr
      change v i*v j=G i j at heq
      norm_num [alpha] at hacc
      nlinarith
    apply hg.trans
    exact Finset.le_sup' (scaledHoleMatrix g v i) (mem_erase.mpr ⟨hji,mem_univ _⟩)
  · apply Finset.sup'_le
    intro j hj
    have hji := (mem_erase.mp hj).1
    apply (div_le_one (mul_pos (hv.pos i) (hv.pos j))).mpr
    exact ((haccuracy i j hji.symm).1).trans (hv.feasible i j hji.symm)



def sigma (D K : ℕ) (epsilon : ℚ) : ℚ := min (alpha/(100*D)) (epsilon/(1000*K))

def ratioEstimate (abar dbar : ℚ) : ℚ := if 0<abar then dbar/abar else 1

def upperEstimate (D : ℕ) (dbar zbar : ℚ) : ℚ :=
  if 0<dbar then max alpha (min 3 ((D:ℚ)*zbar/dbar+alpha)) else 1

end MatchingFPRAS.Counting

end OAI
