import Mathlib
import OAI.Combinatorics.MatchingCount.Sampling.PM

namespace OAI

namespace MatchingFPRAS.Transport

open Finset

variable {V J : Type*} [Fintype V] [DecidableEq V] [Fintype J] [DecidableEq J]

variable {bags : V → Finset J} {G : SimpleGraph J}

noncomputable local instance cumulativeBagEdgeFintype : Fintype (BagEdge bags) :=
  Fintype.ofFinite _

noncomputable local instance cumulativeBagEdgePMDecidableEq :
    DecidableEq (PM (BagEdge.Incident (bags := bags))) := Classical.decEq _

end MatchingFPRAS.Transport

namespace MatchingFPRAS.FiniteChoice

open Finset

def cumulative {r : ℕ} (p : Fin r → ℚ) (i : ℕ) : ℚ := ∑ j, if j.val < i then p j else 0

lemma cumulative_zero {r : ℕ} (p : Fin r → ℚ) : cumulative p 0 = 0 := by simp [cumulative]

lemma cumulative_total {r : ℕ} (p : Fin r → ℚ) (hs : ∑ j, p j = 1) : cumulative p r = 1 := by
  simp only [cumulative,Fin.isLt,ite_true]; exact hs

lemma options_pos {r : ℕ} (p : Fin r → ℚ) (hs : ∑ j, p j = 1) : 0 < r := by
  by_contra h
  have hr : r=0 := by omega
  subst r
  simp at hs

lemma cumulative_mono {r : ℕ} (p : Fin r → ℚ) (hp : ∀ j, 0 ≤ p j) : Monotone (cumulative p) := by
  intro a b hab
  apply Finset.sum_le_sum
  intro j _
  by_cases ha : j.val<a
  · simp only [ite_eq_left ha,ite_eq_left (lt_of_lt_of_le ha hab),le_refl]
  · simp only [ite_eq_right ha]
    split_ifs <;> [exact hp j; exact le_refl _]

def candidates {r K : ℕ} (p : Fin r → ℚ) (J : Fin K) : Finset (Fin r) :=
  Finset.univ.filter (fun i => (J.val:ℚ)/K < cumulative p (i.val+1))

lemma candidates_nonempty {r K : ℕ} (p : Fin r → ℚ) (hs : ∑ j, p j = 1)
    (hK : 0 < K) (J : Fin K) : (candidates p J).Nonempty := by
  have hr := options_pos p hs
  refine ⟨⟨r-1,by omega⟩,?_⟩
  simp only [candidates,Finset.mem_filter,Finset.mem_univ,true_and]
  have he : r-1+1=r := by omega
  rw [he,cumulative_total p hs]
  apply (div_lt_one (by exact_mod_cast hK : (0:ℚ)<K)).mpr
  exact_mod_cast J.isLt

def choose {r K : ℕ} (p : Fin r → ℚ) (hs : ∑ j, p j = 1) (hK : 0 < K) (J : Fin K) : Fin r :=
  (candidates p J).min' (candidates_nonempty p hs hK J)

def outputLaw {r K : ℕ} (p : Fin r → ℚ) (hs : ∑ j, p j = 1) (hK : 0 < K) (i : Fin r) : ℚ :=
  ((Finset.univ.filter (fun J : Fin K => choose p hs hK J=i)).card:ℚ)/K




def gridInterval (K : ℕ) (a b : ℚ) : Finset ℕ :=
  (Finset.range K).filter (fun j => a ≤ (j:ℚ)/K ∧ (j:ℚ)/K < b)

lemma gridInterval_eq (K : ℕ) (hK : 0 < K) (a b : ℚ) (hb : b ≤ 1) :
    gridInterval K a b = Finset.Ico ⌈(K:ℚ)*a⌉₊ ⌈(K:ℚ)*b⌉₊ := by
  have hKr : (0:ℚ)<K := by exact_mod_cast hK
  have hlast : ⌈(K:ℚ)*b⌉₊ ≤ K := Nat.ceil_le.mpr (by nlinarith)
  ext j
  simp only [gridInterval,Finset.mem_filter,Finset.mem_range,Finset.mem_Ico,
    Nat.ceil_le,Nat.lt_ceil]
  constructor
  · rintro ⟨_,ha,hb⟩
    constructor
    · have := (le_div_iff₀ hKr).mp ha; nlinarith
    · have := (div_lt_iff₀ hKr).mp hb; nlinarith
  · rintro ⟨ha,hb⟩
    constructor
    · exact lt_of_lt_of_le (Nat.lt_ceil.mpr hb) hlast
    · constructor
      · apply (le_div_iff₀ hKr).mpr; nlinarith
      · apply (div_lt_iff₀ hKr).mpr; nlinarith

lemma gridInterval_card (K : ℕ) (hK : 0 < K) (a b : ℚ) (hab : a ≤ b) (hb : b ≤ 1) :
    ((gridInterval K a b).card:ℚ) = (⌈(K:ℚ)*b⌉₊:ℚ)-(⌈(K:ℚ)*a⌉₊:ℚ) := by
  rw [gridInterval_eq K hK a b hb,Nat.card_Ico,Nat.cast_sub]
  exact Nat.ceil_mono (mul_le_mul_of_nonneg_left hab (by positivity))

lemma gridInterval_error (K : ℕ) (hK : 0 < K) (a b : ℚ) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    |((gridInterval K a b).card:ℚ)/K-(b-a)| ≤ 2/(K:ℚ) := by
  have hKr : (0:ℚ)<K := by exact_mod_cast hK
  rw [gridInterval_card K hK a b hab hb]
  have ha₀ := Nat.le_ceil ((K:ℚ)*a)
  have hb₀ := Nat.le_ceil ((K:ℚ)*b)
  have ha₁ := Nat.ceil_lt_add_one (mul_nonneg hKr.le ha)
  have hb₁ := Nat.ceil_lt_add_one (mul_nonneg hKr.le (ha.trans hab))
  rw [abs_sub_le_iff]
  constructor
  · apply (le_div_iff₀ hKr).mpr
    simp only [sub_mul,div_mul_cancel₀ _ (ne_of_gt hKr)]
    nlinarith
  · apply (le_div_iff₀ hKr).mpr
    simp only [sub_mul,div_mul_cancel₀ _ (ne_of_gt hKr)]
    nlinarith




lemma cumulative_nonneg {r : ℕ} (p : Fin r → ℚ) (hp : ∀ j, 0 ≤ p j) (i : ℕ) :
    0 ≤ cumulative p i := by
  apply Finset.sum_nonneg; intro j _; split_ifs <;> [exact hp j; exact le_rfl]

lemma cumulative_le_one {r : ℕ} (p : Fin r → ℚ) (hp : ∀ j, 0 ≤ p j)
    (hs : ∑ j, p j = 1) (i : ℕ) (hi : i ≤ r) : cumulative p i ≤ 1 := by
  rw [← cumulative_total p hs]; exact cumulative_mono p hp hi

lemma cumulative_step {r : ℕ} (p : Fin r → ℚ) (i : Fin r) :
    cumulative p (i.val+1)-cumulative p i.val = p i := by
  unfold cumulative
  rw [← Finset.sum_sub_distrib]
  have he (j : Fin r) : (if j.val < i.val+1 then p j else 0)-(if j.val < i.val then p j else 0) =
      if j=i then p j else 0 := by
    by_cases h : j=i
    · subst j; simp
    · have hn : j.val ≠ i.val := fun hval => h (Fin.ext hval)
      by_cases hj : j.val < i.val
      · simp [h,hj,show j.val < i.val+1 by omega]
      · simp [h,hj,show ¬j.val < i.val+1 by omega]
  simp_rw [he]
  simp

lemma choose_upper {r K : ℕ} (p : Fin r → ℚ) (hs : ∑ j, p j = 1)
    (hK : 0 < K) (J : Fin K) :
    (J.val:ℚ)/K < cumulative p ((choose p hs hK J).val+1) := by
  have hm := Finset.min'_mem (candidates p J) (candidates_nonempty p hs hK J)
  exact (Finset.mem_filter.mp hm).2

lemma choose_le {r K : ℕ} (p : Fin r → ℚ) (hs : ∑ j, p j = 1)
    (hK : 0 < K) (J : Fin K) (i : Fin r)
    (hi : (J.val:ℚ)/K < cumulative p (i.val+1)) : choose p hs hK J ≤ i := by
  exact Finset.min'_le (candidates p J) i (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩)

lemma choose_lower {r K : ℕ} (p : Fin r → ℚ) (hs : ∑ j, p j = 1)
    (hK : 0 < K) (J : Fin K) :
    cumulative p (choose p hs hK J).val ≤ (J.val:ℚ)/K := by
  let i := choose p hs hK J
  by_cases hi : i.val=0
  · rw [show (choose p hs hK J).val=0 from hi,cumulative_zero]
    positivity
  · by_contra hh
    have hx : (J.val:ℚ)/K < cumulative p i.val := lt_of_not_ge hh
    let j : Fin r := ⟨i.val-1,by have := i.isLt; omega⟩
    have he : j.val+1=i.val := by dsimp [j]; omega
    have hj : (J.val:ℚ)/K < cumulative p (j.val+1) := by rw [he]; exact hx
    have hm := choose_le p hs hK J j hj
    have hv : i.val ≤ j.val := hm
    dsimp [j] at hv
    omega

lemma choose_eq_iff {r K : ℕ} (p : Fin r → ℚ) (hp : ∀ j, 0 ≤ p j)
    (hs : ∑ j, p j = 1) (hK : 0 < K) (J : Fin K) (i : Fin r) :
    choose p hs hK J=i ↔ cumulative p i.val ≤ (J.val:ℚ)/K ∧
      (J.val:ℚ)/K < cumulative p (i.val+1) := by
  constructor
  · intro he
    have hl := choose_lower p hs hK J
    have hu := choose_upper p hs hK J
    rw [he] at hl hu
    exact ⟨hl,hu⟩
  · rintro ⟨hl,hu⟩
    apply le_antisymm (choose_le p hs hK J i hu)
    by_contra h
    have hlt : (choose p hs hK J).val+1 ≤ i.val := by
      have hh : choose p hs hK J < i := lt_of_not_ge h
      exact hh
    have hm := cumulative_mono p hp hlt
    have hh := choose_upper p hs hK J
    linarith

lemma outputLaw_grid {r K : ℕ} (p : Fin r → ℚ) (hp : ∀ j, 0 ≤ p j)
    (hs : ∑ j, p j = 1) (hK : 0 < K) (i : Fin r) :
    outputLaw p hs hK i = ((gridInterval K (cumulative p i.val) (cumulative p (i.val+1))).card:ℚ)/K := by
  unfold outputLaw
  congr 2
  apply Finset.card_bij (fun J _ => J.val)
  · intro J hJ
    have he := (Finset.mem_filter.mp hJ).2
    have hc := (choose_eq_iff p hp hs hK J i).mp he
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr J.isLt,hc⟩
  · intro J _ J' _ h; exact Fin.ext h
  · intro j hj
    have hh := Finset.mem_filter.mp hj
    let J : Fin K := ⟨j,Finset.mem_range.mp hh.1⟩
    refine ⟨J,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩,rfl⟩
    exact (choose_eq_iff p hp hs hK J i).mpr hh.2

lemma outputLaw_error {r K : ℕ} (p : Fin r → ℚ) (hp : ∀ j, 0 ≤ p j)
    (hs : ∑ j, p j = 1) (hK : 0 < K) (i : Fin r) :
    |outputLaw p hs hK i-p i| ≤ 2/(K:ℚ) := by
  rw [outputLaw_grid p hp hs hK i,← cumulative_step p i]
  exact gridInterval_error K hK _ _ (cumulative_nonneg p hp i.val)
    (cumulative_mono p hp (by omega)) (cumulative_le_one p hp hs _ (by have := i.isLt; omega))




theorem fixed_bit_choice {r : ℕ} (p : Fin r → ℚ) (hp : ∀ i, 0 ≤ p i)
    (hs : ∑ i, p i = 1) (k : ℕ) :
    (∑ i, |outputLaw p hs (pow_pos (by norm_num : 0 < (2:ℕ)) k) i-p i|)/2 ≤
      2*r/(2:ℚ)^k := by
  have hK : 0 < (2:ℕ)^k := pow_pos (by norm_num) k
  have hh := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => outputLaw_error p hp hs hK i)
  simp only [Finset.sum_const,Finset.card_fin,nsmul_eq_mul,Nat.cast_pow,Nat.cast_ofNat] at hh
  have hr : (0:ℚ) ≤ r := Nat.cast_nonneg r
  have hpow : (0:ℚ) < 2^k := pow_pos (by norm_num) k
  have hz : 0 ≤ r/(2:ℚ)^k := div_nonneg hr hpow.le
  calc
    (∑ i, |outputLaw p hs hK i-p i|)/2 ≤ ((r:ℚ)*(2/(2:ℚ)^k))/2 :=
      div_le_div_of_nonneg_right hh (by norm_num)
    _ = (r:ℚ)/(2:ℚ)^k := by ring
    _ ≤ 2*r/(2:ℚ)^k := div_le_div_of_nonneg_right (by linarith) hpow.le




lemma outputLaw_nonneg {r K : ℕ} (p : Fin r → ℚ) (hs : ∑ j, p j = 1)
    (hK : 0 < K) (i : Fin r) : 0 ≤ outputLaw p hs hK i := by unfold outputLaw; positivity

lemma outputLaw_sum {r K : ℕ} (p : Fin r → ℚ) (hs : ∑ j, p j = 1)
    (hK : 0 < K) : ∑ i, outputLaw p hs hK i = 1 := by
  have hc (i : Fin r) : ((univ.filter (fun J : Fin K => choose p hs hK J=i)).card:ℚ) =
      ∑ J : Fin K, if choose p hs hK J=i then (1:ℚ) else 0 := by simp
  simp only [outputLaw,hc,← Finset.sum_div]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq,Finset.mem_univ,ite_true,Finset.sum_const,Finset.card_fin,nsmul_eq_mul,mul_one]
  exact div_self (by exact_mod_cast hK.ne' : (K:ℚ) ≠ 0)




lemma fixed_bit_l1 {r : ℕ} (p : Fin r → ℚ) (hp : ∀ i, 0 ≤ p i)
    (hs : ∑ i, p i = 1) (k : ℕ) :
    ∑ i, |outputLaw p hs (pow_pos (by norm_num : 0 < (2:ℕ)) k) i-p i| ≤ 4*r/(2:ℚ)^k := by
  have h := fixed_bit_choice p hp hs k
  calc
    _ = 2 * ((∑ i, |outputLaw p hs (pow_pos (by norm_num : 0 < (2:ℕ)) k) i-p i|) / 2) := by ring
    _ ≤ 2 * (2 * (r:ℚ) / 2^k) := mul_le_mul_of_nonneg_left h (by norm_num)
    _ = _ := by ring

end MatchingFPRAS.FiniteChoice

namespace MatchingFPRAS.BoundedSimulation

open Finset

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

def categoricalStep {r : ℕ} (μ : Ω → ℚ) (p : Ω → Fin r → ℚ)
    (next : Ω → Fin r → Ω) (t : Ω) : ℚ :=
  ∑ s, μ s * ∑ i, if next s i=t then p s i else 0

def idealRun {r : ℕ} (μ : Ω → ℚ) (p : ℕ → Ω → Fin r → ℚ)
    (next : ℕ → Ω → Fin r → Ω) : ℕ → Ω → ℚ
  | 0 => μ
  | n+1 => categoricalStep (idealRun μ p next n) (p n) (next n)

def bitRun {r : ℕ} (μ : Ω → ℚ) (p : ℕ → Ω → Fin r → ℚ)
    (hs : ∀ n s, ∑ i, p n s i = 1) (next : ℕ → Ω → Fin r → Ω) (k : ℕ) : ℕ → Ω → ℚ
  | 0 => μ
  | n+1 => categoricalStep (bitRun μ p hs next k n)
      (fun s => MatchingFPRAS.FiniteChoice.outputLaw (p n s) (hs n s) (pow_pos (by norm_num : 0 < (2:ℕ)) k)) (next n)




omit [Fintype Ω] in
lemma row_nonneg [Fintype Ω] {r : ℕ} (p : Fin r → ℚ) (hp : ∀ i, 0 ≤ p i)
    (next : Fin r → Ω) (t) : 0 ≤ ∑ i, if next i=t then p i else 0 := by
  apply sum_nonneg; intro i _; split_ifs <;> simp_all

lemma row_sum {r : ℕ} (p : Fin r → ℚ) (hs : ∑ i, p i = 1)
    (next : Fin r → Ω) : (∑ t, ∑ i, if next i=t then p i else 0) = 1 := by
  rw [sum_comm]; simp only [sum_ite_eq,mem_univ,ite_true]; exact hs

lemma step_nonneg {r : ℕ} (μ : Ω → ℚ) (hμ : ∀ s, 0 ≤ μ s)
    (p : Ω → Fin r → ℚ) (hp : ∀ s i, 0 ≤ p s i) (next : Ω → Fin r → Ω) (t) :
    0 ≤ categoricalStep μ p next t :=
  sum_nonneg (fun s _ => mul_nonneg (hμ s) (row_nonneg _ (hp s) _ _))

lemma step_sum {r : ℕ} (μ : Ω → ℚ) (hμs : ∑ s, μ s=1)
    (p : Ω → Fin r → ℚ) (hs : ∀ s, ∑ i, p s i=1) (next : Ω → Fin r → Ω) :
    ∑ t, categoricalStep μ p next t=1 := by
  unfold categoricalStep
  rw [sum_comm]
  simp_rw [← mul_sum,row_sum _ (hs _),mul_one]
  exact hμs

lemma row_l1 {r : ℕ} (p q : Fin r → ℚ) (next : Fin r → Ω) :
    ∑ t, |(∑ i, if next i=t then p i else 0)-(∑ i, if next i=t then q i else 0)| ≤
      ∑ i, |p i-q i| := by
  calc
    _ = ∑ t, |∑ i, if next i=t then p i-q i else 0| := by
      apply sum_congr rfl; intro t _; congr 1
      rw [← sum_sub_distrib]; apply sum_congr rfl; intro i _; split_ifs <;> simp
    _ ≤ ∑ t, ∑ i, |if next i=t then p i-q i else 0| :=
      sum_le_sum (fun t _ => abs_sum_le_sum_abs _ _)
    _ = _ := by rw [sum_comm]; simp only [apply_ite abs,abs_zero,sum_ite_eq,mem_univ,ite_true]

lemma step_l1 {r : ℕ} (μ ν : Ω → ℚ) (hν : ∀ s, 0 ≤ ν s) (hνs : ∑ s, ν s=1)
    (p q : Ω → Fin r → ℚ) (hp : ∀ s i, 0 ≤ p s i) (hps : ∀ s, ∑ i, p s i=1)
    (next : Ω → Fin r → Ω) (ε : ℚ)
    (he : ∀ s, ∑ i, |p s i-q s i| ≤ ε) :
    ∑ t, |categoricalStep μ p next t-categoricalStep ν q next t| ≤ (∑ s, |μ s-ν s|)+ε := by
  let P (s t : Ω) := ∑ i, if next s i=t then p s i else 0
  let Q (s t : Ω) := ∑ i, if next s i=t then q s i else 0
  have hb (s t) : |μ s*P s t-ν s*Q s t| ≤ |μ s-ν s| *P s t+ν s*|P s t-Q s t| := by
    have heq : μ s*P s t-ν s*Q s t=(μ s-ν s)*P s t+ν s*(P s t-Q s t) := by ring
    rw [heq]
    have h := abs_add_le ((μ s-ν s)*P s t) (ν s*(P s t-Q s t))
    have hP0 : 0 ≤ P s t := row_nonneg _ (hp s) (next s) t
    simpa only [abs_mul,abs_of_nonneg (hν s),abs_of_nonneg hP0] using h
  calc
    _ = ∑ t, |∑ s, (μ s*P s t-ν s*Q s t)| := by simp only [categoricalStep,P,Q,sum_sub_distrib]
    _ ≤ ∑ t, ∑ s, |μ s*P s t-ν s*Q s t| := sum_le_sum (fun t _ => abs_sum_le_sum_abs _ _)
    _ ≤ ∑ t, ∑ s, (|μ s-ν s| *P s t+ν s*|P s t-Q s t|) := sum_le_sum (fun t _ => sum_le_sum (fun s _ => hb s t))
    _ = (∑ s, |μ s-ν s|)+(∑ s, ν s*∑ t, |P s t-Q s t|) := by
      rw [sum_comm]; simp only [sum_add_distrib,← mul_sum,P,row_sum _ (hps _),mul_one]
    _ ≤ (∑ s, |μ s-ν s|)+(∑ s, ν s*ε) := by
      apply add_le_add le_rfl
      apply sum_le_sum; intro s _
      exact mul_le_mul_of_nonneg_left ((row_l1 (p s) (q s) (next s)).trans (he s)) (hν s)
    _ = _ := by rw [← sum_mul,hνs,one_mul]

lemma idealRun_prob {r : ℕ} (μ : Ω → ℚ) (hμ : ∀ s, 0 ≤ μ s) (hμs : ∑ s, μ s=1)
    (p : ℕ → Ω → Fin r → ℚ) (hp : ∀ n s i, 0 ≤ p n s i)
    (hs : ∀ n s, ∑ i, p n s i=1) (next : ℕ → Ω → Fin r → Ω) (n : ℕ) :
    (∀ s, 0 ≤ idealRun μ p next n s) ∧ ∑ s, idealRun μ p next n s=1 := by
  induction n with
  | zero => exact ⟨hμ,hμs⟩
  | succ n ih => exact ⟨step_nonneg _ ih.1 _ (hp n) _, step_sum _ ih.2 _ (hs n) _⟩




lemma bitRun_step_l1 {r : ℕ} (μ : Ω → ℚ) (hμ : ∀ s, 0 ≤ μ s)
    (hμs : ∑ s, μ s = 1) (p : ℕ → Ω → Fin r → ℚ)
    (hp : ∀ n s i, 0 ≤ p n s i) (hs : ∀ n s, ∑ i, p n s i = 1)
    (next : ℕ → Ω → Fin r → Ω) (k n : ℕ) :
    (∑ s, |bitRun μ p hs next k (n+1) s-idealRun μ p next (n+1) s|) ≤
    (∑ s, |bitRun μ p hs next k n s-idealRun μ p next n s|)+4*r/(2:ℚ)^k := by
  have hν := idealRun_prob μ hμ hμs p hp hs next n
  exact step_l1 (bitRun μ p hs next k n) (idealRun μ p next n) hν.1 hν.2
    (fun s => MatchingFPRAS.FiniteChoice.outputLaw (p n s) (hs n s) (pow_pos (by norm_num : 0 < (2:ℕ)) k))
    (p n) (fun s i => MatchingFPRAS.FiniteChoice.outputLaw_nonneg _ _ _ _)
    (fun s => MatchingFPRAS.FiniteChoice.outputLaw_sum _ _ _) (next n) (4*r/(2:ℚ)^k)
    (fun s => MatchingFPRAS.FiniteChoice.fixed_bit_l1 (p n s) (hp n s) (hs n s) k)




theorem finite_bit_simulation {r : ℕ} (μ : Ω → ℚ) (hμ : ∀ s, 0 ≤ μ s)
    (hμs : ∑ s, μ s = 1) (p : ℕ → Ω → Fin r → ℚ)
    (hp : ∀ n s i, 0 ≤ p n s i) (hs : ∀ n s, ∑ i, p n s i = 1)
    (next : ℕ → Ω → Fin r → Ω) (k n : ℕ) :
    (∑ s, |bitRun μ p hs next k n s-idealRun μ p next n s|)/2 ≤
      2*n*r/(2:ℚ)^k := by
  have hmain : ∑ s, |bitRun μ p hs next k n s-idealRun μ p next n s| ≤
      4*n*r/(2:ℚ)^k := by
    induction n with
    | zero => simp [bitRun,idealRun]
    | succ n ih =>
      have hh := bitRun_step_l1 μ hμ hμs p hp hs next k n
      calc
        _ ≤ (∑ s, |bitRun μ p hs next k n s-idealRun μ p next n s|)+4*r/(2:ℚ)^k := hh
        _ ≤ 4*n*r/(2:ℚ)^k+4*r/(2:ℚ)^k := add_le_add ih le_rfl
        _ = _ := by push_cast; ring
  calc
    _ ≤ (4*n*r/(2:ℚ)^k)/2 := div_le_div_of_nonneg_right hmain (by norm_num)
    _ = _ := by ring

end MatchingFPRAS.BoundedSimulation

namespace MatchingFPRAS.FiniteChoice

open Finset

def tapeIndex (k : ℕ) : (Fin k → Bool) ≃ Fin (2^k) :=
  (Equiv.piCongrRight (fun _ : Fin k => finTwoEquiv.symm)).trans finFunctionFinEquiv

def chooseBits {r : ℕ} (p : Fin r → ℚ) (hs : ∑ i, p i = 1) (k : ℕ)
    (bits : Fin k → Bool) : Fin r :=
  choose p hs (pow_pos (by norm_num : 0 < (2:ℕ)) k) (tapeIndex k bits)

def tapeLaw {r : ℕ} (p : Fin r → ℚ) (hs : ∑ i, p i = 1) (k : ℕ) (i : Fin r) : ℚ :=
  ((univ.filter (fun bits : Fin k → Bool => chooseBits p hs k bits=i)).card:ℚ)/(2:ℚ)^k

end MatchingFPRAS.FiniteChoice

end OAI
