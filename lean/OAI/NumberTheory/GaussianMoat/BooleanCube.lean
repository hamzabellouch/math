import OAI.NumberTheory.GaussianMoat.SignConcentration

namespace OAI

universe uIota

namespace GaussianMoat
open MeasureTheory ProbabilityTheory
open scoped NNReal

@[reducible] def Cube : ℕ → Type
  | 0 => Unit
  | n + 1 => Bool × Cube n
instance cubeFintype : (n : ℕ) → Fintype (Cube n)
  | 0 => inferInstanceAs (Fintype Unit)
  | n + 1 => @instFintypeProd Bool (Cube n) inferInstance (cubeFintype n)
instance cubeDecidableEq : (n : ℕ) → DecidableEq (Cube n)
  | 0 => inferInstanceAs (DecidableEq Unit)
  | n + 1 => @instDecidableEqProd Bool (Cube n) inferInstance (cubeDecidableEq n)
def cubeDist : (n : ℕ) → Cube n → Cube n → ℕ
  | 0, _, _ => 0
  | n + 1, (b,x), (c,y) => (if b = c then 0 else 1) + cubeDist n x y
@[simp] theorem cubeDist_self (n : ℕ) (x : Cube n) : cubeDist n x x = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => obtain ⟨b,x⟩ := x; simp [cubeDist, ih]
@[simp] theorem cubeDist_zero_iff (n : ℕ) (x y : Cube n) : cubeDist n x y = 0 ↔ x = y := by
  induction n with
  | zero => simp only [cubeDist]
  | succ n ih =>
    obtain ⟨b,x⟩ := x
    obtain ⟨c,y⟩ := y
    by_cases h : b = c <;> simp [cubeDist, h, ih, Prod.mk.injEq]
theorem cubeDist_symm (n : ℕ) (x y : Cube n) : cubeDist n x y = cubeDist n y x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    obtain ⟨b,x⟩ := x
    obtain ⟨c,y⟩ := y
    simp [cubeDist, eq_comm (a := b) (b := c), ih x y]
theorem cubeDist_triangle (n : ℕ) (x y z : Cube n) :
    cubeDist n x z ≤ cubeDist n x y + cubeDist n y z := by
  induction n with
  | zero => simp [cubeDist]
  | succ n ih =>
    obtain ⟨b,x⟩ := x
    obtain ⟨c,y⟩ := y
    obtain ⟨d,z⟩ := z
    have h := ih x y z
    cases b <;> cases c <;> cases d <;> simp [cubeDist] <;> omega

noncomputable def cubeSize {n : ℕ} (S : Cube n → Prop) : ℕ := by
  classical
  exact ∑ x, if S x then 1 else 0
noncomputable def cubeBoundary {n : ℕ} (S : Cube n → Prop) : ℕ := by
  classical
  exact ∑ x, ∑ y, if S x ∧ ¬ S y ∧ cubeDist n x y = 1 then 1 else 0
noncomputable def cubeCross {n : ℕ} (A B : Cube n → Prop) : ℕ := by
  classical
  exact ∑ x, if A x ∧ ¬ B x then 1 else 0

theorem cubeSize_succ {n : ℕ} (S : Cube (n+1) → Prop) :
    cubeSize S = cubeSize (fun x => S (false,x)) + cubeSize (fun x => S (true,x)) := by
  classical
  simp only [cubeSize, Fintype.sum_prod_type, Fintype.sum_bool]
  ac_rfl

theorem cubeBoundary_succ {n : ℕ} (S : Cube (n+1) → Prop) :
    cubeBoundary S = cubeBoundary (fun x => S (false,x)) + cubeBoundary (fun x => S (true,x)) +
      cubeCross (fun x => S (false,x)) (fun x => S (true,x)) +
      cubeCross (fun x => S (true,x)) (fun x => S (false,x)) := by
  classical
  simp only [cubeBoundary, cubeCross, Fintype.sum_prod_type, Fintype.sum_bool, cubeDist,
    Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte, zero_add, Nat.add_eq_left,
    cubeDist_zero_iff, Finset.sum_add_distrib]
  simp only [and_assoc, and_left_comm, and_comm, ite_and, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  omega

theorem cubeCross_card_le {n : ℕ} (A B : Cube n → Prop) : cubeSize A ≤ cubeSize B + cubeCross A B := by
  classical
  rw [cubeSize, cubeSize, cubeCross, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro x _
  by_cases ha : A x <;> by_cases hb : B x <;> simp [ha, hb]

theorem cube_degree (n : ℕ) (x : Cube n) : (∑ y, if cubeDist n x y = 1 then 1 else 0) = n := by
  classical
  induction n with
  | zero => simp [cubeDist]
  | succ n ih =>
    obtain ⟨b,x⟩ := x
    cases b <;> simp only [Fintype.sum_prod_type, Fintype.sum_bool, cubeDist,
      Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte, zero_add, Nat.add_eq_left,
      cubeDist_zero_iff, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, ih]
    omega

theorem binEntropy_ge_two_mul {p : ℝ} (hp0 : 0 ≤ p) (hp2 : p ≤ 1/2) :
    2 * p * Real.log 2 ≤ Real.binEntropy p := by
  have hc : ConcaveOn ℝ (Set.Icc 0 1) Real.binEntropy := Real.strictConcave_binEntropy.concaveOn
  have h := hc.2 (show (0 : ℝ) ∈ Set.Icc 0 1 by norm_num)
    (show (2 : ℝ)⁻¹ ∈ Set.Icc 0 1 by norm_num)
    (show 0 ≤ 1 - 2*p by linarith) (show 0 ≤ 2*p by positivity) (by ring)
  simpa only [smul_eq_mul, Real.binEntropy_zero, Real.binEntropy_two_inv,
    mul_zero, zero_add, show 2*p*(2:ℝ)⁻¹ = p by ring] using h

theorem entropy_merge_of_le {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    2 * a * Real.log 2 ≤ (a+b)*Real.log (a+b) - a*Real.log a - b*Real.log b := by
  by_cases ha0 : a = 0
  · simp [ha0]
  have hap : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
  have hbp : 0 < b := hap.trans_le hab
  have ht : 0 < a+b := by positivity
  have hp0 : 0 ≤ a/(a+b) := by positivity
  have hp2 : a/(a+b) ≤ 1/2 := (div_le_iff₀ ht).mpr (by linarith)
  have h := mul_le_mul_of_nonneg_left (binEntropy_ge_two_mul hp0 hp2) ht.le
  have heq : (a+b) * Real.binEntropy (a/(a+b)) =
      (a+b)*Real.log (a+b) - a*Real.log a - b*Real.log b := by
    have hsub : 1-a/(a+b) = b/(a+b) := by field_simp; ring
    rw [Real.binEntropy, hsub, Real.log_inv, Real.log_inv,
      Real.log_div hap.ne' ht.ne', Real.log_div hbp.ne' ht.ne']
    field_simp
    ring
  rw [heq] at h
  have heq' : (a+b) * (2 * (a/(a+b)) * Real.log 2) = 2*a*Real.log 2 := by
    field_simp
  rwa [heq'] at h

theorem entropy_merge {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    2 * min a b * Real.log 2 ≤ (a+b)*Real.log (a+b) - a*Real.log a - b*Real.log b := by
  rcases le_total a b with hab | hba
  · simpa [min_eq_left hab] using entropy_merge_of_le ha hab
  · have h := entropy_merge_of_le hb hba
    rw [min_eq_right hba]
    convert h using 1
    rw [add_comm b a]
    ring

theorem cube_edge_isoperimetric (n : ℕ) (S : Cube n → Prop) :
    (cubeSize S : ℝ) * ((n : ℝ) * Real.log 2 - Real.log (cubeSize S)) ≤
      (cubeBoundary S : ℝ) * Real.log 2 := by
  classical
  induction n with
  | zero =>
    by_cases hs : S () <;> simp [cubeSize, cubeBoundary, cubeDist, hs]
  | succ n ih =>
    have h0 := ih (fun x => S (false,x))
    have h1 := ih (fun x => S (true,x))
    have hac := cubeCross_card_le (fun x => S (false,x)) (fun x => S (true,x))
    have hbc := cubeCross_card_le (fun x => S (true,x)) (fun x => S (false,x))
    have hac' : (cubeSize (fun x => S (false,x)) : ℝ) ≤
        cubeSize (fun x => S (true,x)) + cubeCross (fun x => S (false,x)) (fun x => S (true,x)) := by
      exact_mod_cast hac
    have hbc' : (cubeSize (fun x => S (true,x)) : ℝ) ≤
        cubeSize (fun x => S (false,x)) + cubeCross (fun x => S (true,x)) (fun x => S (false,x)) := by
      exact_mod_cast hbc
    have he := entropy_merge (a := (cubeSize (fun x => S (false,x)) : ℝ))
      (b := (cubeSize (fun x => S (true,x)) : ℝ)) (by positivity) (by positivity)
    have hl : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    rw [cubeSize_succ, cubeBoundary_succ]
    push_cast
    rcases le_total (cubeSize (fun x => S (false,x)) : ℝ) (cubeSize (fun x => S (true,x)) : ℝ) with hab | hba
    · rw [min_eq_left hab] at he
      have hn : (0 : ℝ) ≤ cubeCross (fun x => S (false,x)) (fun x => S (true,x)) := by positivity
      nlinarith
    · rw [min_eq_right hba] at he
      have hn : (0 : ℝ) ≤ cubeCross (fun x => S (true,x)) (fun x => S (false,x)) := by positivity
      nlinarith

def cubeExpand {n : ℕ} (S : Cube n → Prop) (y : Cube n) : Prop :=
  S y ∨ ∃ x, S x ∧ cubeDist n x y = 1

def cubeExpandIter {n : ℕ} (S : Cube n → Prop) : ℕ → Cube n → Prop
  | 0 => S
  | h+1 => cubeExpand (cubeExpandIter S h)

theorem cubeSize_mono {n : ℕ} {S T : Cube n → Prop} (h : ∀ x, S x → T x) :
    cubeSize S ≤ cubeSize T := by
  classical
  apply Finset.sum_le_sum
  intro x _
  by_cases hs : S x
  · simp [hs, h x hs]
  · simp [hs]

theorem cube_card (n : ℕ) : Fintype.card (Cube n) = 2^n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change Fintype.card (Bool × Cube n) = _
    rw [Fintype.card_prod, Fintype.card_bool, ih, pow_succ]
    omega

theorem cubeSize_le (n : ℕ) (S : Cube n → Prop) : cubeSize S ≤ 2^n := by
  classical
  calc
    cubeSize S ≤ ∑ _ : Cube n, 1 := by
      apply Finset.sum_le_sum
      intro x _
      split_ifs <;> omega
    _ = 2^n := by simp [cube_card]

theorem cubeBoundary_expand_bound {n : ℕ} (S : Cube n → Prop) :
    cubeBoundary S + n * cubeSize S ≤ n * cubeSize (cubeExpand S) := by
  classical
  have hdegree (y : Cube n) :
      (∑ x, if S x ∧ ¬ S y ∧ cubeDist n x y = 1 then 1 else 0) ≤
        n * (if ¬S y ∧ (∃ x, S x ∧ cubeDist n x y = 1) then 1 else 0) := by
    by_cases hy : ¬S y ∧ (∃ x, S x ∧ cubeDist n x y = 1)
    · rw [ite_eq_left hy, mul_one]
      calc
        _ ≤ ∑ x, if cubeDist n y x = 1 then 1 else 0 := by
          apply Finset.sum_le_sum
          intro x _
          by_cases h : S x ∧ ¬ S y ∧ cubeDist n x y = 1
          · simp [h, cubeDist_symm n y x]
          · simp [h]
        _ = n := cube_degree n y
    · simp only [hy, ↓reduceIte, mul_zero, Nat.le_zero]
      apply Finset.sum_eq_zero
      intro x _
      have hnot : ¬(S x ∧ ¬S y ∧ cubeDist n x y = 1) := by
        rintro ⟨hs, hns, hd⟩
        exact hy ⟨hns,x,hs,hd⟩
      simp [hnot]
  have hb := Finset.sum_le_sum (s := Finset.univ) (fun y _ => hdegree y)
  rw [← Finset.mul_sum] at hb
  have heq : cubeSize (cubeExpand S) = cubeSize S +
      ∑ y, if ¬S y ∧ (∃ x, S x ∧ cubeDist n x y = 1) then 1 else 0 := by
    rw [cubeSize, cubeSize, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro y _
    by_cases hs : S y <;> simp [cubeExpand, hs]
  unfold cubeBoundary
  rw [Finset.sum_comm, heq, Nat.mul_add]
  omega

theorem cubeExpandIter_witness {n h : ℕ} {S : Cube n → Prop} {x : Cube n}
    (hx : cubeExpandIter S h x) : ∃ y, S y ∧ cubeDist n y x ≤ h := by
  induction h generalizing x with
  | zero => exact ⟨x,hx,by simp⟩
  | succ h ih =>
    rcases hx with hx | ⟨z,hz,hzx⟩
    · obtain ⟨y,hy,hyx⟩ := ih hx
      exact ⟨y,hy,by omega⟩
    · obtain ⟨y,hy,hyz⟩ := ih hz
      exact ⟨y,hy,by have ht := cubeDist_triangle n y z x; omega⟩

theorem cubeExpandIter_disjoint {n h : ℕ} {S T : Cube n → Prop}
    (hsep : ∀ x, S x → ∀ y, T y → 2*h < cubeDist n x y) :
    ∀ x, ¬(cubeExpandIter S h x ∧ cubeExpandIter T h x) := by
  rintro x ⟨hs,ht⟩
  obtain ⟨y,hy,hyx⟩ := cubeExpandIter_witness hs
  obtain ⟨z,hz,hzx⟩ := cubeExpandIter_witness ht
  have h := hsep y hy z hz
  have htri := cubeDist_triangle n y x z
  rw [cubeDist_symm n x z] at htri
  omega

theorem cubeSize_sum_le {n : ℕ} {ι : Type uIota} [Fintype ι] (S : ι → Cube n → Prop)
    (hd : ∀ i j, i ≠ j → ∀ x, ¬(S i x ∧ S j x)) :
    ∑ i, cubeSize (S i) ≤ 2^n := by
  classical
  unfold cubeSize
  rw [Finset.sum_comm]
  calc
    _ ≤ ∑ _ : Cube n, 1 := by
      apply Finset.sum_le_sum
      intro x _
      by_cases he : ∃ i, S i x
      · obtain ⟨i,hi⟩ := he
        rw [Finset.sum_eq_single i]
        · simp [hi]
        · intro j _ hji
          have hnot : ¬S j x := fun hj => hd j i hji x ⟨hj,hi⟩
          simp [hnot]
        · simp
      · have hh : ∀ i, ¬S i x := by simpa only [not_exists] using he
        simp [hh]
    _ = 2^n := by simp [cube_card]

theorem cube_growth {n : ℕ} (hn : 0 < n) (S : Cube n → Prop) {a E : ℝ}
    (hE : 0 < E) (hlogE : Real.log E ≤ (n : ℝ) * Real.log 2 - a)
    (hsize : (cubeSize S : ℝ) ≤ E) :
    (1 + a / ((n : ℝ) * Real.log 2)) * cubeSize S ≤ cubeSize (cubeExpand S) := by
  by_cases hz : cubeSize S = 0
  · simp [hz]
  have hpos : (0 : ℝ) < cubeSize S := by exact_mod_cast Nat.pos_of_ne_zero hz
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hlogtwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hden : 0 < (n : ℝ) * Real.log 2 := mul_pos hnpos hlogtwo
  have hl := ((Real.log_le_log_iff hpos hE).mpr hsize).trans hlogE
  have hi := cube_edge_isoperimetric n S
  have hb : (cubeBoundary S : ℝ) + n * cubeSize S ≤ n * cubeSize (cubeExpand S) := by
    exact_mod_cast cubeBoundary_expand_bound S
  apply (mul_le_mul_iff_left₀ hden).mp
  field_simp at ⊢
  nlinarith [mul_le_mul_of_nonneg_left hl hpos.le,
    mul_le_mul_of_nonneg_right hb hlogtwo.le]

theorem cube_iter_growth {n : ℕ} (S : Cube n → Prop) {δ E : ℝ} (hδ : 0 ≤ δ)
    (hgrow : ∀ T : Cube n → Prop, (cubeSize T : ℝ) ≤ E →
      (1+δ)*cubeSize T ≤ cubeSize (cubeExpand T)) (h : ℕ) :
    min E ((1+δ)^h * cubeSize S) ≤ cubeSize (cubeExpandIter S h) := by
  induction h with
  | zero => simpa only [pow_zero, one_mul, cubeExpandIter] using
      (min_le_right E (cubeSize S : ℝ))
  | succ h ih =>
    have hmono : (cubeSize (cubeExpandIter S h) : ℝ) ≤ cubeSize (cubeExpandIter S (h+1)) := by
      exact_mod_cast cubeSize_mono (S := cubeExpandIter S h) (T := cubeExpand (cubeExpandIter S h))
        (fun _ hx => Or.inl hx)
    by_cases hlarge : E ≤ (cubeSize (cubeExpandIter S h) : ℝ)
    · exact (min_le_left _ _).trans (hlarge.trans hmono)
    · have hsmall : (cubeSize (cubeExpandIter S h) : ℝ) ≤ E := le_of_not_ge hlarge
      have hpow : (1+δ)^h * cubeSize S ≤ E := by
        by_contra hnot
        rw [min_eq_left (le_of_not_ge hnot)] at ih
        exact hlarge ih
      rw [min_eq_right hpow] at ih
      have hmul := mul_le_mul_of_nonneg_left ih (by linarith : 0 ≤ 1+δ)
      have hg := hgrow (cubeExpandIter S h) hsmall
      apply (min_le_right _ _).trans
      simpa only [pow_succ, mul_assoc, mul_left_comm, cubeExpandIter] using hmul.trans hg

theorem cube_separated_bound {n h : ℕ} (hn : 0 < n) {ι : Type uIota} [Fintype ι]
    (S : ι → Cube n → Prop) {a E A : ℝ} (ha : 0 ≤ a) (hE : 0 < E)
    (hlogE : Real.log E ≤ (n : ℝ) * Real.log 2 - a)
    (hseed : ∀ i, A * cubeSize (S i) ≤ E)
    (hfactor : A ≤ (1 + a / ((n : ℝ)*Real.log 2))^h)
    (hsep : ∀ i j, i ≠ j → ∀ x, S i x → ∀ y, S j y → 2*h < cubeDist n x y) :
    A * (∑ i, (cubeSize (S i) : ℝ)) ≤ (2 : ℝ)^n := by
  have hδ : 0 ≤ a / ((n : ℝ)*Real.log 2) := by
    apply div_nonneg ha
    exact mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by norm_num))
  have hlarge (i : ι) : A * cubeSize (S i) ≤ cubeSize (cubeExpandIter (S i) h) := by
    apply le_trans (le_min (hseed i) (mul_le_mul_of_nonneg_right hfactor (Nat.cast_nonneg _)))
    exact cube_iter_growth (S i) hδ (fun T ht => cube_growth hn T hE hlogE ht) h
  rw [Finset.mul_sum]
  apply (Finset.sum_le_sum (fun i _ => hlarge i)).trans
  have hd : ∀ i j, i ≠ j → ∀ x, ¬(cubeExpandIter (S i) h x ∧ cubeExpandIter (S j) h x) := by
    intro i j hij
    exact cubeExpandIter_disjoint (hsep i j hij)
  exact_mod_cast cubeSize_sum_le (fun i => cubeExpandIter (S i) h) hd

end GaussianMoat

end OAI
