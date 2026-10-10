import OAI.MathematicalPhysics.AlternatingFlow.ProfileNames

namespace OAI

section RecursiveBoundsDevelopment

open scoped BigOperators Topology ContDiff
open Filter

namespace AlternatingNS.Effective
attribute [local instance] Arithmetic.rationalCoding

lemma nat_sum_range {A : Type*} [Primcodable A] {f : A → ℕ → ℕ} (hf : Computable₂ f) :
    Computable₂ (fun a n => ∑ i ∈ Finset.range n, f a i) := by
  have hs : Computable₂ (fun a : A => fun z : ℕ × ℕ => z.2 + f a z.1) :=
    Primrec.nat_add.to_comp.comp (Computable.snd.comp Computable.snd)
      (hf.comp Computable.fst (Computable.fst.comp Computable.snd))
  have h := Computable.nat_rec (Computable.snd : Computable (fun z : A × ℕ => z.2))
    (Computable.const (0 : ℕ))
    (hs.comp (Computable.fst.comp Computable.fst) Computable.snd).to₂
  refine h.to₂.of_eq ?_
  rintro ⟨a,n⟩
  induction n with
  | zero => simp
  | succ n ih => simp only [Finset.sum_range_succ, ih]

def Scaled {A E F : Type*} [Primcodable A] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (s : A → ℕ → ℝ) (f : A → ℕ → E → F) : Prop :=
  (∀ a n, ContDiff ℝ ∞ (f a n)) ∧ ∃ B : A × ℕ → ℕ, Computable B ∧
    ∀ a r n x, ‖iteratedFDeriv ℝ r (f a n) x‖ ≤ (B (a,r) : ℝ) * s a n ^ r

variable {A A' E F G : Type*} [Primcodable A] [Primcodable A']
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

lemma Scaled.congr {s : A → ℕ → ℝ} {f g : A → ℕ → E → F} (hf : Scaled s f)
    (he : ∀ a n x, f a n x = g a n x) : Scaled s g := by
  rwa [← show f = g from funext (fun a => funext (fun n => funext (he a n)))]

lemma Scaled.param {s : A → ℕ → ℝ} {f : A → ℕ → E → F} (hf : Scaled s f)
    (g : A' → A) (hg : Computable g) : Scaled (fun a => s (g a)) (fun a => f (g a)) := by
  obtain ⟨hf,B,hB,h⟩ := hf
  exact ⟨fun a n => hf (g a) n, fun z => B (g z.1,z.2),
    hB.comp ((hg.comp Computable.fst).pair Computable.snd), fun a => h (g a)⟩

lemma Scaled.const {s : A → ℕ → ℝ} (hs : ∀ a n, 0 ≤ s a n) (f : A → ℕ → F)
    (B : A → ℕ) (hB : Computable B) (h : ∀ a n, ‖f a n‖ ≤ B a) :
    Scaled s (fun a n (_ : E) => f a n) := by
  refine ⟨fun _ _ => contDiff_const, fun z => B z.1, hB.comp Computable.fst, ?_⟩
  intro a r n x
  cases r with
  | zero => simpa using h a n
  | succ r =>
    rw [iteratedFDeriv_const_of_ne (Nat.succ_ne_zero _), Pi.zero_apply, norm_zero]
    exact mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (hs a n) _)

lemma Scaled.add {s : A → ℕ → ℝ} {f g : A → ℕ → E → F}
    (hf : Scaled s f) (hg : Scaled s g) : Scaled s (fun a n x => f a n x + g a n x) := by
  obtain ⟨sf,Bf,hA,hfa⟩ := hf
  obtain ⟨sg,B,hB,hgb⟩ := hg
  refine ⟨fun a n => (sf a n).add (sg a n), fun z => Bf z + B z,
    Primrec.nat_add.to_comp.comp hA hB, fun a r n x => ?_⟩
  rw [fun_iteratedFDeriv_add_apply ((sf a n).of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt
    ((sg a n).of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt]
  push_cast
  exact (norm_add_le _ _).trans (by linarith [hfa a r n x, hgb a r n x])

lemma Scaled.sub {s : A → ℕ → ℝ} {f g : A → ℕ → E → F}
    (hf : Scaled s f) (hg : Scaled s g) : Scaled s (fun a n x => f a n x - g a n x) := by
  obtain ⟨sf,Bf,hA,hfa⟩ := hf
  obtain ⟨sg,B,hB,hgb⟩ := hg
  refine ⟨fun a n => (sf a n).sub (sg a n), fun z => Bf z + B z,
    Primrec.nat_add.to_comp.comp hA hB, fun a r n x => ?_⟩
  rw [fun_iteratedFDeriv_sub_apply ((sf a n).of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt
    ((sg a n).of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt]
  push_cast
  exact (norm_sub_le _ _).trans (by linarith [hfa a r n x, hgb a r n x])

lemma Scaled.smul {s : A → ℕ → ℝ} (_ : ∀ a n, 0 ≤ s a n) {f : A → ℕ → E → F}
    (hf : Scaled s f) (c : A → ℕ → ℝ) (B : A → ℕ) (hB : Computable B)
    (hc : ∀ a n, |c a n| ≤ B a) : Scaled s (fun a n x => c a n • f a n x) := by
  obtain ⟨sf,C,hC,hfC⟩ := hf
  refine ⟨fun a n => contDiff_const.smul (sf a n), fun z => B z.1 * C z,
    Primrec.nat_mul.to_comp.comp (hB.comp Computable.fst) hC, fun a r n x => ?_⟩
  rw [iteratedFDeriv_const_smul_apply' ((sf a n).of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt,
    norm_smul, Real.norm_eq_abs]
  push_cast
  calc
    _ ≤ (B a : ℝ) * ((C (a,r) : ℝ) * s a n ^ r) := by gcongr; exact hc a n; exact hfC a r n x
    _ = _ := by ring

lemma Scaled.mul {s : A → ℕ → ℝ} (hs : ∀ a n, 0 ≤ s a n) {f g : A → ℕ → E → ℝ}
    (hf : Scaled s f) (hg : Scaled s g) : Scaled s (fun a n x => f a n x * g a n x) := by
  obtain ⟨sf,Bf,hA,hfa⟩ := hf
  obtain ⟨sg,B,hB,hgb⟩ := hg
  let C (z : A × ℕ) := ∑ i ∈ Finset.range (z.2+1), z.2.choose i * Bf (z.1,i) * B (z.1,z.2-i)
  have hi : Computable₂ (fun z : A × ℕ => fun i : ℕ => z.2.choose i * Bf (z.1,i) * B (z.1,z.2-i)) :=
    Primrec.nat_mul.to_comp.comp
      (Primrec.nat_mul.to_comp.comp
        (choose.to_comp.comp (Computable.snd.comp Computable.fst) Computable.snd)
        (hA.comp ((Computable.fst.comp Computable.fst).pair Computable.snd)))
      (hB.comp ((Computable.fst.comp Computable.fst).pair
        (Primrec.nat_sub.to_comp.comp (Computable.snd.comp Computable.fst) Computable.snd)))
  have hC : Computable C := (nat_sum_range hi).comp Computable.id
    (Computable.succ.comp Computable.snd)
  refine ⟨fun a n => (sf a n).mul (sg a n), C, hC, fun a r n x => ?_⟩
  apply (norm_iteratedFDeriv_mul_le (sf a n) (sg a n) x
    (WithTop.coe_le_coe.mpr le_top : (r : ℕ∞ω) ≤ ∞)).trans
  calc
    _ ≤ ∑ i ∈ Finset.range (r+1),
          (r.choose i : ℝ) * (Bf (a,i) * s a n ^ i) * (B (a,r-i) * s a n ^ (r-i)) := by
      apply Finset.sum_le_sum
      intro i hi
      gcongr
      · exact mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (hs a n) _))
      · exact hfa a i n x
      · exact hgb a (r-i) n x
    _ = _ := by
      simp only [C, Nat.cast_sum, Nat.cast_mul, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      have hir : i ≤ r := by simpa using Finset.mem_range.mp hi
      rw [show (r.choose i : ℝ) * (Bf (a,i) * s a n ^ i) * (B (a,r-i) * s a n ^ (r-i)) =
        (r.choose i * Bf (a,i) * B (a,r-i)) * (s a n ^ i * s a n ^ (r-i)) by ring,
        ← pow_add, Nat.add_sub_of_le hir]

lemma Scaled.ite {s : A → ℕ → ℝ} (hs : ∀ a n, 0 ≤ s a n) {f g : A → ℕ → E → F}
    (hf : Scaled s f) (hg : Scaled s g) (p : A → ℕ → Prop) [DecidableRel p] :
    Scaled s (fun a n => if p a n then f a n else g a n) := by
  obtain ⟨sf,Bf,hA,hfa⟩ := hf
  obtain ⟨sg,B,hB,hgb⟩ := hg
  refine ⟨fun a n => by dsimp only; split_ifs <;> [exact sf a n; exact sg a n],
    fun z => Bf z + B z, Primrec.nat_add.to_comp.comp hA hB, fun a r n x => ?_⟩
  dsimp only
  split_ifs
  · exact (hfa a r n x).trans (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.le_add_right _ _) (pow_nonneg (hs a n) _))
  · exact (hgb a r n x).trans (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.le_add_left _ _) (pow_nonneg (hs a n) _))

lemma Scaled.sum_range {s : A → ℕ → ℝ} (_ : ∀ a n, 0 ≤ s a n)
    {f : (A × ℕ) → ℕ → E → F} (hf : Scaled (fun a => s a.1) f)
    (N : A → ℕ) (hN : Computable N) : Scaled s (fun a n x => ∑ i ∈ Finset.range (N a), f (a,i) n x) := by
  obtain ⟨sf,B,hB,hfB⟩ := hf
  have hi : Computable₂ (fun z : A × ℕ => fun i : ℕ => B ((z.1,i),z.2)) :=
    hB.comp (((Computable.fst.comp Computable.fst).pair Computable.snd).pair
      (Computable.snd.comp Computable.fst))
  refine ⟨fun a n => ContDiff.sum fun i _ => sf (a,i) n,
    fun z => ∑ i ∈ Finset.range (N z.1), B ((z.1,i),z.2),
    (nat_sum_range hi).comp Computable.id (hN.comp Computable.fst), fun a r n x => ?_⟩
  rw [iteratedFDeriv_fun_sum_apply (fun i _ => ((sf (a,i) n).of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt)]
  apply (norm_sum_le _ _).trans
  simp only [Nat.cast_sum, Finset.sum_mul]
  exact Finset.sum_le_sum (fun i _ => hfB (a,i) r n x)

lemma Scaled.comp {s : A → ℕ → ℝ} (hs : ∀ a n, 0 ≤ s a n) {f : A → ℕ → E → F}
    (hf : Scaled s f) {g : A → F → G} (hg : Scaled (fun _ _ => 1) (fun a _ => g a)) :
    Scaled s (fun a n => g a ∘ f a n) := by
  obtain ⟨sf,Bf,hA,hfa⟩ := hf
  obtain ⟨sg,B,hB,hgb⟩ := hg
  let C (z : A × ℕ) := ∑ i ∈ Finset.range (z.2+1), B (z.1,i)
  let D (z : A × ℕ) := 1 + ∑ i ∈ Finset.range (z.2+1), Bf (z.1,i)
  have hC : Computable C := (nat_sum_range hB.to₂).comp Computable.fst
    (Computable.succ.comp Computable.snd)
  have hD : Computable D := Primrec.nat_add.to_comp.comp (Computable.const 1)
    ((nat_sum_range hA.to₂).comp Computable.fst (Computable.succ.comp Computable.snd))
  refine ⟨fun a n => (sg a 0).comp (sf a n), fun z => z.2.factorial * C z * D z ^ z.2,
    Primrec.nat_mul.to_comp.comp
      (Primrec.nat_mul.to_comp.comp (factorial.to_comp.comp Computable.snd) hC)
      (nat_pow.to_comp.comp hD Computable.snd), fun a r n x => ?_⟩
  have hDone : (1 : ℝ) ≤ D (a,r) := by dsimp [D]; exact_mod_cast Nat.le_add_right 1 _
  have h := norm_iteratedFDeriv_comp_le (sg a 0) (sf a n)
    (WithTop.coe_le_coe.mpr le_top : (r : ℕ∞ω) ≤ ∞) x
    (C := (C (a,r) : ℝ)) (D := (D (a,r) : ℝ) * s a n) ?_ ?_
  · simpa only [Nat.cast_mul, Nat.cast_pow, mul_pow, mul_assoc] using h
  · intro i hi
    have hle : B (a,i) ≤ C (a,r) := Finset.single_le_sum (s := Finset.range (r+1)) (f := fun i => B (a,i)) (fun i _ => Nat.zero_le _)
      (Finset.mem_range.mpr (by omega))
    have ht : ‖iteratedFDeriv ℝ i (g a) (f a n x)‖ ≤ (B (a,i) : ℝ) := by simpa using hgb a i 0 (f a n x)
    exact ht.trans (by exact_mod_cast hle)
  · intro i hi hir
    have hai : (Bf (a,i) : ℝ) ≤ D (a,r) := by
      have h := Finset.single_le_sum (s := Finset.range (r+1)) (f := fun i => Bf (a,i))
        (fun i _ => Nat.zero_le _) (Finset.mem_range.mpr (by omega : i < r+1))
      exact_mod_cast (by dsimp [D]; omega : Bf (a,i) ≤ D (a,r))
    have hai' := hai.trans (le_self_pow₀ hDone (by omega : i ≠ 0))
    calc
      _ ≤ (Bf (a,i) : ℝ) * s a n ^ i := hfa a i n x
      _ ≤ (D (a,r) : ℝ) ^ i * s a n ^ i := mul_le_mul_of_nonneg_right hai' (pow_nonneg (hs a n) _)
      _ = _ := (mul_pow _ _ _).symm

lemma Scaled.comp_linear {s : A → ℕ → ℝ} (hs : ∀ a n, 0 ≤ s a n) {f : A → ℕ → E → F}
    (hf : Scaled s f) (L : A → ℕ → G →L[ℝ] E) (B : A → ℕ) (hB : Computable B)
    (hL : ∀ a n, ‖L a n‖ ≤ B a) : Scaled s (fun a n => f a n ∘ L a n) := by
  obtain ⟨sf,C,hC,hfC⟩ := hf
  refine ⟨fun a n => (sf a n).comp (L a n).contDiff, fun z => C z * B z.1 ^ z.2,
    Primrec.nat_mul.to_comp.comp hC (nat_pow.to_comp.comp (hB.comp Computable.fst) Computable.snd),
    fun a r n x => ?_⟩
  apply (Bounds.norm_comp_linear (f a n) (sf a n) (L a n) r x).trans
  push_cast
  calc
    _ ≤ ((C (a,r) : ℝ) * s a n ^ r) * (B a : ℝ) ^ r := by
      gcongr
      · exact mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (hs a n) _)
      · exact hfC a r n _
      · exact hL a n
    _ = _ := by ring

lemma Scaled.comp_scaled_linear {s : A → ℕ → ℝ} (_ : ∀ a n, 0 ≤ s a n) {f : A → E → F}
    (hf : Scaled (fun _ _ => 1) (fun a _ => f a))
    (L : A → ℕ → G →L[ℝ] E) (hL : ∀ a n, ‖L a n‖ ≤ s a n) :
    Scaled s (fun a n => f a ∘ L a n) := by
  obtain ⟨sf,B,hB,hfB⟩ := hf
  refine ⟨fun a n => (sf a 0).comp (L a n).contDiff, B,hB, fun a r n x => ?_⟩
  apply (Bounds.norm_comp_linear (f a) (sf a 0) (L a n) r x).trans
  apply mul_le_mul (by simpa using hfB a r 0 (L a n x)) (pow_le_pow_left₀ (norm_nonneg _) (hL a n) _)
    (by positivity) (by positivity)

lemma Scaled.fixed {s : A → ℕ → ℝ} (hs : ∀ a n, 1 ≤ s a n) {f : A → E → F}
    (hf : Scaled (fun _ _ => 1) (fun a _ => f a)) : Scaled s (fun a _ => f a) := by
  obtain ⟨sf,B,hB,hfB⟩ := hf
  refine ⟨sf,B,hB,fun a r n x => ?_⟩
  have h : ‖iteratedFDeriv ℝ r (f a) x‖ ≤ (B (a,r) : ℝ) := by simpa using hfB a r n x
  exact h.trans (le_mul_of_one_le_right (Nat.cast_nonneg _) (one_le_pow₀ (hs a n)))

end AlternatingNS.Effective

end RecursiveBoundsDevelopment

end OAI
