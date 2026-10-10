import OAI.MathematicalPhysics.AlternatingFlow.DerivativeBounds
import OAI.MathematicalPhysics.AlternatingFlow.Arithmetic

namespace OAI

section NamesDevelopment

open scoped BigOperators Topology ContDiff
open Filter

namespace AlternatingNS.Effective

attribute [local instance] Arithmetic.rationalCoding

def tolerance (n : ℕ) : ℚ := (1 / 2 : ℚ) ^ n

lemma tolerance_cast (n : ℕ) : (tolerance n : ℝ) = dyadicError n := by
  simp [tolerance, dyadicError]

lemma tolerance_primrec : Primrec tolerance :=
  Arithmetic.rat_pow.comp (Primrec.const (1 / 2)) Primrec.id

lemma tolerance_pos (n : ℕ) : (0 : ℝ) < tolerance n := by
  rw [tolerance_cast]; exact pow_pos (by norm_num) _

lemma tolerance_tendsto : Tendsto (fun n => (tolerance n : ℝ)) atTop (𝓝 0) := by
  simp only [tolerance_cast, dyadicError]
  exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)

def Named {A : Type*} [Primcodable A] (f : A → ℝ) : Prop :=
  ∃ a : A × ℕ → ℚ, Computable a ∧
    ∀ x n, |f x - (a (x,n) : ℝ)| ≤ tolerance n

lemma computable_find {A : Type*} [Primcodable A] (p : A → ℕ → Prop)
    [DecidableRel p] (hp : Computable (fun z : A × ℕ => decide (p z.1 z.2)))
    (h : ∀ a, ∃ n, p a n) : Computable (fun a => @Nat.find (p a) (fun _ => inferInstance) (h a)) := by
  have hr : Partrec (fun a => Nat.rfind (fun n => Part.some (decide (p a n)))) :=
    Partrec.rfind hp.to₂.partrec₂
  apply hr.of_eq_tot
  intro a
  apply Nat.mem_rfind.mpr
  refine ⟨?_, fun {m} hm => ?_⟩
  · simp [Nat.find_spec (h a)]
  · simp [Nat.find_min (h a) hm]

lemma Named.of_certificate {A : Type*} [Primcodable A] (f : A → ℝ)
    (a e : A × ℕ → ℚ) (ha : Computable a) (he : Computable e)
    (hbound : ∀ x n, |f x - (a (x,n) : ℝ)| ≤ (e (x,n) : ℝ))
    (hlim : ∀ x, Tendsto (fun n => (e (x,n) : ℝ)) atTop (𝓝 0)) : Named f := by
  classical
  let p (z : A × ℕ) (n : ℕ) : Prop := e (z.1,n) ≤ tolerance z.2
  have hp : Computable (fun z : (A × ℕ) × ℕ => decide (p z.1 z.2)) :=
    Arithmetic.rat_le.decide.to_comp.comp
      (he.comp ((Computable.fst.comp Computable.fst).pair Computable.snd))
      (tolerance_primrec.to_comp.comp (Computable.snd.comp Computable.fst))
  have hex (z : A × ℕ) : ∃ n, p z n := by
    have hE := (hlim z.1).eventually (gt_mem_nhds (tolerance_pos z.2))
    obtain ⟨n,hn⟩ := hE.exists
    exact ⟨n, by exact_mod_cast hn.le⟩
  let N (z : A × ℕ) : ℕ := Nat.find (hex z)
  have hN : Computable N := computable_find p hp hex
  refine ⟨fun z => a (z.1,N z), ha.comp (Computable.fst.pair hN), fun x k => ?_⟩
  exact (hbound x (N (x,k))).trans (by exact_mod_cast Nat.find_spec (hex (x,k)))

lemma Named.congr {A : Type*} [Primcodable A] {f g : A → ℝ}
    (hf : Named f) (h : ∀ a, f a = g a) : Named g := by
  simpa only [show f = g from funext h] using hf

lemma Named.comp {A B : Type*} [Primcodable A] [Primcodable B] {f : A → ℝ}
    (hf : Named f) {g : B → A} (hg : Computable g) : Named (f ∘ g) := by
  obtain ⟨a, ha, hb⟩ := hf
  exact ⟨fun z => a (g z.1,z.2),
    ha.comp ((hg.comp Computable.fst).pair Computable.snd), fun z n => hb (g z) n⟩

lemma Named.rational {A : Type*} [Primcodable A] {f : A → ℚ} (hf : Computable f) :
    Named (fun a => (f a : ℝ)) :=
  ⟨fun z => f z.1, hf.comp Computable.fst, fun _ n => by
    simp only [sub_self, abs_zero]; exact (tolerance_pos n).le⟩

lemma Named.const {A : Type*} [Primcodable A] (q : ℚ) : Named (fun _ : A => (q : ℝ)) :=
  Named.rational (Computable.const q)

lemma approximation_tendsto {x : ℝ} {a : ℕ → ℚ}
    (h : ∀ n, |x - (a n : ℝ)| ≤ tolerance n) :
    Tendsto (fun n => (a n : ℝ)) atTop (𝓝 x) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le (g := fun n => x - (tolerance n : ℝ))
    (h := fun n => x + (tolerance n : ℝ))
  · simpa using tendsto_const_nhds.sub tolerance_tendsto
  · simpa using tendsto_const_nhds.add tolerance_tendsto
  · intro n; have := (abs_le.mp (h n)).2; linarith
  · intro n; have := (abs_le.mp (h n)).1; linarith

lemma Named.add {A : Type*} [Primcodable A] {f g : A → ℝ}
    (hf : Named f) (hg : Named g) : Named (fun x => f x + g x) := by
  obtain ⟨a,ha,hae⟩ := hf
  obtain ⟨b,hb,hbe⟩ := hg
  apply Named.of_certificate _ (fun z => a z + b z) (fun z => 2 * tolerance z.2)
    (Arithmetic.rat_add.to_comp.comp ha hb)
    (Arithmetic.rat_mul.to_comp.comp (Computable.const 2)
      (tolerance_primrec.to_comp.comp Computable.snd))
  · intro x n
    push_cast
    calc
      _ = |(f x - (a (x,n) : ℝ)) + (g x - (b (x,n) : ℝ))| := by congr 1; ring
      _ ≤ _ := (abs_add_le _ _).trans (by linarith [hae x n, hbe x n])
  · intro x; simpa using (tolerance_tendsto.const_mul 2)

lemma Named.neg {A : Type*} [Primcodable A] {f : A → ℝ} (hf : Named f) :
    Named (fun x => -f x) := by
  obtain ⟨a,ha,h⟩ := hf
  refine ⟨fun z => -a z, Arithmetic.rat_neg.to_comp.comp ha, fun x n => ?_⟩
  simpa only [Rat.cast_neg, neg_sub_neg, abs_sub_comm] using h x n

lemma Named.sub {A : Type*} [Primcodable A] {f g : A → ℝ}
    (hf : Named f) (hg : Named g) : Named (fun x => f x - g x) :=
  (hf.add hg.neg).congr (fun _ => (sub_eq_add_neg _ _).symm)

lemma Named.mul {A : Type*} [Primcodable A] {f g : A → ℝ}
    (hf : Named f) (hg : Named g) : Named (fun x => f x * g x) := by
  obtain ⟨a,ha,hae⟩ := hf
  obtain ⟨b,hb,hbe⟩ := hg
  let e : A × ℕ → ℚ := fun z => (|a z| + |b z| + tolerance z.2) * tolerance z.2
  have he : Computable e := Arithmetic.rat_mul.to_comp.comp
    (Arithmetic.rat_add.to_comp.comp
      (Arithmetic.rat_add.to_comp.comp (Arithmetic.rat_abs.to_comp.comp ha)
        (Arithmetic.rat_abs.to_comp.comp hb))
      (tolerance_primrec.to_comp.comp Computable.snd))
    (tolerance_primrec.to_comp.comp Computable.snd)
  apply Named.of_certificate _ (fun z => a z * b z) e
    (Arithmetic.rat_mul.to_comp.comp ha hb) he
  · intro x n
    dsimp [e]; push_cast
    have hf : |f x| ≤ |(a (x,n) : ℝ)| + (tolerance n : ℝ) := by
      have h := abs_add_le (f x - (a (x,n) : ℝ)) (a (x,n))
      ring_nf at h
      linarith [hae x n]
    calc
      _ = |f x * (g x - (b (x,n) : ℝ)) + (f x - (a (x,n) : ℝ)) * (b (x,n) : ℝ)| := by congr 1; ring
      _ ≤ |f x| * |g x - (b (x,n) : ℝ)| + |f x - (a (x,n) : ℝ)| * |(b (x,n) : ℝ)| := by
        simpa only [abs_mul] using abs_add_le (f x * (g x - (b (x,n) : ℝ))) ((f x - (a (x,n) : ℝ)) * (b (x,n) : ℝ))
      _ ≤ (|(a (x,n) : ℝ)| + (tolerance n : ℝ)) * (tolerance n : ℝ) +
          (tolerance n : ℝ) * |(b (x,n) : ℝ)| :=
        add_le_add (mul_le_mul hf (hbe x n) (abs_nonneg _) (add_nonneg (abs_nonneg _) (tolerance_pos n).le))
          (mul_le_mul_of_nonneg_right (hae x n) (abs_nonneg _))
      _ = _ := by ring
  · intro x
    dsimp [e]
    simp only [Rat.cast_mul, Rat.cast_add, Rat.cast_abs]
    simpa using (((approximation_tendsto (hae x)).abs.add
      (approximation_tendsto (hbe x)).abs).add tolerance_tendsto).mul tolerance_tendsto

lemma Named.ite {A : Type*} [Primcodable A] (p : A → Prop) [DecidablePred p]
    (hp : Computable (fun a => decide (p a))) {f g : A → ℝ}
    (hf : Named f) (hg : Named g) : Named (fun x => if p x then f x else g x) := by
  obtain ⟨a,ha,hae⟩ := hf
  obtain ⟨b,hb,hbe⟩ := hg
  refine ⟨fun z => if p z.1 then a z else b z,
    (Computable.cond (hp.comp Computable.fst) ha hb).of_eq (by simp), ?_⟩
  intro x n; dsimp only; split_ifs <;> simp_all

lemma Named.apply_lipschitz {A : Type*} [Primcodable A] (g : A → ℝ → ℝ)
    (L : A → ℚ) (hL : Computable L) (hpos : ∀ a, 0 ≤ L a)
    (hLip : ∀ a x y, |g a x - g a y| ≤ (L a : ℝ) * |x - y|)
    (hg : Named (fun z : A × ℚ => g z.1 z.2))
    {f : A → ℝ} (hf : Named f) : Named (fun a => g a (f a)) := by
  obtain ⟨a,ha,hae⟩ := hf
  obtain ⟨b,hb,hbe⟩ := hg
  apply Named.of_certificate _ (fun z => b ((z.1,a z),z.2))
    (fun z => (L z.1 + 1) * tolerance z.2)
    (hb.comp ((Computable.fst.pair ha).pair Computable.snd))
    (Arithmetic.rat_mul.to_comp.comp
      (Arithmetic.rat_add.to_comp.comp (hL.comp Computable.fst) (Computable.const 1))
      (tolerance_primrec.to_comp.comp Computable.snd))
  · intro x n
    push_cast
    calc
      _ ≤ |g x (f x) - g x (a (x,n))| + |g x (a (x,n)) - (b ((x,a (x,n)),n) : ℝ)| := abs_sub_le _ _ _
      _ ≤ (L x : ℝ) * (tolerance n : ℝ) + (tolerance n : ℝ) :=
        add_le_add ((hLip x _ _).trans (mul_le_mul_of_nonneg_left (hae x n) (by exact_mod_cast hpos x)))
          (hbe (x,a (x,n)) n)
      _ = _ := by ring
  · intro x; simpa using tolerance_tendsto.const_mul ((L x : ℝ) + 1)

end AlternatingNS.Effective

end NamesDevelopment

end OAI
