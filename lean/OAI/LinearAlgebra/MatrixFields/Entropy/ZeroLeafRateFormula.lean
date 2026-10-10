import Mathlib
import OAI.LinearAlgebra.MatrixFields.Certificates.CertificatesReplay
import OAI.LinearAlgebra.MatrixFields.Parameters.ParametersWeights

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.Foundation

open scoped BigOperators

def entropyTerm (p : ℝ) : ℝ := -p * Real.log p

def finiteEntropy {A : Type*} [Fintype A] (p : A → ℝ) : ℝ := ∑ a, entropyTerm (p a)

theorem finiteEntropy_equiv {A B : Type*} [Fintype A] [Fintype B]
    (e : A ≃ B) (p : B → ℝ) : finiteEntropy (fun a => p (e a)) = finiteEntropy p :=
  e.sum_comp (fun b => entropyTerm (p b))

@[simp] theorem entropyTerm_zero : entropyTerm 0 = 0 := by simp [entropyTerm]

theorem entropyTerm_mul (p q : ℝ) :
    entropyTerm (p * q) = q * entropyTerm p + p * entropyTerm q := by
  by_cases hp : p = 0
  · simp [hp]
  by_cases hq : q = 0
  · simp [hq]
  rw [entropyTerm, Real.log_mul hp hq]
  unfold entropyTerm
  ring

theorem finiteEntropy_chain {A B : Type*} [Fintype A] [Fintype B]
    (p : A → ℝ) (q : A → B → ℝ) (hq : ∀ a, ∑ b, q a b = 1) :
    finiteEntropy (fun ab : A × B => p ab.1 * q ab.1 ab.2) =
      finiteEntropy p + ∑ a, p a * finiteEntropy (q a) := by
  simp only [finiteEntropy, Fintype.sum_prod_type, entropyTerm_mul,
    Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum, hq, one_mul]

structure FiniteLaw (A : Type*) [Fintype A] where
  mass : A → ℝ
  nonneg : ∀ a, 0 ≤ mass a
  total : ∑ a, mass a = 1

namespace FiniteLaw

variable {A B : Type*} [Fintype A] [Fintype B]

def map (p : FiniteLaw A) (f : A → B) : FiniteLaw B := by
  classical
  exact
    { mass := fun b => ∑ a, if f a = b then p.mass a else 0
      nonneg := fun b => Finset.sum_nonneg fun a _ => by
        split_ifs
        · exact p.nonneg a
        · exact le_rfl
      total := by
        rw [Finset.sum_comm]
        simpa using p.total }

@[simp] theorem map_mass [DecidableEq B] (p : FiniteLaw A) (f : A → B) (b : B) :
    (p.map f).mass b = ∑ a, if f a = b then p.mass a else 0 := by
  classical
  dsimp only [map]
  apply Finset.sum_congr rfl
  intro a _
  by_cases h : f a = b <;> simp only [h, ite_true, ite_false]

theorem map_mass_apply (p : FiniteLaw A) (f : A → B)
    (hf : Function.Injective f) (a : A) : (p.map f).mass (f a) = p.mass a := by
  classical
  simp [map_mass, hf.eq_iff]

theorem map_entropy_of_injective (p : FiniteLaw A) (f : A → B)
    (hf : Function.Injective f) : finiteEntropy (p.map f).mass = finiteEntropy p.mass := by
  classical
  have hterm (b : B) : entropyTerm ((p.map f).mass b) =
      ∑ a, if f a = b then entropyTerm (p.mass a) else 0 := by
    by_cases hb : ∃ a, f a = b
    · obtain ⟨a, rfl⟩ := hb
      rw [map_mass_apply p f hf]
      simp [hf.eq_iff]
    · simp [map_mass, not_exists.mp hb]
  unfold finiteEntropy
  simp_rw [hterm]
  rw [Finset.sum_comm]
  simp

def joint (p : FiniteLaw A) (q : A → FiniteLaw B) : FiniteLaw (A × B) where
  mass ab := p.mass ab.1 * (q ab.1).mass ab.2
  nonneg ab := mul_nonneg (p.nonneg ab.1) ((q ab.1).nonneg ab.2)
  total := by simp [Fintype.sum_prod_type, ← Finset.mul_sum, (q _).total, p.total]

theorem joint_entropy (p : FiniteLaw A) (q : A → FiniteLaw B) :
    finiteEntropy (p.joint q).mass =
      finiteEntropy p.mass + ∑ a, p.mass a * finiteEntropy (q a).mass :=
  finiteEntropy_chain p.mass (fun a => (q a).mass) (fun a => (q a).total)

theorem mass_le_map_mass (p : FiniteLaw A) (f : A → B) (a : A) :
    p.mass a ≤ (p.map f).mass (f a) := by
  classical
  rw [map_mass]
  have h := Finset.single_le_sum
    (s := (Finset.univ : Finset A))
    (f := fun a' => if f a' = f a then p.mass a' else 0)
    (fun a' _ => by
      split_ifs
      · exact p.nonneg a'
      · exact le_rfl)
    (Finset.mem_univ a)
  simpa using h

def conditional (p : FiniteLaw A) (f : A → B) (b : B) : FiniteLaw A := by
  classical
  exact if hzero : (p.map f).mass b = 0 then p else
    { mass := fun a => (if f a = b then p.mass a else 0) / (p.map f).mass b
      nonneg := fun a => div_nonneg
        (by split_ifs; exact p.nonneg a; exact le_rfl) ((p.map f).nonneg b)
      total := by
        rw [← Finset.sum_div, ← map_mass p f b, div_self hzero] }

theorem map_mass_mul_conditional [DecidableEq B]
    (p : FiniteLaw A) (f : A → B) (b : B) (a : A) :
    (p.map f).mass b * (p.conditional f b).mass a =
      if f a = b then p.mass a else 0 := by
  classical
  by_cases hzero : (p.map f).mass b = 0
  · have ha : f a = b → p.mass a = 0 := by
      intro hab
      have hle := p.mass_le_map_mass f a
      rw [hab, hzero] at hle
      exact le_antisymm hle (p.nonneg a)
    rw [hzero, zero_mul]
    by_cases hab : f a = b
    · rw [ite_eq_left hab, ha hab]
    · rw [ite_eq_right hab]
  · simp only [conditional, hzero, ↓reduceDIte]
    by_cases hab : f a = b
    · simpa only [hab, ite_true] using (mul_div_cancel₀ (p.mass a) hzero)
    · simp only [hab, ite_false, zero_div, mul_zero]

theorem entropy_eq_map_add_conditional (p : FiniteLaw A) (f : A → B) :
    finiteEntropy p.mass = finiteEntropy (p.map f).mass +
      ∑ b, (p.map f).mass b * finiteEntropy (p.conditional f b).mass := by
  classical
  let graph : A → B × A := fun a => (f a, a)
  have hinj : Function.Injective graph := fun _ _ h => congrArg Prod.snd h
  have hmass : ((p.map f).joint (p.conditional f)).mass = (p.map graph).mass := by
    funext ba
    rcases ba with ⟨b, a⟩
    change (p.map f).mass b * (p.conditional f b).mass a = (p.map graph).mass (b, a)
    rw [map_mass_mul_conditional, map_mass, Finset.sum_eq_single a]
    · simp only [graph, Prod.mk.injEq, and_true]
    · intro x _ hxa
      simp only [graph, Prod.mk.injEq, hxa, and_false, ite_false]
    · intro ha
      exact (ha (Finset.mem_univ a)).elim
  calc
    finiteEntropy p.mass = finiteEntropy (p.map graph).mass :=
      (p.map_entropy_of_injective graph hinj).symm
    _ = finiteEntropy ((p.map f).joint (p.conditional f)).mass := by rw [hmass]
    _ = _ := (p.map f).joint_entropy (p.conditional f)

end FiniteLaw
end MatrixMultiplication.Foundation

end
end
namespace MatrixMultiplication.CompactCertificate
open AllFieldCertificates AllFieldCertificates.Replay

inductive EntropyDatum where
  | zero
  | log (input output logarithm : Ball) (witness : LogData)

def EntropyDatum.input : EntropyDatum → Ball
  | .zero => .exact 0
  | .log p _ _ _ => p

def EntropyDatum.output : EntropyDatum → Ball
  | .zero => .exact 0
  | .log _ e _ _ => e

def EntropyDatum.check (two : Ball) : EntropyDatum → Bool
  | .zero => true
  | .log p e l w => checkLog two p l w && contains (Ball.mul (Ball.neg p) l) e

lemma EntropyDatum.sound {two : Ball} (htwo : two.Encloses (Real.log 2))
    {c : EntropyDatum} (hc : c.check two = true) {x : ℝ}
    (hx : c.input.Encloses x) : c.output.Encloses (Foundation.entropyTerm x) := by
  cases c with
  | zero =>
    have hb := Ball.bounds hx
    have h : x = 0 := by
      norm_num [EntropyDatum.input, Ball.lower, Ball.upper, Ball.exact] at hb
      linarith
    simp only [h, Foundation.entropyTerm, neg_zero, zero_mul]
    simpa only [EntropyDatum.output, Rat.cast_zero] using Ball.exact_sound 0
  | log p e l w =>
    simp only [EntropyDatum.check, Bool.and_eq_true] at hc
    obtain ⟨hl, he⟩ := hc
    exact contains_sound (Ball.mul_sound (Ball.neg_sound hx)
      (checkLog_sound htwo hx hl)) he

def entropyLookup (cs : List EntropyDatum) (i : ℕ) : EntropyDatum :=
  (cs[i]?).getD .zero

lemma entropyLookup_check {two : Ball} {cs : List EntropyDatum}
    (h : cs.all (fun c => c.check two) = true) (i : ℕ) :
    (entropyLookup cs i).check two = true := by
  induction cs generalizing i with
  | nil => simp [entropyLookup, EntropyDatum.check]
  | cons c cs ih =>
    simp only [List.all_cons, Bool.and_eq_true] at h
    cases i with
    | zero => simpa [entropyLookup] using h.1
    | succ i => simpa [entropyLookup] using ih h.2 i

lemma entropyLookup_sound {two : Ball} (htwo : two.Encloses (Real.log 2))
    {cs : List EntropyDatum} (h : cs.all (fun c => c.check two) = true)
    (i : ℕ) {x : ℝ} (hx : (entropyLookup cs i).input.Encloses x) :
    (entropyLookup cs i).output.Encloses (Foundation.entropyTerm x) :=
  EntropyDatum.sound htwo (entropyLookup_check h i) hx

end MatrixMultiplication.CompactCertificate

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
namespace MatrixMultiplication.AllFieldParameters

open MatrixMultiplication.Foundation
open scoped BigOperators

noncomputable section

def homogeneousEntropy {A : Type*} [Fintype A] (p : A → ℝ) : ℝ :=
  (∑ a, p a) * Real.log (∑ a, p a) + finiteEntropy p

theorem homogeneousEntropy_normalized {A : Type*} [Fintype A]
    (p : A → ℝ) (hp : ∑ a, p a = 1) :
    homogeneousEntropy p = finiteEntropy p := by
  simp [homogeneousEntropy, hp]

theorem entropyTerm_divide (x m : ℝ) :
    entropyTerm (x / m) = entropyTerm x / m + (x / m) * Real.log m := by
  by_cases hx : x = 0
  · simp [hx]
  by_cases hm : m = 0
  · simp [hm]
  rw [entropyTerm, Real.log_div hx hm]
  unfold entropyTerm
  ring

theorem homogeneousEntropy_eq_mass_mul {A : Type*} [Fintype A]
    (p : A → ℝ) (hm : ∑ a, p a ≠ 0) :
    homogeneousEntropy p =
      (∑ a, p a) * finiteEntropy (fun a => p a / ∑ b, p b) := by
  simp only [finiteEntropy, entropyTerm_divide, Finset.sum_add_distrib,
    ← Finset.sum_div, ← Finset.sum_mul]
  unfold homogeneousEntropy finiteEntropy
  rw [div_self hm]
  field_simp
  ring

theorem homogeneousEntropy_zero {A : Type*} [Fintype A] :
    homogeneousEntropy (fun _ : A => 0) = 0 := by
  simp [homogeneousEntropy, finiteEntropy]

theorem homogeneousEntropy_expansion {A : Type*} [Fintype A] (p : A → ℝ) :
    homogeneousEntropy p =
      (∑ a, p a) * Real.log (∑ a, p a) - ∑ a, p a * Real.log (p a) := by
  simp only [homogeneousEntropy, finiteEntropy, entropyTerm, neg_mul,
    Finset.sum_neg_distrib, sub_eq_add_neg]

end

end MatrixMultiplication.AllFieldParameters

end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

open scoped Topology
open Filter

namespace MatrixMultiplication.Foundation

theorem entropyTerm_eq_negMulLog (p : ℝ) : entropyTerm p = Real.negMulLog p := rfl

@[simp] theorem entropyTerm_one : entropyTerm 1 = 0 := by simp [entropyTerm]

theorem mul_entropyTerm_inv (x : ℝ) : x * entropyTerm x⁻¹ = Real.log x := by
  by_cases hx : x = 0
  · simp [hx]
  · simp only [entropyTerm, Real.log_inv]
    calc
      _ = (x * x⁻¹) * Real.log x := by ring
      _ = Real.log x := by rw [mul_inv_cancel₀ hx, one_mul]

theorem finiteEntropy_uniform {A : Type*} [Fintype A] :
    finiteEntropy (fun _a : A => (Fintype.card A : ℝ)⁻¹) =
      Real.log (Fintype.card A) := by
  simp only [finiteEntropy, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  exact mul_entropyTerm_inv (Fintype.card A)

theorem finiteEntropy_deterministic {A : Type*} [Fintype A] [DecidableEq A]
    (a : A) : finiteEntropy (fun b => if b = a then 1 else 0) = 0 := by
  apply Finset.sum_eq_zero
  intro b hb
  change entropyTerm (if b = a then 1 else 0) = 0
  split_ifs <;> simp

@[fun_prop] theorem continuous_entropyTerm : Continuous entropyTerm :=
  Real.continuous_negMulLog

theorem entropyTerm_nonneg {p : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) :
    0 ≤ entropyTerm p :=
  Real.negMulLog_nonneg hp₀ hp₁

theorem concaveOn_entropyTerm : ConcaveOn ℝ (Set.Ici 0) entropyTerm :=
  Real.concaveOn_negMulLog

@[fun_prop] theorem continuous_finiteEntropy {A : Type*} [Fintype A] :
    Continuous (finiteEntropy : (A → ℝ) → ℝ) := by
  unfold finiteEntropy
  exact continuous_finsetSum _ fun a _ => continuous_entropyTerm.comp (continuous_apply a)

theorem tendsto_entropyTerm {I : Type*} {l : Filter I} {p : I → ℝ} {q : ℝ}
    (h : Tendsto p l (𝓝 q)) :
    Tendsto (fun i => entropyTerm (p i)) l (𝓝 (entropyTerm q)) :=
  continuous_entropyTerm.continuousAt.tendsto.comp h

theorem tendsto_entropyTerm_zero {I : Type*} {l : Filter I} {p : I → ℝ}
    (h : Tendsto p l (𝓝 0)) :
    Tendsto (fun i => entropyTerm (p i)) l (𝓝 0) := by
  simpa only [entropyTerm_zero] using tendsto_entropyTerm h

theorem tendsto_finiteEntropy_of_tendsto {I A : Type*} [Fintype A]
    {l : Filter I} {p : I → A → ℝ} {q : A → ℝ}
    (h : ∀ a, Tendsto (fun i => p i a) l (𝓝 (q a))) :
    Tendsto (fun i => finiteEntropy (p i)) l (𝓝 (finiteEntropy q)) :=
  continuous_finiteEntropy.continuousAt.tendsto.comp (tendsto_pi_nhds.mpr h)

theorem finiteEntropy_nonneg {A : Type*} [Fintype A] (p : A → ℝ)
    (hp₀ : ∀ a, 0 ≤ p a) (hp₁ : ∀ a, p a ≤ 1) : 0 ≤ finiteEntropy p := by
  exact Finset.sum_nonneg fun a _ => entropyTerm_nonneg (hp₀ a) (hp₁ a)

theorem finiteEntropy_mix_le {A : Type*} [Fintype A] (p q : A → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    a * finiteEntropy p + b * finiteEntropy q ≤
      finiteEntropy (fun i => a * p i + b * q i) := by
  calc
    a * finiteEntropy p + b * finiteEntropy q =
        ∑ i, (a * entropyTerm (p i) + b * entropyTerm (q i)) := by
      simp only [finiteEntropy, Finset.sum_add_distrib, ← Finset.mul_sum]
    _ ≤ finiteEntropy (fun i => a * p i + b * q i) := by
      apply Finset.sum_le_sum
      intro i hi
      exact concaveOn_entropyTerm.2 (hp i) (hq i) ha hb hab

theorem finiteEntropy_le_log_card {A : Type*} [Fintype A] (p : A → ℝ)
    (hp : ∀ a, 0 ≤ p a) (htotal : ∑ a, p a = 1) :
    finiteEntropy p ≤ Real.log (Fintype.card A) := by
  classical
  have hcard : 0 < Fintype.card A := by
    by_contra h
    have : IsEmpty A := Fintype.card_eq_zero_iff.mp (Nat.eq_zero_of_not_pos h)
    simp at htotal
  have hn : (0 : ℝ) < Fintype.card A := Nat.cast_pos.mpr hcard
  have hw : ∑ _a : A, (Fintype.card A : ℝ)⁻¹ = 1 := by
    simp [Finset.sum_const, nsmul_eq_mul, hn.ne']
  have hJ := concaveOn_entropyTerm.le_map_sum
    (t := (Finset.univ : Finset A))
    (w := fun _a : A => (Fintype.card A : ℝ)⁻¹) (p := p)
    (fun _a _ha => (inv_pos.mpr hn).le) hw (fun a _ha => hp a)
  have hJ' : (Fintype.card A : ℝ)⁻¹ * finiteEntropy p ≤
      entropyTerm (Fintype.card A : ℝ)⁻¹ := by
    simpa only [smul_eq_mul, ← Finset.mul_sum, htotal, mul_one, finiteEntropy] using hJ
  calc
    finiteEntropy p = (Fintype.card A : ℝ) *
        ((Fintype.card A : ℝ)⁻¹ * finiteEntropy p) := by
      rw [← mul_assoc, mul_inv_cancel₀ hn.ne', one_mul]
    _ ≤ (Fintype.card A : ℝ) * entropyTerm (Fintype.card A : ℝ)⁻¹ :=
      mul_le_mul_of_nonneg_left hJ' hn.le
    _ = Real.log (Fintype.card A) := mul_entropyTerm_inv (Fintype.card A)

namespace FiniteLaw

variable {A : Type*} [Fintype A]

def uniform (A : Type*) [Fintype A] [Nonempty A] : FiniteLaw A where
  mass _a := (Fintype.card A : ℝ)⁻¹
  nonneg _a := inv_nonneg.mpr (Nat.cast_nonneg _)
  total := by
    have hn : (Fintype.card A : ℝ) ≠ 0 :=
      (Nat.cast_pos.mpr (Fintype.card_pos : 0 < Fintype.card A)).ne'
    simp [Finset.sum_const, nsmul_eq_mul, hn]

@[simp] theorem uniform_mass [Nonempty A] (a : A) :
    (uniform A).mass a = (Fintype.card A : ℝ)⁻¹ := rfl

@[simp] theorem uniform_entropy [Nonempty A] :
    finiteEntropy (uniform A).mass = Real.log (Fintype.card A) :=
  finiteEntropy_uniform

def pure (a : A) : FiniteLaw A := by
  classical
  exact
    { mass := fun b => if b = a then 1 else 0
      nonneg := fun b => by split_ifs <;> norm_num
      total := by simp }

@[simp] theorem pure_entropy (a : A) : finiteEntropy (pure a).mass = 0 := by
  classical
  exact finiteEntropy_deterministic a

theorem mass_le_one (p : FiniteLaw A) (a : A) : p.mass a ≤ 1 := by
  calc
    p.mass a ≤ ∑ b, p.mass b :=
      Finset.single_le_sum (fun b _hb => p.nonneg b) (Finset.mem_univ a)
    _ = 1 := p.total

theorem entropy_nonneg (p : FiniteLaw A) : 0 ≤ finiteEntropy p.mass :=
  finiteEntropy_nonneg p.mass p.nonneg p.mass_le_one

theorem entropy_le_log_card (p : FiniteLaw A) :
    finiteEntropy p.mass ≤ Real.log (Fintype.card A) :=
  finiteEntropy_le_log_card p.mass p.nonneg p.total

theorem map_entropy_le {B : Type*} [Fintype B] (p : FiniteLaw A) (f : A → B) :
    finiteEntropy (p.map f).mass ≤ finiteEntropy p.mass := by
  calc
    finiteEntropy (p.map f).mass ≤ finiteEntropy (p.map f).mass +
        ∑ b, (p.map f).mass b * finiteEntropy (p.conditional f b).mass :=
      le_add_of_nonneg_right (Finset.sum_nonneg fun b _ =>
        mul_nonneg ((p.map f).nonneg b) ((p.conditional f b).entropy_nonneg))
    _ = finiteEntropy p.mass := (p.entropy_eq_map_add_conditional f).symm

theorem entropy_tendsto {I : Type*} {l : Filter I}
    {p : I → FiniteLaw A} {q : FiniteLaw A}
    (h : ∀ a, Tendsto (fun i => (p i).mass a) l (𝓝 (q.mass a))) :
    Tendsto (fun i => finiteEntropy (p i).mass) l (𝓝 (finiteEntropy q.mass)) :=
  tendsto_finiteEntropy_of_tendsto h

end FiniteLaw
end MatrixMultiplication.Foundation

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
namespace MatrixMultiplication.Foundation

open scoped BigOperators

universe u v

noncomputable section

namespace FiniteLaw

theorem map_mass_mul_conditional_map {A B C : Type*}
    [Fintype A] [Fintype B] [Fintype C]
    (p : FiniteLaw A) (f : A → B) (g : A → C) (b : B) (c : C) :
    (p.map f).mass b * ((p.conditional f b).map g).mass c =
      (p.map (fun a => (f a, g a))).mass (b, c) := by
  classical
  rw [map_mass (p.conditional f b) g c, Finset.mul_sum,
    map_mass p (fun a => (f a, g a)) (b, c)]
  apply Finset.sum_congr rfl
  intro a _
  by_cases hgc : g a = c
  · rw [ite_eq_left hgc, map_mass_mul_conditional]
    simp only [Prod.mk.injEq, hgc, and_true]
  · rw [ite_eq_right hgc, mul_zero]
    have hpair : (f a, g a) ≠ (b, c) :=
      fun he => hgc (congrArg Prod.snd he)
    rw [ite_eq_right hpair]

end FiniteLaw

def LabelRecord (Label : ℕ → Type u) : ℕ → Type u
  | 0 => PUnit
  | n + 1 => LabelRecord Label n × Label n

instance labelRecordFintype (Label : ℕ → Type u) [∀ n, Fintype (Label n)] :
    (n : ℕ) → Fintype (LabelRecord Label n)
  | 0 => by
      change Fintype PUnit
      infer_instance
  | n + 1 => by
      letI := labelRecordFintype Label n
      change Fintype (LabelRecord Label n × Label n)
      infer_instance

def labelRecordOf {A : Type v} {Label : ℕ → Type u}
    (labels : ∀ n, A → Label n) : (n : ℕ) → A → LabelRecord Label n
  | 0, _ => PUnit.unit
  | n + 1, a => (labelRecordOf labels n a, labels n a)

structure FiniteLabelHierarchy (Label : ℕ → Type u) [∀ n, Fintype (Label n)]
    (depth : ℕ) where
  conditional : ∀ n, n < depth → LabelRecord Label n → FiniteLaw (Label n)

namespace FiniteLabelHierarchy

variable {Label : ℕ → Type u} [∀ n, Fintype (Label n)] {depth : ℕ}

def prefixLaw (h : FiniteLabelHierarchy Label depth) :
    (n : ℕ) → n ≤ depth → FiniteLaw (LabelRecord Label n)
  | 0, _ =>
      { mass := fun _ => 1
        nonneg := fun _ => zero_le_one
        total := by
          change (∑ _ : PUnit, (1 : ℝ)) = 1
          simp }
  | n + 1, hn =>
      (h.prefixLaw n (Nat.le_of_succ_le hn)).joint
        (h.conditional n (Nat.lt_of_succ_le hn))

@[simp] theorem prefixLaw_zero_mass (h : FiniteLabelHierarchy Label depth)
    (hn : 0 ≤ depth) (r : LabelRecord Label 0) :
    (h.prefixLaw 0 hn).mass r = 1 := rfl

@[simp] theorem prefixLaw_succ (h : FiniteLabelHierarchy Label depth)
    (n : ℕ) (hn : n + 1 ≤ depth) :
    h.prefixLaw (n + 1) hn =
      (h.prefixLaw n (Nat.le_of_succ_le hn)).joint
        (h.conditional n (Nat.lt_of_succ_le hn)) := rfl

@[simp] theorem prefixLaw_succ_mass (h : FiniteLabelHierarchy Label depth)
    (n : ℕ) (hn : n + 1 ≤ depth) (r : LabelRecord Label n) (s : Label n) :
    (h.prefixLaw (n + 1) hn).mass (r, s) =
      (h.prefixLaw n (Nat.le_of_succ_le hn)).mass r *
        (h.conditional n (Nat.lt_of_succ_le hn) r).mass s := rfl

def refinementEntropy (h : FiniteLabelHierarchy Label depth) (n : ℕ) : ℝ :=
  if hn : n < depth then
    ∑ r, (h.prefixLaw n (Nat.le_of_lt hn)).mass r *
      finiteEntropy (h.conditional n hn r).mass
  else 0

theorem refinementEntropy_eq (h : FiniteLabelHierarchy Label depth)
    (n : ℕ) (hn : n < depth) :
    h.refinementEntropy n =
      ∑ r, (h.prefixLaw n (Nat.le_of_lt hn)).mass r *
        finiteEntropy (h.conditional n hn r).mass := by
  simp only [refinementEntropy, dite_eq_left hn]

@[simp] theorem refinementEntropy_eq_zero_of_le
    (h : FiniteLabelHierarchy Label depth) {n : ℕ} (hn : depth ≤ n) :
    h.refinementEntropy n = 0 := by
  simp only [refinementEntropy, dite_eq_right (Nat.not_lt.mpr hn)]

theorem zero_prefix_contribution (h : FiniteLabelHierarchy Label depth)
    (n : ℕ) (hn : n < depth) (r : LabelRecord Label n)
    (hr : (h.prefixLaw n (Nat.le_of_lt hn)).mass r = 0) :
    (h.prefixLaw n (Nat.le_of_lt hn)).mass r *
      finiteEntropy (h.conditional n hn r).mass = 0 := by
  rw [hr, zero_mul]

theorem prefixLaw_entropy_succ (h : FiniteLabelHierarchy Label depth)
    (n : ℕ) (hn : n + 1 ≤ depth) :
    finiteEntropy (h.prefixLaw (n + 1) hn).mass =
      finiteEntropy (h.prefixLaw n (Nat.le_of_succ_le hn)).mass +
        h.refinementEntropy n := by
  change finiteEntropy ((h.prefixLaw n (Nat.le_of_succ_le hn)).joint
    (h.conditional n (Nat.lt_of_succ_le hn))).mass = _
  rw [FiniteLaw.joint_entropy]
  rw [refinementEntropy_eq h n (Nat.lt_of_succ_le hn)]

theorem prefixLaw_entropy (h : FiniteLabelHierarchy Label depth)
    (n : ℕ) (hn : n ≤ depth) :
    finiteEntropy (h.prefixLaw n hn).mass =
      ∑ j ∈ Finset.range n, h.refinementEntropy j := by
  induction n with
  | zero =>
      simp [prefixLaw, finiteEntropy, entropyTerm, LabelRecord]
  | succ n ih =>
      rw [prefixLaw_entropy_succ h n hn,
        ih (Nat.le_of_succ_le hn), Finset.sum_range_succ]

def recordLaw (h : FiniteLabelHierarchy Label depth) :
    FiniteLaw (LabelRecord Label depth) := h.prefixLaw depth le_rfl

theorem recordLaw_entropy (h : FiniteLabelHierarchy Label depth) :
    finiteEntropy h.recordLaw.mass =
      ∑ j ∈ Finset.range depth, h.refinementEntropy j :=
  h.prefixLaw_entropy depth le_rfl

theorem refinementEntropy_sum_of_injective_record
    {A : Type v} [Fintype A] (h : FiniteLabelHierarchy Label depth)
    (p : FiniteLaw A) (record : A → LabelRecord Label depth)
    (hinjective : Function.Injective record)
    (hmass : h.recordLaw.mass = (p.map record).mass) :
    (∑ j ∈ Finset.range depth, h.refinementEntropy j) = finiteEntropy p.mass := by
  calc
    (∑ j ∈ Finset.range depth, h.refinementEntropy j) =
        finiteEntropy h.recordLaw.mass := h.recordLaw_entropy.symm
    _ = finiteEntropy (p.map record).mass := congrArg finiteEntropy hmass
    _ = finiteEntropy p.mass := p.map_entropy_of_injective record hinjective

def ofLawLabels {A : Type v} [Fintype A] (p : FiniteLaw A)
    (labels : ∀ n, A → Label n) (depth : ℕ) : FiniteLabelHierarchy Label depth where
  conditional n _ r := (p.conditional (labelRecordOf labels n) r).map (labels n)

theorem ofLawLabels_prefixLaw_mass {A : Type v} [Fintype A]
    (p : FiniteLaw A) (labels : ∀ n, A → Label n)
    (depth n : ℕ) (hn : n ≤ depth) :
    ((ofLawLabels p labels depth).prefixLaw n hn).mass =
      (p.map (labelRecordOf labels n)).mass := by
  classical
  induction n with
  | zero =>
      funext r
      cases r
      change 1 = (p.map (fun _ : A => (PUnit.unit : PUnit))).mass PUnit.unit
      simp [FiniteLaw.map_mass, p.total]
  | succ n ih =>
      funext rs
      rcases rs with ⟨r, s⟩
      rw [prefixLaw_succ_mass]
      change ((ofLawLabels p labels depth).prefixLaw n
          (Nat.le_of_succ_le hn)).mass r *
        ((p.conditional (labelRecordOf labels n) r).map (labels n)).mass s =
          (p.map (labelRecordOf labels (n + 1))).mass (r, s)
      rw [ih (Nat.le_of_succ_le hn)]
      exact p.map_mass_mul_conditional_map
        (labelRecordOf labels n) (labels n) r s

theorem ofLawLabels_refinementEntropy_eq {A : Type v} [Fintype A]
    (p : FiniteLaw A) (labels : ∀ n, A → Label n)
    (depth n : ℕ) (hn : n < depth) :
    (ofLawLabels p labels depth).refinementEntropy n =
      ∑ r : LabelRecord Label n, (p.map (labelRecordOf labels n)).mass r *
        finiteEntropy ((p.conditional (labelRecordOf labels n) r).map (labels n)).mass := by
  rw [refinementEntropy_eq _ n hn,
    ofLawLabels_prefixLaw_mass p labels depth n (Nat.le_of_lt hn)]
  rfl

theorem ofLawLabels_refinementEntropy_sum {A : Type v} [Fintype A]
    (p : FiniteLaw A) (labels : ∀ n, A → Label n) (depth : ℕ)
    (hinjective : Function.Injective (labelRecordOf labels depth)) :
    (∑ j ∈ Finset.range depth,
      (ofLawLabels p labels depth).refinementEntropy j) = finiteEntropy p.mass := by
  apply (ofLawLabels p labels depth).refinementEntropy_sum_of_injective_record
    p (labelRecordOf labels depth) hinjective
  exact ofLawLabels_prefixLaw_mass p labels depth depth le_rfl

theorem entropy_eq_sum_conditional_labels {A : Type v} [Fintype A]
    (p : FiniteLaw A) (labels : ∀ n, A → Label n) (depth : ℕ)
    (hinjective : Function.Injective (labelRecordOf labels depth)) :
    finiteEntropy p.mass =
      ∑ j ∈ Finset.range depth, ∑ r : LabelRecord Label j,
        (p.map (labelRecordOf labels j)).mass r *
          finiteEntropy ((p.conditional (labelRecordOf labels j) r).map (labels j)).mass := by
  rw [← ofLawLabels_refinementEntropy_sum p labels depth hinjective]
  apply Finset.sum_congr rfl
  intro j hj
  exact ofLawLabels_refinementEntropy_eq p labels depth j (Finset.mem_range.mp hj)

end FiniteLabelHierarchy

end
end MatrixMultiplication.Foundation

end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

open scoped BigOperators
open MatrixMultiplication.Foundation

namespace MatrixMultiplication.JointEntropyMax

theorem entropy_nonneg {A : Type*} [Fintype A] (p : FiniteLaw A) :
    0 ≤ finiteEntropy p.mass :=
  FiniteLaw.entropy_nonneg p

theorem map_entropy_le {A B : Type*} [Fintype A] [Fintype B]
    (p : FiniteLaw A) (f : A → B) :
    finiteEntropy (p.map f).mass ≤ finiteEntropy p.mass :=
  FiniteLaw.map_entropy_le p f

theorem entropy_sub_map_nonneg {A B : Type*} [Fintype A] [Fintype B]
    (p : FiniteLaw A) (f : A → B) :
    0 ≤ finiteEntropy p.mass - finiteEntropy (p.map f).mass :=
  sub_nonneg.mpr (map_entropy_le p f)

theorem entropyTerm_le_crossEntropyTerm {p q : ℝ} (hp : 0 < p) (hq : 0 ≤ q) :
    entropyTerm q ≤ -q * Real.log p + p - q := by
  by_cases hzero : q = 0
  · simpa [hzero] using hp.le
  have hqpos : 0 < q := lt_of_le_of_ne hq (Ne.symm hzero)
  have hlog := Real.log_le_sub_one_of_pos (div_pos hp hqpos)
  rw [Real.log_div hp.ne' hqpos.ne'] at hlog
  have hmul := mul_le_mul_of_nonneg_left hlog hq
  have hcancel : q * (p / q - 1) = p - q := by
    field_simp
  rw [hcancel] at hmul
  unfold entropyTerm
  linarith

theorem entropy_le_crossEntropy {A : Type*} [Fintype A]
    (p q : FiniteLaw A) (hp : ∀ a, 0 < p.mass a) :
    finiteEntropy q.mass ≤ ∑ a, -q.mass a * Real.log (p.mass a) := by
  calc
    finiteEntropy q.mass ≤
        ∑ a, (-q.mass a * Real.log (p.mass a) + p.mass a - q.mass a) :=
      Finset.sum_le_sum fun a _ => entropyTerm_le_crossEntropyTerm (hp a) (q.nonneg a)
    _ = ∑ a, -q.mass a * Real.log (p.mass a) := by
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, p.total, q.total]
      ring

theorem sum_mass_mul_coordinate {A B : Type*} [Fintype A] [Fintype B]
    (p : FiniteLaw A) (f : A → B) (v : B → ℝ) :
    (∑ a, p.mass a * v (f a)) = ∑ b, (p.map f).mass b * v b := by
  classical
  simp_rw [FiniteLaw.map_mass, Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  simp

theorem sum_mass_mul_coordinate_eq {A B : Type*} [Fintype A] [Fintype B]
    (p q : FiniteLaw A) (f : A → B) (v : B → ℝ)
    (hmarginal : (q.map f).mass = (p.map f).mass) :
    (∑ a, q.mass a * v (f a)) = ∑ a, p.mass a * v (f a) := by
  rw [sum_mass_mul_coordinate q f v, sum_mass_mul_coordinate p f v, hmarginal]

theorem entropy_le_of_three_marginals
    {A X Y Z : Type*} [Fintype A] [Fintype X] [Fintype Y] [Fintype Z]
    (p q : FiniteLaw A) (fX : A → X) (fY : A → Y) (fZ : A → Z)
    (u : X → ℝ) (v : Y → ℝ) (w : Z → ℝ) (c : ℝ)
    (hp : ∀ a, 0 < p.mass a)
    (hlog : ∀ a, Real.log (p.mass a) = u (fX a) + v (fY a) + w (fZ a) - c)
    (hX : (q.map fX).mass = (p.map fX).mass)
    (hY : (q.map fY).mass = (p.map fY).mass)
    (hZ : (q.map fZ).mass = (p.map fZ).mass) :
    finiteEntropy q.mass ≤ finiteEntropy p.mass := by
  have hx := sum_mass_mul_coordinate_eq p q fX u hX
  have hy := sum_mass_mul_coordinate_eq p q fY v hY
  have hz := sum_mass_mul_coordinate_eq p q fZ w hZ
  have hexpand (r : FiniteLaw A) :
      (∑ a, r.mass a * (u (fX a) + v (fY a) + w (fZ a) - c)) =
        (∑ a, r.mass a * u (fX a)) + (∑ a, r.mass a * v (fY a)) +
          (∑ a, r.mass a * w (fZ a)) - c := by
    simp_rw [mul_sub, mul_add]
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
      ← Finset.sum_mul, r.total, one_mul]
  have hexpect : (∑ a, q.mass a * Real.log (p.mass a)) =
      ∑ a, p.mass a * Real.log (p.mass a) := by
    simp_rw [hlog]
    rw [hexpand q, hexpand p, hx, hy, hz]
  calc
    finiteEntropy q.mass ≤ ∑ a, -q.mass a * Real.log (p.mass a) :=
      entropy_le_crossEntropy p q hp
    _ = -(∑ a, q.mass a * Real.log (p.mass a)) := by
      simp only [neg_mul, Finset.sum_neg_distrib]
    _ = -(∑ a, p.mass a * Real.log (p.mass a)) := by rw [hexpect]
    _ = finiteEntropy p.mass := by
      simp only [finiteEntropy, entropyTerm, neg_mul, Finset.sum_neg_distrib]

def normalizedPositiveLaw {A : Type*} [Fintype A] [Nonempty A]
    (weight : A → ℝ) (hweight : ∀ a, 0 < weight a) : FiniteLaw A where
  mass a := weight a / ∑ b, weight b
  nonneg a := div_nonneg (hweight a).le
    (Finset.sum_nonneg fun b _ => (hweight b).le)
  total := by
    have htotal : 0 < ∑ b, weight b :=
      Finset.sum_pos (fun b _ => hweight b) Finset.univ_nonempty
    rw [← Finset.sum_div, div_self htotal.ne']

theorem normalizedPositiveLaw_mass_pos {A : Type*} [Fintype A] [Nonempty A]
    (weight : A → ℝ) (hweight : ∀ a, 0 < weight a) (a : A) :
    0 < (normalizedPositiveLaw weight hweight).mass a := by
  exact div_pos (hweight a)
    (Finset.sum_pos (fun b _ => hweight b) Finset.univ_nonempty)

theorem entropy_le_normalized_product
    {A X Y Z : Type*} [Fintype A] [Nonempty A]
    [Fintype X] [Fintype Y] [Fintype Z]
    (fX : A → X) (fY : A → Y) (fZ : A → Z)
    (wx : X → ℝ) (wy : Y → ℝ) (wz : Z → ℝ)
    (hx : ∀ x, 0 < wx x) (hy : ∀ y, 0 < wy y) (hz : ∀ z, 0 < wz z)
    (q : FiniteLaw A)
    (hX : (q.map fX).mass =
      ((normalizedPositiveLaw (fun a => wx (fX a) * wy (fY a) * wz (fZ a))
        (fun _ => mul_pos (mul_pos (hx _) (hy _)) (hz _))).map fX).mass)
    (hY : (q.map fY).mass =
      ((normalizedPositiveLaw (fun a => wx (fX a) * wy (fY a) * wz (fZ a))
        (fun _ => mul_pos (mul_pos (hx _) (hy _)) (hz _))).map fY).mass)
    (hZ : (q.map fZ).mass =
      ((normalizedPositiveLaw (fun a => wx (fX a) * wy (fY a) * wz (fZ a))
        (fun _ => mul_pos (mul_pos (hx _) (hy _)) (hz _))).map fZ).mass) :
    finiteEntropy q.mass ≤
      finiteEntropy (normalizedPositiveLaw
        (fun a => wx (fX a) * wy (fY a) * wz (fZ a))
        (fun _ => mul_pos (mul_pos (hx _) (hy _)) (hz _))).mass := by
  let weight : A → ℝ := fun a => wx (fX a) * wy (fY a) * wz (fZ a)
  have hweight : ∀ a, 0 < weight a := fun a => mul_pos (mul_pos (hx _) (hy _)) (hz _)
  let p := normalizedPositiveLaw weight hweight
  have htotal : 0 < ∑ a, weight a :=
    Finset.sum_pos (fun a _ => hweight a) Finset.univ_nonempty
  apply entropy_le_of_three_marginals p q fX fY fZ
    (fun x => Real.log (wx x)) (fun y => Real.log (wy y))
    (fun z => Real.log (wz z)) (Real.log (∑ a, weight a))
    (normalizedPositiveLaw_mass_pos weight hweight)
  · intro a
    change Real.log (weight a / ∑ b, weight b) = _
    rw [Real.log_div (hweight a).ne' htotal.ne']
    dsimp only [weight]
    rw [Real.log_mul (mul_pos (hx _) (hy _)).ne' (hz _).ne',
      Real.log_mul (hx _).ne' (hy _).ne']
  · exact hX
  · exact hY
  · exact hZ

end MatrixMultiplication.JointEntropyMax

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.AllFieldZeroLeafRates

open MatrixMultiplication.Foundation AllFieldParameters
open scoped BigOperators

def fourRate (t : Shape) : ℝ :=
  finiteEntropy (fun s : PairSlot => (zeroPairLaw t s.1 s.2 : ℝ)) +
    ∑ s : PairSlot, (zeroPairLaw t s.1 s.2 : ℝ) *
      Real.log (AllFieldParameters.multiplicity s.1 * AllFieldParameters.multiplicity s.2 : ℕ)

end MatrixMultiplication.AllFieldZeroLeafRates

end
end

end MatrixAllFields

end OAI
