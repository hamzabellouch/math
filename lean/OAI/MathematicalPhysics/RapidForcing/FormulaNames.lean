import OAI.MathematicalPhysics.RapidForcing.FieldExpressions

namespace OAI

section

open scoped BigOperators Topology
open Set Filter
namespace RapidForcing.EffectiveProfile
namespace Formula
variable {d : ℕ}

def lipBound (R : ℚ) : Formula d → ℚ
  | .const _ => 0
  | .var _ => 1
  | .add a b => a.lipBound R + b.lipBound R
  | .mul a b => a.bound R * b.lipBound R + b.bound R * a.lipBound R
  | .profile e a => e.diff.bound * a.lipBound R

lemma lipBound_nonneg (a : Formula d) (R : ℚ) : 0 ≤ a.lipBound R := by
  induction a with
  | const q => rfl
  | var i => norm_num [lipBound]
  | add a b ha hb => exact add_nonneg ha hb
  | mul a b ha hb =>
    exact add_nonneg (mul_nonneg (a.bound_nonneg R) hb) (mul_nonneg (b.bound_nonneg R) ha)
  | profile e a ha => exact mul_nonneg e.diff.bound_nonneg ha

lemma abs_sub_le_lipBound (a : Formula d) (R : ℚ) (x y : Fin d → ℝ)
    (hx : ∀ i, |x i| ≤ |(R : ℝ)|) (hy : ∀ i, |y i| ≤ |(R : ℝ)|) :
    |a.value x - a.value y| ≤ (a.lipBound R : ℝ) * ‖x - y‖ := by
  induction a with
  | const q => simp [value, lipBound]
  | var i => simpa [value, lipBound, Real.norm_eq_abs] using norm_le_pi_norm (x - y) i
  | add a b ha hb =>
    calc
      _ = |(a.value x - a.value y) + (b.value x - b.value y)| := by dsimp [value]; congr 1; ring
      _ ≤ |a.value x - a.value y| + |b.value x - b.value y| := abs_add_le _ _
      _ ≤ (a.lipBound R : ℝ) * ‖x - y‖ + (b.lipBound R : ℝ) * ‖x - y‖ := add_le_add ha hb
      _ = _ := by simp [lipBound, add_mul]
  | mul a b ha hb =>
    calc
      _ = |a.value x * (b.value x - b.value y) + b.value y * (a.value x - a.value y)| := by
        dsimp [value]; congr 1; ring
      _ ≤ |a.value x| * |b.value x - b.value y| + |b.value y| * |a.value x - a.value y| := by
        simpa [abs_mul] using abs_add_le (a.value x * (b.value x - b.value y))
          (b.value y * (a.value x - a.value y))
      _ ≤ (a.bound R : ℝ) * ((b.lipBound R : ℝ) * ‖x - y‖) +
          (b.bound R : ℝ) * ((a.lipBound R : ℝ) * ‖x - y‖) := by
        apply add_le_add
        · exact mul_le_mul (a.abs_value_le R x hx) hb (abs_nonneg _) (by exact_mod_cast a.bound_nonneg R)
        · exact mul_le_mul (b.abs_value_le R y hy) ha (abs_nonneg _) (by exact_mod_cast b.bound_nonneg R)
      _ = _ := by simp only [lipBound, Rat.cast_add, Rat.cast_mul]; ring
  | profile e a ha =>
    have he : |e.value (a.value x) - e.value (a.value y)| ≤
        (e.diff.bound : ℝ) * |a.value x - a.value y| := e.lipschitz.dist_le_mul _ _
    exact he.trans (by simpa only [lipBound, Rat.cast_mul, mul_assoc] using
      mul_le_mul_of_nonneg_left ha (show (0 : ℝ) ≤ e.diff.bound by exact_mod_cast e.diff.bound_nonneg))

def RationalName (name : ℕ → Part (Fin d → ℚ)) (x : Fin d → ℝ) : Prop :=
  ∀ n, ∃ q, q ∈ name n ∧ ‖(fun i => (q i : ℝ)) - x‖ ≤ accuracy n

def choosePrecision (L ε : ℚ) : Part ℕ :=
  Nat.rfindOpt fun n => if (1 / 2 : ℚ) ^ n * L ≤ ε / 2 then some n else none

lemma choosePrecision_spec (L ε : ℚ) {n : ℕ} (hn : n ∈ choosePrecision L ε) :
    (1 / 2 : ℚ) ^ n * L ≤ ε / 2 := by
  obtain ⟨m, hm⟩ := Nat.rfindOpt_spec hn
  split_ifs at hm with h
  · have he := Option.mem_some_iff.mp hm
    subst m
    exact h
  · cases hm

lemma choosePrecision_dom (L ε : ℚ) (hε : 0 < ε) : (choosePrecision L ε).Dom := by
  have he : (0 : ℝ) < (ε : ℝ) / 2 := by exact_mod_cast (half_pos hε)
  have hlim : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n * (L : ℝ)) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)).mul_const (L : ℝ)
  obtain ⟨n, hn⟩ := (hlim.eventually (Iio_mem_nhds he)).exists
  have hn'' : (((1 / 2 : ℚ) ^ n * L : ℚ) : ℝ) ≤ ((ε / 2 : ℚ) : ℝ) := by
    simpa only [Rat.cast_mul, Rat.cast_pow, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using hn.le
  have hn' : (1 / 2 : ℚ) ^ n * L ≤ ε / 2 := by exact_mod_cast hn''
  exact Nat.rfindOpt_dom.mpr ⟨n, n, by rw [ite_eq_left hn']; rfl⟩

def evalName (a : Formula d) (name : ℕ → Part (Fin d → ℚ)) (ε : ℚ) : Part Ball := do
  let q₀ ← name 0
  let R := 2 + ∑ i, |q₀ i|
  let L := a.lipBound R
  let n ← choosePrecision L ε
  let q ← name n
  let b ← a.evalAt q (ε / 2)
  pure ⟨b.center, b.radius + (1 / 2 : ℚ) ^ n * L⟩

lemma rationalName_spec {name : ℕ → Part (Fin d → ℚ)} {x : Fin d → ℝ}
    (hn : RationalName name x) (n : ℕ) {q : Fin d → ℚ} (hq : q ∈ name n) :
    ‖(fun i => (q i : ℝ)) - x‖ ≤ accuracy n := by
  obtain ⟨q', hq', he⟩ := hn n
  exact Part.mem_unique hq hq' ▸ he

lemma accuracy_le_one (n : ℕ) : accuracy n ≤ 1 :=
  pow_le_one₀ (by norm_num) (by norm_num)

lemma name_box {name : ℕ → Part (Fin d → ℚ)} {x : Fin d → ℝ}
    (hn : RationalName name x) {q₀ q : Fin d → ℚ} (h₀ : q₀ ∈ name 0)
    {n : ℕ} (hq : q ∈ name n) :
    (∀ i, |x i| ≤ |((2 + ∑ j, |q₀ j| : ℚ) : ℝ)|) ∧
    (∀ i, |(q i : ℝ)| ≤ |((2 + ∑ j, |q₀ j| : ℚ) : ℝ)|) := by
  have hdist₀ := rationalName_spec hn 0 h₀
  have hdist := (rationalName_spec hn n hq).trans (accuracy_le_one n)
  have hp : (0 : ℚ) ≤ 2 + ∑ j, |q₀ j| := by positivity
  have hp' : (0 : ℝ) ≤ ((2 + ∑ j, |q₀ j| : ℚ) : ℝ) := by exact_mod_cast hp
  constructor
  · intro i
    have hi := (norm_le_pi_norm ((fun j => (q₀ j : ℝ)) - x) i).trans hdist₀
    have hsum : |(q₀ i : ℝ)| ≤ (∑ j, |q₀ j| : ℚ) := by
      exact_mod_cast (Finset.single_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin d))) => abs_nonneg (q₀ j))
        (Finset.mem_univ i))
    have ht := abs_sub_le (x i) (q₀ i : ℝ) 0
    simp only [Real.norm_eq_abs, Pi.sub_apply, accuracy, pow_zero] at hi
    rw [abs_sub_comm] at hi
    simp only [sub_zero] at ht
    rw [abs_of_nonneg hp', Rat.cast_add, Rat.cast_ofNat]
    linarith
  · intro i
    have hi := (norm_le_pi_norm ((fun j => (q₀ j : ℝ)) - x) i).trans hdist₀
    have hi' := (norm_le_pi_norm ((fun j => (q j : ℝ)) - x) i).trans hdist
    have hsum : |(q₀ i : ℝ)| ≤ (∑ j, |q₀ j| : ℚ) := by
      exact_mod_cast (Finset.single_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin d))) => abs_nonneg (q₀ j))
        (Finset.mem_univ i))
    have ht := abs_sub_le (q i : ℝ) (x i) (q₀ i : ℝ)
    have ht' := abs_sub_le (q i : ℝ) (q₀ i : ℝ) 0
    simp only [Real.norm_eq_abs, Pi.sub_apply, accuracy, pow_zero] at hi hi'
    rw [abs_sub_comm] at hi
    simp only [sub_zero] at ht'
    rw [abs_of_nonneg hp', Rat.cast_add, Rat.cast_ofNat]
    linarith

lemma evalName_spec (a : Formula d) {name : ℕ → Part (Fin d → ℚ)} {x : Fin d → ℝ}
    (hn : RationalName name x) (ε : ℚ) (hε : 0 < ε) {b : Ball} (hb : b ∈ a.evalName name ε) :
    b.Covers (a.value x) ∧ b.radius ≤ ε := by
  obtain ⟨q₀, h₀, hrest⟩ := Part.mem_bind_iff.mp hb
  obtain ⟨n, hn', hrest⟩ := Part.mem_bind_iff.mp hrest
  obtain ⟨q, hq, hrest⟩ := Part.mem_bind_iff.mp hrest
  obtain ⟨c, hc, hb⟩ := Part.mem_bind_iff.mp hrest
  have he : b = ⟨c.center, c.radius + (1 / 2 : ℚ) ^ n * a.lipBound (2 + ∑ i, |q₀ i|)⟩ :=
    Part.mem_some_iff.mp hb
  subst b
  have hprec := choosePrecision_spec _ _ hn'
  obtain ⟨hc, hc'⟩ := a.evalAt_spec q (ε / 2) (by positivity) hc
  obtain ⟨hx, hy⟩ := name_box hn h₀ hq
  have hdist := a.abs_sub_le_lipBound _ _ _ hy hx
  have hbound := rationalName_spec hn n hq
  have hL : (0 : ℝ) ≤ a.lipBound (2 + ∑ i, |q₀ i|) := by exact_mod_cast a.lipBound_nonneg _
  refine ⟨?_, by change c.radius + (1 / 2 : ℚ) ^ n * a.lipBound (2 + ∑ i, |q₀ i|) ≤ ε; linarith⟩
  change |(c.center : ℝ) - a.value x| ≤ _
  calc
    _ ≤ |(c.center : ℝ) - a.value (fun i => (q i : ℝ))| +
        |a.value (fun i => (q i : ℝ)) - a.value x| := abs_sub_le _ _ _
    _ ≤ (c.radius : ℝ) + (a.lipBound (2 + ∑ i, |q₀ i|) : ℝ) * accuracy n :=
      add_le_add hc (hdist.trans (mul_le_mul_of_nonneg_left hbound hL))
    _ = _ := by simp [accuracy, mul_comm]

lemma evalName_dom (a : Formula d) {name : ℕ → Part (Fin d → ℚ)} {x : Fin d → ℝ}
    (hn : RationalName name x) (ε : ℚ) (hε : 0 < ε) : (a.evalName name ε).Dom := by
  have ht (n : ℕ) : (name n).Dom := let ⟨_, h, _⟩ := hn n; h.fst
  refine ⟨ht 0, choosePrecision_dom _ _ hε, ht _, ?_⟩
  exact ⟨a.evalAt_dom _ _ (by positivity), trivial⟩

end Formula
end RapidForcing.EffectiveProfile

end

end OAI
