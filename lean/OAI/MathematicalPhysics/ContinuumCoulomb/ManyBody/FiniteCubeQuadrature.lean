import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.RectangleQuadrature

namespace OAI

/-! Product-interval integration and its uniform coordinate modulus. The
application uses dimension six; the recursion only avoids repeating six
identical one-dimensional estimates. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb.UniformQuadrature

def cubeMem {n : ℕ} (a b : ℝ) (v : Fin n → ℝ) : Prop := ∀ i, v i ∈ Set.Icc a b

def cubeModulus {n : ℕ} (a b L : ℝ) (f : (Fin n → ℝ) → ℝ) : Prop :=
  ∀ v, cubeMem a b v → ∀ w, cubeMem a b w →
    |f v - f w| ≤ L * ∑ i, |v i - w i|

def cubeIntegral (a b : ℝ) : (n : ℕ) → ((Fin n → ℝ) → ℝ) → ℝ
  | 0, f => f Fin.elim0
  | n + 1, f => ∫ x in a..b, cubeIntegral a b n (fun v => f (Fin.cons x v))

def cubeSample (h : ℝ) (N : ℕ) : (n : ℕ) → ((Fin n → ℕ) → ℝ) → ℝ
  | 0, v => v Fin.elim0
  | n + 1, v => sampleSum h N (fun i => cubeSample h N n (fun w => v (Fin.cons i w)))

theorem cubeMem_cons {n : ℕ} {a b x : ℝ} {v : Fin n → ℝ}
    (hx : x ∈ Set.Icc a b) (hv : cubeMem a b v) : cubeMem a b (Fin.cons x v) := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact hx
  · exact hv j

theorem cubeModulus_section {n : ℕ} {a b L : ℝ} {f : (Fin (n + 1) → ℝ) → ℝ}
    (hf : cubeModulus a b L f) {x : ℝ} (hx : x ∈ Set.Icc a b) :
    cubeModulus a b L (fun v => f (Fin.cons x v)) := by
  intro v hv w hw
  have h := hf (Fin.cons x v) (cubeMem_cons hx hv) (Fin.cons x w) (cubeMem_cons hx hw)
  simpa only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, sub_self, abs_zero, zero_add] using h

theorem cubeModulus_head {n : ℕ} {a b L x y : ℝ} {f : (Fin (n + 1) → ℝ) → ℝ}
    (hf : cubeModulus a b L f) (hx : x ∈ Set.Icc a b) (hy : y ∈ Set.Icc a b)
    {v : Fin n → ℝ} (hv : cubeMem a b v) :
    |f (Fin.cons x v) - f (Fin.cons y v)| ≤ L * |x - y| := by
  have h := hf (Fin.cons x v) (cubeMem_cons hx hv) (Fin.cons y v) (cubeMem_cons hy hv)
  simpa only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, sub_self, abs_zero,
    Finset.sum_const_zero, add_zero] using h

theorem cubeIntegral_difference (n : ℕ) {a b Lf Lg ε : ℝ}
    (hab : a ≤ b) (hLf : 0 ≤ Lf) (hLg : 0 ≤ Lg) (hε : 0 ≤ ε)
    {f g : (Fin n → ℝ) → ℝ}
    (hf : cubeModulus a b Lf f) (hg : cubeModulus a b Lg g)
    (hfg : ∀ v, cubeMem a b v → |f v - g v| ≤ ε) :
    |cubeIntegral a b n f - cubeIntegral a b n g| ≤ (b - a) ^ n * ε := by
  induction n generalizing a b Lf Lg ε with
  | zero =>
    simpa only [cubeIntegral, pow_zero, one_mul] using hfg Fin.elim0 (by intro i; exact Fin.elim0 i)
  | succ n ih =>
    let F : ℝ → ℝ := fun x => cubeIntegral a b n (fun v => f (Fin.cons x v))
    let G : ℝ → ℝ := fun x => cubeIntegral a b n (fun v => g (Fin.cons x v))
    have hF : ContinuousOn F (Set.Icc a b) := by
      apply continuousOn_of_abs_sub_le (L := (b - a) ^ n * Lf)
      intro x hx y hy
      have hi := ih hab hLf hLf (mul_nonneg hLf (abs_nonneg (x - y)))
        (cubeModulus_section hf hx) (cubeModulus_section hf hy)
        (fun v hv => cubeModulus_head hf hx hy hv)
      convert hi using 1
      ring
    have hG : ContinuousOn G (Set.Icc a b) := by
      apply continuousOn_of_abs_sub_le (L := (b - a) ^ n * Lg)
      intro x hx y hy
      have hi := ih hab hLg hLg (mul_nonneg hLg (abs_nonneg (x - y)))
        (cubeModulus_section hg hx) (cubeModulus_section hg hy)
        (fun v hv => cubeModulus_head hg hx hy hv)
      convert hi using 1
      ring
    have hdiff (x : ℝ) (hx : x ∈ Set.Icc a b) : |F x - G x| ≤ (b - a) ^ n * ε :=
      ih hab hLf hLg hε (cubeModulus_section hf hx) (cubeModulus_section hg hx)
        (fun v hv => hfg (Fin.cons x v) (cubeMem_cons hx hv))
    change |(∫ x in a..b, F x) - ∫ x in a..b, G x| ≤ _
    rw [← intervalIntegral.integral_sub (hF.intervalIntegrable_of_Icc hab)
      (hG.intervalIntegrable_of_Icc hab)]
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (f := fun x => F x - G x) (a := a) (b := b) (C := (b - a) ^ n * ε) (by
        intro x hx
        have hx' : x ∈ Set.Ioc a b := by simpa only [Set.uIoc_of_le hab] using hx
        simpa only [Real.norm_eq_abs] using hdiff x ⟨hx'.1.le, hx'.2⟩)
    rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hab)] at h
    convert h using 1
    rw [pow_succ]
    ring

theorem cubeIntegral_head_modulus {n : ℕ} {a b L : ℝ}
    (hab : a ≤ b) (hL : 0 ≤ L) {f : (Fin (n + 1) → ℝ) → ℝ}
    (hf : cubeModulus a b L f) {x y : ℝ}
    (hx : x ∈ Set.Icc a b) (hy : y ∈ Set.Icc a b) :
    |cubeIntegral a b n (fun v => f (Fin.cons x v)) -
      cubeIntegral a b n (fun v => f (Fin.cons y v))| ≤
        ((b - a) ^ n * L) * |x - y| := by
  have h := cubeIntegral_difference n hab hL hL (mul_nonneg hL (abs_nonneg (x - y)))
    (cubeModulus_section hf hx) (cubeModulus_section hf hy)
    (fun v hv => cubeModulus_head hf hx hy hv)
  convert h using 1
  ring


theorem cube_quadrature_error (n : ℕ) {a h L ε : ℝ} {N : ℕ}
    (hh : 0 ≤ h) (hL : 0 ≤ L) (hε : 0 ≤ ε)
    {f : (Fin n → ℝ) → ℝ} {v : (Fin n → ℕ) → ℝ}
    (hf : cubeModulus a (node a h N) L f)
    (hv : ∀ w, (∀ i, w i < N) →
      |v w - f (fun i => node a h (w i))| ≤ ε) :
    |cubeSample h N n v - cubeIntegral a (node a h N) n f| ≤
      ((N : ℝ) * h) ^ n * ((n : ℝ) * L * h + ε) := by
  induction n generalizing a h N L ε with
  | zero =>
    have hbase := hv Fin.elim0 (by intro i; exact Fin.elim0 i)
    have he : (fun i : Fin 0 => node a h (Fin.elim0 i)) = Fin.elim0 := Subsingleton.elim _ _
    simpa only [cubeSample, cubeIntegral, he, pow_zero, Nat.cast_zero, zero_mul,
      zero_add, one_mul] using hbase
  | succ n ih =>
    let b := node a h N
    let F : ℝ → ℝ := fun x => cubeIntegral a b n (fun w => f (Fin.cons x w))
    let V : ℕ → ℝ := fun i => cubeSample h N n (fun w => v (Fin.cons i w))
    have hab : a ≤ b := (node_mem hh (Nat.le_refl N)).1
    have hlen : b - a = (N : ℝ) * h := by dsimp [b, node]; ring
    have hLf : 0 ≤ (b - a) ^ n * L := mul_nonneg (pow_nonneg (sub_nonneg.mpr hab) _) hL
    have hLip : ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b,
        |F x - F y| ≤ ((b - a) ^ n * L) * |x - y| := by
      intro x hx y hy
      exact cubeIntegral_head_modulus hab hL hf hx hy
    have hinner : ∀ i < N, |V i - F (node a h i)| ≤
        ((N : ℝ) * h) ^ n * ((n : ℝ) * L * h + ε) := by
      intro i hi
      apply ih hh hL hε (cubeModulus_section hf (node_mem hh hi.le))
      intro w hw
      have hwi : ∀ j : Fin (n + 1), (Fin.cons i w : Fin (n + 1) → ℕ) j < N := by
        intro j
        refine Fin.cases ?_ (fun k => ?_) j
        · simpa only [Fin.cons_zero] using hi
        · simpa only [Fin.cons_succ] using hw k
      have hpoint := hv (Fin.cons i w) hwi
      have he : (fun j : Fin (n + 1) => node a h ((Fin.cons i w : Fin (n + 1) → ℕ) j)) =
          Fin.cons (node a h i) (fun j => node a h (w j)) := by
        funext j
        exact Fin.cases rfl (fun _ => rfl) j
      simpa only [he] using hpoint
    have hout := samples_error_lipschitz F V a h N hh hLf hLip hinner
    change |cubeSample h N (n + 1) v - cubeIntegral a b (n + 1) f| ≤ _
    change |sampleSum h N V - ∫ x in a..b, F x| ≤ _
    apply hout.trans_eq
    rw [hlen, pow_succ, Nat.cast_add, Nat.cast_one]
    ring

end ContinuumCoulomb.UniformQuadrature

end

end OAI
