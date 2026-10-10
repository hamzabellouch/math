import OAI.NumberTheory.JointDickman.Counting.SamplingSkeleton
import Mathlib.InformationTheory.Hamming

namespace OAI

/-!
# Concentration after restriction to a common good event

The extension used in the manuscript's sampling argument is constructed
explicitly from a finite good set. The only concentration hypothesis below
is the uniform-constant finite-product specialization of McDiarmid's
published bounded-differences inequality.
-/

open Finset
open scoped BigOperators

namespace JointDickman

section Extension

variable {ι A : Type*} [Fintype ι] [DecidableEq A]

/-- The finite McShane extension, clamped at the chosen upper bound. -/
noncomputable def goodSetExtension (G : Finset (ι → A)) (hG : G.Nonempty)
    (f : (ι → A) → ℝ) (c L : ℝ) (x : ι → A) : ℝ :=
  min L (G.inf' hG (fun y => f y + c * hammingDist x y))

theorem goodSetExtension_le (G : Finset (ι → A)) (hG : G.Nonempty)
    (f : (ι → A) → ℝ) (c L : ℝ) (x : ι → A) :
    goodSetExtension G hG f c L x ≤ L := min_le_left _ _

theorem goodSetExtension_nonneg (G : Finset (ι → A)) (hG : G.Nonempty)
    (f : (ι → A) → ℝ) {c L : ℝ} (hc : 0 ≤ c) (hL : 0 ≤ L)
    (hf : ∀ x ∈ G, 0 ≤ f x) (x : ι → A) :
    0 ≤ goodSetExtension G hG f c L x := by
  apply le_min hL
  apply Finset.le_inf'
  intro y hy
  exact add_nonneg (hf y hy) (mul_nonneg hc (Nat.cast_nonneg _))

theorem goodSetExtension_eq (G : Finset (ι → A)) (hG : G.Nonempty)
    (f : (ι → A) → ℝ) {c L : ℝ}
    (hlip : ∀ x ∈ G, ∀ y ∈ G, |f x - f y| ≤ c * hammingDist x y)
    (hupper : ∀ x ∈ G, f x ≤ L) {x : ι → A} (hx : x ∈ G) :
    goodSetExtension G hG f c L x = f x := by
  have hlow : f x ≤ G.inf' hG (fun y => f y + c * hammingDist x y) := by
    apply Finset.le_inf'
    intro y hy
    have h := (le_abs_self (f x - f y)).trans (hlip x hx y hy)
    linarith
  have hhigh : G.inf' hG (fun y => f y + c * hammingDist x y) ≤ f x := by
    calc
      _ ≤ f x + c * (hammingDist x x : ℝ) :=
        Finset.inf'_le (fun y => f y + c * (hammingDist x y : ℝ)) hx
      _ = f x := by simp
  unfold goodSetExtension
  rw [le_antisymm hhigh hlow, min_eq_right (hupper x hx)]

private theorem min_upper_add {L a b r : ℝ} (hr : 0 ≤ r) (hab : a ≤ b + r) :
    min L a ≤ min L b + r := by
  by_cases h : L ≤ b
  · rw [min_eq_left h]
    exact (min_le_left L a).trans (le_add_of_nonneg_right hr)
  · rw [min_eq_right (le_of_not_ge h)]
    exact (min_le_right L a).trans hab

theorem goodSetExtension_lipschitz (G : Finset (ι → A)) (hG : G.Nonempty)
    (f : (ι → A) → ℝ) {c : ℝ} (hc : 0 ≤ c) (L : ℝ) (x y : ι → A) :
    |goodSetExtension G hG f c L x - goodSetExtension G hG f c L y| ≤
      c * hammingDist x y := by
  have hone (x y : ι → A) :
      G.inf' hG (fun z => f z + c * hammingDist x z) ≤
        G.inf' hG (fun z => f z + c * hammingDist y z) + c * hammingDist x y := by
    suffices h : G.inf' hG (fun z => f z + c * hammingDist x z) -
        c * hammingDist x y ≤ G.inf' hG (fun z => f z + c * hammingDist y z) by
      linarith
    apply Finset.le_inf'
    intro z hz
    have hinf := Finset.inf'_le (fun z => f z + c * (hammingDist x z : ℝ)) hz
    have htri : (hammingDist x z : ℝ) ≤ hammingDist x y + hammingDist y z := by
      exact_mod_cast hammingDist_triangle x y z
    have hmul := mul_le_mul_of_nonneg_left htri hc
    linarith
  have hxy := min_upper_add (L := L) (mul_nonneg hc (Nat.cast_nonneg _)) (hone x y)
  have hyx := min_upper_add (L := L) (mul_nonneg hc (Nat.cast_nonneg _)) (hone y x)
  rw [hammingDist_comm y x] at hyx
  unfold goodSetExtension
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end Extension

section FiniteProbability

variable {Ω : Type*} [Fintype Ω]

/-- Expectation with respect to an explicitly supplied finite mass function. -/
noncomputable def finiteExpectation (w : Ω → ℝ) (f : Ω → ℝ) : ℝ :=
  ∑ x, w x * f x

/-- Event mass for the same finite law. -/
noncomputable def finiteProbability (w : Ω → ℝ) (E : Ω → Prop) : ℝ :=
  by classical exact ∑ x, if E x then w x else 0

theorem finiteProbability_mono (w : Ω → ℝ) (hw : ∀ x, 0 ≤ w x)
    {E F : Ω → Prop} (hEF : ∀ x, E x → F x) :
    finiteProbability w E ≤ finiteProbability w F := by
  classical
  apply sum_le_sum
  intro x _
  by_cases hE : E x
  · simp [hE, hEF x hE]
  · by_cases hF : F x <;> simp [hE, hF, hw x]

theorem finiteProbability_union_le {J : Type*} [Fintype J]
    (w : Ω → ℝ) (hw : ∀ x, 0 ≤ w x) (E : J → Ω → Prop) :
    finiteProbability w (fun x => ∃ j, E j x) ≤ ∑ j, finiteProbability w (E j) := by
  classical
  unfold finiteProbability
  rw [sum_comm]
  apply sum_le_sum
  intro x _
  by_cases h : ∃ j, E j x
  · obtain ⟨j, hj⟩ := h
    simp only [show (∃ j, E j x) from ⟨j, hj⟩, ite_true]
    have ht : (if E j x then w x else 0) ≤ ∑ k, if E k x then w x else 0 :=
      single_le_sum (f := fun k => if E k x then w x else 0)
        (fun k _ => by by_cases hk : E k x <;> simp [hk, hw x]) (mem_univ j)
    simpa [hj] using ht
  · simp only [h, ite_false]
    exact sum_nonneg (fun j _ => by by_cases hj : E j x <;> simp [hj, hw x])

/-- A common exceptional event is paid once, before the union over tests. -/
theorem finiteProbability_union_on_good {J : Type*} [Fintype J]
    (w : Ω → ℝ) (hw : ∀ x, 0 ≤ w x) (G : Ω → Prop) (E : J → Ω → Prop) :
    finiteProbability w (fun x => ∃ j, E j x) ≤
      finiteProbability w (fun x => ¬ G x) +
        ∑ j, finiteProbability w (fun x => G x ∧ E j x) := by
  classical
  have hs : finiteProbability w (fun x => ∃ j, E j x) ≤
      finiteProbability w (fun x => ¬ G x) +
        finiteProbability w (fun x => ∃ j, G x ∧ E j x) := by
    unfold finiteProbability
    rw [← sum_add_distrib]
    apply sum_le_sum
    intro x _
    by_cases hG : G x <;> by_cases hE : ∃ j, E j x
    · obtain ⟨j, hj⟩ := hE
      have hEx : ∃ j, E j x := ⟨j, hj⟩
      simp [hG, hEx]
    · simp [hG, hE]
    · simp [hG, hE]
    · simp [hG, hE, hw x]
  have hu := finiteProbability_union_le w hw (fun j x => G x ∧ E j x)
  linarith

variable {ι A : Type*} [Fintype ι] [DecidableEq ι] [Fintype A] [DecidableEq A]

theorem goodSetExtension_mean_le (G : Finset (ι → A)) (hG : G.Nonempty)
    (f : (ι → A) → ℝ) {c L : ℝ}
    (hlip : ∀ x ∈ G, ∀ y ∈ G, |f x - f y| ≤ c * hammingDist x y)
    (hupper : ∀ x ∈ G, f x ≤ L) (hf : ∀ x, 0 ≤ f x)
    (w : (ι → A) → ℝ) (hw : ∀ x, 0 ≤ w x) :
    finiteExpectation w (goodSetExtension G hG f c L) ≤
      finiteExpectation w f + L * finiteProbability w (fun x => x ∉ G) := by
  have hpoint (x : ι → A) : goodSetExtension G hG f c L x ≤
      f x + L * (if x ∉ G then 1 else 0) := by
    by_cases hx : x ∈ G
    · rw [goodSetExtension_eq G hG f hlip hupper hx]
      simp [hx]
    · have hu := goodSetExtension_le G hG f c L x
      simp only [hx, not_false_eq_true, ite_eq_left, mul_one]
      linarith [hf x]
  calc
    _ ≤ ∑ x, w x * (f x + L * (if x ∉ G then 1 else 0)) := by
      exact sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hpoint x) (hw x)
    _ = _ := by
      simp only [finiteExpectation, finiteProbability, mul_add, sum_add_distrib, mul_sum]
      congr 1
      apply sum_congr rfl
      intro x _
      split_ifs <;> ring

end FiniteProbability

namespace PublishedInputs

/-- Independent site mass, retaining the actual coordinate laws. -/
noncomputable def siteProductMass {ι A : Type*} [Fintype ι]
    (p : ι → A → ℝ) (x : ι → A) : ℝ := ∏ i, p i (x i)

/-- McDiarmid, *On the method of bounded differences*, Surveys in
Combinatorics 1989, Theorem (6.7), pp. 166–167 (proof p. 168),
DOI `10.1017/CBO9781107359949.008`. The one-sided estimate follows by
applying that martingale theorem to the coordinate Doob martingale.
Only independent finite sites and one common coordinate bound are needed.
The global Hamming bound is a stronger sufficient hypothesis on `f`. -/
def FiniteMcDiarmidInput (ι A : Type*) [Fintype ι] [DecidableEq ι]
    [Fintype A] [DecidableEq A] : Prop :=
  ∀ (p : ι → A → ℝ), (∀ i a, 0 ≤ p i a) → (∀ i, ∑ a, p i a = 1) →
    ∀ (f : (ι → A) → ℝ) (c : ℝ), 0 ≤ c →
      (∀ x y, |f x - f y| ≤ c * hammingDist x y) →
      ∀ a : ℝ, 0 < a →
        finiteProbability (siteProductMass p)
          (fun x => a < f x - finiteExpectation (siteProductMass p) f) ≤
          Real.exp (-2 * a ^ 2 / ((Fintype.card ι : ℝ) * c ^ 2))

end PublishedInputs

section TailBound

variable {ι A : Type*} [Fintype ι] [DecidableEq ι] [Fintype A] [DecidableEq A]

theorem abs_clamp_sub_clamp_le (L x y : ℝ) : |min L x - min L y| ≤ |x - y| := by
  simpa using abs_min_sub_min_le_max L x L y

/-- A concentration bound valid on one common good event. The cost of the
bad event enters the mean only once, before any later union bound. -/
theorem goodSet_concentration (hMC : PublishedInputs.FiniteMcDiarmidInput ι A)
    (p : ι → A → ℝ) (hp : ∀ i a, 0 ≤ p i a) (hpone : ∀ i, ∑ a, p i a = 1)
    (G : Finset (ι → A)) (hG : G.Nonempty) (Z : (ι → A) → ℝ)
    {c L u a : ℝ} (hc : 0 ≤ c) (hL : 0 ≤ L) (ha : 0 < a)
    (hZ : ∀ x, 0 ≤ Z x)
    (hlip : ∀ x ∈ G, ∀ y ∈ G, |Z x - Z y| ≤ c * hammingDist x y)
    (hmean : finiteExpectation (PublishedInputs.siteProductMass p) Z +
      L * finiteProbability (PublishedInputs.siteProductMass p) (fun x => x ∉ G) ≤ u)
    (hcut : u + a < L) :
    finiteProbability (PublishedInputs.siteProductMass p)
      (fun x => x ∈ G ∧ u + a < Z x) ≤
        Real.exp (-2 * a ^ 2 / ((Fintype.card ι : ℝ) * c ^ 2)) := by
  let f : (ι → A) → ℝ := fun x => min L (Z x)
  let W := goodSetExtension G hG f c L
  have hw (x : ι → A) : 0 ≤ PublishedInputs.siteProductMass p x :=
    prod_nonneg fun i _ => hp i (x i)
  have hf (x : ι → A) : 0 ≤ f x := le_min hL (hZ x)
  have hupper (x : ι → A) (_ : x ∈ G) : f x ≤ L := min_le_left _ _
  have hflips : ∀ x ∈ G, ∀ y ∈ G, |f x - f y| ≤ c * hammingDist x y := by
    intro x hx y hy
    exact (abs_clamp_sub_clamp_le L (Z x) (Z y)).trans (hlip x hx y hy)
  have hEW : finiteExpectation (PublishedInputs.siteProductMass p) W ≤ u := by
    have hext := goodSetExtension_mean_le G hG f hflips hupper hf
      (PublishedInputs.siteProductMass p) hw
    have hfZ : finiteExpectation (PublishedInputs.siteProductMass p) f ≤
        finiteExpectation (PublishedInputs.siteProductMass p) Z :=
      sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (min_le_right _ _) (hw x)
    linarith
  have hWlip : ∀ x y, |W x - W y| ≤ c * hammingDist x y :=
    goodSetExtension_lipschitz G hG f hc L
  have htail := hMC p hp hpone W c hc hWlip a ha
  refine (finiteProbability_mono _ hw ?_).trans htail
  intro x ⟨hxG, hxZ⟩
  have heq : W x = f x := goodSetExtension_eq G hG f hflips hupper hxG
  have hxf : u + a < f x := lt_min hcut hxZ
  rw [heq]
  linarith

end TailBound

section SparseKernel

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
private theorem column_abs_sum_sub_le (K K' : ι → ι → ℝ) :
    |(∑ j, |∑ i, K i j|) - (∑ j, |∑ i, K' i j|)| ≤
      ∑ j, ∑ i, |K i j - K' i j| := by
  rw [← sum_sub_distrib]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun j _ => ?_)
  exact (abs_abs_sub_abs_le_abs_sub _ _).trans (by
    rw [← sum_sub_distrib]
    exact abs_sum_le_sum_abs _ _)

/-- Only edges incident to changed coordinates contribute to the response.
The argument uses the two endpoint degree bounds directly, without a path
of intermediate good configurations. -/
theorem incident_change_mass_le (K K' H : ι → ι → ℝ) (T : Finset ι)
    (hsym : ∀ i j, H i j = H j i) (hH : ∀ i j, 0 ≤ H i j)
    (d : ℝ) (hrow : ∀ i, (∑ j, H i j) ≤ d)
    (hbound : ∀ i j, |K i j - K' i j| ≤ H i j)
    (heq : ∀ i ∉ T, ∀ j ∉ T, K i j = K' i j) :
    (∑ j, ∑ i, |K i j - K' i j|) ≤ 2 * T.card * d := by
  let b : ι → ℝ := fun i => if i ∈ T then 1 else 0
  have hterm (i j : ι) : |K i j - K' i j| ≤ H i j * b i + H i j * b j := by
    by_cases hi : i ∈ T <;> by_cases hj : j ∈ T
    · simp only [b, hi, hj, ite_eq_left, mul_one]
      linarith [hbound i j, hH i j]
    · simpa [b, hi, hj]
        using hbound i j
    · simpa [b, hi, hj]
        using hbound i j
    · simp [b, hi, hj, heq i hi j hj]
  have hfirst : (∑ j, ∑ i, H i j * b i) ≤ T.card * d := by
    rw [sum_comm]
    simp_rw [← sum_mul]
    calc
      _ = ∑ i ∈ T, ∑ j, H i j := by simp [b]
      _ ≤ ∑ _i ∈ T, d := sum_le_sum fun i _ => hrow i
      _ = _ := by simp
  have hsecond : (∑ j, ∑ i, H i j * b j) ≤ T.card * d := by
    simp_rw [← sum_mul]
    calc
      _ = ∑ j ∈ T, ∑ i, H i j := by simp [b]
      _ = ∑ j ∈ T, ∑ i, H j i := by simp_rw [hsym]
      _ ≤ ∑ _j ∈ T, d := sum_le_sum fun j _ => hrow j
      _ = _ := by simp
  have hs := sum_le_sum (s := (univ : Finset ι))
    (fun j _ => sum_le_sum (s := (univ : Finset ι)) (fun i _ => hterm i j))
  simp only [sum_add_distrib] at hs
  linarith

variable {A : Type*} [DecidableEq A]

/-- The unnormalized residual column response for fixed single-site tests. -/
noncomputable def siteColumnResponse (E : ι → ι → A → A → ℝ)
    (g : ι → A → ℝ) (x : ι → A) : ℝ :=
  ∑ j, |∑ i, E i j (x i) (x j) * g i (x i)|

theorem siteColumnResponse_lipschitz_on_good
    (E H : ι → ι → A → A → ℝ) (g : ι → A → ℝ)
    (hsym : ∀ i j a b, H i j a b = H j i b a)
    (hdom : ∀ i j a b, |E i j a b| ≤ H i j a b)
    (hg : ∀ i a, |g i a| ≤ 1) (d : ℝ) (x y : ι → A)
    (hx : ∀ i, (∑ j, H i j (x i) (x j)) ≤ d)
    (hy : ∀ i, (∑ j, H i j (y i) (y j)) ≤ d) :
    |siteColumnResponse E g x - siteColumnResponse E g y| ≤
      (4 * d) * hammingDist x y := by
  let K : ι → ι → ℝ := fun i j => E i j (x i) (x j) * g i (x i)
  let K' : ι → ι → ℝ := fun i j => E i j (y i) (y j) * g i (y i)
  let V : ι → ι → ℝ := fun i j => H i j (x i) (x j) + H i j (y i) (y j)
  let T : Finset ι := univ.filter (fun i => x i ≠ y i)
  have hV (i j : ι) : 0 ≤ V i j := add_nonneg
    ((abs_nonneg _).trans (hdom i j (x i) (x j)))
    ((abs_nonneg _).trans (hdom i j (y i) (y j)))
  have hrow (i : ι) : (∑ j, V i j) ≤ 2 * d := by
    simp only [V, sum_add_distrib]
    linarith [hx i, hy i]
  have hmul (i j : ι) (a b : A) : |E i j a b * g i a| ≤ H i j a b := by
    rw [abs_mul]
    exact ((mul_le_mul_of_nonneg_left (hg i a) (abs_nonneg _)).trans_eq (mul_one _)).trans
      (hdom i j a b)
  have hbound (i j : ι) : |K i j - K' i j| ≤ V i j :=
    (abs_sub _ _).trans (add_le_add (hmul i j (x i) (x j)) (hmul i j (y i) (y j)))
  have heq (i : ι) (hi : i ∉ T) (j : ι) (hj : j ∉ T) : K i j = K' i j := by
    have hei : x i = y i := by simpa [T] using hi
    have hej : x j = y j := by simpa [T] using hj
    simp [K, K', hei, hej]
  have hmass := incident_change_mass_le K K' V T
    (fun i j => by simp only [V, hsym]) hV (2 * d) hrow hbound heq
  have hcol := column_abs_sum_sub_le K K'
  change |siteColumnResponse E g x - siteColumnResponse E g y| ≤ _ at hcol
  have hc : T.card = hammingDist x y := rfl
  rw [hc] at hmass
  nlinarith

end SparseKernel

end JointDickman

end OAI
