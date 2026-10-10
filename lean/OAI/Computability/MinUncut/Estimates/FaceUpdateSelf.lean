import Mathlib
import OAI.Computability.MinUncut.Analysis.FaceCorrelation
import OAI.Computability.MinUncut.Estimates.SelectedProject
import OAI.Computability.MinUncut.Graphs.Vertex

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory Polynomial Filter
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory WithLp
open scoped BigOperators RealInnerProductSpace
open scoped BigOperators
namespace MinUncut.Inner
open scoped BigOperators
variable {m n : ℕ}

lemma face_update_self (x : Point m n) (i : Fin m) (z : Fin n) :
    face (Function.update x i z) i = face x i := by
  funext j
  exact Function.update_of_ne j.property _ _

theorem faceCorrelation_box_cs (hm : 0 < m) (hn : 0 < n) (v : Point m n → ℝ) :
    faceCorrelation v ^ (2^m) ≤ Box.moment v := by
  have : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  obtain ⟨z, _, hz⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
    (fun z : Code m n => |𝔼 x : Point m n, v x * BinaryFourier.sign (z.val x)|)
  change faceCorrelation v = _ at hz
  obtain ⟨b, hb⟩ := z.property
  let a : Fin m → Point m n → ℝ := fun i x => BinaryFourier.sign (b ⟨i, face x i⟩)
  have ha : Box.Local a := by
    intro i x t
    simp only [a, face_update_self]
  have hc : |Box.correlation v a| = faceCorrelation v := by
    rw [hz]
    unfold Box.correlation
    congr 1
    apply Finset.expect_congr rfl
    intro x _
    congr 1
    have hbx : z.val x = ∑ i, b ⟨i, face x i⟩ := congrFun hb.symm x
    simp only [hbx, RowNoise.sign_sum, a]
  rw [← hc]
  exact Box.abs_correlation_cs hm v a ha (fun _ _ => (BinaryFourier.sign_abs _).le)
end MinUncut.Inner

namespace MinUncut.GaussianHermite
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def indexSym (s : ℕ) (I : {I : ι → ℕ // I ∈ low s}) : Sym (Option ι) s :=
  ⟨(∑ i, Multiset.replicate (I.val i) (some i)) +
    Multiset.replicate (s-degree I.val) none, by
      rw [Multiset.card_add, Multiset.card_sum, Multiset.card_replicate]
      simp only [Multiset.card_replicate]
      exact Nat.add_sub_of_le ((mem_low _ _).mp I.property)⟩

lemma count_indexSym (s : ℕ) (I : {I : ι → ℕ // I ∈ low s}) (i : ι) :
    Multiset.count (some i) (indexSym s I).val = I.val i := by
  simp [indexSym, Multiset.count_sum', Multiset.count_replicate]

lemma indexSym_injective (s : ℕ) : Function.Injective (indexSym (ι := ι) s) := by
  intro I J h
  apply Subtype.ext
  funext i
  simpa only [count_indexSym] using congrArg (fun z : Sym (Option ι) s => Multiset.count (some i) z.val) h

lemma card_low_le (s : ℕ) : (low (ι := ι) s).card ≤ (Fintype.card ι+s).choose s := by
  have h := Fintype.card_le_of_injective _ (indexSym_injective (ι := ι) s)
  simpa only [Fintype.card_coe, Sym.card_sym_eq_choose, Fintype.card_option,
    Nat.add_right_comm (Fintype.card ι) 1 s, Nat.add_sub_cancel] using h
end MinUncut.GaussianHermite
namespace MinUncut.RowNoise
open MeasureTheory ProbabilityTheory BinaryFourier GaussianHermite
open scoped BigOperators
local instance faceUpdateSelfRowDualFintype {U : Type*}
    [AddCommGroup U] [Module F₂ U] [Fintype U] :
    Fintype (Module.Dual F₂ U) := BinaryFourier.dualFintype
variable {R W ι : Type*} [Fintype R] [DecidableEq R] [Fintype W] [DecidableEq W]
  [AddCommGroup W] [Module F₂ W] [Fintype ι] [DecidableEq ι]

lemma selectedProject_atom_mean_uniform (s : ℕ) (J : Finset (Finset R × (ι → ℕ)))
    (hJ : ∀ j ∈ J, GaussianHermite.degree j.2 ≤ s) (r : R) (one : W)
    (u : (R → W) → (ι → ℝ) → ℝ) (hu : ∀ B, MemLp (u B) 2 (γpi ι)) :
    (𝔼 D, ∫ c, oddAtom r one (fun B => selectedProject J u B c) D ∂γpi ι) ≤
      (4:ℝ)^Fintype.card R * ((Fintype.card ι+s).choose s : ℝ) * Real.sqrt
        (𝔼 D, ∫ c, (oddAtom r one (fun B => u B c) D)^2 ∂γpi ι) := by
  have hj : J ⊆ (Finset.univ : Finset (Finset R)) ×ˢ low s := by
    intro j hj
    exact Finset.mem_product.mpr ⟨Finset.mem_univ _, (mem_low _ _).mpr (hJ j hj)⟩
  have hc : J.card ≤ 2^Fintype.card R * (Fintype.card ι+s).choose s := by
    calc
      J.card ≤ ((Finset.univ : Finset (Finset R)) ×ˢ low s).card := Finset.card_le_card hj
      _ = 2^Fintype.card R * (low (ι := ι) s).card := by simp
      _ ≤ _ := Nat.mul_le_mul_left _ (card_low_le s)
  have hc' : (J.card : ℝ) ≤ (2:ℝ)^Fintype.card R * ((Fintype.card ι+s).choose s : ℝ) := by exact_mod_cast hc
  refine (selectedProject_atom_mean J r one u hu).trans ?_
  have hp : (2:ℝ)^Fintype.card R * (2:ℝ)^Fintype.card R = (4:ℝ)^Fintype.card R := by
    rw [← mul_pow]; norm_num
  calc
    _ ≤ ((2:ℝ)^Fintype.card R * ((Fintype.card ι+s).choose s : ℝ)) *
        (2:ℝ)^Fintype.card R * Real.sqrt
        (𝔼 D, ∫ c, (oddAtom r one (fun B => u B c) D)^2 ∂γpi ι) := by
      gcongr
    _ = _ := by rw [mul_right_comm ((2:ℝ)^Fintype.card R), hp]
end MinUncut.RowNoise
namespace MinUncut.Slice
open BinaryFourier
variable {W : Type*} [Fintype W] [DecidableEq W] [AddCommGroup W] [Module F₂ W]

def clip (A z : ℝ) : ℝ := max (-A) (min z A)

lemma clip_abs_le {A : ℝ} (hA : 0 ≤ A) (z : ℝ) : |clip A z| ≤ A := by
  rw [abs_le]
  constructor
  · exact le_max_left _ _
  · exact max_le (by linarith) (min_le_right _ _)

lemma clip_abs_le_self {A : ℝ} (hA : 0 ≤ A) (z : ℝ) : |clip A z| ≤ |z| := by
  unfold clip
  rcases le_total z A with hz | hz
  · rw [min_eq_left hz]
    rcases le_total (-A) z with ha | ha
    · rw [max_eq_right ha]
    · rw [max_eq_left ha, abs_neg, abs_of_nonneg hA, abs_of_nonpos (by linarith)]
      linarith
  · rw [min_eq_right hz, max_eq_right (by linarith), abs_of_nonneg hA,
      abs_of_nonneg (by linarith)]
    exact hz

lemma clip_loss {A : ℝ} (hA : 0 < A) (z : ℝ) : |z-clip A z| ≤ z^2/A := by
  rw [le_div_iff₀ hA]
  unfold clip
  rcases le_total z A with hz | hz
  · rw [min_eq_left hz]
    rcases le_total (-A) z with ha | ha
    · rw [max_eq_right ha]; simpa using sq_nonneg z
    · rw [max_eq_left ha, abs_of_nonpos (by linarith)]
      nlinarith [sq_nonneg (z+A), mul_nonneg (le_of_lt hA) (show 0 ≤ -z-A by linarith)]
  · rw [min_eq_right hz, max_eq_right (by linarith), abs_of_nonneg (by linarith)]
    nlinarith [sq_nonneg (z-A), mul_nonneg (le_of_lt hA) (show 0 ≤ z-A by linarith)]

lemma clip_sq_le {A : ℝ} (hA : 0 ≤ A) (z : ℝ) : clip A z ^2 ≤ z^2 := by
  have h := clip_abs_le_self hA z
  nlinarith [abs_nonneg (clip A z), abs_nonneg z, sq_abs (clip A z), sq_abs z]

omit [DecidableEq W] in
lemma coefficient_lipschitz (f g : W → ℝ) (α : Module.Dual F₂ W) :
    |coefficient f α - coefficient g α| ≤ 𝔼 w, |f w-g w| := by
  simp only [coefficient, ← Finset.expect_sub_distrib, ← sub_mul]
  calc
    _ ≤ 𝔼 w, |(f w-g w)*character α w| := by
      simp only [Finset.expect_eq_sum_div_card, abs_div, Nat.abs_cast]
      exact div_le_div_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) (by positivity)
    _ = _ := by simp only [abs_mul, character_abs, mul_one]

omit [DecidableEq W] [AddCommGroup W] [Module F₂ W] in
lemma clip_mean_loss {A : ℝ} (hA : 0 < A) (f : W → ℝ) :
    (𝔼 w, |f w-clip A (f w)|) ≤ (𝔼 w, (f w)^2)/A := by
  calc
    _ ≤ 𝔼 w, (f w)^2/A := Finset.expect_le_expect (fun w _ => clip_loss hA (f w))
    _ = _ := by simp [Finset.expect_div]

local instance faceUpdateSelfSliceDualFintype : Fintype (Module.Dual F₂ W) :=
  BinaryFourier.dualFintype

def oddMax (one : W) (f : W → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun α : Module.Dual F₂ W =>
    if α one = 1 then |coefficient f α| else 0)

omit [DecidableEq W] in
lemma oddMax_nonneg (one : W) (f : W → ℝ) : 0 ≤ oddMax one f := by
  have h := Finset.le_sup' (fun α : Module.Dual F₂ W =>
    if α one = 1 then |coefficient f α| else 0) (Finset.mem_univ 0)
  change 0 ≤ Finset.univ.sup' Finset.univ_nonempty _
  simpa only [LinearMap.zero_apply, zero_ne_one, ↓reduceIte] using h

omit [DecidableEq W] in
lemma coefficient_le_oddMax (one : W) (f : W → ℝ)
    (hodd : ∀ α : Module.Dual F₂ W, α one ≠ 1 → coefficient f α = 0)
    (α : Module.Dual F₂ W) : |coefficient f α| ≤ oddMax one f := by
  by_cases h : α one = 1
  · have h' := Finset.le_sup' (fun α : Module.Dual F₂ W =>
      if α one = 1 then |coefficient f α| else 0) (Finset.mem_univ α)
    simpa only [h, ↓reduceIte, oddMax] using h'
  · rw [hodd α h, abs_zero]
    exact oddMax_nonneg one f

def processed (H γ A : ℝ) (one : W) (f : W → ℝ) (w : W) : ℝ :=
  if H < Real.sqrt (𝔼 b, (f b)^2) ∨ γ < oddMax one f then 0 else clip A (f w)

omit [DecidableEq W] in
lemma processed_abs_le {H γ A : ℝ} (hA : 0 ≤ A) (one : W) (f : W → ℝ) (w : W) :
    |processed H γ A one f w| ≤ A := by
  unfold processed; split_ifs
  · simpa using hA
  · exact clip_abs_le hA _

omit [DecidableEq W] in
lemma processed_sq_le {H γ A : ℝ} (hA : 0 ≤ A) (one : W) (f : W → ℝ) (w : W) :
    (processed H γ A one f w)^2 ≤ (f w)^2 := by
  unfold processed; split_ifs
  · simpa using sq_nonneg (f w)
  · exact clip_sq_le hA _

omit [DecidableEq W] in
lemma processed_energy_le {H γ A : ℝ} (hA : 0 ≤ A) (one : W) (f : W → ℝ) :
    (𝔼 w, (processed H γ A one f w)^2) ≤ H^2 := by
  by_cases h : H < Real.sqrt (𝔼 b, (f b)^2) ∨ γ < oddMax one f
  · simp only [processed, h, ↓reduceIte, zero_pow (by omega : 2 ≠ 0), Fintype.expect_const]
    exact sq_nonneg H
  · have hs : Real.sqrt (𝔼 b, (f b)^2) ≤ H := le_of_not_gt (fun ht => h (Or.inl ht))
    have he : 0 ≤ 𝔼 b, (f b)^2 := Finset.expect_nonneg (fun _ _ => sq_nonneg _)
    calc
      _ ≤ 𝔼 w, (f w)^2 := Finset.expect_le_expect (fun w _ => processed_sq_le hA one f w)
      _ ≤ H^2 := by nlinarith [Real.sq_sqrt he, Real.sqrt_nonneg (𝔼 b, (f b)^2)]

omit [DecidableEq W] in
lemma processed_coefficient_le {H γ A : ℝ} (hA : 0 < A) (hγ : 0 ≤ γ)
    (one : W) (f : W → ℝ)
    (hodd : ∀ α : Module.Dual F₂ W, α one ≠ 1 → coefficient f α = 0)
    (α : Module.Dual F₂ W) :
    |coefficient (processed H γ A one f) α| ≤ γ + H^2/A := by
  by_cases h : H < Real.sqrt (𝔼 b, (f b)^2) ∨ γ < oddMax one f
  · simp only [processed, h, ↓reduceIte, coefficient, zero_mul, Fintype.expect_const, abs_zero]
    positivity
  · have hs : Real.sqrt (𝔼 b, (f b)^2) ≤ H := le_of_not_gt (fun ht => h (Or.inl ht))
    have hq : oddMax one f ≤ γ := le_of_not_gt (fun ht => h (Or.inr ht))
    have he : 0 ≤ 𝔼 b, (f b)^2 := Finset.expect_nonneg (fun _ _ => sq_nonneg _)
    have hE : (𝔼 b, (f b)^2) ≤ H^2 := by
      nlinarith [Real.sq_sqrt he, Real.sqrt_nonneg (𝔼 b, (f b)^2)]
    have hp : processed H γ A one f = fun w => clip A (f w) := by funext w; simp only [processed, h, ↓reduceIte]
    rw [hp]
    calc
      _ ≤ |coefficient (fun w => clip A (f w)) α - coefficient f α| + |coefficient f α| := by
        have hh := abs_add_le (coefficient (fun w => clip A (f w)) α - coefficient f α) (coefficient f α)
        simpa only [sub_add_cancel] using hh
      _ ≤ (𝔼 w, |clip A (f w)-f w|) + oddMax one f := add_le_add
        (coefficient_lipschitz _ _ _) (coefficient_le_oddMax one f hodd α)
      _ = (𝔼 w, |f w-clip A (f w)|) + oddMax one f := by simp_rw [abs_sub_comm]
      _ ≤ (𝔼 w, (f w)^2)/A + γ := add_le_add (clip_mean_loss hA f) hq
      _ ≤ γ + H^2/A := by linarith [div_le_div_of_nonneg_right hE (le_of_lt hA)]

open BinaryFourier
variable {W : Type*} [Fintype W] [DecidableEq W] [AddCommGroup W] [Module F₂ W]

omit [DecidableEq W] [Module F₂ W] in
lemma mean_abs_le_sqrt (f : W → ℝ) :
    (𝔼 w, |f w|) ≤ Real.sqrt (𝔼 w, (f w)^2) := by
  have h := Box.expect_sq_le (fun w => |f w|)
  simp only [sq_abs] at h
  have he : 0 ≤ 𝔼 w, (f w)^2 := Finset.expect_nonneg (fun _ _ => sq_nonneg _)
  exact (Real.le_sqrt (Finset.expect_nonneg (fun _ _ => abs_nonneg _)) he).mpr h

omit [DecidableEq W] in
lemma processed_mean_loss {H γ A : ℝ} (hH : 0 < H) (hA : 0 < A)
    (one : W) (f : W → ℝ) :
    (𝔼 w, |f w-processed H γ A one f w|) ≤
      (𝔼 w, (f w)^2)/H +
      (if γ < oddMax one f then Real.sqrt (𝔼 w, (f w)^2) else 0) +
      (𝔼 w, (f w)^2)/A := by
  have hE : 0 ≤ 𝔼 w, (f w)^2 := Finset.expect_nonneg (fun _ _ => sq_nonneg _)
  have hu : 0 ≤ (𝔼 w, (f w)^2)/H := div_nonneg hE hH.le
  have hv : 0 ≤ (𝔼 w, (f w)^2)/A := div_nonneg hE hA.le
  by_cases hn : H < Real.sqrt (𝔼 w, (f w)^2)
  · simp only [processed, hn, true_or, ↓reduceIte, sub_zero]
    have ht : Real.sqrt (𝔼 w, (f w)^2) ≤ (𝔼 w, (f w)^2)/H := by
      rw [le_div_iff₀ hH]
      have hh := mul_le_mul_of_nonneg_left hn.le (Real.sqrt_nonneg (𝔼 w, (f w)^2))
      nlinarith [Real.sq_sqrt hE]
    have hi : 0 ≤ if γ < oddMax one f then Real.sqrt (𝔼 w, (f w)^2) else 0 := by split_ifs <;> positivity
    linarith [mean_abs_le_sqrt f]
  · by_cases hq : γ < oddMax one f
    · simp only [processed, hq, or_true, ↓reduceIte, sub_zero]
      linarith [mean_abs_le_sqrt f]
    · simp only [processed, hn, hq, or_self, ↓reduceIte, add_zero]
      linarith [clip_mean_loss hA f]
end MinUncut.Slice
namespace MinUncut.IndependentSquares
open BinaryFourier
variable {C W : Type*} [Fintype C] [DecidableEq C] [Fintype W]
  [DecidableEq W] [AddCommGroup W] [Module F₂ W]

lemma expect_prod {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : ι → Type*} [∀ i, Fintype (A i)] (f : ∀ i, A i → ℝ) :
    (𝔼 x : ∀ i, A i, ∏ i, f i (x i)) = ∏ i, 𝔼 a, f i a := by
  simp only [Fintype.expect_eq_sum_div_card, Fintype.card_pi]
  rw [← Fintype.prod_sum, Nat.cast_prod, Finset.prod_div_distrib]

omit [DecidableEq W] [Module F₂ W] in
lemma factor_squares (V : C → Bool → Bool → W → ℝ) :
    (𝔼 r₀ : C → W, 𝔼 r₁ : C → W, 𝔼 s₀ : C → W, 𝔼 s₁ : C → W,
      ∏ c, V c false false (r₀ c+s₀ c) * V c false true (r₀ c+s₁ c) *
        V c true false (r₁ c+s₀ c) * V c true true (r₁ c+s₁ c)) =
      ∏ c, 𝔼 r₀, 𝔼 r₁, 𝔼 s₀, 𝔼 s₁,
        V c false false (r₀+s₀) * V c false true (r₀+s₁) *
        V c true false (r₁+s₀) * V c true true (r₁+s₁) := by
  calc
    _ = 𝔼 r₀ : C → W, 𝔼 r₁ : C → W, 𝔼 s₀ : C → W, ∏ c, 𝔼 s₁,
        V c false false (r₀ c+s₀ c) * V c false true (r₀ c+s₁) *
        V c true false (r₁ c+s₀ c) * V c true true (r₁ c+s₁) := by
      apply Finset.expect_congr rfl; intro r₀ _
      apply Finset.expect_congr rfl; intro r₁ _
      apply Finset.expect_congr rfl; intro s₀ _
      exact expect_prod (fun c s₁ => V c false false (r₀ c+s₀ c) * V c false true (r₀ c+s₁) * V c true false (r₁ c+s₀ c) * V c true true (r₁ c+s₁))
    _ = 𝔼 r₀ : C → W, 𝔼 r₁ : C → W, ∏ c, 𝔼 s₀, 𝔼 s₁,
        V c false false (r₀ c+s₀) * V c false true (r₀ c+s₁) *
        V c true false (r₁ c+s₀) * V c true true (r₁ c+s₁) := by
      apply Finset.expect_congr rfl; intro r₀ _
      apply Finset.expect_congr rfl; intro r₁ _
      exact expect_prod (fun c s₀ => 𝔼 s₁, V c false false (r₀ c+s₀) * V c false true (r₀ c+s₁) * V c true false (r₁ c+s₀) * V c true true (r₁ c+s₁))
    _ = 𝔼 r₀ : C → W, ∏ c, 𝔼 r₁, 𝔼 s₀, 𝔼 s₁,
        V c false false (r₀ c+s₀) * V c false true (r₀ c+s₁) *
        V c true false (r₁+s₀) * V c true true (r₁+s₁) := by
      apply Finset.expect_congr rfl; intro r₀ _
      exact expect_prod (fun c r₁ => 𝔼 s₀, 𝔼 s₁, V c false false (r₀ c+s₀) * V c false true (r₀ c+s₁) * V c true false (r₁+s₀) * V c true true (r₁+s₁))
    _ = _ := expect_prod (fun c r₀ => 𝔼 r₁, 𝔼 s₀, 𝔼 s₁, V c false false (r₀+s₀) * V c false true (r₀+s₁) * V c true false (r₁+s₀) * V c true true (r₁+s₁))

omit [DecidableEq W] in
lemma independent_square_bound (V : C → Bool → Bool → W → ℝ) (ε H : ℝ)
    (hε : 0 ≤ ε)
    (hcoef : ∀ c a b α, |coefficient (V c a b) α| ≤ ε)
    (henergy : ∀ c a b, (𝔼 w, (V c a b w)^2) ≤ H^2) :
    |𝔼 r₀ : C → W, 𝔼 r₁ : C → W, 𝔼 s₀ : C → W, 𝔼 s₁ : C → W,
      ∏ c, V c false false (r₀ c+s₀ c) * V c false true (r₀ c+s₁ c) *
        V c true false (r₁ c+s₀ c) * V c true true (r₁ c+s₁ c)| ≤
      (ε^2*H^2)^Fintype.card C := by
  rw [factor_squares, Finset.abs_prod]
  calc
    _ ≤ ∏ _c : C, ε^2*H^2 := by
      apply Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _)
      intro c _
      exact square_bound _ _ _ _ ε H hε (hcoef c false false) (hcoef c false true)
        (henergy c true false) (henergy c true true)
    _ = _ := by simp

def restrictLinear {R D : Type*} (j : D → R) : (R → W) →ₗ[F₂] (D → W) where
  toFun B := B ∘ j
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [Fintype W] [DecidableEq W] in
lemma restrict_surjective {R D : Type*} (j : D → R) (hj : Function.Injective j) :
    Function.Surjective (restrictLinear (W := W) j) := by
  classical
  intro b
  refine ⟨Function.extend j b (fun _ => 0), ?_⟩
  funext d
  exact hj.extend_apply b (fun _ => 0) d

lemma expect_surjective_linear {G H : Type*} [Fintype G] [AddCommGroup G] [Module F₂ G]
    [Fintype H] [AddCommGroup H] [Module F₂ H]
    (φ : G →ₗ[F₂] H) (hφ : Function.Surjective φ) (f : H → ℝ) :
    (𝔼 g, f (φ g)) = 𝔼 h, f h := by
  have h (h : H) : (𝔼 g, f (h+φ g)) = 𝔼 g, f (φ g) := by
    obtain ⟨g, rfl⟩ := hφ h
    simpa only [map_add] using expect_translate (fun a => f (φ a)) g
  calc
    _ = 𝔼 h', 𝔼 g, f (h'+φ g) := by simp_rw [h]; simp
    _ = 𝔼 g, 𝔼 h', f (h'+φ g) := Finset.expect_comm _ _ _
    _ = 𝔼 g : G, 𝔼 h', f h' := by
      apply Finset.expect_congr rfl
      intro g _
      simpa only [add_comm] using expect_translate f (φ g)
    _ = _ := by simp

omit [DecidableEq W] in
lemma expect_restrict {R D : Type*} [Fintype R] [Fintype D] [DecidableEq R] [DecidableEq D]
    (j : D → R) (hj : Function.Injective j) (f : (D → W) → ℝ) :
    (𝔼 B : R → W, f (B ∘ j)) = 𝔼 b, f b :=
  expect_surjective_linear (restrictLinear j) (restrict_surjective j hj) f
end MinUncut.IndependentSquares

namespace MinUncut.Slice
open MeasureTheory Filter
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

lemma clip_memLp {f : Ω → ℝ} {A : ℝ} (hA : 0 ≤ A) (hf : MemLp f 2 μ) :
    MemLp (fun x => clip A (f x)) 2 μ := by
  apply MemLp.of_bound
    ((aemeasurable_const.max (hf.aestronglyMeasurable.aemeasurable.min aemeasurable_const)).aestronglyMeasurable) A
  exact Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs, clip] using clip_abs_le hA (f x))

lemma clip_integral_loss {f : Ω → ℝ} {A : ℝ} (hA : 0 < A) (hf : MemLp f 2 μ) :
    (∫ x, |f x-clip A (f x)| ∂μ) ≤ (∫ x, (f x)^2 ∂μ)/A := by
  have hh : Integrable (fun x => |f x-clip A (f x)|) μ :=
    ((hf.sub (clip_memLp hA.le hf)).integrable (by norm_num)).abs
  calc
    _ ≤ ∫ x, (f x)^2/A ∂μ := integral_mono hh (hf.integrable_sq.div_const _) (fun x => clip_loss hA (f x))
    _ = _ := integral_div _ _

def centeredClip (μ : Measure Ω) (A : ℝ) (f : Ω → ℝ) (x : Ω) : ℝ :=
  clip A (f x) - ∫ y, clip A (f y) ∂μ

lemma centeredClip_mean_zero {f : Ω → ℝ} {A : ℝ} (hA : 0 ≤ A) (hf : MemLp f 2 μ) :
    (∫ x, centeredClip μ A f x ∂μ) = 0 := by
  unfold centeredClip
  rw [integral_sub ((clip_memLp hA hf).integrable (by norm_num)) (integrable_const _)]
  simp

lemma centeredClip_abs_le {f : Ω → ℝ} {A : ℝ} (hA : 0 ≤ A) (hf : MemLp f 2 μ) (x : Ω) :
    |centeredClip μ A f x| ≤ 2*A := by
  have hc : |∫ y, clip A (f y) ∂μ| ≤ A := by
    calc
      _ ≤ ∫ y, |clip A (f y)| ∂μ := abs_integral_le_integral_abs
      _ ≤ ∫ _y : Ω, A ∂μ := integral_mono ((clip_memLp hA hf).integrable (by norm_num)).abs
        (integrable_const _) (fun y => clip_abs_le hA (f y))
      _ = _ := by simp
  exact (abs_sub _ _).trans (by linarith [clip_abs_le hA (f x)])

lemma centeredClip_loss {f : Ω → ℝ} {A : ℝ} (hA : 0 < A) (hf : MemLp f 2 μ)
    (hm : (∫ x, f x ∂μ) = 0) :
    (∫ x, |f x-centeredClip μ A f x| ∂μ) ≤ 2*(∫ x, (f x)^2 ∂μ)/A := by
  have hc := (clip_memLp hA.le hf).integrable (by norm_num)
  have hf' := hf.integrable (by norm_num)
  have he : |∫ x, clip A (f x) ∂μ| ≤ ∫ x, |f x-clip A (f x)| ∂μ := by
    have h := abs_integral_le_integral_abs (μ := μ) (f := fun x => f x-clip A (f x))
    rw [integral_sub hf' hc, hm, zero_sub, abs_neg] at h
    exact h
  have hl := clip_integral_loss hA hf
  have hi : Integrable (fun x => |f x-centeredClip μ A f x|) μ :=
    (hf'.sub (hc.sub (integrable_const _))).abs
  calc
    _ ≤ ∫ x, |f x-clip A (f x)| + |∫ y, clip A (f y) ∂μ| ∂μ := by
      refine integral_mono hi ((hf'.sub hc).abs.add (integrable_const _)) ?_
      intro x
      have hrewrite : f x - centeredClip μ A f x =
          (f x - clip A (f x)) + ∫ y, clip A (f y) ∂μ := by
        unfold centeredClip
        ring
      simpa only [hrewrite] using
        abs_add_le (f x - clip A (f x)) (∫ y, clip A (f y) ∂μ)
    _ = (∫ x, |f x-clip A (f x)| ∂μ) + |∫ y, clip A (f y) ∂μ| := by
      have hh : Integrable (fun x => |f x-clip A (f x)|) μ := (hf'.sub hc).abs
      rw [integral_add hh (integrable_const _)]; simp
    _ ≤ 2*(∫ x, (f x)^2 ∂μ)/A := by rw [mul_div_assoc]; linarith

lemma tail_probability {q : Ω → ℝ} (hq : Integrable q μ) (hqpos : ∀ x, 0 ≤ q x)
    {γ : ℝ} (hγ : 0 < γ) : μ.real {x | γ < q x} ≤ (∫ x, q x ∂μ)/γ := by
  have h := mul_meas_ge_le_integral_of_nonneg (Eventually.of_forall hqpos) hq γ
  have hm : μ.real {x | γ < q x} ≤ μ.real {x | γ ≤ q x} :=
    measureReal_mono (fun x hx => (show γ < q x from hx).le)
  rw [le_div_iff₀ hγ]
  nlinarith

lemma integral_tail_loss {ν q : Ω → ℝ} (hν : MemLp ν 2 μ)
    (hq : Measurable q) (hqi : Integrable q μ) (hqpos : ∀ x, 0 ≤ q x)
    {γ : ℝ} (hγ : 0 < γ) :
    (∫ x in {x | γ < q x}, |ν x| ∂μ) ≤
      Real.sqrt (∫ x, (ν x)^2 ∂μ) * Real.sqrt ((∫ x, q x ∂μ)/γ) := by
  let S := {x | γ < q x}
  have hS : MeasurableSet S := measurableSet_lt measurable_const hq
  have hg : MemLp (S.indicator (fun _ => (1:ℝ))) 2 μ :=
    (memLp_const (1:ℝ)).indicator hS
  have h := GaussianHermite.integral_norm_mul_le_sqrt hν hg
  have hl : (∫ x, |ν x| * |S.indicator (fun _ => (1:ℝ)) x| ∂μ) = ∫ x in S, |ν x| ∂μ := by
    rw [← integral_indicator hS]
    apply integral_congr_ae
    exact Eventually.of_forall (fun x => by by_cases hx : x ∈ S <;> simp [hx])
  have hr : (∫ x, (S.indicator (fun _ => (1:ℝ)) x)^2 ∂μ) = μ.real S := by
    have he : (fun x => (S.indicator (fun _ => (1:ℝ)) x)^2) = S.indicator (fun _ => (1:ℝ)) := by
      funext x; by_cases hx : x ∈ S <;> simp [hx]
    rw [he, integral_indicator hS]; simp
  rw [hl, hr] at h
  exact h.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (tail_probability hqi hqpos hγ)) (Real.sqrt_nonneg _))
end MinUncut.Slice

namespace MinUncut.CubeRows
open BinaryFourier IndependentSquares
variable {ι A W : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype W] [DecidableEq W] [AddCommGroup W] [Module F₂ W]

abbrev Other (i j : ι) := {k : ι // k ≠ i ∧ k ≠ j}

def join (i j : ι) (c : Other i j → Bool) (a b : Bool) (k : ι) : Bool :=
  if hi : k = i then a else if hj : k = j then b else c ⟨k,hi,hj⟩

omit [Fintype ι] in
@[simp] lemma join_i (i j : ι) (c : Other i j → Bool) (a b : Bool) : join i j c a b i = a := by simp [join]
omit [Fintype ι] in
@[simp] lemma join_j (i j : ι) (hij : i ≠ j) (c : Other i j → Bool) (a b : Bool) :
    join i j c a b j = b := by simp [join, hij.symm]
omit [Fintype ι] in
@[simp] lemma join_other (i j : ι) (c : Other i j → Bool) (a b : Bool) (k : Other i j) :
    join i j c a b k = c k := by simp [join, k.property.1, k.property.2]

def splitEquiv (i j : ι) (hij : i ≠ j) : (ι → Bool) ≃ ((Other i j → Bool) × Bool × Bool) where
  toFun ν := (fun k => ν k, ν i, ν j)
  invFun v := join i j v.1 v.2.1 v.2.2
  left_inv ν := by funext k; by_cases hi : k=i <;> by_cases hj : k=j <;> simp [join, hi, hj, hij.symm]
  right_inv v := by ext k <;> simp [hij]

def vertex (ν : ι → Bool) (x y : ι → A) (k : ι) : A := if ν k then x k else y k

def face (i : ι) (x : ι → A) : {k : ι // k ≠ i} → A := fun k => x k

def rowJ (i j : ι) (x y : ι → A) (v : (Other i j → Bool) × Bool) : {k : ι // k ≠ j} → A :=
  face j (vertex (join i j v.1 v.2 false) x y)

def rowI (i j : ι) (x y : ι → A) (v : (Other i j → Bool) × Bool) : {k : ι // k ≠ i} → A :=
  face i (vertex (join i j v.1 false v.2) x y)

lemma bool_choice_injective {x y : A} (hxy : x ≠ y) : Function.Injective (fun b : Bool => if b then x else y) := by
  intro a b h; cases a <;> cases b <;> simp_all

omit [Fintype ι] in
lemma rowJ_injective (i j : ι) (hij : i ≠ j) (x y : ι → A) (hxy : ∀ k, x k ≠ y k) :
    Function.Injective (rowJ i j x y) := by
  intro v w h
  apply Prod.ext
  · funext k
    apply bool_choice_injective (hxy k)
    have hh := congrFun h ⟨k,k.property.2⟩
    simpa only [rowJ, face, vertex, join_other] using hh
  · apply bool_choice_injective (hxy i)
    have hh := congrFun h ⟨i,hij⟩
    simpa only [rowJ, face, vertex, join_i] using hh

omit [Fintype ι] in
lemma rowI_injective (i j : ι) (hij : i ≠ j) (x y : ι → A) (hxy : ∀ k, x k ≠ y k) :
    Function.Injective (rowI i j x y) := by
  intro v w h
  apply Prod.ext
  · funext k
    apply bool_choice_injective (hxy k)
    have hh := congrFun h ⟨k,k.property.1⟩
    simpa only [rowI, face, vertex, join_other] using hh
  · apply bool_choice_injective (hxy j)
    have hh := congrFun h ⟨j,hij.symm⟩
    simpa only [rowI, face, vertex, join_j i j hij] using hh

omit [Fintype ι] in
lemma face_join_J (i j : ι) (_hij : i ≠ j) (x y : ι → A)
    (c : Other i j → Bool) (a b : Bool) :
    face j (vertex (join i j c a b) x y) = rowJ i j x y (c,a) := by
  funext k
  dsimp [face, vertex, rowJ]
  congr 1
  unfold join
  split_ifs <;> simp_all [k.property]

omit [Fintype ι] in
lemma face_join_I (i j : ι) (_hij : i ≠ j) (x y : ι → A)
    (c : Other i j → Bool) (a b : Bool) :
    face i (vertex (join i j c a b) x y) = rowI i j x y (c,b) := by
  funext k
  dsimp [face, vertex, rowI]
  congr 1
  unfold join
  split_ifs <;> simp_all [k.property]

lemma prod_split (i j : ι) (hij : i ≠ j) (F : (ι → Bool) → ℝ) :
    (∏ ν, F ν) = ∏ c : Other i j → Bool,
      F (join i j c false false) * F (join i j c false true) *
      F (join i j c true false) * F (join i j c true true) := by
  have h := Fintype.prod_equiv (splitEquiv i j hij)
    F (fun v => F (join i j v.1 v.2.1 v.2.2))
    (fun ν => congrArg F ((splitEquiv i j hij).left_inv ν).symm)
  rw [h, Fintype.prod_prod_type]
  apply Finset.prod_congr rfl
  intro c _
  simp only [Fintype.prod_prod_type, Fintype.prod_bool]
  ring

variable {C : Type*} [Fintype C] [DecidableEq C]
def boolSplitEquiv : ((C × Bool) → W) ≃ ((C → W) × (C → W)) where
  toFun t := (fun c => t (c,false), fun c => t (c,true))
  invFun v := fun cb => if cb.2 then v.2 cb.1 else v.1 cb.1
  left_inv t := by funext cb; rcases cb with ⟨c,b⟩; cases b <;> rfl
  right_inv v := by ext c <;> rfl

omit [DecidableEq W] [AddCommGroup W] [Module F₂ W] in
lemma expect_boolSplit (f : (C → W) → (C → W) → ℝ) :
    (𝔼 t : (C × Bool) → W, f (fun c => t (c,false)) (fun c => t (c,true))) =
      𝔼 t₀ : C → W, 𝔼 t₁ : C → W, f t₀ t₁ := by
  rw [← Finset.expect_product', Finset.univ_product_univ]
  exact Fintype.expect_equiv boolSplitEquiv _ _ (fun _ => rfl)

def cubeExpectation (i j : ι) (x y : ι → A) [Fintype A] [DecidableEq A]
    (V : (ι → Bool) → W → ℝ) : ℝ :=
  𝔼 Bj : ({k : ι // k ≠ j} → A) → W,
  𝔼 Bi : ({k : ι // k ≠ i} → A) → W,
    ∏ ν : ι → Bool, V ν (Bj (face j (vertex ν x y)) + Bi (face i (vertex ν x y)))

def squareProduct (i j : ι) (V : (ι → Bool) → W → ℝ)
    (r s : ((Other i j → Bool) × Bool) → W) : ℝ :=
  ∏ c : Other i j → Bool,
    V (join i j c false false) (r (c,false)+s (c,false)) *
    V (join i j c false true) (r (c,false)+s (c,true)) *
    V (join i j c true false) (r (c,true)+s (c,false)) *
    V (join i j c true true) (r (c,true)+s (c,true))

omit [Fintype W] [DecidableEq W] [Module F₂ W] in
lemma cubeProduct_eq (i j : ι) (hij : i ≠ j) (x y : ι → A)
    (V : (ι → Bool) → W → ℝ)
    (Bj : ({k : ι // k ≠ j} → A) → W) (Bi : ({k : ι // k ≠ i} → A) → W) :
    (∏ ν : ι → Bool, V ν (Bj (face j (vertex ν x y)) + Bi (face i (vertex ν x y)))) =
      squareProduct i j V (Bj ∘ rowJ i j x y) (Bi ∘ rowI i j x y) := by
  rw [prod_split i j hij]
  simp only [face_join_J i j hij, face_join_I i j hij, squareProduct, Function.comp_apply]

omit [DecidableEq W] in
lemma cubeExpectation_restrict [Fintype A] [DecidableEq A]
    (i j : ι) (hij : i ≠ j) (x y : ι → A) (hxy : ∀ k, x k ≠ y k)
    (V : (ι → Bool) → W → ℝ) :
    cubeExpectation i j x y V = 𝔼 r, 𝔼 s, squareProduct i j V r s := by
  unfold cubeExpectation
  simp_rw [cubeProduct_eq i j hij]
  have hBi (r) := expect_restrict (rowI i j x y) (rowI_injective i j hij x y hxy)
    (squareProduct i j V r)
  calc
    _ = 𝔼 Bj, 𝔼 s, squareProduct i j V (Bj ∘ rowJ i j x y) s := by
      apply Finset.expect_congr rfl
      intro Bj _
      exact hBi (Bj ∘ rowJ i j x y)
    _ = _ := expect_restrict (rowJ i j x y) (rowJ_injective i j hij x y hxy)
      (fun r => 𝔼 s, squareProduct i j V r s)

omit [DecidableEq W] in
lemma cubeExpectation_eq_squares [Fintype A] [DecidableEq A]
    (i j : ι) (hij : i ≠ j) (x y : ι → A) (hxy : ∀ k, x k ≠ y k)
    (V : (ι → Bool) → W → ℝ) :
    cubeExpectation i j x y V =
    𝔼 r₀ : (Other i j → Bool) → W, 𝔼 r₁ : (Other i j → Bool) → W,
    𝔼 s₀ : (Other i j → Bool) → W, 𝔼 s₁ : (Other i j → Bool) → W,
      ∏ c : Other i j → Bool,
        V (join i j c false false) (r₀ c+s₀ c) * V (join i j c false true) (r₀ c+s₁ c) *
        V (join i j c true false) (r₁ c+s₀ c) * V (join i j c true true) (r₁ c+s₁ c) := by
  rw [cubeExpectation_restrict i j hij x y hxy V]
  let F := squareProduct i j V
  change (𝔼 r, 𝔼 s, F r s) = _
  have hs (r : ((Other i j → Bool) × Bool) → W) : (𝔼 s, F r s) =
      𝔼 s₀ : (Other i j → Bool) → W, 𝔼 s₁ : (Other i j → Bool) → W,
      ∏ c : Other i j → Bool,
        V (join i j c false false) (r (c,false)+s₀ c) * V (join i j c false true) (r (c,false)+s₁ c) *
        V (join i j c true false) (r (c,true)+s₀ c) * V (join i j c true true) (r (c,true)+s₁ c) := expect_boolSplit (fun s₀ s₁ =>
      ∏ c : Other i j → Bool,
        V (join i j c false false) (r (c,false)+s₀ c) * V (join i j c false true) (r (c,false)+s₁ c) *
        V (join i j c true false) (r (c,true)+s₀ c) * V (join i j c true true) (r (c,true)+s₁ c))
  trans 𝔼 r : ((Other i j → Bool) × Bool) → W,
      𝔼 s₀ : (Other i j → Bool) → W, 𝔼 s₁ : (Other i j → Bool) → W,
        ∏ c : Other i j → Bool,
          V (join i j c false false) (r (c,false)+s₀ c) * V (join i j c false true) (r (c,false)+s₁ c) *
          V (join i j c true false) (r (c,true)+s₀ c) * V (join i j c true true) (r (c,true)+s₁ c)
  · exact Finset.expect_congr rfl (fun r _ => hs r)
  · exact expect_boolSplit (fun r₀ r₁ : (Other i j → Bool) → W =>
      𝔼 s₀ : (Other i j → Bool) → W, 𝔼 s₁ : (Other i j → Bool) → W,
        ∏ c : Other i j → Bool,
          V (join i j c false false) (r₀ c+s₀ c) * V (join i j c false true) (r₀ c+s₁ c) *
          V (join i j c true false) (r₁ c+s₀ c) * V (join i j c true true) (r₁ c+s₁ c))

omit [DecidableEq W] in
lemma cubeExpectation_bound [Fintype A] [DecidableEq A]
    (i j : ι) (hij : i ≠ j) (x y : ι → A) (hxy : ∀ k, x k ≠ y k)
    (V : (ι → Bool) → W → ℝ) (ε H : ℝ) (hε : 0 ≤ ε)
    (hcoef : ∀ ν α, |coefficient (V ν) α| ≤ ε)
    (henergy : ∀ ν, (𝔼 w, (V ν w)^2) ≤ H^2) :
    |cubeExpectation i j x y V| ≤ (ε^2*H^2)^(2^Fintype.card (Other i j)) := by
  rw [cubeExpectation_eq_squares i j hij x y hxy V]
  have h := independent_square_bound (fun c a b => V (join i j c a b)) ε H hε
    (fun c a b => hcoef _) (fun c a b => henergy _)
  simpa only [Fintype.card_fun, Fintype.card_bool] using h
end MinUncut.CubeRows

end

end OAI
