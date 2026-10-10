import Mathlib
import OAI.Probability.BinarySweep.MatrixBounds.SymmetricDensity

namespace OAI

noncomputable section

section

open scoped BigOperators Classical ComplexOrder
open Matrix

namespace BinaryCoordinateSweeps.Density
variable {K A B : Type*} [Fintype K] [DecidableEq K] [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B]

def reshape (e : K → A × B) (v : K → ℂ) : Matrix A B ℂ :=
  fun a b => ∑ k, if e k = (a,b) then v k else 0

def kraus (e : K → A × B) (b : B) : Matrix A K ℂ :=
  fun a k => if e k = (a,b) then 1 else 0

def densityChannel (e : K → A × B) (M : Matrix K K ℂ) : Matrix A A ℂ :=
  ∑ b, kraus e b * M * (kraus e b).conjTranspose

omit [DecidableEq K] in
lemma densityChannel_psd (e : K → A × B) {M : Matrix K K ℂ} (hM : M.PosSemidef) :
    (densityChannel e M).PosSemidef :=
  Matrix.posSemidef_sum _ (fun _ _ => hM.mul_mul_conjTranspose_same _)

omit [DecidableEq K] [Fintype A] in
lemma densityChannel_sub (e : K → A × B) (M N : Matrix K K ℂ) :
    densityChannel e (M-N) = densityChannel e M - densityChannel e N := by
  simp only [densityChannel, Matrix.mul_sub, Matrix.sub_mul, Finset.sum_sub_distrib]

omit [DecidableEq K] [Fintype A] in
lemma densityChannel_smul (e : K → A × B) (c : ℂ) (M : Matrix K K ℂ) :
    densityChannel e (c • M) = c • densityChannel e M := by
  simp only [densityChannel, Matrix.mul_smul, Matrix.smul_mul, Finset.smul_sum]

omit [DecidableEq K] [Fintype A] in
lemma densityChannel_sum {T : Type*} [Fintype T] (e : K → A × B) (M : T → Matrix K K ℂ) :
    densityChannel e (∑ t, M t) = ∑ t, densityChannel e (M t) := by
  simp only [densityChannel, Matrix.mul_sum, Matrix.sum_mul]
  exact Finset.sum_comm

omit [DecidableEq K] [Fintype A] [Fintype B] in
lemma kraus_mulVec (e : K → A × B) (v : K → ℂ) (b : B) :
    (kraus e b).mulVec v = fun a => reshape e v a b := by
  ext a
  simp only [Matrix.mulVec, dotProduct, kraus, reshape, ite_mul, one_mul, zero_mul]

omit [DecidableEq K] in
lemma densityChannel_rankOne (e : K → A × B) (v : K → ℂ) :
    densityChannel e (rankOne v) = reshape e v * (reshape e v).conjTranspose := by
  simp only [densityChannel, rankOne_conjugate, kraus_mulVec]
  ext a b
  simp only [Matrix.sum_apply, rankOne, vecMulVec_apply, Pi.star_apply,
    Matrix.mul_apply, Matrix.conjTranspose_apply]

omit [Fintype A] [Fintype B] in
lemma reshape_injective_apply (e : K → A × B) (he : Function.Injective e) (v : K → ℂ) (k : K) :
    reshape e v (e k).1 (e k).2 = v k := by
  simp only [reshape, Prod.mk.eta, he.eq_iff, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

omit [DecidableEq K] [Fintype A] [Fintype B] in
lemma reshape_outside (e : K → A × B) (v : K → ℂ) (a : A) (b : B)
    (h : (a,b) ∉ Set.range e) : reshape e v a b = 0 := by
  apply Finset.sum_eq_zero
  intro k hk
  exact ite_eq_right (fun hh => h ⟨k,hh⟩)

def wordPair (n : ℕ) (e : K → A × B) : (Fin n → K) → (Fin n → A) × (Fin n → B) :=
  fun w => (fun i => (e (w i)).1, fun i => (e (w i)).2)

omit [Fintype K] [DecidableEq K] [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] in
lemma wordPair_eq_iff (n : ℕ) (e : K → A × B) (w : Fin n → K)
    (x : Fin n → A) (y : Fin n → B) : wordPair n e w = (x,y) ↔ ∀ i, e (w i) = (x i,y i) := by
  simp only [wordPair, funext_iff, Prod.ext_iff]
  exact ⟨fun h i => ⟨h.1 i,h.2 i⟩, fun h => ⟨fun i => (h i).1, fun i => (h i).2⟩⟩

omit [Fintype K] [DecidableEq K] [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] in
lemma wordPair_injective (n : ℕ) (e : K → A × B) (he : Function.Injective e) :
    Function.Injective (wordPair n e) := by
  intro w v h
  funext i
  apply he
  exact Prod.ext (congrFun (congrArg Prod.fst h) i) (congrFun (congrArg Prod.snd h) i)

omit [DecidableEq K] [Fintype A] [Fintype B] in
lemma reshape_tensor (n : ℕ) (e : K → A × B) (u : K → ℂ)
    (x : Fin n → A) (y : Fin n → B) :
    reshape (wordPair n e) (tensorProductVector n u) x y = ∏ i, reshape e u (x i) (y i) := by
  simp only [reshape, tensorProductVector, wordPair_eq_iff]
  rw [Fintype.prod_sum (fun i k => if e k = (x i,y i) then u k else 0)]
  apply Finset.sum_congr rfl
  intro w hw
  by_cases h : ∀ i, e (w i) = (x i,y i)
  · simp only [ite_eq_left h]
    apply Finset.prod_congr rfl
    intro i hi
    rw [ite_eq_left (h i)]
  · rw [ite_eq_right h]
    obtain ⟨i,hi⟩ := not_forall.mp h
    exact (Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)).symm

def matrixTensorPower (n : ℕ) (M : Matrix A A ℂ) : Matrix (Fin n → A) (Fin n → A) ℂ :=
  fun x y => ∏ i, M (x i) (y i)

def matrixTensorRect (n : ℕ) (U : Matrix A B ℂ) : Matrix (Fin n → A) (Fin n → B) ℂ :=
  fun x y => ∏ i, U (x i) (y i)

omit [Fintype A] [DecidableEq A] [DecidableEq B] in
lemma tensor_gram (n : ℕ) (U : Matrix A B ℂ) :
    matrixTensorRect n U * (matrixTensorRect n U).conjTranspose =
    matrixTensorPower n (U * U.conjTranspose) := by
  ext x z
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, matrixTensorPower, matrixTensorRect, star_prod,
    ← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun i b => U (x i) b * star (U (z i) b))).symm

omit [DecidableEq K] in
lemma densityChannel_tensorRankOne (n : ℕ) (e : K → A × B) (u : K → ℂ) :
    densityChannel (wordPair n e) (rankOne (tensorProductVector n u)) =
      matrixTensorPower n (reshape e u * (reshape e u).conjTranspose) := by
  rw [densityChannel_rankOne]
  have he : reshape (wordPair n e) (tensorProductVector n u) =
      matrixTensorRect n (reshape e u) := by
    ext x y
    exact reshape_tensor n e u x y
  rw [he, tensor_gram]

end BinaryCoordinateSweeps.Density

end

open scoped BigOperators Classical ComplexOrder
open Matrix

namespace BinaryCoordinateSweeps.Density
variable {K A B : Type*} [Fintype K] [DecidableEq K] [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B]

lemma reshape_trace (e : K → A × B) (he : Function.Injective e) (v : K → ℂ) :
    (reshape e v * (reshape e v).conjTranspose).trace = (rankOne v).trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    rankOne, Matrix.vecMulVec_apply, Pi.star_apply]
  symm
  calc
    _ = ∑ x : A × B, reshape e v x.1 x.2 * star (reshape e v x.1 x.2) :=
      Fintype.sum_of_injective e he (fun k => v k * star (v k))
        (fun x : A × B => reshape e v x.1 x.2 * star (reshape e v x.1 x.2))
        (by rintro ⟨a,b⟩ h; rw [reshape_outside e v a b h]; simp)
        (by intro k; rw [reshape_injective_apply e he])
    _ = _ := Fintype.sum_prod_type _

omit [DecidableEq A] in
lemma gram_psd (U : Matrix A B ℂ) : (U * U.conjTranspose).PosSemidef := by
  simpa only [Matrix.mul_one] using
    (Matrix.PosSemidef.one : (1 : Matrix B B ℂ).PosSemidef).mul_mul_conjTranspose_same U

omit [DecidableEq K] [Fintype A] in
lemma reshape_even {P : Type*} (pa : A → P) (pb : B → P) (e : K → A × B)
    (he : ∀ k, pa (e k).1 = pb (e k).2) (v : K → ℂ) (a a' : A)
    (haa : pa a ≠ pa a') : (reshape e v * (reshape e v).conjTranspose) a a' = 0 := by
  apply Finset.sum_eq_zero
  intro b hb
  change reshape e v a b * star (reshape e v a' b) = 0
  by_cases ha : pa a = pb b
  · have hn : (a', b) ∉ Set.range e := by
      rintro ⟨k,hk⟩
      have hh := he k
      rw [hk] at hh
      exact haa (ha.trans hh.symm)
    rw [reshape_outside e v a' b hn, star_zero, mul_zero]
  · have hn : (a,b) ∉ Set.range e := by
      rintro ⟨k,hk⟩
      have hh := he k
      rw [hk] at hh
      exact ha hh
    rw [reshape_outside e v a b hn, zero_mul]

def reducedPhaseDensity (n : ℕ) (e : K → A × B) (c : WordType K n)
    (t : K → ZMod (n+1)) : Matrix A A ℂ :=
  reshape e (phasedVector n (empirical n c) t) *
    (reshape e (phasedVector n (empirical n c) t)).conjTranspose

lemma reducedPhaseDensity_psd (n : ℕ) (e : K → A × B) (c : WordType K n)
    (t : K → ZMod (n+1)) : (reducedPhaseDensity n e c t).PosSemidef := gram_psd _

lemma reducedPhaseDensity_trace (n : ℕ) (hn : 0 < n) (e : K → A × B)
    (he : Function.Injective e) (c : WordType K n) (t : K → ZMod (n+1)) :
    (reducedPhaseDensity n e c t).trace = 1 := by
  rw [reducedPhaseDensity, reshape_trace e he]
  exact phasedVector_trace n (empirical n c) (empirical_nonneg n c) (empirical_sum n hn c) t

omit [Fintype A] in
lemma reducedPhaseDensity_even {P : Type*} (n : ℕ) (pa : A → P) (pb : B → P)
    (e : K → A × B) (he : ∀ k, pa (e k).1 = pb (e k).2)
    (c : WordType K n) (t : K → ZMod (n+1)) (a a' : A) (haa : pa a ≠ pa a') :
    reducedPhaseDensity n e c t a a' = 0 := reshape_even pa pb e he _ a a' haa

end BinaryCoordinateSweeps.Density

end

end OAI
