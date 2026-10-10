import OAI.Analysis.Kaplansky.Main
import OAI.Analysis.Kaplansky.Regular.FreeFamily

namespace OAI

noncomputable section

namespace KaplanskyConsequences.Regular

open scoped ComplexOrder InnerProductSpace BigOperators ENNReal
attribute [local instance] Classical.propDecidable
variable {G H : Type*} [Group G] [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] [CompleteSpace H]

omit [Group G] [CompleteSpace H] in
@[simp] lemma diagonal_apply (T : H →L[ℂ] H) (x : HilbertSum G H) (g : G) :
    diagonal T x g = T (x g) := rfl
omit [Group G] [CompleteSpace H] in
lemma diagonal_norm_le (T : H →L[ℂ] H) : ‖diagonal (G:=G) T‖ ≤ ‖T‖ :=
  lp.norm_mapCLM_le _ _ _ _
omit [Group G] [CompleteSpace H] in
@[simp] lemma diagonal_one : diagonal (G:=G) (1 : H →L[ℂ] H) = 1 := by ext; rfl
omit [Group G] [CompleteSpace H] in
@[simp] lemma diagonal_mul (T S : H →L[ℂ] H) : diagonal (G:=G) (T*S) = diagonal T * diagonal S := by
  ext; rfl
omit [Group G] in
@[simp] lemma diagonal_star (T : H →L[ℂ] H) : diagonal (G:=G) (star T) = star (diagonal T) := by
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).2
  intro x y
  rw [lp.inner_eq_tsum,lp.inner_eq_tsum]
  apply tsum_congr; intro g
  exact T.adjoint_inner_left _ _

def diagonalHom : (H →L[ℂ] H) →⋆ₐ[ℂ] (HilbertSum G H →L[ℂ] HilbertSum G H) where
  toFun := diagonal
  map_zero' := by ext; rfl
  map_one' := diagonal_one
  map_add' _ _ := by ext; rfl
  map_mul' := diagonal_mul
  commutes' _ := by ext; rfl
  map_star' := diagonal_star

omit [CompleteSpace H] in
lemma diagonal_left_commute (T : H →L[ℂ] H) (g : G) :
    Commute (diagonal T) (left g) := by ext; rfl

def mask (P : G → Prop) [DecidablePred P] : HilbertSum G H →L[ℂ] HilbertSum G H :=
  lp.mapCLM 2 (fun g => if P g then 1 else 0) (by norm_num : (0:ℝ) ≤ 1)
    (fun g => by
      split_ifs
      · exact ContinuousLinearMap.norm_id_le
      · simp)
omit [Group G] [CompleteSpace H] in
@[simp] lemma mask_apply (P : G → Prop) [DecidablePred P] (x : HilbertSum G H) (g : G) :
    mask P x g = if P g then x g else 0 := by
  change (if P g then (1 : H →L[ℂ] H) else 0) (x g) = _
  split_ifs <;> rfl
omit [Group G] [CompleteSpace H] in
lemma mask_norm_le (P : G → Prop) [DecidablePred P] : ‖mask (H:=H) P‖ ≤ 1 :=
  lp.norm_mapCLM_le _ _ _ _
omit [Group G] in
@[simp] lemma mask_star (P : G → Prop) [DecidablePred P] : star (mask (H:=H) P) = mask P := by
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).2
  intro x y
  rw [lp.inner_eq_tsum,lp.inner_eq_tsum]
  apply tsum_congr; intro g
  simp only [mask_apply]; split_ifs <;> simp
omit [Group G] [CompleteSpace H] in
@[simp] lemma mask_sq (P : G → Prop) [DecidablePred P] : mask (H:=H) P * mask P = mask P := by
  ext x g
  simp only [mul_apply_eq_comp,mask_apply]
  split_ifs <;> simp
omit [Group G] [CompleteSpace H] in
lemma diagonal_mask_commute (T : H →L[ℂ] H) (P : G → Prop) [DecidablePred P] :
    Commute (diagonal T) (mask P) := by
  ext x g
  simp only [mul_apply_eq_comp,mask_apply,diagonal_apply]
  split_ifs <;> simp

open Classical in
def negative (n : ℕ) : HilbertSum F2 H →L[ℂ] HilbertSum F2 H :=
  mask (fun w => Prefix (n:ℤ) false (coordinate w))

def creation (n : ℕ) : HilbertSum F2 H →L[ℂ] HilbertSum F2 H :=
  left (freeGen n) * (1-negative n)
def annihilation (n : ℕ) : HilbertSum F2 H →L[ℂ] HilbertSum F2 H :=
  left (freeGen n) * negative n
omit [CompleteSpace H] in
lemma left_split (n : ℕ) : left (H:=H) (freeGen n) = creation n + annihilation n := by
  simp [creation,annihilation,mul_sub]

omit [CompleteSpace H] in
@[simp] lemma creation_apply (n : ℕ) (x : HilbertSum F2 H) (w : F2) :
    creation n x w = if Prefix (n:ℤ) false (coordinate ((freeGen n)⁻¹*w)) then 0
      else x ((freeGen n)⁻¹*w) := by
  classical
  change (x ((freeGen n)⁻¹*w) - (mask (fun w => Prefix (n:ℤ) false (coordinate w)) x) ((freeGen n)⁻¹*w)) = _
  rw [mask_apply]
  split_ifs <;> simp

omit [CompleteSpace H] in
lemma creation_support (n : ℕ) (x : HilbertSum F2 H) (w : F2)
    (h : ¬ Prefix (n:ℤ) true (coordinate w)) : creation n x w = 0 := by
  classical
  rw [creation_apply,ite_eq_left]
  exact not_not.mp (h ∘ positive_of_not_negative_inverse n w)

lemma creation_orthogonal {m n : ℕ} (h : m ≠ n) :
    star (creation (H:=H) m) * creation n = 0 := by
  apply ContinuousLinearMap.ext
  intro x
  apply (ext_inner_left ℂ)
  intro y
  change inner ℂ y ((creation m).adjoint (creation n x)) = inner ℂ y 0
  rw [ContinuousLinearMap.adjoint_inner_right,inner_zero_right,lp.inner_eq_tsum]
  rw [← (tsum_zero : (∑' _ : F2, (0 : ℂ)) = 0)]
  apply tsum_congr
  intro w
  by_cases hm : Prefix (m:ℤ) true (coordinate w)
  · have hn : ¬ Prefix (n:ℤ) true (coordinate w) := by
      intro hn
      exact h (Int.ofNat_inj.mp (prefix_disjoint hm hn).1)
    rw [creation_support n x w hn,inner_zero_right]
  · rw [creation_support m y w hm,inner_zero_left]

@[simp] lemma creation_star_mul_self (n : ℕ) :
    star (creation (H:=H) n) * creation n = 1-negative n := by
  have hu : star (left (H:=H) (freeGen n)) * left (freeGen n) = 1 := by
    rw [left_star,← left_mul,inv_mul_cancel,left_one]
  have hp : star (negative (H:=H) n) = negative n := mask_star _
  have hq : negative (H:=H) n * negative n = negative n := mask_sq _
  simp only [creation,star_mul]
  rw [mul_assoc,← mul_assoc (star (left (H := H) (freeGen n))),hu,one_mul,
    star_sub (1 : HilbertSum F2 H →L[ℂ] HilbertSum F2 H) (negative n),star_one,hp]
  simp only [mul_sub, sub_mul, one_mul, mul_one, hq]
  abel

@[simp] lemma annihilation_star_mul_self (n : ℕ) :
    star (annihilation (H:=H) n) * annihilation n = negative n := by
  simp only [annihilation,star_mul,mul_assoc]
  rw [← mul_assoc (star (left (H := H) (freeGen n))),left_star,← left_mul,inv_mul_cancel,left_one,one_mul]
  exact (congrArg (fun a => a * negative (H:=H) n) (mask_star _)).trans (mask_sq _)


end KaplanskyConsequences.Regular

end

end OAI
