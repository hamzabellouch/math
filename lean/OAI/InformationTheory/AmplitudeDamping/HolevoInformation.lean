import OAI.InformationTheory.AmplitudeDamping.Naimark

namespace OAI

noncomputable section

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7

section
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace GAD

def factorError (ε d : ℝ) (D : ℕ) : ℝ :=
  (d/(4*ε)+ε)*Real.log D+(1+d/(4*ε)+ε)*Real.log 2

theorem factorError_mono {ε d e : ℝ} {D : ℕ} (hε : 0 < ε) (hD : 0 < D) (hde : d ≤ e) :
    factorError ε d D ≤ factorError ε e D := by
  have hd := div_le_div_of_nonneg_right hde (show 0 ≤ 4*ε by positivity)
  have hlog : 0 ≤ Real.log D := Real.log_nonneg (by exact_mod_cast hD)
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  dsimp [factorError]
  exact add_le_add (mul_le_mul_of_nonneg_right (by linarith) hlog)
    (mul_le_mul_of_nonneg_right (by linarith) hlog2)

theorem factorError_average {μ : Type u_1} [Fintype μ] (ε : ℝ) (D : ℕ)
    (w d : μ → ℝ) (hws : ∑ m, w m=1) :
    (∑ m, w m*factorError ε (d m) D)=factorError ε (∑ m, w m*d m) D := by
  let c := (Real.log D+Real.log 2)/(4*ε)
  let v := ε*Real.log D+(1+ε)*Real.log 2
  have he (x : ℝ) : factorError ε x D=x*c+v := by dsimp [factorError,c,v]; ring
  simp only [he,mul_add,← mul_assoc,Finset.sum_add_distrib,← Finset.sum_mul,hws,one_mul]

variable {ι : Type u_2} {κ : Type u_3} {μ : Type u_4} [Fintype ι] [Fintype κ] [Fintype μ]
  [DecidableEq ι] [DecidableEq κ] [DecidableEq μ] [Nonempty ι] [Nonempty μ]

theorem orthogonal_cq_bound (w : μ → ℝ) (hw : ∀ m, 0 ≤ w m) (hws : ∑ m, w m=1)
    (X Y : μ → Matrix (ι × μ) κ ℂ) (hX : ∀ m, mass (X m)=1) (hY : ∀ m, mass (Y m)=1)
    (hPY : ∀ m, blockProjection (ι := ι) m*Y m=Y m) {ε : ℝ} (hε : 0 < ε) :
    (∑ m, Real.negMulLog (w m)) ≤
      entropy (gram (concatenate w X))-(∑ m, w m*entropy (gram (X m)))+
        2*factorError ε (∑ m, w m*mass (X m-Y m)) (Fintype.card (ι × μ)) := by
  have havg := factor_entropy_bound (concatenate w Y) (concatenate w X)
    (concatenate_mass_one w Y hw hws hY) (concatenate_mass_one w X hw hws hX) hε
  have hmn : mass (concatenate w Y-concatenate w X)=∑ m, w m*mass (X m-Y m) := by
    rw [concatenate_sub,mass_concatenate w _ hw]
    apply Finset.sum_congr rfl
    intro m _
    congr 1
    rw [mass_sub,mass_sub,real_inner_comm]
    ring
  rw [hmn] at havg
  change entropy (gram (concatenate w Y))-entropy (gram (concatenate w X)) ≤
    factorError ε (∑ m, w m*mass (X m-Y m)) (Fintype.card (ι × μ)) at havg
  have hind := Finset.sum_le_sum (s := Finset.univ) (fun m _ ↦
    mul_le_mul_of_nonneg_left (factor_entropy_bound (X m) (Y m) (hX m) (hY m) hε) (hw m))
  change (∑ m, w m*(entropy (gram (X m))-entropy (gram (Y m)))) ≤
    (∑ m, w m*factorError ε (mass (X m-Y m)) (Fintype.card (ι × μ))) at hind
  rw [factorError_average ε _ w _ hws] at hind
  simp only [mul_sub,Finset.sum_sub_distrib] at hind
  rw [gram_concatenate w Y hw,orthogonal_factor_entropy w Y hY hPY,Finset.sum_add_distrib] at havg
  linarith

end GAD

end

open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace GAD
variable {ι : Type u_5} {μ : Type u_6} [Fintype ι] [Fintype μ] [DecidableEq ι] [DecidableEq μ]
  [Nonempty ι] [Nonempty μ]

def uniformWeight (μ : Type u_7) [Fintype μ] (_ : μ) : ℝ := (Fintype.card μ : ℝ)⁻¹

omit [DecidableEq μ] in
theorem uniformWeight_nonneg (m : μ) : 0 ≤ uniformWeight μ m := by
  dsimp [uniformWeight]; positivity

omit [DecidableEq μ] in
theorem uniformWeight_sum : (∑ m : μ, uniformWeight μ m)=1 := by
  simp only [uniformWeight,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  exact mul_inv_cancel₀ (by exact_mod_cast (Fintype.card_pos (α := μ)).ne')

omit [DecidableEq μ] in
theorem uniformWeight_entropy : (∑ m : μ, Real.negMulLog (uniformWeight μ m))=Real.log (Fintype.card μ) := by
  have hc : (Fintype.card μ : ℝ) ≠ 0 := by exact_mod_cast (Fintype.card_pos (α := μ)).ne'
  simp only [uniformWeight,Real.negMulLog,Real.log_inv,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  field_simp

theorem cq_decoding_entropy_bound (A D : μ → Matrix ι ι ℂ)
    (hA : ∀ m, IsState (A m)) (hD : ∀ m, (D m).PosSemidef) (hDs : ∑ m, D m=1)
    {ε : ℝ} (hε : 0 < ε) :
    Real.log (Fintype.card μ) ≤
      entropy (∑ m, uniformWeight μ m • A m)-(∑ m, uniformWeight μ m*entropy (A m))+
      2*factorError ε (2*(1-∑ m, uniformWeight μ m*(D m*A m).trace.re)) (Fintype.card (ι × μ)) := by
  let W := naimark D hD
  let F := fun m ↦ spectralFactor (hA m).1
  let X := fun m ↦ W*F m
  have hW : Wᴴ*W=1 := naimark_isometry D hD hDs
  have hF (m : μ) : mass (F m)=1 := by dsimp [F,mass]; rw [spectralFactor_gram,(hA m).2]; rfl
  have hX (m : μ) : mass (X m)=1 := by rw [mass_isometry W hW,hF]
  obtain ⟨Y,hY,hPY,hd⟩ := exists_orthogonal_factors A D hA hD hDs
  have hb := orthogonal_cq_bound (uniformWeight μ) uniformWeight_nonneg uniformWeight_sum X Y hX hY hPY hε
  rw [uniformWeight_entropy] at hb
  have hc : concatenate (uniformWeight μ) X=W*concatenate (uniformWeight μ) F := by
    ext i mk
    dsimp [concatenate,X]
    simp only [Matrix.mul_apply,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    dsimp [concatenate]
    ring
  have hi (m : μ) : entropy (gram (X m))=entropy (A m) := by
    rw [entropy_gram_isometry W hW,spectralFactor_gram]
  have ha : entropy (gram (concatenate (uniformWeight μ) X))=
      entropy (∑ m, uniformWeight μ m • A m) := by
    rw [hc,entropy_gram_isometry W hW,gram_concatenate _ _ uniformWeight_nonneg]
    simp only [F,spectralFactor_gram]
  rw [ha] at hb
  simp only [hi] at hb
  have hd' : (∑ m, uniformWeight μ m*mass (X m-Y m)) ≤
      2*(1-∑ m, uniformWeight μ m*(D m*A m).trace.re) := by
    calc
      _ ≤ ∑ m, uniformWeight μ m*(2*(1-(D m*A m).trace.re)) :=
        Finset.sum_le_sum (fun m _ ↦ mul_le_mul_of_nonneg_left (hd m) (uniformWeight_nonneg m))
      _ = _ := by
        simp only [mul_sub,mul_one,Finset.sum_sub_distrib,← Finset.mul_sum,
          show ∀ a b : ℝ, a*(2*b)=2*(a*b) by intros; ring,← Finset.sum_mul,uniformWeight_sum]
        ring
  exact hb.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left
    (factorError_mono hε (Fintype.card_pos (α := ι × μ)) hd') (by norm_num)))

end GAD

end

end OAI
