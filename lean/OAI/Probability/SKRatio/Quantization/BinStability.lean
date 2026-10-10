import Mathlib
import OAI.Probability.SKRatio.Quantization.BinForm
import OAI.Probability.SKRatio.Quantization.BinNet

namespace OAI

noncomputable section
open scoped BigOperators Matrix
open MeasureTheory ProbabilityTheory Filter Real
namespace SKRatio.Bins
open Planted Scalar SKRatioClock.Regression MatrixNet Calculus
variable {n : ℕ}
attribute [local instance] Classical.propDecidable

def siteNorm (f : Fin n → ℝ) : ℝ := ‖WithLp.toLp 2 f‖/sqrt (n:ℝ)

lemma siteNorm_nonneg (f : Fin n → ℝ) : 0≤ siteNorm f := by unfold siteNorm; positivity

lemma siteNorm_sq (f : Fin n → ℝ) : siteNorm f^2=(∑ i, f i^2)/(n:ℝ) := by
  rw [siteNorm,div_pow,EuclideanSpace.real_norm_sq_eq,sq_sqrt (Nat.cast_nonneg n)]

lemma siteNorm_add (f g : Fin n → ℝ) :
    siteNorm (fun i => f i+g i)≤ siteNorm f+siteNorm g := by
  unfold siteNorm
  rw [←add_div]
  exact div_le_div_of_nonneg_right
    (norm_add_le (WithLp.toLp 2 f) (WithLp.toLp 2 g)) (sqrt_nonneg _)

lemma siteNorm_le_of_abs_le {f : Fin n → ℝ} {D : ℝ} (hD : 0≤D)
    (hf : ∀ i, |f i|≤D) : siteNorm f≤D := by
  have hs : (∑ i, f i^2)≤(n:ℝ)*D^2 := by
    calc
      _ ≤ ∑ _i : Fin n, D^2 := Finset.sum_le_sum (fun i _ => by
        simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hD).mpr (hf i))
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  by_cases hn : n=0
  · simp only [siteNorm,hn,Nat.cast_zero,sqrt_zero,div_zero]
    exact hD
  · have hnR : (0:ℝ)<n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    have hh : siteNorm f^2≤D^2 := by
      rw [siteNorm_sq]
      exact (div_le_iff₀ hnR).mpr (by nlinarith only [hs])
    nlinarith only [hh,siteNorm_nonneg f,hD]

lemma siteNorm_mul_le {f g : Fin n → ℝ} {D : ℝ} (hD : 0≤D)
    (hg : ∀ i, |g i|≤D) : siteNorm (fun i => f i*g i)≤D*siteNorm f := by
  have hs : (∑ i, (f i*g i)^2)≤D^2*(∑ i, f i^2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    have hh : g i^2≤D^2 := by simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hD).mpr (hg i)
    rw [mul_pow,mul_comm (D^2)]
    exact mul_le_mul_of_nonneg_left hh (sq_nonneg _)
  have hh : siteNorm (fun i => f i*g i)^2≤(D*siteNorm f)^2 := by
    rw [mul_pow,siteNorm_sq,siteNorm_sq,←mul_div_assoc]
    exact div_le_div_of_nonneg_right hs (Nat.cast_nonneg n)
  have hz : 0≤D*siteNorm f := mul_nonneg hD (siteNorm_nonneg f)
  nlinarith only [hh,siteNorm_nonneg (fun i => f i*g i),hz]

lemma siteMoment_abs_le {p : Fin n → ℝ} (hp : ∑ i, p i^2=1) (f : Fin n → ℝ) :
    |siteMoment p f|≤ siteNorm f := by
  have hh := abs_real_inner_le_norm (WithLp.toLp 2 p) (WithLp.toLp 2 f)
  rw [norm_of_sum_sq_one hp,one_mul] at hh
  have he : inner ℝ (WithLp.toLp 2 p) (WithLp.toLp 2 f) = ∑ i, p i*f i := by
    simp only [PiLp.inner_apply,RCLike.inner_apply,conj_trivial,mul_comm]
  rw [he] at hh
  unfold siteMoment siteNorm
  rw [abs_div,abs_of_nonneg (sqrt_nonneg _)]
  exact div_le_div_of_nonneg_right hh (sqrt_nonneg _)

lemma siteMoment_sub (p f g : Fin n → ℝ) :
    siteMoment p (fun i => f i-g i)=siteMoment p f-siteMoment p g := by
  simp only [siteMoment,mul_sub,Finset.sum_sub_distrib,sub_div]

lemma siteMoment_one {p : Fin n → ℝ} (hp : ∑ i, p i^2=1) :
    |siteMoment p (fun _ => 1)|≤1 :=
  (siteMoment_abs_le hp _).trans (siteNorm_le_of_abs_le (by norm_num) (fun _ => by norm_num))

lemma v_abs_le_one (x : ℝ) : |v x|≤1 := by rw [abs_of_nonneg (v_pos x).le]; exact v_le_one x

lemma siteMoment_v {p : Fin n → ℝ} (hp : ∑ i, p i^2=1) (H : Fin n → ℝ) :
    |siteMoment p (fun i => v (H i))|≤1 :=
  (siteMoment_abs_le hp _).trans (siteNorm_le_of_abs_le (by norm_num) (fun _ => v_abs_le_one _))

lemma product_error {x y x' y' S T d e : ℝ} (hS : 0≤S) (hT : 0≤T)
    (hy : |y|≤S) (hx : |x'|≤T) (hd : |x-x'|≤d) (he : |y-y'|≤e) :
    |x*y-x'*y'|≤d*S+T*e := by
  rw [show x*y-x'*y'=(x-x')*y+x'*(y-y') by ring]
  calc
    _ ≤ |(x-x')*y|+|x'*(y-y')| := abs_add_le _ _
    _ ≤ d*S+T*e := by
      simp only [abs_mul]
      exact add_le_add ((mul_le_mul_of_nonneg_left hy (abs_nonneg _)).trans
        (mul_le_mul_of_nonneg_right hd hS))
        (mul_le_mul hx he (abs_nonneg _) hT)

lemma mean_constant_rows (hn : 0<n) (β : ℝ) (_ : Fin n) :
    (∑ _j : Fin n, |β^2/(n:ℝ)|)=β^2 := by
  simp only [abs_of_nonneg (by positivity : 0≤β^2/(n:ℝ)),Finset.sum_const,
    Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  exact mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr hn.ne')

theorem correctedForm_field_error (hn : 0<n) (β : ℝ) (H H' p : Fin n → ℝ)
    (hp : ∑ i, p i^2=1) {a d T : ℝ} (ha : 0≤a) (hd : 0≤d) (hT : 0≤T)
    (he : siteNorm (fun i => H i-H' i)≤d) (hsize : siteNorm H'≤T)
    (hv : ∀ i, |v (H i)-v (H' i)|≤a)
    (hmv : ∀ i, |m (H i)*v (H i)-m (H' i)*v (H' i)|≤a)
    (hf : ∀ i j, |compactF (compactWeight (H i),compactWeight (H j))-
      compactF (compactWeight (H' i),compactWeight (H' j))|≤a)
    (hk : ∀ i j, |compactK (compactWeight (H i),compactWeight (H j))-
      compactK (compactWeight (H' i),compactWeight (H' j))|≤a) :
    |correctedForm β H p-correctedForm β H' p|≤2*d+2*T*a+5*β^2*a := by
  have hH : |siteMoment p H-siteMoment p H'|≤d := by
    rw [←siteMoment_sub]
    exact (siteMoment_abs_le hp _).trans he
  have hV : |siteMoment p (fun i => v (H i))-siteMoment p (fun i => v (H' i))|≤a := by
    rw [←siteMoment_sub]
    exact (siteMoment_abs_le hp _).trans (siteNorm_le_of_abs_le ha hv)
  have hMV : |siteMoment p (fun i => m (H i)*v (H i))-
      siteMoment p (fun i => m (H' i)*v (H' i))|≤a := by
    rw [←siteMoment_sub]
    exact (siteMoment_abs_le hp _).trans (siteNorm_le_of_abs_le ha hmv)
  have hHv : |siteMoment p (fun i => H i*v (H i))-
      siteMoment p (fun i => H' i*v (H' i))|≤d+T*a := by
    rw [←siteMoment_sub]
    apply (siteMoment_abs_le hp _).trans
    have heq : (fun i => H i*v (H i)-H' i*v (H' i))=
        (fun i => (H i-H' i)*v (H i)+H' i*(v (H i)-v (H' i))) := by funext i; ring
    rw [heq]
    apply (siteNorm_add _ _).trans
    have h1 := siteNorm_mul_le (f := fun i => H i-H' i) (by norm_num : (0:ℝ)≤1)
      (fun i => v_abs_le_one (H i))
    have h2 := siteNorm_mul_le (f := H') ha hv
    have h3 := mul_le_mul_of_nonneg_left hsize ha
    nlinarith only [h1,h2,h3,he]
  have h1 := product_error (by norm_num : (0:ℝ)≤1) hT (siteMoment_v hp H)
    ((siteMoment_abs_le hp H').trans hsize) hH hV
  have h₂ : |siteMoment p (fun _ => 1)*siteMoment p (fun i => H i*v (H i))-
      siteMoment p (fun _ => 1)*siteMoment p (fun i => H' i*v (H' i))|≤d+T*a := by
    rw [←mul_sub,abs_mul,mul_comm]
    exact (mul_le_mul hHv (siteMoment_one hp) (abs_nonneg _)
      (add_nonneg hd (mul_nonneg hT ha))).trans_eq (mul_one _)
  have h₃ : |β^2*siteMoment p (fun _ => 1)*
      (siteMoment p (fun i => v (H i))-siteMoment p (fun i => v (H' i)))|≤β^2*a := by
    rw [abs_mul,abs_mul,abs_of_nonneg (sq_nonneg β)]
    exact mul_le_mul ((mul_le_mul_of_nonneg_left (siteMoment_one hp) (sq_nonneg β)).trans_eq (mul_one _))
      hV (abs_nonneg _) (sq_nonneg β)
  have h₄ : |2*β^2*siteMoment p (fun _ => 1)*
      (siteMoment p (fun i => m (H i)*v (H i))-siteMoment p (fun i => m (H' i)*v (H' i)))|≤2*β^2*a := by
    rw [abs_mul,abs_mul,abs_of_nonneg (by positivity : 0≤2*β^2)]
    exact mul_le_mul ((mul_le_mul_of_nonneg_left (siteMoment_one hp) (by positivity : 0≤2*β^2)).trans_eq (mul_one _))
      hMV (abs_nonneg _) (by positivity)
  have h₅ := diagonalForm_field_bound (fun _ _ => β^2/(n:ℝ)) compactF
    (fun i => compactWeight (H i)) (fun i => compactWeight (H' i)) p ha
    (fun i => (mean_constant_rows hn β i).le) hf
  have h₆ := weightedForm_field_bound (fun _ _ => β^2/(n:ℝ)) compactK
    (fun i => compactWeight (H i)) (fun i => compactWeight (H' i)) p ha (sq_nonneg β)
    (fun i => (mean_constant_rows hn β i).le) (fun i => (mean_constant_rows hn β i).le) hk
  rw [hp,mul_one] at h₅ h₆
  let A := siteMoment p H*siteMoment p (fun i => v (H i))-
    siteMoment p H'*siteMoment p (fun i => v (H' i))
  let B := siteMoment p (fun _ => 1)*siteMoment p (fun i => H i*v (H i))-
    siteMoment p (fun _ => 1)*siteMoment p (fun i => H' i*v (H' i))
  let C := β^2*siteMoment p (fun _ => 1)*(siteMoment p (fun i => v (H i))-siteMoment p (fun i => v (H' i)))
  let D := 2*β^2*siteMoment p (fun _ => 1)*(siteMoment p (fun i => m (H i)*v (H i))-
    siteMoment p (fun i => m (H' i)*v (H' i)))
  let E := diagonalForm (fun _ _ => β^2/(n:ℝ)) compactF (fun i => compactWeight (H i)) p-
    diagonalForm (fun _ _ => β^2/(n:ℝ)) compactF (fun i => compactWeight (H' i)) p
  let F := weightedForm (fun _ _ => β^2/(n:ℝ)) compactK (fun i => compactWeight (H i)) p-
    weightedForm (fun _ _ => β^2/(n:ℝ)) compactK (fun i => compactWeight (H' i)) p
  have heq : correctedForm β H p-correctedForm β H' p=A+B-C+D+E+F := by
    dsimp [correctedForm,A,B,C,D,E,F]; ring
  rw [heq]
  have ht : |A+B-C+D+E+F|≤|A|+|B|+|C|+|D|+|E|+|F| := by
    calc
      _ ≤ |A+B-C+D+E|+|F| := abs_add_le _ _
      _ ≤ (|A+B-C+D|+|E|)+|F| := by gcongr; exact abs_add_le _ _
      _ ≤ ((|A+B-C|+|D|)+|E|)+|F| := by gcongr; exact abs_add_le _ _
      _ ≤ (((|A+B|+|C|)+|D|)+|E|)+|F| := by gcongr; exact abs_sub _ _
      _ ≤ _ := by gcongr; exact abs_add_le _ _
  change |A|≤_ at h1
  change |B|≤_ at h₂
  change |C|≤_ at h₃
  change |D|≤_ at h₄
  change |E|≤_ at h₅
  change |F|≤_ at h₆
  nlinarith only [ht,h1,h₂,h₃,h₄,h₅,h₆]

end SKRatio.Bins

end

end OAI
