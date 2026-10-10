import Mathlib
import OAI.NumberTheory.CubicGram.GlobalRecurrence
import OAI.NumberTheory.CubicGram.CubeEstimates

namespace OAI

/-! Quantitative cube and dual bounds under a sieve exponent. -/

section

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def SieveExponent (ξ : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∀ (S H : Finset Eisenstein) (M N : ℝ), 1 ≤ M → 1 ≤ N →
      (∀ a ∈ S, primary a ∧ Squarefree a ∧ norm a ≤ N) →
      (∀ b ∈ H, primary b ∧ Squarefree b ∧ norm b ≤ M) →
      finiteCubicBound S H ≤ C*(M*N)^ε*(M+(M*N)^(2/3 : ℝ)+N^ξ)

lemma dyadic_polynomial_small_power (d : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ j : ℕ, ((j : ℝ)+2)^d ≤ C*((2 : ℝ)^j)^ε := by
  let r : ℝ := (2^ε)⁻¹
  have hp : (1 : ℝ) < 2^ε := Real.one_lt_rpow (by norm_num) hε
  have hr : 0 < r := by dsimp [r]; positivity
  have hr1 : r < 1 := by dsimp [r]; exact inv_lt_one_of_one_lt₀ hp
  have hs := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) d (r := r) (by simpa only [Real.norm_eq_abs,abs_of_pos hr] using hr1)
  let D : ℝ := (∑' n : ℕ, (n : ℝ)^d*r^n)+1
  have hD : 0 < D := by
    have hh : 0 ≤ ∑' n : ℕ, (n : ℝ)^d*r^n := tsum_nonneg (fun n => by positivity)
    dsimp [D]; linarith
  refine ⟨D*(2^ε)^2,by positivity,?_⟩
  intro j
  have hh := hs.le_tsum (j+2) (fun n _ => by positivity)
  have hh' : (((j : ℝ)+2)^d*r^j)*r^2 ≤ D := by
    simpa only [Nat.cast_add,Nat.cast_ofNat,pow_add,mul_assoc] using hh.trans (le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 1))
  have he : (2^ε)^j = ((2 : ℝ)^j)^ε := by
    rw [← Real.rpow_natCast_mul (by norm_num),mul_comm,Real.rpow_mul_natCast (by norm_num)]
  have he' : r^j*r^2*((2^ε)^2*((2 : ℝ)^j)^ε) = 1 := by
    rw [← he]
    dsimp [r]
    rw [inv_pow,inv_pow]
    field_simp
  have hmul := mul_le_mul_of_nonneg_right hh' (by positivity : 0 ≤ (2^ε)^2*((2 : ℝ)^j)^ε)
  have he'' : ((j : ℝ)+2)^d*r^j*r^2*((2^ε)^2*((2 : ℝ)^j)^ε) = ((j : ℝ)+2)^d := by
    calc
      _ = ((j : ℝ)+2)^d*(r^j*r^2*((2^ε)^2*((2 : ℝ)^j)^ε)) := by ring
      _ = _ := by rw [he',mul_one]
  rw [he''] at hmul
  exact hmul.trans_eq (by ring)

lemma squarefreePrimaryDyad_card_le (j : ℕ) :
    ((squarefreePrimaryDyad j).card : ℝ) ≤ 36*(2 : ℝ)^j := by
  exact (Nat.cast_le.mpr (Finset.card_filter_le _ _)).trans (frequencyDyad_card_le j)

lemma cubeDyad_sizes {j : ℕ} {z : ℕ×ℕ×ℕ} (hz : z ∈ cubeDyadTriples j) :
    (2 : ℝ)^z.1*((2 : ℝ)^z.2.1)^2*((2 : ℝ)^z.2.2)^3 ≤ 2*(2 : ℝ)^j := by
  have hh := (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (mem_cubeDyadTriples.mp hz))
  calc
    _ = (2 : ℝ)^(z.1+2*z.2.1+3*z.2.2) := by
      simp only [pow_add,pow_mul,mul_comm 2 z.2.1,mul_comm 3 z.2.2]
    _ ≤ 2^(j+1) := hh
    _ = _ := by rw [pow_succ]; ring

end CubicFirstMoment
end
end

section

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma cube_block_scaled {S T K N J ξ C : ℝ}
    (hS : 1 ≤ S) (hT : 1 ≤ T) (hK : 1 ≤ K) (hN : 0 ≤ N)
    (hJ : S*T^2*K^3 ≤ J) (hξ : 1 ≤ ξ) (hξ2 : ξ ≤ 2) (hC : 0 ≤ C) :
    min (T*K*(C*(N+(N*S)^(2/3 : ℝ)+S^ξ)))
      (S*K*(C*(N+(N*T)^(2/3 : ℝ)+T^ξ))) ≤
      C*(N*J^(1/3 : ℝ)+(J*N)^(2/3 : ℝ)+J^ξ+J) := by
  have he (a b : ℝ) : a*K*(C*b) = C*(K*a*b) := by ring
  simp only [he,← mul_min_of_nonneg _ _ hC]
  exact mul_le_mul_of_nonneg_left (cube_block_numerical hS hT hK hN hJ hξ hξ2) hC

lemma cube_scaled_sizes {j : ℕ} {z : ℕ×ℕ×ℕ} (hz : z ∈ cubeDyadTriples j) :
    (2*(2 : ℝ)^z.1)*(2*(2 : ℝ)^z.2.1)^2*(2*(2 : ℝ)^z.2.2)^3 ≤ 128*(2 : ℝ)^j := by
  have h := mul_le_mul_of_nonneg_left (cubeDyad_sizes hz) (by norm_num : (0 : ℝ) ≤ 64)
  nlinarith only [h]

lemma SieveExponent.cube_bound {ξ : ℝ} (hξ : 1 ≤ ξ) (hξ2 : ξ ≤ 2)
    (hExp : SieveExponent ξ) {ε : ℝ} (hε : 0 < ε) :
    ∃ D : ℝ, 0 < D ∧ ∀ (P : Finset Eisenstein) (N : ℝ), 1 ≤ N →
      (∀ b ∈ P, primary b ∧ Squarefree b ∧ norm b ≤ N) →
      ∀ j : ℕ,
      finiteCubicBound P (frequencyDyad j) ≤ D*(N*(128*(2 : ℝ)^j))^ε*
        (N*(128*(2 : ℝ)^j)^(1/3 : ℝ)+(128*(2 : ℝ)^j*N)^(2/3 : ℝ)+
         (128*(2 : ℝ)^j)^ξ+128*(2 : ℝ)^j) := by
  obtain ⟨C,hC,hbound⟩ := hExp (ε/2) (by linarith)
  obtain ⟨E,hE,hpoly⟩ := dyadic_polynomial_small_power 3 (show 0 < ε/2 by linarith)
  refine ⟨((nonzeroNormBall 729).card+1)*324*C*E,by positivity,?_⟩
  intro P N hN hP j
  let J : ℝ := 128*(2 : ℝ)^j
  let F : ℝ := N*J^(1/3 : ℝ)+(J*N)^(2/3 : ℝ)+J^ξ+J
  have hN0 : 0 < N := zero_lt_one.trans_le hN
  have hJ : 1 ≤ J := by dsimp [J]; have : (1 : ℝ) ≤ 2^j := one_le_pow₀ (by norm_num); linarith
  have hJ0 : 0 < J := zero_lt_one.trans_le hJ
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hpp := fun b hb => (hP b hb).1
  have hsf (i : ℕ) : ∀ a ∈ squarefreePrimaryDyad i, primary a ∧ Squarefree a ∧ norm a ≤ 2*(2 : ℝ)^i := by
    intro a ha
    have hh := mem_squarefreePrimaryDyad.mp ha
    exact ⟨hh.2.1,hh.2.2,(frequencyDyad_norm hh.1).2⟩
  have hn (i : ℕ) : 1 ≤ 2*(2 : ℝ)^i := by have : (1 : ℝ) ≤ 2^i := one_le_pow₀ (by norm_num); linarith
  have hsieve (i : ℕ) (hi : 2*(2 : ℝ)^i ≤ J) :
      finiteCubicBound P (squarefreePrimaryDyad i) ≤ C*(N*J)^(ε/2)*
        (N+(N*(2*(2 : ℝ)^i))^(2/3 : ℝ)+(2*(2 : ℝ)^i)^ξ) := by
    rw [finiteCubicBound_symm P _ hpp (fun a ha => (hsf i a ha).1)]
    apply (hbound _ _ N (2*(2 : ℝ)^i) hN (hn i) (hsf i) hP).trans
    gcongr
  have hblock (z : ℕ×ℕ×ℕ) (hz : z ∈ cubeDyadTriples j) :
      min (((squarefreePrimaryDyad z.2.1).card : ℝ)*(frequencyDyad z.2.2).card*
        finiteCubicBound P (squarefreePrimaryDyad z.1))
        (((squarefreePrimaryDyad z.1).card : ℝ)*(frequencyDyad z.2.2).card*
        finiteCubicBound P (squarefreePrimaryDyad z.2.1)) ≤
          324*C*(N*J)^(ε/2)*F := by
    let S : ℝ := 2*(2 : ℝ)^z.1
    let T : ℝ := 2*(2 : ℝ)^z.2.1
    let K : ℝ := 2*(2 : ℝ)^z.2.2
    have hS : 1 ≤ S := hn _
    have hT : 1 ≤ T := hn _
    have hK : 1 ≤ K := hn _
    have hprod : S*T^2*K^3 ≤ J := cube_scaled_sizes hz
    have hSle : S ≤ J := (le_mul_of_one_le_right (by linarith : 0 ≤ S)
      (one_le_mul_of_one_le_of_one_le (one_le_pow₀ hT) (one_le_pow₀ hK))).trans
      (by simpa only [mul_assoc] using hprod)
    have hTle : T ≤ J := by
      have ht : T ≤ T^2 := le_self_pow₀ hT (by norm_num : (2 : ℕ) ≠ 0)
      have ht' : T^2 ≤ S*T^2*K^3 := by
        calc
          _ ≤ S*T^2 := le_mul_of_one_le_left (sq_nonneg _) hS
          _ ≤ _ := le_mul_of_one_le_right (by positivity) (one_le_pow₀ hK)
      exact ht.trans (ht'.trans hprod)
    have hcardS : ((squarefreePrimaryDyad z.1).card : ℝ) ≤ 18*S := by dsimp [S]; nlinarith [squarefreePrimaryDyad_card_le z.1]
    have hcardT : ((squarefreePrimaryDyad z.2.1).card : ℝ) ≤ 18*T := by dsimp [T]; nlinarith [squarefreePrimaryDyad_card_le z.2.1]
    have hcardK : ((frequencyDyad z.2.2).card : ℝ) ≤ 18*K := by dsimp [K]; nlinarith [frequencyDyad_card_le z.2.2]
    calc
      _ ≤ min ((18*T)*(18*K)*(C*(N*J)^(ε/2)*(N+(N*S)^(2/3 : ℝ)+S^ξ)))
          ((18*S)*(18*K)*(C*(N*J)^(ε/2)*(N+(N*T)^(2/3 : ℝ)+T^ξ))) := by
        have hbs := hsieve _ hSle
        have hbt := hsieve _ hTle
        have hbs0 := finiteCubicBound_nonneg P (squarefreePrimaryDyad z.1)
        have hbt0 := finiteCubicBound_nonneg P (squarefreePrimaryDyad z.2.1)
        apply min_le_min <;> gcongr
      _ = min (T*K*((324*C*(N*J)^(ε/2))*(N+(N*S)^(2/3 : ℝ)+S^ξ)))
          (S*K*((324*C*(N*J)^(ε/2))*(N+(N*T)^(2/3 : ℝ)+T^ξ))) := by congr 1 <;> ring
      _ ≤ _ := cube_block_scaled hS hT hK hN0.le hprod hξ hξ2 (by positivity)
  have hcount : ((cubeDyadTriples j).card : ℝ) ≤ E*J^(ε/2) := by
    have hc : ((cubeDyadTriples j).card : ℝ) ≤ ((j : ℝ)+2)^3 := by exact_mod_cast cubeDyadTriples_card j
    apply (hc.trans (hpoly j)).trans
    gcongr
    dsimp [J]
    have hh : (0 : ℝ) ≤ 2^j := by positivity
    linarith
  have hpow : J^(ε/2)*(N*J)^(ε/2) ≤ (N*J)^ε := by
    calc
      _ ≤ (N*J)^(ε/2)*(N*J)^(ε/2) := by
        gcongr
        exact le_mul_of_one_le_left hJ0.le hN
      _ = _ := by rw [← Real.rpow_add (by positivity)]; congr 1; ring
  calc
    _ ≤ (nonzeroNormBall 729).card*∑ z ∈ cubeDyadTriples j,
        min (((squarefreePrimaryDyad z.2.1).card : ℝ)*(frequencyDyad z.2.2).card*
          finiteCubicBound P (squarefreePrimaryDyad z.1))
          (((squarefreePrimaryDyad z.1).card : ℝ)*(frequencyDyad z.2.2).card*
          finiteCubicBound P (squarefreePrimaryDyad z.2.1)) := finiteCubicBound_frequency_cube P hpp j
    _ ≤ (nonzeroNormBall 729).card*(((cubeDyadTriples j).card : ℝ)*(324*C*(N*J)^(ε/2)*F)) :=
      mul_le_mul_of_nonneg_left ((Finset.sum_le_card_nsmul _ _ _ hblock).trans_eq (by rw [nsmul_eq_mul])) (by positivity)
    _ ≤ (nonzeroNormBall 729).card*(E*J^(ε/2)*(324*C*(N*J)^(ε/2)*F)) := by gcongr
    _ = ((nonzeroNormBall 729).card*324*C*E)*(J^(ε/2)*(N*J)^(ε/2))*F := by ring
    _ ≤ ((nonzeroNormBall 729).card*324*C*E)*(N*J)^ε*F := by gcongr
    _ ≤ _ := by dsimp only [F,J]; gcongr; linarith

end CubicFirstMoment
end
end

section

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def decayConstant (α : ℝ) : ℝ := 4*2^α/(2^α-1)

lemma decayConstant_pos {α : ℝ} (hα : 0 < α) : 0 < decayConstant α := by
  have hp := Real.one_lt_rpow (by norm_num : (1 : ℝ) < 2) hα
  dsimp [decayConstant]; positivity

lemma finite_polynomial_dyadic_bound {ι : Type*} [Fintype ι]
    (a v : ι → ℝ) (ha : ∀ i, 0 < a i ∧ a i ≤ 4) (hv : ∀ i, 0 ≤ v i)
    (f : ℕ → ℝ) (hf : ∀ j, 0 ≤ f j)
    (hb : ∀ j, f j ≤ ∑ i, v i*((2 : ℝ)^j)^(a i))
    {c : ℝ} (hc : 0 < c) :
    (∑' j : ℕ, f j/(1+c*2^j)^8) ≤ ∑ i, v i*decayConstant (a i)*c^(-(a i)) := by
  have hs (i : ι) := (real_dyadic_decay (a i) (ha i).1 (ha i).2 hc).1.mul_left (v i)
  have hsum : Summable (fun j : ℕ => ∑ i, v i*(((2 : ℝ)^j)^(a i)/(1+c*2^j)^8)) :=
    summable_sum (fun i _ => hs i)
  have hmajor (j : ℕ) : f j/(1+c*2^j)^8 ≤ ∑ i, v i*(((2 : ℝ)^j)^(a i)/(1+c*2^j)^8) := by
    simp only [← mul_div_assoc]
    rw [← Finset.sum_div]
    exact div_le_div_of_nonneg_right (hb j) (by positivity)
  have hf' := hsum.of_nonneg_of_le (fun j => div_nonneg (hf j) (by positivity)) hmajor
  calc
    _ ≤ ∑' j : ℕ, ∑ i, v i*(((2 : ℝ)^j)^(a i)/(1+c*2^j)^8) := hf'.tsum_le_tsum hmajor hsum
    _ = ∑ i, v i*∑' j : ℕ, ((2 : ℝ)^j)^(a i)/(1+c*2^j)^8 := by
      rw [Summable.tsum_finsetSum (fun i _ => hs i)]
      simp only [tsum_mul_left]
    _ ≤ _ := Finset.sum_le_sum (fun i _ => (mul_le_mul_of_nonneg_left
      (real_dyadic_decay (a i) (ha i).1 (ha i).2 hc).2 (hv i)).trans_eq (by dsimp [decayConstant]; ring))

lemma SieveExponent.dual_bound {ξ : ℝ} (hξ : 1 ≤ ξ) (hξ2 : ξ ≤ 2)
    (hExp : SieveExponent ξ) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : Finset Eisenstein) (N c : ℝ), 1 ≤ N → 0 < c →
      (∀ b ∈ P, primary b ∧ Squarefree b ∧ norm b ≤ N) →
      dualDyadicNorm P c 8 ≤ C*N^δ*
        (N*c^(-(δ+1/3 : ℝ))+N^(2/3 : ℝ)*c^(-(δ+2/3 : ℝ))+
          c^(-(δ+ξ))+c^(-(δ+1))) := by
  obtain ⟨D,hD,hcube⟩ := hExp.cube_bound hξ hξ2 hδ
  let a : Fin 4 → ℝ := ![δ+1/3,δ+2/3,δ+ξ,δ+1]
  have ha : ∀ i, 0 < a i ∧ a i ≤ 4 := by intro i; fin_cases i <;> dsimp [a] <;> constructor <;> linarith
  let E : ℝ := ∑ i : Fin 4, (128 : ℝ)^(a i)*decayConstant (a i)
  have htermpos (i : Fin 4) : 0 < (128 : ℝ)^(a i)*decayConstant (a i) :=
    mul_pos (by positivity) (decayConstant_pos (ha i).1)
  have hE : 0 < E := by
    exact Finset.sum_pos (fun i _ => htermpos i) (Finset.univ_nonempty)
  refine ⟨D*E,by positivity,?_⟩
  intro P N c hN hc hP
  have hN0 : 0 < N := zero_lt_one.trans_le hN
  let w : Fin 4 → ℝ := ![N,N^(2/3 : ℝ),1,1]
  have hw : ∀ i, 0 ≤ w i := by intro i; fin_cases i <;> dsimp [w] <;> positivity
  let v : Fin 4 → ℝ := fun i => D*N^δ*w i*(128 : ℝ)^(a i)
  have hv : ∀ i, 0 ≤ v i := by intro i; dsimp [v]; exact mul_nonneg (mul_nonneg (by positivity) (hw i)) (by positivity)
  have hexpand (j : ℕ) : D*(N*(128*(2 : ℝ)^j))^δ*
        (N*(128*(2 : ℝ)^j)^(1/3 : ℝ)+(128*(2 : ℝ)^j*N)^(2/3 : ℝ)+
         (128*(2 : ℝ)^j)^ξ+128*(2 : ℝ)^j) =
      ∑ i : Fin 4, v i*((2 : ℝ)^j)^(a i) := by
    simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,Fin.isValue,Matrix.cons_val_zero,
      Matrix.cons_val_succ,v,w,a,add_zero]
    simp only [Real.mul_rpow (by positivity : (0 : ℝ) ≤ N) (by positivity : (0 : ℝ) ≤ 128*(2 : ℝ)^j),
      Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 128) (by positivity : (0 : ℝ) ≤ (2 : ℝ)^j),
      Real.mul_rpow (by positivity : (0 : ℝ) ≤ 128*(2 : ℝ)^j) (by positivity : (0 : ℝ) ≤ N),
      Real.rpow_add (by norm_num : (0 : ℝ) < 128),Real.rpow_add (by positivity : (0 : ℝ) < (2 : ℝ)^j),Real.rpow_one]
    ring
  have hh := finite_polynomial_dyadic_bound a v ha hv (fun j => finiteCubicBound P (frequencyDyad j))
    (fun j => finiteCubicBound_nonneg _ _)
    (fun j => (hcube P N hN hP j).trans_eq (hexpand j)) hc
  have hEi (i : Fin 4) : (128 : ℝ)^(a i)*decayConstant (a i) ≤ E :=
    Finset.single_le_sum (fun i _ => (htermpos i).le) (Finset.mem_univ i)
  calc
    _ ≤ ∑ i : Fin 4, v i*decayConstant (a i)*c^(-(a i)) := hh
    _ = ∑ i : Fin 4, (D*N^δ)*(w i*c^(-(a i)))*((128 : ℝ)^(a i)*decayConstant (a i)) := by
      apply Finset.sum_congr rfl; intro i _; dsimp [v]; ring
    _ ≤ ∑ i : Fin 4, (D*N^δ)*(w i*c^(-(a i)))*E := by
      apply Finset.sum_le_sum; intro i _
      exact mul_le_mul_of_nonneg_left (hEi i) (mul_nonneg (by positivity) (mul_nonneg (hw i) (by positivity)))
    _ = _ := by
      simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,Fin.isValue,a,w,Matrix.cons_val_zero,
        Matrix.cons_val_succ,add_zero,one_mul]
      ring

end CubicFirstMoment
end
end

end OAI
