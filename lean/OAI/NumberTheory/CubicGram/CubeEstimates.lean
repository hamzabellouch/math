import Mathlib
import OAI.NumberTheory.CubicGram.DyadicRecurrence
import OAI.NumberTheory.CubicGram.FullCubeExtraction

namespace OAI

/-! Geometric decay, cube frequency dyads and numerical block inequalities. -/

section

noncomputable section
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma geometric_decay_step {q d : ℝ} (hq : 1 < q) (hd : 0 < d) (j : ℕ) :
    q^j/(1+d*q^j)^2 ≤
      (q/(d*(q-1)))*(1/(1+d*q^j)-1/(1+d*q^(j+1))) := by
  have hq0 : 0 < q := zero_lt_one.trans hq
  have ht : 0 < q^j := by positivity
  have h1 : 0 < 1+d*q^j := by positivity
  have h2 : 0 < 1+d*q^j*q := by positivity
  have hdq : 0 < d*(q-1) := by positivity
  have he : (q/(d*(q-1)))*(1/(1+d*q^j)-1/(1+d*q^(j+1))) =
      q*q^j/((1+d*q^j)*(1+d*q^j*q)) := by
    rw [pow_succ]
    have hqm : q-1 ≠ 0 := by linarith
    field_simp
    ring
  rw [he]
  apply (div_le_div_iff₀ (sq_pos_of_pos h1) (mul_pos h1 h2)).mpr
  have ht' : 0 ≤ q^j*(1+d*q^j) := by positivity
  nlinarith [mul_nonneg (sub_nonneg.mpr hq.le) ht']

lemma geometric_decay_partial_sum {q d : ℝ} (hq : 1 < q) (hd : 0 < d) (n : ℕ) :
    (∑ j ∈ Finset.range n, q^j/(1+d*q^j)^2) ≤ q/(d*(q-1)) := by
  have hq0 : 0 < q := zero_lt_one.trans hq
  have h := Finset.sum_le_sum (s := Finset.range n) (fun j _ => geometric_decay_step hq hd j)
  rw [← Finset.mul_sum] at h
  have ht : (∑ j ∈ Finset.range n, (1/(1+d*q^j)-1/(1+d*q^(j+1)))) =
      1/(1+d) - 1/(1+d*q^n) := by
    have hh := Finset.sum_range_sub (fun j => (1 : ℝ)/(1+d*q^j)) n
    rw [Finset.sum_sub_distrib] at hh ⊢
    simp only [pow_zero,mul_one] at hh
    linarith
  rw [ht] at h
  have hdq : 0 ≤ q/(d*(q-1)) := by positivity
  have hfirst : 1/(1+d) ≤ (1 : ℝ) := (div_le_one (by positivity)).mpr (by linarith)
  have hlast : (0 : ℝ) ≤ 1/(1+d*q^n) := by positivity
  exact h.trans ((mul_le_mul_of_nonneg_left (by linarith : 1/(1+d)-1/(1+d*q^n) ≤ 1) hdq).trans_eq (mul_one _))

lemma geometric_decay_tsum {q d : ℝ} (hq : 1 < q) (hd : 0 < d) :
    Summable (fun j : ℕ => q^j/(1+d*q^j)^2) ∧
      (∑' j : ℕ, q^j/(1+d*q^j)^2) ≤ q/(d*(q-1)) := by
  have hq0 : 0 < q := zero_lt_one.trans hq
  have hs := summable_of_sum_range_le (fun j => by positivity : ∀ j : ℕ, 0 ≤ q^j/(1+d*q^j)^2)
    (geometric_decay_partial_sum hq hd)
  exact ⟨hs,hs.tsum_le_of_sum_range_le (geometric_decay_partial_sum hq hd)⟩

lemma rpow_cutoff_comparison {α x : ℝ} (hα : 0 < α) (hα4 : α ≤ 4) (hx : 0 ≤ x) :
    (1+x^α)^2 ≤ 4*(1+x)^8 := by
  by_cases hx1 : x ≤ 1
  · have hp := Real.rpow_le_rpow hx hx1 hα.le
    rw [Real.one_rpow] at hp
    have hn := Real.rpow_nonneg hx α
    have hb : 1 ≤ (1+x)^8 := one_le_pow₀ (by linarith)
    nlinarith
  · have hx1 : 1 ≤ x := le_of_not_ge hx1
    have hp : x^α ≤ x^4 := by simpa using Real.rpow_le_rpow_of_exponent_le hx1 hα4
    have hn := Real.rpow_nonneg hx α
    have he : (1+x^α)^2 ≤ (1+x^4)^2 := by gcongr
    have hpow : 1+x^4 ≤ (1+x)^4 := by simpa using pow_add_pow_le (by norm_num : (0 : ℝ) ≤ 1) hx (by norm_num : (4 : ℕ) ≠ 0)
    have he' : (1+x^4)^2 ≤ (1+x)^8 := by
      have := pow_le_pow_left₀ (by positivity) hpow 2
      simpa only [← pow_mul] using this
    have hb : 0 ≤ (1+x)^8 := by positivity
    linarith

lemma real_dyadic_decay (α : ℝ) (hα : 0 < α) (hα4 : α ≤ 4) {c : ℝ} (hc : 0 < c) :
    Summable (fun j : ℕ => ((2 : ℝ)^j)^α/(1+c*2^j)^8) ∧
      (∑' j : ℕ, ((2 : ℝ)^j)^α/(1+c*2^j)^8) ≤
        (4*2^α/(2^α-1))*c^(-α) := by
  have hq : (1 : ℝ) < 2^α := Real.one_lt_rpow (by norm_num) hα
  have hd : 0 < c^α := Real.rpow_pos_of_pos hc α
  have he (j : ℕ) : ((2 : ℝ)^j)^α = (2^α)^j := by
    rw [← Real.rpow_natCast_mul (by norm_num),mul_comm,Real.rpow_mul_natCast (by norm_num)]
  have hmajor (j : ℕ) : ((2 : ℝ)^j)^α/(1+c*2^j)^8 ≤
      4*((2^α)^j/(1+c^α*(2^α)^j)^2) := by
    have hnum : 0 ≤ ((2 : ℝ)^j)^α := by positivity
    have hi : (1+(c*2^j)^α)^2 ≤ 4*(1+c*2^j)^8 := rpow_cutoff_comparison hα hα4 (by positivity)
    rw [Real.mul_rpow hc.le (by positivity),he] at hi
    rw [he]
    rw [← mul_div_assoc]
    apply (div_le_div_iff₀ (by positivity : 0 < (1+c*2^j)^8)
      (by positivity : 0 < (1+c^α*(2^α)^j)^2)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hi (show 0 ≤ (2^α)^j by positivity)]
  have hs := (geometric_decay_tsum hq hd).1.mul_left 4
  have hs' := hs.of_nonneg_of_le (fun _ => by positivity) hmajor
  refine ⟨hs',?_⟩
  calc
    _ ≤ ∑' j : ℕ, 4*((2^α)^j/(1+c^α*(2^α)^j)^2) := hs'.tsum_le_tsum hmajor hs
    _ = 4*∑' j : ℕ, (2^α)^j/(1+c^α*(2^α)^j)^2 := tsum_mul_left
    _ ≤ 4*(2^α/(c^α*(2^α-1))) := mul_le_mul_of_nonneg_left (geometric_decay_tsum hq hd).2 (by norm_num)
    _ = _ := by rw [Real.rpow_neg hc.le]; field_simp

end CubicFirstMoment
end
end

section

noncomputable section
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def squarefreePrimaryDyad (j : ℕ) : Finset Eisenstein :=
  (frequencyDyad j).filter (fun n => primary n ∧ Squarefree n)

lemma mem_squarefreePrimaryDyad {n : Eisenstein} {j : ℕ} :
    n ∈ squarefreePrimaryDyad j ↔ n ∈ frequencyDyad j ∧ primary n ∧ Squarefree n := by
  simp [squarefreePrimaryDyad]

def cubeDyadTriples (j : ℕ) : Finset (ℕ×ℕ×ℕ) :=
  ((Finset.range (j+2)).product ((Finset.range (j+2)).product (Finset.range (j+2)))).filter
    (fun z => z.1+2*z.2.1+3*z.2.2 ≤ j+1)

lemma mem_cubeDyadTriples {j i t c : ℕ} :
    (i,t,c) ∈ cubeDyadTriples j ↔ i+2*t+3*c ≤ j+1 := by
  simp [cubeDyadTriples,Finset.mem_product,Finset.mem_range]
  omega

lemma cubeDyadTriples_card (j : ℕ) : (cubeDyadTriples j).card ≤ (j+2)^3 := by
  have h := Finset.card_filter_le (s := (Finset.range (j+2)).product
    ((Finset.range (j+2)).product (Finset.range (j+2))))
    (p := fun z : ℕ×ℕ×ℕ => z.1+2*z.2.1+3*z.2.2 ≤ j+1)
  simpa [cubeDyadTriples,Finset.card_product,Finset.card_range,pow_succ,mul_assoc] using h

lemma eisenstein_norm_pow (a : Eisenstein) (k : ℕ) : norm (a^k) = norm a ^ k := by
  induction k with
  | zero => simp
  | succ k ih => simp only [pow_succ,norm_mul_eq,ih]

def cubeFrequencyCover (j : ℕ) : Finset Eisenstein :=
  (cubeDyadTriples j).biUnion (fun z => residualCubeSupport (nonzeroNormBall 729)
    (squarefreePrimaryDyad z.1) (squarefreePrimaryDyad z.2.1) (frequencyDyad z.2.2))

lemma frequencyDyad_subset_cubeCover (j : ℕ) : frequencyDyad j ⊆ cubeFrequencyCover j := by
  intro n hn
  obtain ⟨r,s,t,c,hr0,hr,hs,ht,hss,hst,hcop,hc0,he⟩ :=
    full_cube_decomposition (mem_frequencyDyad.mp hn).1
  let i := Nat.log 2 (normNat s)
  let l := Nat.log 2 (normNat t)
  let k := Nat.log 2 (normNat c)
  have hsi : s ∈ frequencyDyad i := mem_frequencyDyad.mpr ⟨primary_ne_zero hs,rfl⟩
  have htl : t ∈ frequencyDyad l := mem_frequencyDyad.mpr ⟨primary_ne_zero ht,rfl⟩
  have hck : c ∈ frequencyDyad k := mem_frequencyDyad.mpr ⟨hc0,rfl⟩
  have hprod : (2 : ℝ)^i*((2 : ℝ)^l)^2*((2 : ℝ)^k)^3 ≤ norm n := by
    calc
      _ ≤ norm s*(norm t)^2*(norm c)^3 := by
        have hsn := norm_nonneg s
        have htn := norm_nonneg t
        have hcn := norm_nonneg c
        gcongr <;> exact (frequencyDyad_norm ‹_›).1
      _ ≤ norm r*norm s*(norm t)^2*(norm c)^3 := by
        have hsn := norm_nonneg s
        have hcn := norm_nonneg c
        have hprim : 0 ≤ norm s*(norm t)^2*(norm c)^3 := by positivity [norm_nonneg s]
        have hmul := le_mul_of_one_le_left hprim (one_le_norm hr0)
        nlinarith
      _ = norm n := by rw [he]; simp only [norm_mul_eq,eisenstein_norm_pow]
  have hexp : i+2*l+3*k ≤ j+1 := by
    apply (pow_le_pow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mp
    have heq : (2 : ℝ)^(i+2*l+3*k) = 2^i*(2^l)^2*(2^k)^3 := by
      simp only [pow_add,pow_mul,mul_comm 2 l,mul_comm 3 k]
    rw [heq]
    exact hprod.trans ((frequencyDyad_norm hn).2.trans_eq (by rw [pow_succ]; ring))
  apply Finset.mem_biUnion.mpr
  refine ⟨(i,l,k),mem_cubeDyadTriples.mpr hexp,?_⟩
  apply Finset.mem_biUnion.mpr
  refine ⟨r,mem_nonzeroNormBall.mpr ⟨hr,hr0⟩,?_⟩
  apply Finset.mem_image.mpr
  refine ⟨s*t^2*c^3,Finset.mem_image.mpr ⟨(s,t,c),?_ ,rfl⟩,?_⟩
  · exact Finset.mem_product.mpr ⟨mem_squarefreePrimaryDyad.mpr ⟨hsi,hs,hss⟩,
      Finset.mem_product.mpr ⟨mem_squarefreePrimaryDyad.mpr ⟨htl,ht,hst⟩,hck⟩⟩
  · rw [he]; ring

lemma finiteCubicBound_biUnion {ι : Type*} (I : Finset ι) (P : Finset Eisenstein)
    (H : ι → Finset Eisenstein) :
    finiteCubicBound P (I.biUnion H) ≤ ∑ i ∈ I, finiteCubicBound P (H i) := by
  apply (finiteCubicBound_le_iff _ _ (Finset.sum_nonneg (fun _ _ => finiteCubicBound_nonneg _ _))).mpr
  intro u
  have hmass : (∑ n ∈ I.biUnion H, ‖∑ b ∈ P, u b*cubicSymbol b n‖^2) ≤
      ∑ i ∈ I, ∑ n ∈ H i, ‖∑ b ∈ P, u b*cubicSymbol b n‖^2 := by
    induction I using Finset.induction_on with
    | empty => simp
    | @insert i I hi ih =>
      rw [Finset.biUnion_insert,Finset.sum_insert hi]
      have he := Finset.sum_union_inter (s₁ := H i) (s₂ := I.biUnion H)
        (f := fun n => ‖∑ b ∈ P, u b*cubicSymbol b n‖^2)
      have hn : 0 ≤ ∑ n ∈ H i ∩ I.biUnion H, ‖∑ b ∈ P, u b*cubicSymbol b n‖^2 :=
        Finset.sum_nonneg (fun _ _ => sq_nonneg _)
      linarith
  calc
    _ ≤ ∑ i ∈ I, ∑ n ∈ H i, ‖∑ b ∈ P, u b*cubicSymbol b n‖^2 := hmass
    _ ≤ ∑ i ∈ I, finiteCubicBound P (H i)*∑ b ∈ P, ‖u b‖^2 :=
      Finset.sum_le_sum (fun i _ => finiteCubicBound_controls_mass _ _ _)
    _ = _ := by rw [Finset.sum_mul]

theorem finiteCubicBound_frequency_cube (P : Finset Eisenstein)
    (hP : ∀ b ∈ P, primary b) (j : ℕ) :
    finiteCubicBound P (frequencyDyad j) ≤
      (nonzeroNormBall 729).card * ∑ z ∈ cubeDyadTriples j,
        min (((squarefreePrimaryDyad z.2.1).card : ℝ)*(frequencyDyad z.2.2).card*
               finiteCubicBound P (squarefreePrimaryDyad z.1))
            (((squarefreePrimaryDyad z.1).card : ℝ)*(frequencyDyad z.2.2).card*
               finiteCubicBound P (squarefreePrimaryDyad z.2.1)) := by
  apply (finiteCubicBound_mono (Finset.Subset.refl P) (frequencyDyad_subset_cubeCover j)).trans
  apply (finiteCubicBound_biUnion (cubeDyadTriples j) P _).trans
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum (fun z hz => finiteCubicBound_residualCube _ _ _ _ _ hP)

end CubicFirstMoment
end
end

section

noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma rpow_third_cube {x : ℝ} (hx : 0 ≤ x) : (x^(1/3 : ℝ))^3 = x := by
  rw [← Real.rpow_natCast,← Real.rpow_mul hx]
  norm_num

lemma rpow_two_thirds_cube {x : ℝ} (hx : 0 ≤ x) : (x^(2/3 : ℝ))^3 = x^2 := by
  rw [← Real.rpow_natCast,← Real.rpow_mul hx]
  norm_num

lemma cube_block_numerical {S T K N J ξ : ℝ}
    (hS : 1 ≤ S) (hT : 1 ≤ T) (hK : 1 ≤ K) (hN : 0 ≤ N)
    (hJ : S*T^2*K^3 ≤ J) (hξ : 1 ≤ ξ) (hξ2 : ξ ≤ 2) :
    min (K*T*(N+(N*S)^(2/3 : ℝ)+S^ξ))
        (K*S*(N+(N*T)^(2/3 : ℝ)+T^ξ)) ≤
      N*J^(1/3 : ℝ)+(J*N)^(2/3 : ℝ)+J^ξ+J := by
  have hS0 : 0 ≤ S := zero_le_one.trans hS
  have hT0 : 0 ≤ T := zero_le_one.trans hT
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  have hJ0 : 0 ≤ J := (by positivity : 0 ≤ S*T^2*K^3).trans hJ
  have hJξ : 0 ≤ J^ξ := Real.rpow_nonneg hJ0 _
  have hcrossLeft : K*T*(N*S)^(2/3 : ℝ) ≤ (J*N)^(2/3 : ℝ) := by
    apply (pow_le_pow_iff_left₀ (by positivity : 0 ≤ K*T*(N*S)^(2/3 : ℝ))
      (by positivity : 0 ≤ (J*N)^(2/3 : ℝ)) (by norm_num : (3 : ℕ) ≠ 0)).mp
    rw [mul_pow,mul_pow,rpow_two_thirds_cube (by positivity),rpow_two_thirds_cube (by positivity)]
    calc
      _ = S^2*T^3*K^3*N^2 := by ring
      _ ≤ S^2*T^4*K^6*N^2 := by
        have ht : T^3 ≤ T^4 := pow_le_pow_right₀ hT (by norm_num)
        have hk : K^3 ≤ K^6 := pow_le_pow_right₀ hK (by norm_num)
        gcongr
      _ = (S*T^2*K^3*N)^2 := by ring
      _ ≤ _ := by gcongr
  by_cases hST : T ≤ S
  · have hsmall : K*T ≤ J^(1/3 : ℝ) := by
      apply (pow_le_pow_iff_left₀ (by positivity : 0 ≤ K*T)
        (by positivity : 0 ≤ J^(1/3 : ℝ)) (by norm_num : (3 : ℕ) ≠ 0)).mp
      rw [rpow_third_cube hJ0]
      calc
        _ = T*T^2*K^3 := by ring
        _ ≤ S*T^2*K^3 := by gcongr
        _ ≤ J := hJ
    have hp : K*T*S^ξ ≤ J^ξ := by
      have hTK : K*T ≤ T^2*K^3 := by
        calc
          _ = T*K := mul_comm _ _
          _ ≤ T^2*K^3 := by
            gcongr
            · nlinarith [sq_nonneg (T-1)]
            · exact (le_self_pow₀ hK (by norm_num : (3 : ℕ) ≠ 0))
      have hTK1 : 1 ≤ T^2*K^3 := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hT) (one_le_pow₀ hK)
      have htξ := Real.self_le_rpow_of_one_le hTK1 hξ
      calc
        _ ≤ (T^2*K^3)^ξ*S^ξ := mul_le_mul_of_nonneg_right (hTK.trans htξ) (by positivity)
        _ = (S*T^2*K^3)^ξ := by rw [← Real.mul_rpow (by positivity) hS0]; congr 1; ring
        _ ≤ J^ξ := Real.rpow_le_rpow (by positivity) hJ (by linarith)
    apply (min_le_left _ _).trans
    have hn := mul_le_mul_of_nonneg_right hsmall hN
    nlinarith
  · have hST : S ≤ T := (le_of_not_ge hST)
    have hsmall : K*S ≤ J^(1/3 : ℝ) := by
      apply (pow_le_pow_iff_left₀ (by positivity : 0 ≤ K*S)
        (by positivity : 0 ≤ J^(1/3 : ℝ)) (by norm_num : (3 : ℕ) ≠ 0)).mp
      rw [rpow_third_cube hJ0]
      calc
        _ = S*S^2*K^3 := by ring
        _ ≤ S*T^2*K^3 := by gcongr
        _ ≤ J := hJ
    have hc : K*S*(N*T)^(2/3 : ℝ) ≤ (J*N)^(2/3 : ℝ) := by
      apply (pow_le_pow_iff_left₀ (by positivity : 0 ≤ K*S*(N*T)^(2/3 : ℝ))
        (by positivity : 0 ≤ (J*N)^(2/3 : ℝ)) (by norm_num : (3 : ℕ) ≠ 0)).mp
      rw [mul_pow,mul_pow,rpow_two_thirds_cube (by positivity),rpow_two_thirds_cube (by positivity)]
      have hST2 : S ≤ T^2 := hST.trans (by nlinarith [sq_nonneg (T-1)])
      calc
        _ = S^2*S*T^2*K^3*N^2 := by ring
        _ ≤ S^2*T^2*T^2*K^6*N^2 := by
          have hk : K^3 ≤ K^6 := pow_le_pow_right₀ hK (by norm_num)
          gcongr
        _ = (S*T^2*K^3*N)^2 := by ring
        _ ≤ _ := by gcongr
    have hp : K*S*T^ξ ≤ J := by
      have htξ : T^ξ ≤ T^2 := by simpa using Real.rpow_le_rpow_of_exponent_le hT hξ2
      calc
        _ ≤ K^3*S*T^2 := by
          gcongr
          exact le_self_pow₀ hK (by norm_num : (3 : ℕ) ≠ 0)
        _ = S*T^2*K^3 := by ring
        _ ≤ J := hJ
    apply (min_le_right _ _).trans
    have hn := mul_le_mul_of_nonneg_right hsmall hN
    nlinarith

end CubicFirstMoment
end
end

end OAI
