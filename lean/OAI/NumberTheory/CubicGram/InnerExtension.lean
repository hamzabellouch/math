import Mathlib
import OAI.NumberTheory.CubicGram.SieveImprovement

namespace OAI

/-! Full inner cube covers and sharp coefficient extension bounds. -/

section

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma complex_norm_sum_sq_le {ι : Type*} (I : Finset ι) (v : ι → ℂ) :
    ‖∑ i ∈ I, v i‖^2 ≤ (I.card : ℝ)*∑ i ∈ I, ‖v i‖^2 := by
  have ht := norm_sum_le I v
  have hc := Finset.sum_mul_sq_le_sq_mul_sq I (fun _ => (1 : ℝ)) (fun i => ‖v i‖)
  simp only [one_mul,one_pow,Finset.sum_const,nsmul_eq_mul,mul_one] at hc
  exact (pow_le_pow_left₀ (_root_.norm_nonneg _) ht 2).trans hc

lemma innerCubeBlock_fixed_mass (P S : Finset Eisenstein)
    (hP : ∀ a ∈ P, primary a) (hS : ∀ s ∈ S, primary s)
    (r : Eisenstein) (v : Eisenstein → ℂ) :
    (∑ a ∈ P, ‖∑ s ∈ S, v s*cubicSymbol a (r*s)‖^2) ≤
      finiteCubicBound S P * ∑ s ∈ S, ‖v s‖^2 := by
  apply le_trans _ (finiteCubicBound_controls_mass S P v)
  apply Finset.sum_le_sum
  intro a ha
  have he : (∑ s ∈ S, v s*cubicSymbol a (r*s)) =
      cubicSymbol a r * ∑ s ∈ S, v s*cubicSymbol s a := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s hs
    rw [cubicSymbol_mul_upper (hP a ha),cubic_reciprocity (hP a ha) (hS s hs)]
    ring
  rw [he,norm_mul,mul_pow]
  apply mul_le_of_le_one_left (sq_nonneg _)
  exact (pow_le_pow_left₀ (_root_.norm_nonneg _) (norm_cubicSymbol_le_one (hP a ha) r) 2).trans_eq (by norm_num)

theorem innerCubeBlock_mass (P S T C : Finset Eisenstein)
    (hP : ∀ a ∈ P, primary a) (hS : ∀ s ∈ S, primary s)
    (r : Eisenstein) (v : Eisenstein → Eisenstein → Eisenstein → ℂ)
    (D : ℝ) (_hD : 0 ≤ D) (hv : ∀ s ∈ S, ∀ t ∈ T, ∀ c ∈ C, ‖v s t c‖ ≤ D) :
    (∑ a ∈ P, ‖∑ t ∈ T, ∑ c ∈ C, ∑ s ∈ S,
      v s t c*cubicSymbol a (r*(s*t^2*c^3))‖^2) ≤
      ((T.card : ℝ)*C.card)^2 * finiteCubicBound S P * S.card * D^2 := by
  have hrow (t : Eisenstein) (ht : t ∈ T) (c : Eisenstein) (hc : c ∈ C) :
      (∑ a ∈ P, ‖∑ s ∈ S, v s t c*cubicSymbol a (r*(s*t^2*c^3))‖^2) ≤
      finiteCubicBound S P * S.card * D^2 := by
    have he : ∀ s : Eisenstein, r*(s*t^2*c^3) = (r*t^2*c^3)*s := by intro s; ring
    simp_rw [he]
    apply (innerCubeBlock_fixed_mass P S hP hS _ (fun s => v s t c)).trans
    have hh : (∑ s ∈ S, ‖v s t c‖^2) ≤ (S.card : ℝ)*D^2 := by
      calc
        _ ≤ ∑ s ∈ S, D^2 := Finset.sum_le_sum (fun s hs =>
          pow_le_pow_left₀ (_root_.norm_nonneg _) (hv s hs t ht c hc) 2)
        _ = _ := by simp
    exact (mul_le_mul_of_nonneg_left hh (finiteCubicBound_nonneg _ _)).trans_eq (by ring)
  have htriangle (a : Eisenstein) :
      ‖∑ t ∈ T, ∑ c ∈ C, ∑ s ∈ S, v s t c*cubicSymbol a (r*(s*t^2*c^3))‖^2 ≤
      ((T.card : ℝ)*C.card)*∑ t ∈ T, ∑ c ∈ C,
        ‖∑ s ∈ S, v s t c*cubicSymbol a (r*(s*t^2*c^3))‖^2 := by
    simpa only [Finset.product_eq_sprod,Finset.sum_product,Finset.card_product,Nat.cast_mul] using
      complex_norm_sum_sq_le (T.product C)
        (fun z => ∑ s ∈ S, v s z.1 z.2*cubicSymbol a (r*(s*z.1^2*z.2^3)))
  calc
    _ ≤ ∑ a ∈ P, ((T.card : ℝ)*C.card)*∑ t ∈ T, ∑ c ∈ C,
        ‖∑ s ∈ S, v s t c*cubicSymbol a (r*(s*t^2*c^3))‖^2 :=
      Finset.sum_le_sum (fun a _ => htriangle a)
    _ = ((T.card : ℝ)*C.card)*∑ t ∈ T, ∑ c ∈ C, ∑ a ∈ P,
        ‖∑ s ∈ S, v s t c*cubicSymbol a (r*(s*t^2*c^3))‖^2 := by
      rw [← Finset.mul_sum,Finset.sum_comm (s := P) (t := T)]
      congr 1
      apply Finset.sum_congr rfl
      intro t ht
      exact Finset.sum_comm
    _ ≤ ((T.card : ℝ)*C.card)*∑ t ∈ T, ∑ c ∈ C,
        finiteCubicBound S P * S.card * D^2 := by
      gcongr with t ht c hc
      exact hrow t ht c hc
    _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul]; ring

def finiteCoverCoefficient {ι : Type*} (I : Finset ι) (f : ι → Eisenstein)
    (H : Finset Eisenstein) (v : Eisenstein → ℂ) (x : ι) : ℂ :=
  if f x ∈ H then v (f x) / ((I.filter (fun y => f y = f x)).card : ℂ) else 0

lemma finiteCoverCoefficient_norm_le {ι : Type*} (I : Finset ι) (f : ι → Eisenstein)
    (H : Finset Eisenstein) (v : Eisenstein → ℂ) (D : ℝ) (hD : 0 ≤ D)
    (hv : ∀ n ∈ H, ‖v n‖ ≤ D) {x : ι} (hx : x ∈ I) :
    ‖finiteCoverCoefficient I f H v x‖ ≤ D := by
  unfold finiteCoverCoefficient
  split_ifs with h
  · have hc : 1 ≤ (I.filter (fun y => f y = f x)).card :=
      Finset.one_le_card.mpr ⟨x,Finset.mem_filter.mpr ⟨hx,rfl⟩⟩
    rw [norm_div,Complex.norm_natCast]
    exact (div_le_self (_root_.norm_nonneg _) (by exact_mod_cast hc)).trans (hv _ h)
  · simpa using hD

lemma finiteCoverCoefficient_sum {ι : Type*} (I : Finset ι) (f : ι → Eisenstein)
    (H : Finset Eisenstein) (hcover : H ⊆ I.image f)
    (v k : Eisenstein → ℂ) :
    (∑ x ∈ I, finiteCoverCoefficient I f H v x * k (f x)) =
      ∑ n ∈ H, v n*k n := by
  classical
  have he : (∑ x ∈ I, finiteCoverCoefficient I f H v x * k (f x)) =
      ∑ x ∈ I with f x ∈ H,
        (v (f x) / ((I.filter (fun y => f y = f x)).card : ℂ))*k (f x) := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro x hx
    simp only [finiteCoverCoefficient,ite_mul,zero_mul]
  rw [he,← Finset.sum_fiberwise_eq_sum_filter' I H f
    (fun n => (v n / ((I.filter (fun y => f y = n)).card : ℂ))*k n)]
  apply Finset.sum_congr rfl
  intro n hn
  have hc : (I.filter (fun y => f y = n)).card ≠ 0 := by
    obtain ⟨x,hx,hfx⟩ := Finset.mem_image.mp (hcover hn)
    exact Finset.card_ne_zero.mpr ⟨x,Finset.mem_filter.mpr ⟨hx,hfx⟩⟩
  have hc' : ((I.filter (fun y => f y = n)).card : ℂ) ≠ 0 := by exact_mod_cast hc
  simp only [Finset.sum_const,nsmul_eq_mul]
  field_simp

abbrev InnerCubeIndex := (_index : ℕ×ℕ×ℕ) × (Eisenstein×Eisenstein×Eisenstein×Eisenstein)

def innerCubeIndices (j : ℕ) : Finset InnerCubeIndex :=
  (cubeDyadTriples j).sigma (fun z => (nonzeroNormBall 729).product
    ((squarefreePrimaryDyad z.1).product
      ((squarefreePrimaryDyad z.2.1).product (frequencyDyad z.2.2))))

def innerCubeValue (q : InnerCubeIndex) : Eisenstein :=
  q.2.1*(q.2.2.1*q.2.2.2.1^2*q.2.2.2.2^3)

lemma frequencyDyad_subset_innerCubeImage (j : ℕ) :
    frequencyDyad j ⊆ (innerCubeIndices j).image innerCubeValue := by
  intro n hn
  have hh := frequencyDyad_subset_cubeCover j hn
  obtain ⟨z,hz,hm⟩ := Finset.mem_biUnion.mp hh
  obtain ⟨r,hr,hm⟩ := Finset.mem_biUnion.mp hm
  obtain ⟨m,hm,he⟩ := Finset.mem_image.mp hm
  obtain ⟨⟨s,t,c⟩,hstc,hem⟩ := Finset.mem_image.mp hm
  obtain ⟨hs,htc⟩ := Finset.mem_product.mp hstc
  obtain ⟨ht,hc⟩ := Finset.mem_product.mp htc
  refine Finset.mem_image.mpr ⟨⟨z,r,s,t,c⟩,?_,?_⟩
  · exact Finset.mem_sigma.mpr ⟨hz,Finset.mem_product.mpr ⟨hr,
      Finset.mem_product.mpr ⟨hs,Finset.mem_product.mpr ⟨ht,hc⟩⟩⟩⟩
  · dsimp [innerCubeValue]
    rw [← he,← hem]

def innerCubeCoefficient (j : ℕ) (v : Eisenstein → ℂ) : InnerCubeIndex → ℂ :=
  finiteCoverCoefficient (innerCubeIndices j) innerCubeValue (frequencyDyad j) v

def innerCubeBlockSum (j : ℕ) (v : Eisenstein → ℂ) (a : Eisenstein)
    (z : ℕ×ℕ×ℕ) (r : Eisenstein) : ℂ :=
  ∑ t ∈ squarefreePrimaryDyad z.2.1, ∑ c ∈ frequencyDyad z.2.2,
    ∑ s ∈ squarefreePrimaryDyad z.1,
      innerCubeCoefficient j v ⟨z,r,s,t,c⟩*cubicSymbol a (r*(s*t^2*c^3))

lemma innerCubeCoefficient_sum (j : ℕ) (v : Eisenstein → ℂ) (a : Eisenstein) :
    (∑ n ∈ frequencyDyad j, v n*cubicSymbol a n) =
      ∑ z ∈ cubeDyadTriples j, ∑ r ∈ nonzeroNormBall 729,
        innerCubeBlockSum j v a z r := by
  rw [← finiteCoverCoefficient_sum (innerCubeIndices j) innerCubeValue (frequencyDyad j)
    (frequencyDyad_subset_innerCubeImage j) v (cubicSymbol a)]
  simp only [innerCubeIndices,Finset.sum_sigma,Finset.product_eq_sprod,Finset.sum_product]
  apply Finset.sum_congr rfl
  intro z hz
  apply Finset.sum_congr rfl
  intro r hr
  dsimp only [innerCubeBlockSum,innerCubeValue,innerCubeCoefficient]
  rw [Finset.sum_comm (s := squarefreePrimaryDyad z.1) (t := squarefreePrimaryDyad z.2.1)]
  apply Finset.sum_congr rfl
  intro t ht
  exact Finset.sum_comm

lemma innerCubeCoefficient_block_mass (P : Finset Eisenstein) (hP : ∀ a ∈ P, primary a)
    (j : ℕ) (v : Eisenstein → ℂ) (D : ℝ) (hD : 0 ≤ D)
    (hv : ∀ n ∈ frequencyDyad j, ‖v n‖ ≤ D)
    (z : ℕ×ℕ×ℕ) (hz : z ∈ cubeDyadTriples j) (r : Eisenstein)
    (hr : r ∈ nonzeroNormBall 729) :
    (∑ a ∈ P, ‖innerCubeBlockSum j v a z r‖^2) ≤
      (((squarefreePrimaryDyad z.2.1).card : ℝ)*(frequencyDyad z.2.2).card)^2 *
        finiteCubicBound (squarefreePrimaryDyad z.1) P *
          (squarefreePrimaryDyad z.1).card * D^2 := by
  apply innerCubeBlock_mass P _ _ _ hP
    (fun s hs => (mem_squarefreePrimaryDyad.mp hs).2.1) r
    (fun s t c => innerCubeCoefficient j v ⟨z,r,s,t,c⟩) D hD
  intro s hs t ht c hc
  apply finiteCoverCoefficient_norm_le _ _ _ _ D hD hv
  exact Finset.mem_sigma.mpr ⟨hz,Finset.mem_product.mpr ⟨hr,
    Finset.mem_product.mpr ⟨hs,Finset.mem_product.mpr ⟨ht,hc⟩⟩⟩⟩

lemma complex_mass_sum_sq_le {ι κ : Type*} (I : Finset ι) (P : Finset κ)
    (F : κ → ι → ℂ) :
    (∑ a ∈ P, ‖∑ i ∈ I, F a i‖^2) ≤
      (I.card : ℝ)*∑ i ∈ I, ∑ a ∈ P, ‖F a i‖^2 := by
  calc
    _ ≤ ∑ a ∈ P, (I.card : ℝ)*∑ i ∈ I, ‖F a i‖^2 :=
      Finset.sum_le_sum (fun a _ => complex_norm_sum_sq_le I (F a))
    _ = _ := by rw [← Finset.mul_sum,Finset.sum_comm]

theorem innerCubeCover_mass (P : Finset Eisenstein) (hP : ∀ a ∈ P, primary a)
    (j : ℕ) (v : Eisenstein → ℂ) (D : ℝ) (hD : 0 ≤ D)
    (hv : ∀ n ∈ frequencyDyad j, ‖v n‖ ≤ D) :
    (∑ a ∈ P, ‖∑ n ∈ frequencyDyad j, v n*cubicSymbol a n‖^2) ≤
      (cubeDyadTriples j).card * ((nonzeroNormBall 729).card : ℝ)^2 *
      ∑ z ∈ cubeDyadTriples j,
        (((squarefreePrimaryDyad z.2.1).card : ℝ)*(frequencyDyad z.2.2).card)^2 *
          finiteCubicBound (squarefreePrimaryDyad z.1) P *
            (squarefreePrimaryDyad z.1).card * D^2 := by
  have htriangle := complex_mass_sum_sq_le
    ((cubeDyadTriples j).product (nonzeroNormBall 729)) P
    (fun a q => innerCubeBlockSum j v a q.1 q.2)
  simp only [Finset.product_eq_sprod,Finset.sum_product,Finset.card_product,Nat.cast_mul]
    at htriangle
  simp_rw [innerCubeCoefficient_sum j v]
  apply htriangle.trans
  calc
    _ ≤ ((cubeDyadTriples j).card : ℝ)*(nonzeroNormBall 729).card *
        ∑ z ∈ cubeDyadTriples j, ∑ r ∈ nonzeroNormBall 729,
        (((squarefreePrimaryDyad z.2.1).card : ℝ)*(frequencyDyad z.2.2).card)^2 *
          finiteCubicBound (squarefreePrimaryDyad z.1) P *
            (squarefreePrimaryDyad z.1).card * D^2 := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Finset.sum_le_sum (fun z hz => Finset.sum_le_sum (fun r hr =>
        innerCubeCoefficient_block_mass P hP j v D hD hv z hz r hr))
    _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul,← Finset.mul_sum]; ring

theorem innerCubeBlock_sharp {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : Finset Eisenstein) (N : ℝ), 1 ≤ N →
      (∀ a ∈ P, primary a ∧ Squarefree a ∧ norm a ≤ N) →
      ∀ (j : ℕ) (z : ℕ×ℕ×ℕ), z ∈ cubeDyadTriples j →
        (((squarefreePrimaryDyad z.2.1).card : ℝ)*(frequencyDyad z.2.2).card)^2 *
          finiteCubicBound (squarefreePrimaryDyad z.1) P *
            (squarefreePrimaryDyad z.1).card ≤
        C*(N*(128*(2 : ℝ)^j))^ε*(128*(2 : ℝ)^j)*
          (N+128*(2 : ℝ)^j+(N*(128*(2 : ℝ)^j))^(2/3 : ℝ)) := by
  obtain ⟨C,hC,hsharp⟩ := finiteCubicBound_sharp ε hε
  refine ⟨18^5*C,by positivity,?_⟩
  intro P N hN hP j z hz
  let S : ℝ := 2*(2 : ℝ)^z.1
  let T : ℝ := 2*(2 : ℝ)^z.2.1
  let K : ℝ := 2*(2 : ℝ)^z.2.2
  let J : ℝ := 128*(2 : ℝ)^j
  have htwo (i : ℕ) : (1 : ℝ) ≤ 2*2^i := by
    have hh : (1 : ℝ) ≤ 2^i := one_le_pow₀ (by norm_num)
    linarith
  have hS : 1 ≤ S := htwo _
  have hT : 1 ≤ T := htwo _
  have hK : 1 ≤ K := htwo _
  have hp : S*T^2*K^3 ≤ J := cube_scaled_sizes hz
  have hSJ : S ≤ J := by
    apply le_trans _ hp
    exact (le_mul_of_one_le_right (by positivity : 0 ≤ S) (one_le_pow₀ hT)).trans
      (le_mul_of_one_le_right (by positivity) (one_le_pow₀ hK))
  have hsf : ∀ s ∈ squarefreePrimaryDyad z.1,
      primary s ∧ Squarefree s ∧ norm s ≤ S := by
    intro s hs
    exact ⟨(mem_squarefreePrimaryDyad.mp hs).2.1,(mem_squarefreePrimaryDyad.mp hs).2.2,
      (frequencyDyad_norm (mem_squarefreePrimaryDyad.mp hs).1).2⟩
  have hb : finiteCubicBound (squarefreePrimaryDyad z.1) P ≤
      C*(N*J)^ε*(N+J+(N*J)^(2/3 : ℝ)) := by
    apply (hsharp _ _ N S hN hS hsf hP).trans
    gcongr
  have hcardS : ((squarefreePrimaryDyad z.1).card : ℝ) ≤ 18*S := by
    dsimp [S]; nlinarith [squarefreePrimaryDyad_card_le z.1]
  have hcardT : ((squarefreePrimaryDyad z.2.1).card : ℝ) ≤ 18*T := by
    dsimp [T]; nlinarith [squarefreePrimaryDyad_card_le z.2.1]
  have hcardK : ((frequencyDyad z.2.2).card : ℝ) ≤ 18*K := by
    dsimp [K]; nlinarith [frequencyDyad_card_le z.2.2]
  have hf : (((squarefreePrimaryDyad z.2.1).card : ℝ)*(frequencyDyad z.2.2).card)^2 *
      (squarefreePrimaryDyad z.1).card ≤ 18^5*J := by
    calc
      _ ≤ ((18*T)*(18*K))^2*(18*S) := by gcongr
      _ = 18^5*(S*T^2*K^2) := by ring
      _ ≤ 18^5*(S*T^2*K^3) := by
        gcongr
        norm_num
      _ ≤ _ := mul_le_mul_of_nonneg_left hp (by norm_num)
  calc
    _ = ((((squarefreePrimaryDyad z.2.1).card : ℝ)*(frequencyDyad z.2.2).card)^2 *
        (squarefreePrimaryDyad z.1).card)*finiteCubicBound (squarefreePrimaryDyad z.1) P := by ring
    _ ≤ (18^5*J)*(C*(N*J)^ε*(N+J+(N*J)^(2/3 : ℝ))) :=
      mul_le_mul hf hb (finiteCubicBound_nonneg _ _) (by positivity)
    _ = _ := by dsimp [J]; ring

theorem cubic_inner_extension_scaled {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : Finset Eisenstein) (N : ℝ), 1 ≤ N →
      (∀ a ∈ P, primary a ∧ Squarefree a ∧ norm a ≤ N) →
      ∀ (j : ℕ) (v : Eisenstein → ℂ) (D : ℝ), 0 ≤ D →
      (∀ n ∈ frequencyDyad j, ‖v n‖ ≤ D) →
      (∑ a ∈ P, ‖∑ n ∈ frequencyDyad j, v n*cubicSymbol a n‖^2) ≤
        C*(N*(128*(2 : ℝ)^j))^ε*(128*(2 : ℝ)^j)*
          (N+128*(2 : ℝ)^j+(N*(128*(2 : ℝ)^j))^(2/3 : ℝ))*D^2 := by
  obtain ⟨B,hB,hblock⟩ := innerCubeBlock_sharp (show 0 < ε/2 by linarith)
  obtain ⟨E,hE,hpoly⟩ := dyadic_polynomial_small_power 6 (show 0 < ε/2 by linarith)
  let R : ℝ := (nonzeroNormBall 729).card
  refine ⟨(R+1)^2*B*E,by dsimp [R]; positivity,?_⟩
  intro P N hN hP j v D hD hv
  let J : ℝ := 128*(2 : ℝ)^j
  let F : ℝ := N+J+(N*J)^(2/3 : ℝ)
  have hJpos : 0 < J := by dsimp [J]; positivity
  have hNpos : 0 < N := zero_lt_one.trans_le hN
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hR' : R ≤ R+1 := by linarith
  have hcount : ((cubeDyadTriples j).card : ℝ)^2 ≤ E*J^(ε/2) := by
    have hc : ((cubeDyadTriples j).card : ℝ) ≤ ((j : ℝ)+2)^3 := by
      exact_mod_cast cubeDyadTriples_card j
    calc
      _ ≤ (((j : ℝ)+2)^3)^2 := by gcongr
      _ = ((j : ℝ)+2)^6 := by ring
      _ ≤ E*((2 : ℝ)^j)^(ε/2) := hpoly j
      _ ≤ _ := by
        gcongr
        dsimp [J]
        have hh : (0 : ℝ) ≤ 2^j := by positivity
        linarith
  have heps : J^(ε/2)*(N*J)^(ε/2) ≤ (N*J)^ε := by
    calc
      _ ≤ (N*J)^(ε/2)*(N*J)^(ε/2) := by
        gcongr
        exact le_mul_of_one_le_left hJpos.le hN
      _ = _ := by rw [← Real.rpow_add (by positivity)]; congr 1; ring
  have hh := innerCubeCover_mass P (fun a ha => (hP a ha).1) j v D hD hv
  apply hh.trans
  calc
    _ ≤ (cubeDyadTriples j).card * R^2 *
        ∑ z ∈ cubeDyadTriples j, B*(N*J)^(ε/2)*J*F*D^2 := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum
      intro z hz
      exact mul_le_mul_of_nonneg_right (hblock P N hN hP j z hz) (sq_nonneg D)
    _ = ((cubeDyadTriples j).card : ℝ)^2 * R^2 * B*(N*J)^(ε/2)*J*F*D^2 := by
      simp only [Finset.sum_const,nsmul_eq_mul]; ring
    _ ≤ (E*J^(ε/2)) * (R+1)^2 * B*(N*J)^(ε/2)*J*F*D^2 := by
      gcongr
    _ = ((R+1)^2*B*E)* (J^(ε/2)*(N*J)^(ε/2))*J*F*D^2 := by ring
    _ ≤ ((R+1)^2*B*E)* (N*J)^ε*J*F*D^2 := by gcongr
    _ = _ := rfl

theorem cubic_inner_extension {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : Finset Eisenstein) (N : ℝ), 1 ≤ N →
      (∀ a ∈ P, primary a ∧ Squarefree a ∧ norm a ≤ N) →
      ∀ (j : ℕ) (v : Eisenstein → ℂ) (D : ℝ), 0 ≤ D →
      (∀ n ∈ frequencyDyad j, ‖v n‖ ≤ D) →
      (∑ a ∈ P, ‖∑ n ∈ frequencyDyad j, v n*cubicSymbol a n‖^2) ≤
        C*(N*(2 : ℝ)^j)^ε*(2 : ℝ)^j*
          (N+(2 : ℝ)^j+(N*(2 : ℝ)^j)^(2/3 : ℝ))*D^2 := by
  obtain ⟨C,hC,h⟩ := cubic_inner_extension_scaled hε
  refine ⟨C*128^ε*128^2,by positivity,?_⟩
  intro P N hN hP j v D hD hv
  have hN0 : 0 ≤ N := zero_le_one.trans hN
  have hJ0 : 0 < (2 : ℝ)^j := by positivity
  have hp : (128 : ℝ)^(2/3 : ℝ) ≤ 128 := by
    exact (Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num : (2/3 : ℝ) ≤ 1)).trans_eq (Real.rpow_one _)
  have hm : (N*(128*(2 : ℝ)^j))^(2/3 : ℝ) ≤
      128*((N*(2 : ℝ)^j)^(2/3 : ℝ)) := by
    rw [show N*(128*(2 : ℝ)^j) = 128*(N*(2 : ℝ)^j) by ring,
      Real.mul_rpow (by norm_num) (by positivity)]
    exact mul_le_mul_of_nonneg_right hp (by positivity)
  have hb : N+128*(2 : ℝ)^j+(N*(128*(2 : ℝ)^j))^(2/3 : ℝ) ≤
      128*(N+(2 : ℝ)^j+(N*(2 : ℝ)^j)^(2/3 : ℝ)) := by nlinarith
  have he : (N*(128*(2 : ℝ)^j))^ε = 128^ε*(N*(2 : ℝ)^j)^ε := by
    rw [show N*(128*(2 : ℝ)^j) = 128*(N*(2 : ℝ)^j) by ring,
      Real.mul_rpow (by norm_num) (by positivity)]
  apply (h P N hN hP j v D hD hv).trans
  rw [he]
  calc
    _ ≤ C*(128^ε*(N*(2 : ℝ)^j)^ε)*(128*(2 : ℝ)^j)*
        (128*(N+(2 : ℝ)^j+(N*(2 : ℝ)^j)^(2/3 : ℝ)))*D^2 := by gcongr
    _ = _ := by ring

end CubicFirstMoment
end
end

end OAI
