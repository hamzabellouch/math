import Mathlib
import OAI.NumberTheory.CubicGauss.SmoothBounds

namespace OAI

/-! Power-bound formulations and squarefree-to-cubic extensions. -/

noncomputable section
open scoped BigOperators
open Module Complex UniqueFactorizationMonoid
attribute [local instance] Classical.propDecidable

namespace CubicFirstMoment

 

def CubicPowerBound (α : ℝ) : Prop :=
  ∀ ε : ℝ,0<ε → ∃ C : ℝ,0<C ∧ ∀ (M N : ℝ) (S : Finset Eisenstein) (u : Eisenstein → ℂ),
    1≤M → 1≤N → S ⊆ squarefreePrimaryBall N →
    ∑ m ∈ squarefreePrimaryBall M,cubicRowEnergy S u m ≤
      C*(M*N)^ε*(M+N^α+(M*N)^(2/3:ℝ))*∑ b ∈ S,‖u b‖^2

namespace SieveOperator
lemma Bound.restrict_coeff {ι θ : Type*} [DecidableEq θ] {H : Finset ι} {S T : Finset θ}
    {χ : ι → θ → ℂ} {K : ℝ} (h : Bound H S χ K) (hT : T ⊆ S) : Bound H T χ K := by
  intro u
  let v : θ → ℂ := fun a => if a∈T then u a else 0
  have he (f : θ → ℂ) : (∑ a ∈ S,v a*f a) = ∑ a ∈ T,u a*f a := by
    calc
      _ = ∑ a ∈ S,if a∈T then u a*f a else 0 := by
        apply Finset.sum_congr rfl
        intro a ha
        by_cases ht : a∈T <;> simp [v,ht]
      _ = _ := by rw [← Finset.sum_filter]; congr 1; ext a; simp only [Finset.mem_filter]; exact and_iff_right_of_imp (fun ha => hT ha)
  have hE : (∑ a ∈ S,‖v a‖^2) = ∑ a ∈ T,‖u a‖^2 := by
    calc
      _ = ∑ a ∈ S,if a∈T then ‖u a‖^2 else 0 := by
        apply Finset.sum_congr rfl
        intro a ha
        by_cases ht : a∈T <;> simp [v,ht]
      _ = _ := by rw [← Finset.sum_filter]; congr 1; ext a; simp only [Finset.mem_filter]; exact and_iff_right_of_imp (fun ha => hT ha)
  simpa only [he,hE] using h v
end SieveOperator

lemma cubic_power_bound_transposed {α ε : ℝ} {C : ℝ} (hC : 0≤C)
    (hbound : ∀ (M N : ℝ) (S : Finset Eisenstein) (u : Eisenstein → ℂ),
      1≤M → 1≤N → S ⊆ squarefreePrimaryBall N →
      ∑ m ∈ squarefreePrimaryBall M,cubicRowEnergy S u m ≤
        C*(M*N)^ε*(M+N^α+(M*N)^(2/3:ℝ))*∑ b ∈ S,‖u b‖^2)
    {M N : ℝ} (hM : 1≤M) (hN : 1≤N) (S : Finset Eisenstein)
    (hS : S ⊆ squarefreePrimaryBall N) (u : Eisenstein → ℂ) :
    ∑ m ∈ squarefreePrimaryBall M,cubicRowEnergy S u m ≤
      C*(M*N)^ε*(N+M^α+(M*N)^(2/3:ℝ))*∑ b ∈ S,‖u b‖^2 := by
  have hK : 0 ≤ C*(N*M)^ε*(N+M^α+(N*M)^(2/3:ℝ)) := by positivity
  have hb : SieveOperator.Bound (squarefreePrimaryBall N) (squarefreePrimaryBall M)
      (fun m b => cubicSymbol b m) (C*(N*M)^ε*(N+M^α+(N*M)^(2/3:ℝ))) := by
    intro v
    exact hbound N M _ v hN hM (Finset.Subset.refl _)
  have ht := (hb.transpose hK).restrict_coeff hS u
  have he (m : Eisenstein) (hm : m∈squarefreePrimaryBall M) :
      (∑ b ∈ S,u b*cubicSymbol m b) = ∑ b ∈ S,u b*cubicSymbol b m := by
    apply Finset.sum_congr rfl
    intro b hb
    rw [cubic_reciprocity (mem_squarefreePrimaryBall.mp hm).1 (mem_squarefreePrimaryBall.mp (hS hb)).1]
  have hsum : (∑ m ∈ squarefreePrimaryBall M,‖∑ b ∈ S,u b*cubicSymbol m b‖^2) =
      ∑ m ∈ squarefreePrimaryBall M,cubicRowEnergy S u m := by
    apply Finset.sum_congr rfl
    intro m hm
    rw [he m hm]
    rfl
  simpa only [hsum,mul_comm N M] using ht

 

theorem cubic_power_bound_two : CubicPowerBound 2 := by
  intro ε hε
  obtain ⟨C,hC,hthin⟩ := cubic_sieve_thin_initial (ε/2) (by positivity)
  obtain ⟨D,hD,hbins⟩ := cubic_thin_to_full (ε/2) (by positivity)
  let q : ℝ := 10/9
  refine ⟨D*C*q^(ε/2)*q^2,by dsimp [q]; positivity,?_⟩
  intro M N S u hM hN hS
  let K : ℝ → ℝ := fun X => C*X^(ε/2)*(M+X^2)
  have hK (X : ℝ) (hX : 1≤X) : 0≤K X := by dsimp [K]; positivity
  have hmono : MonotoneOn K (Set.Ici 1) := by
    intro X hX Y hY hXY
    change 1≤X at hX
    change 1≤Y at hY
    dsimp [K]
    gcongr
  have hb := hbins N S (squarefreePrimaryBall M) u K hN hS hK hmono (by
    intro X T hX hT hn
    exact hthin M X T u hM hX hT hn)
  change (∑ m ∈ squarefreePrimaryBall M,cubicRowEnergy S u m) ≤ _ at hb
  apply hb.trans
  have hq : 1 ≤ q := by norm_num [q]
  have hq0 : 0≤q := by linarith
  have hN0 : 0≤N := by linarith
  have hM0 : 0≤M := by linarith
  have hpow : N^(ε/2)*N^(ε/2) = N^ε := by
    rw [← Real.rpow_add (by linarith : 0<N)]
    congr 1
    ring
  have hmain : M+(q*N)^2 ≤ q^2*(M+N^2) := by
    have hq2 : 1≤q^2 := one_le_pow₀ hq
    nlinarith
  have hbase : N^ε ≤ (M*N)^ε := by
    exact Real.rpow_le_rpow hN0 (le_mul_of_one_le_left hN0 hM) hε.le
  have henv : M+N^2 ≤ M+N^(2:ℝ)+(M*N)^(2/3:ℝ) := by
    norm_num
    positivity
  have hb' : D*N^(ε/2)*K (q*N) ≤ (D*C*q^(ε/2)*q^2)*(M*N)^ε*(M+N^(2:ℝ)+(M*N)^(2/3:ℝ)) := by
    dsimp [K]
    rw [Real.mul_rpow hq0 hN0]
    calc
      _ = D*C*q^(ε/2)*(N^(ε/2)*N^(ε/2))*(M+(q*N)^2) := by ring
      _ = D*C*q^(ε/2)*N^ε*(M+(q*N)^2) := by rw [hpow]
      _ ≤ D*C*q^(ε/2)*N^ε*(q^2*(M+N^2)) := by gcongr
      _ = (D*C*q^(ε/2)*q^2)*N^ε*(M+N^2) := by ring
      _ ≤ _ := by gcongr
  exact mul_le_mul_of_nonneg_right hb' (Finset.sum_nonneg fun b _ => sq_nonneg _)



lemma squarefreePrimaryBall_eq_empty_of_lt_one {Y : ℝ} (hY : Y<1) :
    squarefreePrimaryBall Y = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro a ha
  obtain ⟨hp,hs,hn⟩ := mem_squarefreePrimaryBall.mp ha
  have h1 := one_le_norm (primary_ne_zero hp)
  linarith

lemma cube_envelope_sum_bound {X Y α δ : ℝ} (hX : 1≤X) (hY : 0≤Y)
    (hα : (2/3:ℝ)≤α) (hδ : 0<δ) :
    (∑ c ∈ nonzeroNormBall (X^(1/3:ℝ)),
      ∑ t ∈ squarefreePrimaryBall (X^(1/3:ℝ)/norm c),
        (Y+(X/((norm t)^2*(norm c)^3))^α+
          ((X/((norm t)^2*(norm c)^3))*Y)^(2/3:ℝ))) ≤
      (18*latticeZeta (1+δ)+(latticeZeta (4/3))^2)*X^δ*
        (X^α+Y*X^(1/3:ℝ)+(X*Y)^(2/3:ℝ)) := by
  let A := nonzeroNormBall (X^(1/3:ℝ))
  let T := fun c => squarefreePrimaryBall (X^(1/3:ℝ)/norm c)
  let L := fun c t => X/((norm t)^2*(norm c)^3)
  have hX0 : 0<X := by linarith
  have hL (c t : Eisenstein) : 0≤L c t := by
    have hc := norm_nonneg c
    dsimp [L]
    positivity
  have hZδ := latticeZeta_nonneg (1+δ)
  have hZ := latticeZeta_nonneg (4/3)
  have hXδ : 1≤X^δ := Real.one_le_rpow hX hδ.le
  let D : ℝ := 18*latticeZeta (1+δ)+(latticeZeta (4/3))^2
  have hD0 : 0≤D := by dsimp [D]; positivity
  have hD1 : 18*latticeZeta (1+δ) ≤ D := by dsimp [D]; nlinarith
  have hD2 : (latticeZeta (4/3))^2 ≤ D := by dsimp [D]; linarith
  have hconst : (∑ c ∈ A,∑ _t ∈ T c,Y) ≤ D*X^δ*(Y*X^(1/3:ℝ)) := by
    simp only [Finset.sum_const,nsmul_eq_mul]
    rw [← Finset.sum_mul]
    have hc := mul_le_mul_of_nonneg_right (cube_pair_count_bound hX hδ) hY
    apply hc.trans
    rw [Real.rpow_add hX0]
    calc
      _ = (18*latticeZeta (1+δ))*(X^δ*(Y*X^(1/3:ℝ))) := by ring
      _ ≤ _ := by
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hD1
          (show 0≤X^δ*(Y*X^(1/3:ℝ)) by positivity)
  have hpow : (∑ c ∈ A,∑ t ∈ T c,(L c t)^α) ≤ D*X^δ*X^α := by
    apply (cube_rpow_sum_bound hX0.le hα).trans
    have hcoeff : (latticeZeta (4/3))^2 ≤ D*X^δ :=
      hD2.trans (le_mul_of_one_le_right hD0 hXδ)
    simpa only [mul_comm _ (X^α)] using mul_le_mul_of_nonneg_right hcoeff (Real.rpow_nonneg hX0.le α)
  have hmix : (∑ c ∈ A,∑ t ∈ T c,((L c t)*Y)^(2/3:ℝ)) ≤ D*X^δ*(X*Y)^(2/3:ℝ) := by
    simp_rw [Real.mul_rpow (hL _ _) hY]
    simp_rw [← Finset.sum_mul]
    apply (mul_le_mul_of_nonneg_right (cube_rpow_sum_bound hX0.le (le_refl (2/3:ℝ)))
      (Real.rpow_nonneg hY _)).trans
    rw [Real.mul_rpow hX0.le hY]
    have hcoeff : (latticeZeta (4/3))^2 ≤ D*X^δ :=
      hD2.trans (le_mul_of_one_le_right hD0 hXδ)
    calc
      _ = (latticeZeta (4/3))^2*(X^(2/3:ℝ)*Y^(2/3:ℝ)) := by ring
      _ ≤ _ := by
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hcoeff
          (show 0≤X^(2/3:ℝ)*Y^(2/3:ℝ) by positivity)
  change (∑ c ∈ A,∑ t ∈ T c,(Y+(L c t)^α+((L c t)*Y)^(2/3:ℝ))) ≤ _
  simp only [Finset.sum_add_distrib]
  dsimp only [D] at hconst hpow hmix
  nlinarith

def CubicFullPowerBound (α : ℝ) : Prop :=
  ∀ ε : ℝ,0<ε → ∃ C : ℝ,0<C ∧ ∀ (X Y : ℝ) (S : Finset Eisenstein) (u : Eisenstein → ℂ),
    1≤X → 1≤Y → S ⊆ squarefreePrimaryBall Y →
    ∑ m ∈ nonzeroNormBall X,cubicRowEnergy S u m ≤
      C*(X*Y)^ε*(X^α+Y*X^(1/3:ℝ)+(X*Y)^(2/3:ℝ))*∑ b ∈ S,‖u b‖^2

 

theorem cubic_power_full_extension {α : ℝ} (hα : (2/3:ℝ)≤α)
    (hB : CubicPowerBound α) : CubicFullPowerBound α := by
  intro ε hε
  let δ : ℝ := ε/2
  have hδ : 0<δ := by dsimp [δ]; positivity
  obtain ⟨C,hC,hbound⟩ := hB δ hδ
  let D : ℝ := 18*latticeZeta (1+δ)+(latticeZeta (4/3))^2
  have hD : 0<D := by
    have hp := latticeZeta_pos (show 1<1+δ by linarith)
    have hz := sq_nonneg (latticeZeta (4/3))
    dsimp [D]
    linarith
  let W : ℝ := 2*((nonzeroNormBall 9).card:ℝ)
  have hW : 0≤W := by dsimp [W]; positivity
  refine ⟨(W+1)*C*D,by positivity,?_⟩
  intro X Y S u hX hY hS
  have hX0 : 0<X := by linarith
  have hY0 : 0<Y := by linarith
  have hXY : 0<X*Y := mul_pos hX0 hY0
  let K : ℝ → ℝ := fun L => if 1≤L then C*(L*Y)^δ*(Y+L^α+(L*Y)^(2/3:ℝ)) else 0
  have hK (L : ℝ) : 0≤K L := by
    dsimp [K]
    split_ifs with hL
    · positivity
    · rfl
  have hop (L : ℝ) (v : Eisenstein → ℂ) :
      ∑ s ∈ squarefreePrimaryBall L,cubicRowEnergy S v s ≤ K L*∑ b ∈ S,‖v b‖^2 := by
    dsimp [K]
    split_ifs with hL
    · exact cubic_power_bound_transposed hC.le hbound hL hY S hS v
    · rw [squarefreePrimaryBall_eq_empty_of_lt_one (lt_of_not_ge hL)]
      simp
  have hb := cubic_full_cube_bound hX S (fun b hb => (mem_squarefreePrimaryBall.mp (hS hb)).1)
    u K hK hop
  let A := nonzeroNormBall (X^(1/3:ℝ))
  let T := fun c => squarefreePrimaryBall (X^(1/3:ℝ)/norm c)
  let L := fun c t => X/((norm t)^2*(norm c)^3)
  have hcoeff : (∑ c ∈ A,∑ t ∈ T c,K (L c t)) ≤
      C*(X*Y)^δ*(D*X^δ*(X^α+Y*X^(1/3:ℝ)+(X*Y)^(2/3:ℝ))) := by
    calc
      _ ≤ ∑ c ∈ A,∑ t ∈ T c,C*(X*Y)^δ*(Y+(L c t)^α+((L c t)*Y)^(2/3:ℝ)) := by
        apply Finset.sum_le_sum
        intro c hc
        have hc0 := (mem_nonzeroNormBall.mp hc).2
        have hc1 := one_le_norm hc0
        apply Finset.sum_le_sum
        intro t ht
        have ht0 := primary_ne_zero (mem_squarefreePrimaryBall.mp ht).1
        have ht1 := one_le_norm ht0
        have hden : 1≤(norm t)^2*(norm c)^3 :=
          one_le_mul_of_one_le_of_one_le (one_le_pow₀ ht1) (one_le_pow₀ hc1)
        have hL0 : 0≤L c t := by dsimp [L]; positivity
        have hLX : L c t ≤ X := div_le_self hX0.le hden
        dsimp only [K]
        split_ifs with hL
        · gcongr
        · positivity
      _ = C*(X*Y)^δ*(∑ c ∈ A,∑ t ∈ T c,(Y+(L c t)^α+((L c t)*Y)^(2/3:ℝ))) := by
        simp only [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left (cube_envelope_sum_bound hX hY0.le hα hδ) (by positivity)
  have hεpow : (X*Y)^δ*X^δ ≤ (X*Y)^ε := by
    calc
      _ ≤ (X*Y)^δ*(X*Y)^δ := by
        gcongr
        exact le_mul_of_one_le_right hX0.le hY
      _ = _ := by
        rw [← Real.rpow_add hXY]
        congr 1
        dsimp [δ]
        ring
  apply hb.trans
  have hE : 0 ≤ ∑ b ∈ S,‖u b‖^2 := Finset.sum_nonneg fun b _ => sq_nonneg _
  apply mul_le_mul_of_nonneg_right _ hE
  change W*(∑ c ∈ A,∑ t ∈ T c,K (L c t)) ≤ _
  apply (mul_le_mul_of_nonneg_left hcoeff hW).trans
  calc
    _ = W*C*D*((X*Y)^δ*X^δ)*(X^α+Y*X^(1/3:ℝ)+(X*Y)^(2/3:ℝ)) := by ring
    _ ≤ _ := by gcongr; linarith

end CubicFirstMoment
end

end OAI
