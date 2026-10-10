import Mathlib
import OAI.NumberTheory.CubicGauss.PowerBounds
import OAI.NumberTheory.CubicGauss.ScalarBounds

namespace OAI

/-! Gaussian power factoring and the cubic-sieve exponent recurrence. -/

noncomputable section
open scoped BigOperators
open Module Complex UniqueFactorizationMonoid
attribute [local instance] Classical.propDecidable

namespace CubicFirstMoment

lemma cubic_conjugate_row_energy (S : Finset Eisenstein) (u : Eisenstein → ℂ) (m : Eisenstein) :
    ‖∑ a ∈ S,u a*star (cubicSymbol a m)‖^2 = cubicRowEnergy S (fun a => star (u a)) m := by
  change _ = ‖∑ a ∈ S,star (u a)*cubicSymbol a m‖^2
  have he : (∑ a ∈ S,u a*star (cubicSymbol a m)) =
      star (∑ a ∈ S,star (u a)*cubicSymbol a m) := by simp
  rw [he,norm_star]

lemma full_power_cutoff {α ε C X Y : ℝ} (hC : 0≤C) (hY : 1≤Y)
    (hbound : ∀ (X Y : ℝ) (S : Finset Eisenstein) (u : Eisenstein → ℂ),
      1≤X → 1≤Y → S ⊆ squarefreePrimaryBall Y →
      ∑ m ∈ nonzeroNormBall X,cubicRowEnergy S u m ≤
        C*(X*Y)^ε*(X^α+Y*X^(1/3:ℝ)+(X*Y)^(2/3:ℝ))*∑ b ∈ S,‖u b‖^2)
    (hX : 0<X) (S H : Finset Eisenstein) (hS : S ⊆ squarefreePrimaryBall Y) (u : Eisenstein → ℂ) :
    ∑ m ∈ (H.filter (· ≠ 0)).filter (fun m => norm m<X),cubicRowEnergy S u m ≤
      C*Y^ε*(X^(α+ε)+Y*X^((1/3:ℝ)+ε)+Y^(2/3:ℝ)*X^((2/3:ℝ)+ε))*∑ b ∈ S,‖u b‖^2 := by
  have hY0 : 0≤Y := by linarith
  by_cases hX1 : 1≤X
  · have hs : (H.filter (· ≠ 0)).filter (fun m => norm m<X) ⊆ nonzeroNormBall X := by
      intro m hm
      obtain ⟨hm,hxm⟩ := Finset.mem_filter.mp hm
      exact mem_nonzeroNormBall.mpr ⟨hxm.le,(Finset.mem_filter.mp hm).2⟩
    apply (Finset.sum_le_sum_of_subset_of_nonneg hs (fun m _ _ => sq_nonneg _)).trans
    apply (hbound X Y S u hX1 hY hS).trans_eq
    rw [Real.mul_rpow hX.le hY0,Real.mul_rpow hX.le hY0]
    simp only [Real.rpow_add hX]
    ring
  · have he : ((H.filter (· ≠ 0)).filter (fun m => norm m<X)) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro m hm
      obtain ⟨hm,hn⟩ := Finset.mem_filter.mp hm
      have h1 := one_le_norm (Finset.mem_filter.mp hm).2
      linarith
    rw [he,Finset.sum_empty]
    positivity

 

theorem cubic_full_power_gaussian {α : ℝ} (hα : 1≤α)
    (hB : CubicFullPowerBound α) (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ CubicGaussianBound (fun Y r =>
      1+C*Y^ε*((2/r)^(α+ε)+Y*(2/r)^((1/3:ℝ)+ε)+Y^(2/3:ℝ)*(2/r)^((2/3:ℝ)+ε))) := by
  obtain ⟨C,hC,hbound⟩ := hB ε hε
  let G : ℝ := Real.Gamma (α+ε+1)+Real.Gamma ((1/3:ℝ)+ε+1)+Real.Gamma ((2/3:ℝ)+ε+1)
  have hg1 : 0<Real.Gamma (α+ε+1) := Real.Gamma_pos_of_pos (by linarith)
  have hg2 : 0<Real.Gamma ((1/3:ℝ)+ε+1) := Real.Gamma_pos_of_pos (by linarith)
  have hg3 : 0<Real.Gamma ((2/3:ℝ)+ε+1) := Real.Gamma_pos_of_pos (by linarith)
  have hG : 0<G := by dsimp [G]; positivity
  refine ⟨C*G,mul_pos hC hG,?_⟩
  intro Y r hY hr
  have hY0 : 0<Y := by linarith
  refine ⟨by positivity,?_⟩
  intro S hS H u
  let E : ℝ := ∑ a ∈ S,‖u a‖^2
  have hE : 0≤E := Finset.sum_nonneg fun a _ => sq_nonneg _
  have hEs : (∑ a ∈ S,‖star (u a)‖^2) = E := by simp [E]
  let X : ℝ := 2/r
  have hX : 0<X := by dsimp [X]; positivity
  let H0 := H.filter (· ≠ 0)
  have hb := SieveKernel.finite_laplace_three_bound H0 norm
    (fun m => cubicRowEnergy S (fun a => star (u a)) m)
    (X := X) (a := C*Y^ε*E) (b := C*Y^ε*Y*E) (c := C*Y^ε*Y^(2/3:ℝ)*E)
    (p := α+ε) (q := (1/3:ℝ)+ε) (s := (2/3:ℝ)+ε)
    hX (by linarith) (by linarith) (by linarith) (fun m _ => norm_nonneg m) (by
      intro T hT
      have hb := full_power_cutoff hC.le hY hbound hT S H hS (fun a => star (u a))
      rw [hEs] at hb
      apply hb.trans_eq
      ring)
  have hn : (∑ m ∈ H0,Real.exp (-r*norm m/2)*‖∑ a ∈ S,u a*star (cubicSymbol a m)‖^2) ≤
      (C*G)*Y^ε*(X^(α+ε)+Y*X^((1/3:ℝ)+ε)+Y^(2/3:ℝ)*X^((2/3:ℝ)+ε))*E := by
    have he (m : Eisenstein) : -norm m/X = -r*norm m/2 := by dsimp [X]; field_simp
    simp_rw [he] at hb
    simp_rw [cubic_conjugate_row_energy]
    apply hb.trans
    have h1 : Real.Gamma (α+ε+1) ≤ G := by dsimp [G]; linarith
    have h2 : Real.Gamma ((1/3:ℝ)+ε+1) ≤ G := by dsimp [G]; linarith
    have h3 : Real.Gamma ((2/3:ℝ)+ε+1) ≤ G := by dsimp [G]; linarith
    calc
      _ ≤ (C*Y^ε*E)*X^(α+ε)*G+(C*Y^ε*Y*E)*X^((1/3:ℝ)+ε)*G+
          (C*Y^ε*Y^(2/3:ℝ)*E)*X^((2/3:ℝ)+ε)*G := by gcongr
      _ = _ := by ring
  have hsub : H ⊆ insert 0 H0 := by
    intro m hm
    by_cases h0 : m=0
    · simp [h0]
    · exact Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨hm,h0⟩)
  have hz := cubic_zero_row_bound S (fun a ha => (mem_squarefreePrimaryBall.mp (hS ha)).1) u
  have hb' := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (f := fun m => Real.exp (-r*norm m/2)*‖∑ a ∈ S,u a*star (cubicSymbol a m)‖^2)
    (fun m _ _ => by positivity)
  rw [Finset.sum_insert (show (0:Eisenstein)∉H0 by simp [H0])] at hb'
  have hn0 : norm (0:Eisenstein)=0 := by simp [norm]
  simp only [hn0,mul_zero,zero_div,Real.exp_zero,one_mul] at hb'
  apply hb'.trans
  calc
    _ ≤ E+(C*G)*Y^ε*(X^(α+ε)+Y*X^((1/3:ℝ)+ε)+Y^(2/3:ℝ)*X^((2/3:ℝ)+ε))*E := add_le_add hz hn
    _ = _ := by dsimp only [E,X]; ring


open SieveScalar

def recurrenceEnvelope (M N α : ℝ) : ℝ :=
  M+M^(1-α)*N^(2*α-1)+(M*N)^(2/3:ℝ)+M^(1/3:ℝ)*N

lemma recurrenceEnvelope_nonneg {M N α : ℝ} (hM : 0≤M) (hN : 0≤N) :
    0≤recurrenceEnvelope M N α := by unfold recurrenceEnvelope; positivity

lemma gaussian_power_factor_abstract {M N k d α ε C P X : ℝ}
    (hM : 1≤M) (hN : 1≤N) (hk : 1≤k) (hkN : k≤N) (hd : 1≤d) (hdk : d≤k)
    (hα : 1≤α) (hε : 0≤ε) (hC : 0≤C) (hP : 0≤P) (hX : 0<X)
    (hPb : P≤16*(M/(d*(N/k)))) (hXb : X≤d*(N/k)^2/M) :
    P*(1+C*(N/k)^ε*(X^(α+ε)+(N/k)*X^((1/3:ℝ)+ε)+(N/k)^(2/3:ℝ)*X^((2/3:ℝ)+ε))) ≤
      16*(1+C)*N^(3*ε)*recurrenceEnvelope M N α := by
  have hM0 : 0<M := by linarith
  have hN0 : 0<N := by linarith
  have hk0 : 0<k := by linarith
  have hd0 : 0<d := by linarith
  have hy : 0<N/k := div_pos hN0 hk0
  have hy1 : 1≤N/k := (one_le_div hk0).mpr hkN
  have hP0 : P≤16*M := by
    apply hPb.trans
    gcongr
    exact div_le_self hM0.le (one_le_mul_of_one_le_of_one_le hd hy1)
  have heps : (N/k)^ε*X^ε ≤ N^(3*ε) := by
    apply (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hX.le hXb hε) (by positivity)).trans
    exact scale_epsilon hM hN hk hkN hd hdk hε
  have hA : P*X^α ≤ 16*(M^(1-α)*N^(2*α-1)) := by
    calc
      _ ≤ (16*(M/(d*(N/k))))*(d*(N/k)^2/M)^α := by gcongr
      _ = 16*((M/(d*(N/k)))*(d*(N/k)^2/M)^α) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (main_power hM hN hk hkN hd hdk hα) (by norm_num)
  have hB : P*(N/k)*X^(1/3:ℝ) ≤ 16*(M*N)^(2/3:ℝ) := by
    calc
      _ ≤ (16*(M/(d*(N/k))))*(N/k)*(d*(N/k)^2/M)^(1/3:ℝ) := by gcongr
      _ = 16*((M/(d*(N/k)))*(N/k)*(d*(N/k)^2/M)^(1/3:ℝ)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (mixed_one hM hN hk hd) (by norm_num)
  have hD : P*(N/k)^(2/3:ℝ)*X^(2/3:ℝ) ≤ 16*(M^(1/3:ℝ)*N) := by
    calc
      _ ≤ (16*(M/(d*(N/k))))*(N/k)^(2/3:ℝ)*(d*(N/k)^2/M)^(2/3:ℝ) := by gcongr
      _ = 16*((M/(d*(N/k)))*(N/k)^(2/3:ℝ)*(d*(N/k)^2/M)^(2/3:ℝ)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (mixed_two hM hN hk hd) (by norm_num)
  have hone : 1≤N^(3*ε) := Real.one_le_rpow hN (by positivity)
  rw [Real.rpow_add hX,Real.rpow_add hX,Real.rpow_add hX]
  calc
    _ = P+C*((N/k)^ε*X^ε)*(P*X^α+P*(N/k)*X^(1/3:ℝ)+P*(N/k)^(2/3:ℝ)*X^(2/3:ℝ)) := by ring
    _ ≤ 16*M+C*N^(3*ε)*(16*(M^(1-α)*N^(2*α-1))+16*(M*N)^(2/3:ℝ)+16*(M^(1/3:ℝ)*N)) := by gcongr
    _ ≤ _ := by
      have henv : M^(1-α)*N^(2*α-1)+(M*N)^(2/3:ℝ)+M^(1/3:ℝ)*N ≤ recurrenceEnvelope M N α := by
        unfold recurrenceEnvelope
        linarith
      have hMenv : M ≤ recurrenceEnvelope M N α := by
        have hh : 0≤M^(1-α)*N^(2*α-1)+(M*N)^(2/3:ℝ)+M^(1/3:ℝ)*N := by positivity
        unfold recurrenceEnvelope
        linarith
      have h1 := mul_le_mul_of_nonneg_left hMenv (by norm_num : (0:ℝ)≤16)
      have h2 := mul_le_mul_of_nonneg_left (le_mul_of_one_le_right
        (recurrenceEnvelope_nonneg hM0.le hN0.le (α := α)) hone) (by norm_num : (0:ℝ)≤16)
      have h3 := mul_le_mul_of_nonneg_left henv (show 0≤16*C*N^(3*ε) by positivity)
      nlinarith

lemma gaussian_power_factor {M N k d α ε C : ℝ}
    (hM : 1≤M) (hN : 1≤N) (hk : 1≤k) (hkN : k≤N) (hd : 1≤d) (hdk : d≤k)
    (hα : 1≤α) (hε : 0≤ε) (hC : 0≤C) :
    (2/(Real.sqrt 3*(1/M)*d)) *
      (7*(1+C*(N/k)^ε*((2/(4*Real.pi/(3*((1/M)*d)*((9/10:ℝ)*N/k)^2)))^(α+ε)+
        (N/k)*(2/(4*Real.pi/(3*((1/M)*d)*((9/10:ℝ)*N/k)^2)))^((1/3:ℝ)+ε)+
        (N/k)^(2/3:ℝ)*(2/(4*Real.pi/(3*((1/M)*d)*((9/10:ℝ)*N/k)^2)))^((2/3:ℝ)+ε)))/((9/10:ℝ)*N/k)) ≤
      16*(1+C)*N^(3*ε)*recurrenceEnvelope M N α := by
  have hM0 : 0<M := by linarith
  have hN0 : 0<N := by linarith
  have hk0 : 0<k := by linarith
  have hd0 : 0<d := by linarith
  have hs : 0<Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have hs1 : 1≤Real.sqrt 3 := by nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ)≤3)]
  have hp : 0<Real.pi := Real.pi_pos
  let P : ℝ := (2/(Real.sqrt 3*(1/M)*d))*(7/((9/10:ℝ)*N/k))
  let X : ℝ := 2/(4*Real.pi/(3*((1/M)*d)*((9/10:ℝ)*N/k)^2))
  have hP : 0≤P := by dsimp [P]; positivity
  have hX : 0<X := by dsimp [X]; positivity
  have hPb : P≤16*(M/(d*(N/k))) := by
    have he : P = ((140/9:ℝ)/Real.sqrt 3)*(M/(d*(N/k))) := by dsimp [P]; field_simp; ring
    rw [he]
    gcongr
    apply (div_le_iff₀ hs).mpr
    nlinarith
  have hXb : X≤d*(N/k)^2/M := by
    have he : X = ((243/200:ℝ)/Real.pi)*(d*(N/k)^2/M) := by dsimp [X]; field_simp; ring
    rw [he]
    exact mul_le_of_le_one_left (by positivity) ((div_le_one hp).mpr (by linarith [Real.pi_gt_three]))
  have hb := gaussian_power_factor_abstract hM hN hk hkN hd hdk hα hε hC hP hX hPb hXb
  apply le_trans _ hb
  dsimp only [P,X]
  ring_nf
  rfl

end CubicFirstMoment

namespace CubicFirstMoment

 
theorem cubic_recurrence_thin {α : ℝ} (hα : 1≤α) (hB : CubicPowerBound α)
    (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ (M N : ℝ) (S : Finset Eisenstein) (u : Eisenstein → ℂ),
      1≤M → 1≤N → S ⊆ squarefreePrimaryBall N →
      (∀ b ∈ S,(9/10:ℝ)*N ≤ norm b) →
      ∑ m ∈ squarefreePrimaryBall M,cubicRowEnergy S u m ≤
        C*N^ε*recurrenceEnvelope M N α*∑ b ∈ S,‖u b‖^2 := by
  let δ : ℝ := ε/4
  have hδ : 0<δ := by dsimp [δ]; positivity
  obtain ⟨C,hC,hK⟩ := cubic_full_power_gaussian hα
    (cubic_power_full_extension (by linarith) hB) δ hδ
  obtain ⟨D,hD,hDsum⟩ := sieve_divisor_power_bound δ hδ
  refine ⟨Real.exp Real.pi*16*(1+C)*D,by positivity,?_⟩
  intro M N S u hM hN hS hthin
  have hM0 : 0<M := by linarith
  have hN0 : 0<N := by linarith
  have ht : 0<1/M := by positivity
  have hs : ∀ a ∈ S,primary a := fun a ha => (mem_squarefreePrimaryBall.mp (hS ha)).1
  let K : ℝ → ℝ → ℝ := fun Y r =>
    1+C*Y^δ*((2/r)^(α+δ)+Y*(2/r)^((1/3:ℝ)+δ)+Y^(2/3:ℝ)*(2/r)^((2/3:ℝ)+δ))
  have hb := cubic_gaussian_positive_bound hN0 S hS hthin u (1/M) ht K hK
  apply (cubic_cutoff_le_gaussian hM0 S hs u).trans
  apply (mul_le_mul_of_nonneg_left hb (Real.exp_pos _).le).trans
  have hh : (∑ k ∈ squarefreePrimaryBall N,∑ d ∈ primaryDivisors k,
      (2/(Real.sqrt 3*(1/M)*norm d)) *
        (7*K (N/norm k) (4*Real.pi/(3*((1/M)*norm d)*((9/10:ℝ)*N/norm k)^2))/((9/10:ℝ)*N/norm k)) *
        ∑ l ∈ squarefreePrimaryBall (N/norm k),
          ∑ a ∈ (sieveFiber N S k).filter (l ∣ ·),‖u (k*a)‖^2) ≤
      (16*(1+C)*N^(3*δ)*recurrenceEnvelope M N α)*(D*N^δ*∑ b ∈ S,‖u b‖^2) := by
    calc
      _ ≤ ∑ k ∈ squarefreePrimaryBall N,∑ _d ∈ primaryDivisors k,
          (16*(1+C)*N^(3*δ)*recurrenceEnvelope M N α)*
          ∑ l ∈ squarefreePrimaryBall (N/norm k),
            ∑ a ∈ (sieveFiber N S k).filter (l ∣ ·),‖u (k*a)‖^2 := by
        apply Finset.sum_le_sum
        intro k hk
        obtain ⟨hkp,hks,hkn⟩ := mem_squarefreePrimaryBall.mp hk
        apply Finset.sum_le_sum
        intro d hd
        obtain ⟨hdp,hdk⟩ := (mem_primaryDivisors (primary_ne_zero hkp)).mp hd
        apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun l _ => Finset.sum_nonneg fun a _ => sq_nonneg _)
        exact gaussian_power_factor hM hN (one_le_norm (primary_ne_zero hkp)) hkn
          (one_le_norm (primary_ne_zero hdp)) (norm_le_of_dvd (primary_ne_zero hkp) hdk) hα hδ.le hC.le
      _ = (16*(1+C)*N^(3*δ)*recurrenceEnvelope M N α)*
          (∑ k ∈ squarefreePrimaryBall N,∑ _d ∈ primaryDivisors k,
            ∑ l ∈ squarefreePrimaryBall (N/norm k),
              ∑ a ∈ (sieveFiber N S k).filter (l ∣ ·),‖u (k*a)‖^2) := by
        simp only [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left (hDsum N S u hN hS) (by
        have := recurrenceEnvelope_nonneg hM0.le hN0.le (α := α)
        positivity)
  apply (mul_le_mul_of_nonneg_left hh (Real.exp_pos _).le).trans_eq
  have hp : N^(3*δ)*N^δ=N^ε := by
    rw [← Real.rpow_add hN0]
    congr 1
    dsimp [δ]
    ring
  calc
    _ = (Real.exp Real.pi*16*(1+C)*D)*(N^(3*δ)*N^δ)*recurrenceEnvelope M N α*∑ b ∈ S,‖u b‖^2 := by ring
    _ = _ := by rw [hp]

lemma recurrenceEnvelope_mono {M α : ℝ} (hM : 0≤M) (hα : 1≤α) :
    MonotoneOn (fun N => recurrenceEnvelope M N α) (Set.Ici 1) := by
  intro X hX Y hY hXY
  change 1≤X at hX
  change 1≤Y at hY
  dsimp only [recurrenceEnvelope]
  gcongr
  linarith

lemma recurrenceEnvelope_scale {M N α q : ℝ} (hM : 0≤M) (hN : 0≤N)
    (hα : 1≤α) (hq : 1≤q) :
    recurrenceEnvelope M (q*N) α ≤ q^(2*α)*recurrenceEnvelope M N α := by
  have hq0 : 0<q := by linarith
  have hq1 : 1≤q^(2*α) := Real.one_le_rpow hq (by linarith)
  have hq2 : q^(2*α-1)≤q^(2*α) := Real.rpow_le_rpow_of_exponent_le hq (by linarith)
  have hq3 : q^(2/3:ℝ)≤q^(2*α) := Real.rpow_le_rpow_of_exponent_le hq (by linarith)
  have hq4 : q≤q^(2*α) := by
    simpa using Real.rpow_le_rpow_of_exponent_le hq (show (1:ℝ)≤2*α by linarith)
  unfold recurrenceEnvelope
  rw [Real.mul_rpow hq0.le hN,show M*(q*N)=q*(M*N) by ring,Real.mul_rpow hq0.le (by positivity)]
  have h1 := mul_le_mul_of_nonneg_right hq1 hM
  have h2 := mul_le_mul_of_nonneg_right hq2 (show 0≤M^(1-α)*N^(2*α-1) by positivity)
  have h3 := mul_le_mul_of_nonneg_right hq3 (show 0≤(M*N)^(2/3:ℝ) by positivity)
  have h4 := mul_le_mul_of_nonneg_right hq4 (show 0≤M^(1/3:ℝ)*N by positivity)
  nlinarith

 
theorem cubic_recurrence {α : ℝ} (hα : 1≤α) (hB : CubicPowerBound α)
    (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ (M N : ℝ) (S : Finset Eisenstein) (u : Eisenstein → ℂ),
      1≤M → 1≤N → S ⊆ squarefreePrimaryBall N →
      ∑ m ∈ squarefreePrimaryBall M,cubicRowEnergy S u m ≤
        C*N^ε*recurrenceEnvelope M N α*∑ b ∈ S,‖u b‖^2 := by
  obtain ⟨C,hC,hthin⟩ := cubic_recurrence_thin hα hB (ε/2) (by positivity)
  obtain ⟨D,hD,hbins⟩ := cubic_thin_to_full (ε/2) (by positivity)
  let q : ℝ := 10/9
  have hq : 1≤q := by norm_num [q]
  refine ⟨D*C*q^(ε/2)*q^(2*α),by dsimp [q]; positivity,?_⟩
  intro M N S u hM hN hS
  have hM0 : 0≤M := by linarith
  have hN0 : 0<N := by linarith
  let K : ℝ → ℝ := fun X => C*X^(ε/2)*recurrenceEnvelope M X α
  have hK (X : ℝ) (hX : 1≤X) : 0≤K X := by
    have := recurrenceEnvelope_nonneg hM0 (show 0≤X by linarith) (α := α)
    dsimp [K]
    positivity
  have hmono : MonotoneOn K (Set.Ici 1) := by
    intro X hX Y hY hXY
    have hXE : 0≤recurrenceEnvelope M X α := recurrenceEnvelope_nonneg hM0 (by change 1≤X at hX; linarith)
    have he := recurrenceEnvelope_mono hM0 hα hX hY hXY
    change 1≤X at hX
    change 1≤Y at hY
    dsimp [K]
    gcongr
  have hb := hbins N S (squarefreePrimaryBall M) u K hN hS hK hmono (by
    intro X T hX hT hn
    exact hthin M X T u hM hX hT hn)
  change (∑ m ∈ squarefreePrimaryBall M,cubicRowEnergy S u m) ≤ _ at hb
  apply hb.trans
  apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun b _ => sq_nonneg _)
  dsimp only [K]
  rw [Real.mul_rpow (by linarith : 0≤q) hN0.le]
  calc
    _ = D*C*q^(ε/2)*(N^(ε/2)*N^(ε/2))*recurrenceEnvelope M (q*N) α := by ring
    _ ≤ D*C*q^(ε/2)*(N^(ε/2)*N^(ε/2))*(q^(2*α)*recurrenceEnvelope M N α) := by
      apply mul_le_mul_of_nonneg_left (recurrenceEnvelope_scale hM0 hN0.le hα hq)
      positivity
    _ = _ := by
      rw [← Real.rpow_add hN0,show ε/2+ε/2=ε by ring]
      ring



def sieveStep (α : ℝ) : ℝ := (6*α-4)/(3*α-1)
def sieveThreshold (α : ℝ) : ℝ := (6*α-5)/(3*α-1)

lemma sieveStep_algebra {α : ℝ} (hα : (4/3:ℝ)≤α) :
    1≤ sieveThreshold α ∧ sieveThreshold α≤ sieveStep α ∧
    (sieveThreshold α+1)*(2/3:ℝ)=sieveStep α ∧
    sieveThreshold α*(α-(1/3:ℝ))=2*α-(5/3:ℝ) ∧
    (4/3:ℝ)≤ sieveStep α ∧ sieveStep α-(4/3:ℝ)≤(2/3:ℝ)*(α-(4/3:ℝ)) := by
  have hd : 0<3*α-1 := by linarith
  unfold sieveThreshold sieveStep
  refine ⟨(le_div_iff₀ hd).mpr (by linarith),?_,?_,?_,?_,?_⟩
  · exact div_le_div_of_nonneg_right (by linarith) hd.le
  · field_simp [ne_of_gt hd, show α*3-1 ≠ 0 by linarith]
    ring
  · field_simp [ne_of_gt hd, show α*3-1 ≠ 0 by linarith]
    ring
  · apply (le_div_iff₀ hd).mpr
    linarith
  · apply (sub_le_iff_le_add).mpr
    apply (div_le_iff₀ hd).mpr
    nlinarith [sq_nonneg (α-(4/3:ℝ))]

lemma sieve_recurrence_cross {M N α : ℝ} (hM : 1≤ M) (hN : 1≤ N) (hα : (4/3:ℝ)≤α)
    (hMN : N^(sieveThreshold α)≤ M) :
    M^(1-α)*N^(2*α-1) ≤ (M*N)^(2/3:ℝ) := by
  have hM0 : 0<M := by linarith
  have hN0 : 0<N := by linarith
  have hpow : (N^(sieveThreshold α)/M)^(α-(1/3:ℝ)) ≤ 1 := by
    have hb : N^(sieveThreshold α)/M ≤ 1 := (div_le_one hM0).mpr hMN
    have hh := Real.rpow_le_rpow (by positivity : 0≤ N^(sieveThreshold α)/M) hb (show 0≤α-(1/3:ℝ) by linarith)
    simpa using hh
  have he : (M*N)^(2/3:ℝ)*(N^(sieveThreshold α)/M)^(α-(1/3:ℝ)) = M^(1-α)*N^(2*α-1) := by
    rw [Real.mul_rpow hM0.le hN0.le,
      Real.div_rpow (by positivity) hM0.le,← Real.rpow_mul hN0.le]
    calc
      _ = (M^(2/3:ℝ)/M^(α-(1/3:ℝ)))*(N^(2/3:ℝ)*N^(sieveThreshold α*(α-(1/3:ℝ)))) := by ring
      _ = M^((2/3:ℝ)-(α-(1/3:ℝ)))*N^((2/3:ℝ)+sieveThreshold α*(α-(1/3:ℝ))) := by
        rw [Real.rpow_sub hM0 (2/3) (α-(1/3:ℝ)),Real.rpow_add hN0]
      _ = _ := by
        rw [(sieveStep_algebra hα).2.2.2.1]
        congr 1 <;> congr 1 <;> ring
  rw [←he]
  exact mul_le_of_le_one_right (by positivity) hpow

lemma sieve_recurrence_last {M N : ℝ} (hM : 1≤ M) (hN : 1≤ N) (hNM : N≤ M) :
    M^(1/3:ℝ)*N ≤ (M*N)^(2/3:ℝ) := by
  have hM0 : 0<M := by linarith
  have hN0 : 0<N := by linarith
  have hn : N = N^(1/3:ℝ)*N^(2/3:ℝ) := by
    rw [← Real.rpow_add hN0]
    norm_num
  calc
    _ = M^(1/3:ℝ)*(N^(1/3:ℝ)*N^(2/3:ℝ)) := by rw [←hn]
    _ ≤ M^(1/3:ℝ)*(M^(1/3:ℝ)*N^(2/3:ℝ)) := by gcongr
    _ = _ := by rw [←mul_assoc,←Real.rpow_add hM0,Real.mul_rpow hM0.le hN0.le]; norm_num

lemma sieve_threshold_ge {N α : ℝ} (hN : 1≤ N) (hα : (4/3:ℝ)≤α) :
    N≤ N^(sieveThreshold α) := by
  have hh := Real.rpow_le_rpow_of_exponent_le hN (sieveStep_algebra hα).1
  simpa using hh

lemma recurrenceEnvelope_large {M N α : ℝ} (hM : 1≤ M) (hN : 1≤ N) (hα : (4/3:ℝ)≤α)
    (hMN : N^(sieveThreshold α)≤ M) :
    recurrenceEnvelope M N α ≤ M+3*(M*N)^(2/3:ℝ) := by
  have hA := sieve_recurrence_cross hM hN hα hMN
  have hB := sieve_recurrence_last hM hN ((sieve_threshold_ge hN hα).trans hMN)
  unfold recurrenceEnvelope
  linarith

lemma recurrenceEnvelope_threshold {N α : ℝ} (hN : 1≤ N) (hα : (4/3:ℝ)≤α) :
    recurrenceEnvelope (N^(sieveThreshold α)) N α ≤ 4*N^(sieveStep α) := by
  have hN0 : 0<N := by linarith
  have hM : 1≤ N^(sieveThreshold α) := hN.trans (sieve_threshold_ge hN hα)
  apply (recurrenceEnvelope_large hM hN hα le_rfl).trans
  have hmixed : (N^(sieveThreshold α)*N)^(2/3:ℝ) = N^(sieveStep α) := by
    calc
      _ = (N^(sieveThreshold α)*N^(1:ℝ))^(2/3:ℝ) := by rw [Real.rpow_one]
      _ = _ := by rw [←Real.rpow_add hN0,←Real.rpow_mul hN0.le,(sieveStep_algebra hα).2.2.1]
  rw [hmixed]
  have hh := Real.rpow_le_rpow_of_exponent_le hN (sieveStep_algebra hα).2.1
  linarith

end CubicFirstMoment
end

end OAI
