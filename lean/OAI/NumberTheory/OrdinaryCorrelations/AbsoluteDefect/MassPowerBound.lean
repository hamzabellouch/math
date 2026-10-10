import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.GridMinLower
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.TwoPowerRatioLimit
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.CompressEnergy

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory intervalIntegral
open Finset
open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open Filter
open MeasureTheory Filter
open MeasureTheory
open MeasureTheory Set
open Set MeasureTheory Complex
open Set
open Finset Filter

namespace OrdinarySparseTerminal
open Filter Finset OrdinarySmoothRough OrdinarySelbergWeights OrdinaryCorrelations
  OrdinarySparsePowerScales OrdinarySparseNumerics

lemma mass_power_bound (d n : ℕ) :
    (d:ℝ)*n*Real.log 2/2  ≤ 
      actualMass (∏ p∈Nat.primesLE (2^(d*n)),p) (2^(d*n))
        (prime_product_squarefree _ (fun _prime hp => (Nat.mem_primesLE.mp hp).2)) := by
  have h := actualMass_log_bound (z := 2^(d*n))
    (prime_product_squarefree _ (fun p hp => (Nat.mem_primesLE.mp hp).2))
    (fun p hp hz => dvd_prod_of_mem (f := id) (Nat.mem_primesLE.mpr ⟨hz,hp⟩))
  have hl : (d:ℝ)*n*Real.log 2  ≤  Real.log ((2^(d*n)+1:ℕ):ℝ) := by
    calc
      _ = Real.log ((2^(d*n):ℕ):ℝ) := by push_cast; rw [Real.log_pow]; push_cast; ring
      _  ≤  _ := Real.log_le_log (by positivity) (by exact_mod_cast Nat.le_succ (2^(d*n)))
  linarith

lemma remainder_normalize (H G x U z R q L V e : ℝ) (hH : H ≠ 0) :
    ((4*H)*G⁻¹*(1+L)+x*z^4+(4*H)*(2*Real.log 4*e)/V+
      (6*H*G⁻¹*R/q+(8*G⁻¹+4*z^4)*U))/(4*H) =
      G⁻¹*(1+L)+(2*Real.log 4*e)/V+(3/2)*G⁻¹*R/q+
      (x*z^4+(8*G⁻¹+4*z^4)*U)/(4*H) := by
  field_simp
  ring

lemma remainder_at_power (d s q k n : ℕ) (hd : 0 < d) (hs : 1 ≤ s) (hq : 0 < q)
    (hn : 0 < n) (hsmall : 1+Real.log q  ≤  n*Real.log 2)
    (G : ℝ) (hG : (d:ℝ)*n*Real.log 2/2  ≤  G) :
    ((4*2^(8*k*n):ℕ)*(G:ℝ)⁻¹*(1+Real.log (q*2^n:ℕ))+
       (q*2^n:ℕ)*(2^(d*n):ℕ)^4+
       (4*2^(8*k*n):ℕ)*(2*Real.log 4*(d*n:ℕ))/Real.log (q*2^(s*n):ℕ)+
       (6*((2^(8*k*n):ℕ):ℝ)*G⁻¹*((s-1)*n:ℕ)/q+
         (8*G⁻¹+4*((2^(d*n):ℕ):ℝ)^4)*(q*2^(s*n):ℕ))) /
           (4*((2^(8*k*n):ℕ):ℝ))  ≤ 
      4/(d:ℝ)+4*(d:ℝ)/s+6*(s:ℝ)/((q:ℝ)*d)+
        10*(q:ℝ)*(2:ℝ)^((s+4*d)*n)/(2:ℝ)^(8*k*n) := by
  have hd' : (0:ℝ)<d := by exact_mod_cast hd
  have hs' : (0:ℝ)<s := by exact_mod_cast hs
  have hq' : (0:ℝ)<q := by exact_mod_cast hq
  have hn' : (0:ℝ)<n := by exact_mod_cast hn
  have hln : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hGp : 0 < G := lt_of_lt_of_le (by positivity) hG
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hd1 : (1:ℝ) ≤ d := by exact_mod_cast hd
  have hG4 : (1/4:ℝ) ≤ G := by
    have hh := mul_le_mul_of_nonneg_left log_two_lower (by positivity : 0 ≤ (d:ℝ)*n/2)
    nlinarith [mul_le_mul hd1 hn1 (by norm_num : (0:ℝ) ≤ 1) hd'.le]
  have hi4 : G⁻¹ ≤ 4 := by simpa using inv_anti₀ (by norm_num : (0:ℝ)<1/4) hG4
  have hlog (r : ℕ) : Real.log (q*2^r:ℕ) = Real.log q+(r:ℝ)*Real.log 2 := by
    push_cast
    rw [Real.log_mul (ne_of_gt hq') (by positivity),Real.log_pow]
  have hR : (((s-1)*n:ℕ):ℝ) ≤ (s:ℝ)*n := by exact_mod_cast Nat.mul_le_mul_right n (Nat.sub_le s 1)
  have hm := middle_density G d s q n
    (G⁻¹*(1+Real.log q+(n:ℝ)*Real.log 2))
    (2*Real.log 4*((d:ℝ)*n)/(Real.log q+(s:ℝ)*n*Real.log 2))
    ((3/2)*G⁻¹*((s-1)*n:ℕ)/q) hd' hs' hq' hn' hG hsmall
    (le_of_eq (by ring)) (le_of_eq (by ring))
    (Real.log_nonneg (by exact_mod_cast hq : (1:ℝ) ≤ q))
    (by gcongr)
  have hf := floor_error_bound q d s k n hs
  have hfloor :
      (((q*2^n:ℕ):ℝ)*((2^(d*n):ℕ):ℝ)^4+
        (8*G⁻¹+4*((2^(d*n):ℕ):ℝ)^4)*((q*2^(s*n):ℕ):ℝ))/(4*((2^(8*k*n):ℕ):ℝ))  ≤ 
      10*(q:ℝ)*(2:ℝ)^((s+4*d)*n)/(2:ℝ)^(8*k*n) := by
    apply le_trans _ hf
    gcongr
    linarith
  have he := remainder_normalize ((2^(8*k*n):ℕ):ℝ) G (q*2^n:ℕ) (q*2^(s*n):ℕ)
    (2^(d*n):ℕ) ((s-1)*n:ℕ) q (Real.log (q*2^n:ℕ)) (Real.log (q*2^(s*n):ℕ))
    (d*n:ℕ) (by positivity)
  push_cast at he ⊢
  rw [he]
  push_cast at hlog hfloor hm
  rw [hlog n,hlog (s*n)]
  push_cast
  nlinarith only [hm,hfloor]

theorem terminal_raw_bound {f : ℕ → ℂ} (hf : OneBounded f)
    (hm : Multiplicative f) (hNP : UniformlyNonpretentious f)
    (d s q k : ℕ) (hs : 1 ≤ s) (hq : 0 < q) (hk : s+4*d+4 ≤ k)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ (P : Finset ℕ), P ⊆ Nat.primesLE (2^(d*n)) →
      ∀ T : Finset ℝ, (T : Set ℝ).Pairwise (fun x y => 1 ≤ |x-y|) →
      (∀ t∈T, |t| ≤ (2:ℝ)^(9*k*n)) →
      let G := actualMass (∏ p∈Nat.primesLE (2^(d*n)),p) (2^(d*n))
        (prime_product_squarefree _ (fun _prime hp => (Nat.mem_primesLE.mp hp).2))
      cofactorEnergy f P (Ioc (2*2^(8*k*n)) (4*2^(8*k*n))) T ≤
      2*(((s-1)*n*q:ℕ):ℝ)^2*ε^2 *
        ((264*G⁻¹+3200*(T.card:ℝ)*((2^(d*n):ℕ):ℝ)^4*((2^(k*n):ℕ):ℝ)^7/
          ((2^((8*k-s-1)*n):ℕ):ℝ)) *
         (44*G⁻¹+3200*((2^(d*n):ℕ):ℝ)^4*((2^(k*n):ℕ):ℝ)^7/
           ((2^((8*k-s-1)*n):ℕ):ℝ))/4)+
      2*(264+3200*(T.card:ℝ)*((2^(k*n):ℕ):ℝ)^7/((2^(8*k*n):ℕ):ℝ)) *
        (((4*2^(8*k*n):ℕ)*(G:ℝ)⁻¹*(1+Real.log (q*2^n:ℕ))+
          (q*2^n:ℕ)*(2^(d*n):ℕ)^4+
          (4*2^(8*k*n):ℕ)*(2*Real.log 4*(d*n:ℕ))/Real.log (q*2^(s*n):ℕ)+
          (6*((2^(8*k*n):ℕ):ℝ)*G⁻¹*((s-1)*n:ℕ)/q+
            (8*G⁻¹+4*((2^(d*n):ℕ):ℝ)^4)*(q*2^(s*n):ℕ))) /
              (4*((2^(8*k*n):ℕ):ℝ))) := by
  obtain ⟨M₀,hM⟩ := uniform_sparse_grid_cofactor hf hm hNP (9*k+1) (by omega) hε
  filter_upwards [eventually_gt_atTop (0:ℕ),eventually_two_power q,
    eventually_two_power M₀] with n hn hqpow hM₀
  intro P hP T hsep hT
  let S := Nat.primesLE (2^(d*n))
  have hprime : Squarefree (∏ p∈S,p) :=
    prime_product_squarefree _ (fun p hp => (Nat.mem_primesLE.mp hp).2)
  have hh := grid_height q k n hq (by omega) hn T hT
  have hend : n+(s-1)*n=s*n := by
    calc
      _ = (s-1+1)*n := by ring
      _ = _ := by rw [Nat.sub_add_cancel hs]
  have hu : 1 ≤ 2^(k*n) := Nat.one_le_pow _ _ (by norm_num)
  have hU : 1<q*2^(s*n) := by
    have he : 1 < 2^(s*n) := one_lt_pow₀ (by norm_num) (by positivity : s*n ≠ 0)
    exact he.trans_le (Nat.le_mul_of_pos_left _ hq)
  have hz : 1 ≤ 2^(d*n) := Nat.one_le_pow _ _ (by norm_num)
  have hzK : (2^(d*n))^2 ≤ 2^((8*k-s-1)*n) := by
    rw [←pow_mul]
    apply Nat.pow_le_pow_right (by norm_num)
    have hdk : 2*d ≤ 8*k-s-1 := by omega
    simpa only [Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm] using Nat.mul_le_mul_right n hdk
  have hraw := hM P S T (d*n) (2^(8*k*n)) q n ((s-1)*n) (2^(k*n))
    (2^((8*k-s-1)*n)) (2^(d*n)) hprime (by rfl) hP (by positivity) hq hu
    (by rw [←pow_mul, show k*n*8=8*k*n by ring]) (by positivity) hz hzK
    (hM₀.trans (Nat.le_mul_of_pos_left _ hq)) (by rwa [hend])
    (grid_scales q s k n hq hs (by omega) hqpow) hsep hh.1 hh.2
  rw [hend] at hraw
  simpa only [mul_div_assoc] using hraw

lemma sparse_error_compare (c b a v K H n : ℝ) (hb : 1 ≤ b)
    (_hc : 0 ≤ c) (hcb : c ≤ b) (ha : 0 ≤ a) (hv : 0 ≤ v)
    (hK : 0 ≤ K) (hH : 0 ≤ H)
    (hx : 3200*b*a*v/K ≤ 1/n) (hw : 3200*b*v/H ≤ 1) :
    3200*c*a*v/K ≤ 1/n ∧ 3200*a*v/K ≤ 1/n ∧ 3200*c*v/H ≤ 1 := by
  have hh₁ : 3200*c*a*v/K ≤ 3200*b*a*v/K := by gcongr
  have hh₂ : 3200*a*v/K ≤ 3200*b*a*v/K := by
    calc
      _ = 3200*1*a*v/K := by ring
      _ ≤ _ := by gcongr
  have hh₃ : 3200*c*v/H ≤ 3200*b*v/H := by gcongr
  exact ⟨hh₁.trans hx,hh₂.trans hx,hh₃.trans hw⟩

lemma terminal_density_facts (d s q k n : ℕ) (hd : 0 < d)
    (hs : 1 ≤ s) (hq : 0 < q) (hn : 0 < n) (G δ : ℝ)
    (hG : (d:ℝ)*n*Real.log 2/2 ≤ G)
    (hsmall : 1+Real.log q ≤ (n:ℝ)*Real.log 2)
    (hfloor : 10*(q:ℝ)*(2:ℝ)^((s+4*d)*n)/(2:ℝ)^(8*k*n) ≤ δ) :
    ((d:ℝ)/4)*n ≤ G ∧
    let A :=
    ((4*2^(8*k*n):ℕ)*(G:ℝ)⁻¹*(1+Real.log (q*2^n:ℕ))+
       (q*2^n:ℕ)*(2^(d*n):ℕ)^4+
       (4*2^(8*k*n):ℕ)*(2*Real.log 4*(d*n:ℕ))/Real.log (q*2^(s*n):ℕ)+
       (6*((2^(8*k*n):ℕ):ℝ)*G⁻¹*((s-1)*n:ℕ)/q+
         (8*G⁻¹+4*((2^(d*n):ℕ):ℝ)^4)*(q*2^(s*n):ℕ))) /
           (4*((2^(8*k*n):ℕ):ℝ))
    0 ≤ A ∧ A ≤ 4/(d:ℝ)+4*(d:ℝ)/s+6*(s:ℝ)/((q:ℝ)*d)+δ := by
  have hn' : (0:ℝ)<n := by exact_mod_cast hn
  have hd' : (0:ℝ)<d := by exact_mod_cast hd
  have hG' : ((d:ℝ)/4)*n ≤ G := by
    have hh := mul_le_mul_of_nonneg_left log_two_lower (by positivity : 0 ≤ (d:ℝ)*n/2)
    nlinarith only [hh,hG]
  refine ⟨hG',?_⟩
  have hGp : 0<G := lt_of_lt_of_le (by positivity) hG'
  have hU : 1<q*2^(s*n) := by
    have he : 1 < 2^(s*n) := one_lt_pow₀ (by norm_num) (by positivity : s*n ≠ 0)
    exact he.trans_le (Nat.le_mul_of_pos_left _ hq)
  dsimp only
  constructor
  · have hlog₁ : 0 ≤ Real.log (q*2^n:ℕ) := Real.log_nonneg (by
      exact_mod_cast Nat.mul_pos hq (by positivity : 0 < (2:ℕ)^n))
    have hlog₂ : 0 ≤ Real.log (q*2^(s*n):ℕ) := Real.log_nonneg (by exact_mod_cast hU.le)
    positivity
  · exact (remainder_at_power d s q k n hd hs hq hn hsmall G hG).trans (by linarith only [hfloor])

theorem terminal_grid_bound {f : ℕ → ℂ} (hf : OneBounded f)
    (hm : Multiplicative f) (hNP : UniformlyNonpretentious f)
    (d s q k : ℕ) (hd : 0 < d) (hs : 1 ≤ s) (hq : 0 < q)
    (hk : s+4*d+4 ≤ k) {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, ∀ (P : Finset ℕ), P ⊆ Nat.primesLE (2^(d*n)) →
      ∀ T : Finset ℝ, (T : Set ℝ).Pairwise (fun x y => 1 ≤ |x-y|) →
      (∀ t∈T, |t| ≤ (2:ℝ)^(9*k*n)) → T.card ≤ 2^n →
      cofactorEnergy f P (Ioc (2*2^(8*k*n)) (4*2^(8*k*n))) T ≤
        (((s*q:ℕ):ℝ)^2/2*(264/((d:ℝ)/4)+1)*(44/((d:ℝ)/4)+1))*ε^2+
          530*(4/(d:ℝ)+4*(d:ℝ)/s+6*(s:ℝ)/((q:ℝ)*d)+δ) := by
  have hln : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hevent : ∀ᶠ n : ℕ in atTop, (1+Real.log q)/Real.log 2 ≤ (n:ℝ) :=
    tendsto_natCast_atTop_atTop.eventually_ge_atTop _
  filter_upwards [eventually_small_errors d s k q hk hδ,
    terminal_raw_bound hf hm hNP d s q k hs hq hk hε, hevent] with n hn hrawbound hsmall
  obtain ⟨hn,hqpow,hxbase,hwbase,hfloor⟩ := hn
  have hsmall' : 1+Real.log q ≤ (n:ℝ)*Real.log 2 := (div_le_iff₀ hln).mp hsmall
  intro P hP T hsep hT hcard
  let S := Nat.primesLE (2^(d*n))
  have hprime : Squarefree (∏ p∈S,p) :=
    prime_product_squarefree _ (fun p hp => (Nat.mem_primesLE.mp hp).2)
  let G := actualMass (∏ p∈S,p) (2^(d*n)) hprime
  have hG : (d:ℝ)*n*Real.log 2/2 ≤ G := mass_power_bound d n
  have hn' : (0:ℝ)<n := by exact_mod_cast hn
  have hd' : (0:ℝ)<d := by exact_mod_cast hd
  have hg : (0:ℝ)<(d:ℝ)/4 := by positivity
  have hb : (((s-1)*n*q:ℕ):ℝ) ≤ ((s*q:ℕ):ℝ)*(n:ℝ) := by
    exact_mod_cast (show (s-1)*n*q ≤ (s*q)*n by
      simpa only [Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm] using Nat.mul_le_mul_right (n*q) (Nat.sub_le s 1))
  have hraw := hrawbound P hP T hsep hT
  let A :=
    ((4*2^(8*k*n):ℕ)*(G:ℝ)⁻¹*(1+Real.log (q*2^n:ℕ))+
       (q*2^n:ℕ)*(2^(d*n):ℕ)^4+
       (4*2^(8*k*n):ℕ)*(2*Real.log 4*(d*n:ℕ))/Real.log (q*2^(s*n):ℕ)+
       (6*((2^(8*k*n):ℕ):ℝ)*G⁻¹*((s-1)*n:ℕ)/q+
         (8*G⁻¹+4*((2^(d*n):ℕ):ℝ)^4)*(q*2^(s*n):ℕ))) /
           (4*((2^(8*k*n):ℕ):ℝ))
  obtain ⟨hG',hA,hA₀⟩ := terminal_density_facts d s q k n hd hs hq hn G δ hG hsmall' hfloor
  have hc' : (T.card:ℝ) ≤ (2:ℝ)^n := by exact_mod_cast hcard
  obtain ⟨hx,hy,hw⟩ := sparse_error_compare (T.card:ℝ) ((2:ℝ)^n)
    (((2^(d*n):ℕ):ℝ)^4) (((2^(k*n):ℕ):ℝ)^7)
    ((2^((8*k-s-1)*n):ℕ):ℝ) ((2^(8*k*n):ℕ):ℝ) n
    (one_le_pow₀ (by norm_num)) (by positivity) hc' (by positivity) (by positivity)
    (by positivity) (by positivity) hxbase hwbase
  apply compress_scaled_energy _ A _ G (((s-1)*n*q:ℕ):ℝ) (s*q:ℕ) n ((d:ℝ)/4) ε
    (3200*(T.card:ℝ)*((2^(d*n):ℕ):ℝ)^4*((2^(k*n):ℕ):ℝ)^7 / ((2^((8*k-s-1)*n):ℕ):ℝ))
    (3200*((2^(d*n):ℕ):ℝ)^4*((2^(k*n):ℕ):ℝ)^7 / ((2^((8*k-s-1)*n):ℕ):ℝ))
    (3200*(T.card:ℝ)*((2^(k*n):ℕ):ℝ)^7/((2^(8*k*n):ℕ):ℝ))
    hn' hg hG' (Nat.cast_nonneg _) (Nat.cast_nonneg _) hb (by positivity) (by positivity)
    hx hy hw hA hA₀
  simpa only [A,G,mul_div_assoc] using hraw

theorem sparse_terminal_small {f : ℕ → ℂ} (hf : OneBounded f)
    (hm : Multiplicative f) (hNP : UniformlyNonpretentious f)
    {η : ℝ} (hη : 0 < η) :
    ∃ d k : ℕ, 0 < d ∧ 0 < k ∧
      ∀ᶠ n : ℕ in atTop, ∀ (P : Finset ℕ), P ⊆ Nat.primesLE (2^(d*n)) →
      ∀ T : Finset ℝ, (T : Set ℝ).Pairwise (fun x y => 1 ≤ |x-y|) →
      (∀ t∈T, |t| ≤ (2:ℝ)^(9*k*n)) → T.card ≤ 2^n →
      cofactorEnergy f P (Ioc (2*2^(8*k*n)) (4*2^(8*k*n))) T < η := by
  obtain ⟨d,s,q,hd,hs,hq,hcost⟩ := exists_density_parameters (by positivity : 0 < η/2120)
  let k := s+4*d+4
  let C : ℝ := (((s*q:ℕ):ℝ)^2/2*(264/((d:ℝ)/4)+1)*(44/((d:ℝ)/4)+1))
  have hC : 0 < C := by
    have hs' : 0 < s := hs
    unfold C
    positivity
  let ε := Real.sqrt (η/(4*C))
  have hε : 0 < ε := Real.sqrt_pos.2 (by positivity)
  have heq : C*ε^2=η/4 := by
    dsimp [ε]
    rw [Real.sq_sqrt (by positivity)]
    field_simp
  refine ⟨d,k,hd,by omega,?_⟩
  filter_upwards [terminal_grid_bound hf hm hNP d s q k hd hs hq le_rfl hε
    (by positivity : 0 < η/2120)] with n hn
  intro P hP T hsep hT hcard
  apply (hn P hP T hsep hT hcard).trans_lt
  change C*ε^2+530*(_+η/2120)<η
  rw [heq]
  linarith only [hcost,hη]

end OrdinarySparseTerminal

end

end OAI
