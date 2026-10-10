import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.TwoPowerRatioLimit
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.MassPowerBound

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

namespace OrdinarySparseShell
open Filter Finset OrdinaryNarrowGrid OrdinarySparsePowerScales OrdinarySparseTerminal
  OrdinarySparseNumerics OrdinarySmoothRough OrdinaryCorrelations OrdinarySelbergWeights

lemma shell_grid_scales (q s k n H : ℕ) (hq : 0 < q) (hs : 1 ≤ s)
    (hsk : s+1 ≤ 8*k) (hqpow : q ≤ 2^n)
    (hlo : 2^(8*k*n) ≤ H) (hhi : H ≤ 2^(8*k*(n+1))) :
    ∀ i∈grid q n ((s-1)*n),
      2^((8*k-s-1)*n) ≤ (2*H)/(2*lower i) ∧
      (2*H)/(2*lower i) ≤ (2^(k*(n+1)))^8 := by
  intro i hi
  constructor
  · exact ((grid_scales q s k n hq hs hsk hqpow i hi).1).trans
      (Nat.div_le_div_right (Nat.mul_le_mul_left 2 hlo))
  · rw [←pow_mul, show k*(n+1)*8=8*k*(n+1) by ring]
    rw [Nat.mul_div_mul_left _ _ (by norm_num : 0 < 2)]
    exact (Nat.div_le_self _ _).trans hhi

lemma shell_height (q k n : ℕ) (hq : 0 < q) (hk : 0 < k) (hn : 0 < n)
    (T : Finset ℝ) (hT : ∀ t∈T, |t| ≤ (2:ℝ)^(9*k*n)) :
    (∀ t∈T, ∀ s∈T, |t-s| ≤ ((2^(k*(n+1)):ℕ):ℝ)^10) ∧
    (∀ t∈T, |t| ≤ ((q*2^n:ℕ):ℝ)^(9*k+1)/2) := by
  obtain ⟨ha,hb⟩ := grid_height q k n hq hk hn T hT
  refine ⟨?_,hb⟩
  intro t ht s hs
  exact (ha t ht s hs).trans (by gcongr; omega)

lemma shell_small_errors (d s k q : ℕ) (hk : s+4*d+4 ≤ k)
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop,
      0 < n ∧ q ≤ 2^n ∧
      3200*(2:ℝ)^n*((2^(d*n):ℕ):ℝ)^4*((2^(k*(n+1)):ℕ):ℝ)^7 /
        ((2^((8*k-s-1)*n):ℕ):ℝ) ≤ 1/(n:ℝ) ∧
      3200*(2:ℝ)^n*((2^(k*(n+1)):ℕ):ℝ)^7/((2^(8*k*n):ℕ):ℝ) ≤ 1 ∧
      10*(q:ℝ)*(2:ℝ)^((s+4*d)*n)/(2:ℝ)^(8*k*n) ≤ δ := by
  have ha : 1+4*d+7*k < 8*k-s-1 := by omega
  have hb : 1+7*k < 8*k := by omega
  have hc : s+4*d < 8*k := by omega
  have hlim₁ := (two_power_ratio_limit (1+4*d+7*k) (8*k-s-1) 1 ha).const_mul
    (3200*(2:ℝ)^(7*k))
  have hlim₂ := (two_power_ratio_limit (1+7*k) (8*k) 0 hb).const_mul
    (3200*(2:ℝ)^(7*k))
  have hlim₃ := (two_power_ratio_limit (s+4*d) (8*k) 0 hc).const_mul (10*(q:ℝ))
  simp only [mul_zero] at hlim₁ hlim₂ hlim₃
  filter_upwards [eventually_gt_atTop (0:ℕ),eventually_two_power q,
    hlim₁.eventually_le_const (by norm_num : (0:ℝ)<1),
    hlim₂.eventually_le_const (by norm_num : (0:ℝ)<1),
    hlim₃.eventually_le_const hδ] with n hn hq h₁ h₂ h₃
  have hu : ((2^(k*(n+1)):ℕ):ℝ)^7 = (2:ℝ)^(7*k)*(2:ℝ)^(7*k*n) := by
    push_cast
    rw [←pow_mul,←pow_add]
    congr 1
    ring
  refine ⟨hn,hq,?_,?_,?_⟩
  · have he : (2:ℝ)^n*((2^(d*n):ℕ):ℝ)^4*((2^(k*(n+1)):ℕ):ℝ)^7 =
        (2:ℝ)^(7*k)*(2:ℝ)^((1+4*d+7*k)*n) := by
      rw [hu]
      push_cast
      rw [←pow_mul]
      have hp : n+d*n*4+7*k*n=(1+4*d+7*k)*n := by ring
      rw [←hp,pow_add,pow_add]
      ring
    apply (le_div_iff₀ (by exact_mod_cast hn : (0:ℝ)<n)).mpr
    convert h₁ using 1
    push_cast
    push_cast at he
    linear_combination (3200*(n:ℝ)/(2:ℝ)^((8*k-s-1)*n))*he
  · have he : (2:ℝ)^n*((2^(k*(n+1)):ℕ):ℝ)^7 =
        (2:ℝ)^(7*k)*(2:ℝ)^((1+7*k)*n) := by
      rw [hu,show (1+7*k)*n=n+7*k*n by ring,pow_add]
      ring
    apply le_trans (le_of_eq ?_) h₂
    push_cast at he ⊢
    linear_combination (3200/(2:ℝ)^(8*k*n))*he
  · simpa only [pow_zero,one_mul,mul_div_assoc] using h₃

lemma shell_remainder (d s q k n H : ℕ) (hd : 0 < d) (hs : 1 ≤ s) (hq : 0 < q)
    (hn : 0 < n) (hlo : 2^(8*k*n) ≤ H) (G δ : ℝ)
    (hG : (d:ℝ)*n*Real.log 2/2 ≤ G)
    (hsmall : 1+Real.log q ≤ (n:ℝ)*Real.log 2)
    (hfloor : 10*(q:ℝ)*(2:ℝ)^((s+4*d)*n)/(2:ℝ)^(8*k*n) ≤ δ) :
    let A := ((4*H:ℕ)*G⁻¹*(1+Real.log (q*2^n:ℕ))+
      (q*2^n:ℕ)*(2^(d*n):ℕ)^4+
      (4*H:ℕ)*(2*Real.log 4*(d*n:ℕ))/Real.log (q*2^(s*n):ℕ)+
      (6*(H:ℝ)*G⁻¹*((s-1)*n:ℕ)/q+
        (8*G⁻¹+4*((2^(d*n):ℕ):ℝ)^4)*(q*2^(s*n):ℕ)))/(4*(H:ℝ))
    0 ≤ A ∧ A ≤ 4/(d:ℝ)+4*(d:ℝ)/s+6*(s:ℝ)/((q:ℝ)*d)+δ := by
  have hH : (0:ℝ)<H := by exact_mod_cast lt_of_lt_of_le (by positivity : 0 < 2^(8*k*n)) hlo
  have hGp : 0<G := lt_of_lt_of_le (by positivity) hG
  dsimp only
  constructor
  · have hlog₁ : 0 ≤ Real.log (q*2^n:ℕ) := Real.log_nonneg (by
      exact_mod_cast Nat.mul_pos hq (by positivity : 0 < (2:ℕ)^n))
    have hlog₂ : 0 ≤ Real.log (q*2^(s*n):ℕ) := Real.log_nonneg (by
      exact_mod_cast Nat.mul_pos hq (by positivity : 0 < (2:ℕ)^(s*n)))
    positivity
  · apply le_trans _ (terminal_density_facts d s q k n hd hs hq hn G δ hG hsmall hfloor).2.2
    push_cast
    rw [remainder_normalize _ _ _ _ _ _ _ _ _ _ hH.ne',
      remainder_normalize _ _ _ _ _ _ _ _ _ _ (by positivity : (2:ℝ)^(8*k*n) ≠ 0)]
    gcongr
    exact_mod_cast hlo

theorem shell_raw_bound {f : ℕ → ℂ} (hf : OneBounded f)
    (hm : Multiplicative f) (hNP : UniformlyNonpretentious f)
    (d s q k : ℕ) (hs : 1 ≤ s) (hq : 0 < q) (hk : s+4*d+4 ≤ k)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ H : ℕ, 2^(8*k*n) ≤ H → H ≤ 2^(8*k*(n+1)) →
      ∀ (P : Finset ℕ), P ⊆ Nat.primesLE (2^(d*n)) →
      ∀ T : Finset ℝ, (T : Set ℝ).Pairwise (fun x y => 1 ≤ |x-y|) →
      (∀ t∈T, |t| ≤ (2:ℝ)^(9*k*n)) →
      let G := actualMass (∏ p∈Nat.primesLE (2^(d*n)),p) (2^(d*n))
        (prime_product_squarefree _ (fun prime hprime =>
          (show Nat.Prime prime from (Nat.mem_primesLE.mp hprime).2)))
      cofactorEnergy f P (Ioc (2*H) (4*H)) T ≤
      2*(((s-1)*n*q:ℕ):ℝ)^2*ε^2 *
        ((264*G⁻¹+3200*(T.card:ℝ)*((2^(d*n):ℕ):ℝ)^4*((2^(k*(n+1)):ℕ):ℝ)^7/
          ((2^((8*k-s-1)*n):ℕ):ℝ)) *
         (44*G⁻¹+3200*((2^(d*n):ℕ):ℝ)^4*((2^(k*(n+1)):ℕ):ℝ)^7/
           ((2^((8*k-s-1)*n):ℕ):ℝ))/4)+
      2*(264+3200*(T.card:ℝ)*((2^(k*(n+1)):ℕ):ℝ)^7/((H:ℕ):ℝ)) *
        (((4*H:ℕ)*(G:ℝ)⁻¹*(1+Real.log (q*2^n:ℕ))+
          (q*2^n:ℕ)*(2^(d*n):ℕ)^4+
          (4*H:ℕ)*(2*Real.log 4*(d*n:ℕ))/Real.log (q*2^(s*n):ℕ)+
          (6*((H:ℕ):ℝ)*G⁻¹*((s-1)*n:ℕ)/q+
            (8*G⁻¹+4*((2^(d*n):ℕ):ℝ)^4)*(q*2^(s*n):ℕ))) /
              (4*((H:ℕ):ℝ))) := by
  obtain ⟨M₀,hM⟩ := uniform_sparse_grid_cofactor hf hm hNP (9*k+1) (by omega) hε
  filter_upwards [eventually_gt_atTop (0:ℕ),eventually_two_power q,
    eventually_two_power M₀] with n hn hqpow hM₀
  intro H hlo hhi P hP T hsep hT
  have hHp : 0 < H := lt_of_lt_of_le (by positivity : 0 < 2^(8*k*n)) hlo
  let S := Nat.primesLE (2^(d*n))
  have hprime : Squarefree (∏ p∈S,p) :=
    prime_product_squarefree _ (fun p hp => (Nat.mem_primesLE.mp hp).2)
  have hh := shell_height q k n hq (by omega) hn T hT
  have hend : n+(s-1)*n=s*n := by
    calc
      _ = (s-1+1)*n := by ring
      _ = _ := by rw [Nat.sub_add_cancel hs]
  have hu : 1 ≤ 2^(k*(n+1)) := Nat.one_le_pow _ _ (by norm_num)
  have hU : 1<q*2^(s*n) := by
    have he : 1 < 2^(s*n) := one_lt_pow₀ (by norm_num) (by positivity : s*n ≠ 0)
    exact he.trans_le (Nat.le_mul_of_pos_left _ hq)
  have hz : 1 ≤ 2^(d*n) := Nat.one_le_pow _ _ (by norm_num)
  have hzK : (2^(d*n))^2 ≤ 2^((8*k-s-1)*n) := by
    rw [←pow_mul]
    apply Nat.pow_le_pow_right (by norm_num)
    have hdk : 2*d ≤ 8*k-s-1 := by omega
    simpa only [Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm] using Nat.mul_le_mul_right n hdk
  have hraw := hM P S T (d*n) (H) q n ((s-1)*n) (2^(k*(n+1)))
    (2^((8*k-s-1)*n)) (2^(d*n)) hprime (by rfl) hP (by positivity) hq hu
    (by rw [←pow_mul, show k*(n+1)*8=8*k*(n+1) by ring]; exact hhi) (by positivity) hz hzK
    (hM₀.trans (Nat.le_mul_of_pos_left _ hq)) (by rwa [hend])
    (shell_grid_scales q s k n H hq hs (by omega) hqpow hlo hhi) hsep hh.1 hh.2
  rw [hend] at hraw
  simpa only [mul_div_assoc] using hraw

theorem shell_grid_bound {f : ℕ → ℂ} (hf : OneBounded f)
    (hm : Multiplicative f) (hNP : UniformlyNonpretentious f)
    (d s q k : ℕ) (hd : 0 < d) (hs : 1 ≤ s) (hq : 0 < q)
    (hk : s+4*d+4 ≤ k) {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, ∀ H : ℕ, 2^(8*k*n) ≤ H → H ≤ 2^(8*k*(n+1)) →
      ∀ (P : Finset ℕ), P ⊆ Nat.primesLE (2^(d*n)) →
      ∀ T : Finset ℝ, (T : Set ℝ).Pairwise (fun x y => 1 ≤ |x-y|) →
      (∀ t∈T, |t| ≤ (2:ℝ)^(9*k*n)) → T.card ≤ 2^n →
      cofactorEnergy f P (Ioc (2*H) (4*H)) T ≤
        (((s*q:ℕ):ℝ)^2/2*(264/((d:ℝ)/4)+1)*(44/((d:ℝ)/4)+1))*ε^2+
          530*(4/(d:ℝ)+4*(d:ℝ)/s+6*(s:ℝ)/((q:ℝ)*d)+δ) := by
  have hln : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hevent : ∀ᶠ n : ℕ in atTop, (1+Real.log q)/Real.log 2 ≤ (n:ℝ) :=
    tendsto_natCast_atTop_atTop.eventually_ge_atTop _
  filter_upwards [shell_small_errors d s k q hk hδ,
    shell_raw_bound hf hm hNP d s q k hs hq hk hε, hevent] with n hn hrawbound hsmall
  obtain ⟨hn,hqpow,hxbase,hwbase,hfloor⟩ := hn
  have hsmall' : 1+Real.log q ≤ (n:ℝ)*Real.log 2 := (div_le_iff₀ hln).mp hsmall
  intro H hlo hhi P hP T hsep hT hcard
  have hHp : 0 < H := lt_of_lt_of_le (by positivity : 0 < 2^(8*k*n)) hlo
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
  have hraw := hrawbound H hlo hhi P hP T hsep hT
  let A :=
    ((4*H:ℕ)*(G:ℝ)⁻¹*(1+Real.log (q*2^n:ℕ))+
       (q*2^n:ℕ)*(2^(d*n):ℕ)^4+
       (4*H:ℕ)*(2*Real.log 4*(d*n:ℕ))/Real.log (q*2^(s*n):ℕ)+
       (6*((H:ℕ):ℝ)*G⁻¹*((s-1)*n:ℕ)/q+
         (8*G⁻¹+4*((2^(d*n):ℕ):ℝ)^4)*(q*2^(s*n):ℕ))) /
           (4*((H:ℕ):ℝ))
  have hG' := (terminal_density_facts d s q k n hd hs hq hn G δ hG hsmall' hfloor).1
  obtain ⟨hA,hA₀⟩ := shell_remainder d s q k n H hd hs hq hn hlo G δ hG hsmall' hfloor
  have hwbase' : 3200*(2:ℝ)^n*((2^(k*(n+1)):ℕ):ℝ)^7/(H:ℝ) ≤ 1 := by
    apply le_trans _ hwbase
    apply div_le_div_of_nonneg_left (by positivity) (by positivity : (0:ℝ) < ((2^(8*k*n):ℕ):ℝ))
    exact_mod_cast hlo
  have hc' : (T.card:ℝ) ≤ (2:ℝ)^n := by exact_mod_cast hcard
  obtain ⟨hx,hy,hw⟩ := sparse_error_compare (T.card:ℝ) ((2:ℝ)^n)
    (((2^(d*n):ℕ):ℝ)^4) (((2^(k*(n+1)):ℕ):ℝ)^7)
    ((2^((8*k-s-1)*n):ℕ):ℝ) ((H:ℕ):ℝ) n
    (one_le_pow₀ (by norm_num)) (by positivity) hc' (by positivity) (by positivity)
    (by positivity) (by positivity) hxbase hwbase'
  apply compress_scaled_energy _ A _ G (((s-1)*n*q:ℕ):ℝ) (s*q:ℕ) n ((d:ℝ)/4) ε
    (3200*(T.card:ℝ)*((2^(d*n):ℕ):ℝ)^4*((2^(k*(n+1)):ℕ):ℝ)^7 / ((2^((8*k-s-1)*n):ℕ):ℝ))
    (3200*((2^(d*n):ℕ):ℝ)^4*((2^(k*(n+1)):ℕ):ℝ)^7 / ((2^((8*k-s-1)*n):ℕ):ℝ))
    (3200*(T.card:ℝ)*((2^(k*(n+1)):ℕ):ℝ)^7/((H:ℕ):ℝ))
    hn' hg hG' (Nat.cast_nonneg _) (Nat.cast_nonneg _) hb (by positivity) (by positivity)
    hx hy hw hA hA₀
  simpa only [A,G,mul_div_assoc] using hraw

theorem sparse_shell_small {f : ℕ → ℂ} (hf : OneBounded f)
    (hm : Multiplicative f) (hNP : UniformlyNonpretentious f)
    {η : ℝ} (hη : 0 < η) :
    ∃ d k : ℕ, 0 < d ∧ 0 < k ∧
      ∀ᶠ n : ℕ in atTop, ∀ H : ℕ, 2^(8*k*n) ≤ H → H ≤ 2^(8*k*(n+1)) →
      ∀ (P : Finset ℕ), P ⊆ Nat.primesLE (2^(d*n)) →
      ∀ T : Finset ℝ, (T : Set ℝ).Pairwise (fun x y => 1 ≤ |x-y|) →
      (∀ t∈T, |t| ≤ (2:ℝ)^(9*k*n)) → T.card ≤ 2^n →
      cofactorEnergy f P (Ioc (2*H) (4*H)) T < η := by
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
  filter_upwards [shell_grid_bound hf hm hNP d s q k hd hs hq le_rfl hε
    (by positivity : 0 < η/2120)] with n hn
  intro H hlo hhi P hP T hsep hT hcard
  apply (hn H hlo hhi P hP T hsep hT hcard).trans_lt
  change C*ε^2+530*(_+η/2120)<η
  rw [heq]
  linarith only [hcost,hη]

theorem sparse_cofactor_all_lengths {f : ℕ → ℂ} (hf : OneBounded f)
    (hm : Multiplicative f) (hNP : UniformlyNonpretentious f)
    {η : ℝ} (hη : 0 < η) :
    ∃ d r : ℕ, 0 < d ∧ 0 < r ∧
      ∀ᶠ H : ℕ in atTop, ∀ (P : Finset ℕ),
      (∀ p∈P, Nat.Prime p ∧ p^r ≤ H^d) →
      ∀ T : Finset ℝ, (T : Set ℝ).Pairwise (fun x y => 1 ≤ |x-y|) →
      (∀ t∈T, |t| ≤ (H:ℝ)) → T.card^r ≤ H →
      cofactorEnergy f P (Ioc (2*H) (4*H)) T < η := by
  obtain ⟨d,k,hd,hk,hgood⟩ := sparse_shell_small hf hm hNP hη
  obtain ⟨N,hN⟩ := eventually_atTop.mp hgood
  refine ⟨d,16*k,hd,by positivity,?_⟩
  filter_upwards [eventually_ge_atTop (2^(8*k*max N 8))] with H hH
  have hb : 1 < 2^(8*k) := one_lt_pow₀ (by norm_num) (by positivity)
  have hHpos : 0 < H := lt_of_lt_of_le (by positivity : 0 < 2^(8*k*max N 8)) hH
  let n := Nat.log (2^(8*k)) H
  have hn : max N 8 ≤ n := by
    apply Nat.le_log_of_pow_le hb
    simpa only [←pow_mul] using hH
  have hn8 : 8 ≤ n := (le_max_right _ _).trans hn
  have hNn : N ≤ n := (le_max_left _ _).trans hn
  have hlo : 2^(8*k*n) ≤ H := by
    simpa only [←pow_mul] using Nat.pow_log_le_self (2^(8*k)) hHpos.ne'
  have hhi : H ≤ 2^(8*k*(n+1)) := by
    simpa only [←pow_mul] using (Nat.lt_pow_succ_log_self hb H).le
  have hcardpow : H ≤ (2^n)^(16*k) := by
    apply hhi.trans
    rw [←pow_mul]
    apply Nat.pow_le_pow_right (by norm_num)
    nlinarith
  intro P hP T hsep hT hcard
  have hPS : P ⊆ Nat.primesLE (2^(d*n)) := by
    intro p hp
    refine Nat.mem_primesLE.mpr ⟨?_,(hP p hp).1⟩
    apply (Nat.pow_le_pow_iff_left (by positivity : 16*k ≠ 0)).mp
    apply (hP p hp).2.trans
    calc
      H^d ≤ ((2^n)^(16*k))^d := Nat.pow_le_pow_left hcardpow d
      _ = (2^(d*n))^(16*k) := by
        simp only [←pow_mul]
        congr 1
        ring
  have hcard' : T.card ≤ 2^n :=
    (Nat.pow_le_pow_iff_left (by positivity : 16*k ≠ 0)).mp (hcard.trans hcardpow)
  have hheight : ∀ t∈T, |t| ≤ (2:ℝ)^(9*k*n) := by
    intro t ht
    apply (hT t ht).trans
    have hle : H ≤ 2^(9*k*n) := by
      apply hhi.trans
      apply Nat.pow_le_pow_right (by norm_num)
      nlinarith
    exact_mod_cast hle
  exact hN n hNn H hlo hhi P hPS T hsep hheight hcard'

end OrdinarySparseShell

end

end OAI
