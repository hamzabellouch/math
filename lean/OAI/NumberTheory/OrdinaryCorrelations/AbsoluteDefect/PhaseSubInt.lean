import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.PhaseAdd
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.SumRangeCut
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.PhaseEqOneIffInteger
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.ResidueFiberCard

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
open ArithmeticFunction
open MeasureTheory Finset

namespace OrdinaryAdditiveBilinear
lemma phase_sub_int (x : ℝ) (k : ℤ) : phase (x-k)=phase x := by
  have hk : phase (k:ℝ)=1 := (phase_eq_one_iff_integer _).mpr ⟨k,rfl⟩
  have hh := phase_add (x-k) (k:ℝ)
  simpa [hk] using hh.symm

lemma phase_chord_bound (x : ℝ) : 4*|x-(round x:ℝ)|≤‖1-phase x‖ := by
  let y : ℝ := x-(round x:ℝ)
  have hy : |y|≤1/2 := abs_sub_round x
  have hs : 2*|y|≤|Real.sin (Real.pi*y)| := by
    have hr := Real.mul_le_sin (x := Real.pi*|y|)
      (mul_nonneg Real.pi_pos.le (abs_nonneg y))
      (by nlinarith [Real.pi_pos])
    have he : 2/Real.pi*(Real.pi*|y|)=2*|y| := by field_simp
    rw [he] at hr
    by_cases hp : 0≤y
    · rw [abs_of_nonneg hp] at hr ⊢
      exact hr.trans (le_abs_self _)
    · have hn : y≤0 := le_of_not_ge hp
      have hh : Real.pi*|y|=-(Real.pi*y) := by rw [abs_of_nonpos hn]; ring
      rw [hh,Real.sin_neg] at hr
      exact hr.trans (neg_le_abs _)
  have hp : phase y=phase x := phase_sub_int x (round x)
  rw [←hp,norm_sub_rev]
  have he : phase y=Complex.exp (Complex.I*((2*Real.pi*y:ℝ):ℂ)) := by
    unfold phase
    ring_nf
  rw [he,Complex.norm_exp_I_mul_ofReal_sub_one]
  have hh : 2*Real.pi*y/2=Real.pi*y := by ring
  rw [hh,Real.norm_eq_abs,abs_mul]
  norm_num
  nlinarith

lemma rational_integer_separation (a : ℤ) (q p r : ℕ) (hq : 0<q)
    (haq : Int.gcd a q=1) (hpr : p%q≠r%q) (k : ℤ) :
    1/(q:ℝ)≤|(a:ℝ)/q*((p:ℝ)-r)-k| := by
  have hne : a*((p:ℤ)-r)-(q:ℤ)*k≠0 := by
    intro hz
    have hd : (q:ℤ)∣a*((p:ℤ)-r) := ⟨k,by linarith⟩
    have hd' : (q:ℤ)∣(p:ℤ)-r :=
      Int.dvd_of_dvd_mul_right_of_gcd_one hd (by simpa [Int.gcd_comm] using haq)
    have hm : (r:ℤ)≡(p:ℤ) [ZMOD (q:ℤ)] := Int.modEq_iff_dvd.mpr hd'
    exact hpr ((Int.natCast_modEq_iff.mp hm).symm)
  have hz : (1:ℤ)≤|a*((p:ℤ)-r)-(q:ℤ)*k| := Int.one_le_abs hne
  have hr : (1:ℝ)≤|(a:ℝ)*((p:ℝ)-r)-(q:ℝ)*k| := by exact_mod_cast hz
  have hqr : (0:ℝ)<q := by exact_mod_cast hq
  have he : (a:ℝ)*((p:ℝ)-r)-(q:ℝ)*k=
      (q:ℝ)*((a:ℝ)/q*((p:ℝ)-r)-k) := by field_simp
  rw [he,abs_mul,abs_of_pos hqr] at hr
  exact (div_le_iff₀ hqr).mpr (by nlinarith)

lemma near_rational_phase_gap (α : ℝ) (a : ℤ) (q K p r : ℕ)
    (hq : 0<q) (hK : 0<K) (haq : Int.gcd a q=1)
    (hp : p≤K) (hr : r≤K) (hpr : p%q≠r%q)
    (hα : |α-(a:ℝ)/q|≤1/(2*(q:ℝ)*K)) :
    1/(q:ℝ)≤‖1-phase (α*((p:ℝ)-r))‖ := by
  have hqr : (0:ℝ)<q := by exact_mod_cast hq
  have hKr : (0:ℝ)<K := by exact_mod_cast hK
  have hpk : (p:ℝ)≤K := by exact_mod_cast hp
  have hrk : (r:ℝ)≤K := by exact_mod_cast hr
  have hdiff : |(p:ℝ)-r|≤K := by rw [abs_sub_le_iff]; constructor <;> linarith [Nat.cast_nonneg (α := ℝ) p,Nat.cast_nonneg (α := ℝ) r]
  have herr : |(α-(a:ℝ)/q)*((p:ℝ)-r)|≤1/(2*(q:ℝ)) := by
    rw [abs_mul]
    calc
      _ ≤ (1/(2*(q:ℝ)*K))*(K:ℝ) := mul_le_mul hα hdiff (abs_nonneg _) (by positivity)
      _ = _ := by field_simp
  let k := round (α*((p:ℝ)-r))
  have hs := rational_integer_separation a q p r hq haq hpr k
  have ht : |(a:ℝ)/q*((p:ℝ)-r)-k|≤
      |α*((p:ℝ)-r)-k|+|(α-(a:ℝ)/q)*((p:ℝ)-r)| := by
    have he : (a:ℝ)/q*((p:ℝ)-r)-k=
        (α*((p:ℝ)-r)-k)-(α-(a:ℝ)/q)*((p:ℝ)-r) := by ring
    rw [he]
    exact abs_sub _ _
  have hb := phase_chord_bound (α*((p:ℝ)-r))
  have he : 1/(q:ℝ)=2*(1/(2*(q:ℝ))) := by field_simp
  change 4*|α*((p:ℝ)-r)-(k:ℝ)|≤_ at hb
  have hpos : 0≤1/(q:ℝ) := by positivity
  nlinarith
theorem resonant_truncated_energy (P : Finset ℕ) (u : ℕ → ℂ)
    (hu : ∀n,‖u n‖≤1) (c : ℕ → ℂ) (hc : ∀p,‖c p‖≤1)
    (T : ℕ → ℕ) (D a N K : ℕ) (hT : ∀p∈P,T p≤N) (α : ℝ)
    (hP : ∀p∈P,p≤K) (q : ℕ) (hq : 0<q) {κ : ℝ} (hκ : 0<κ)
    (hgap : ∀p∈P,∀r∈P,p%q≠r%q → κ≤‖1-phase (α*((p:ℝ)-r))‖) :
    (∑n∈range N,‖∑p∈P,if n<T p then
      c p*smooth u D (p*(a+n))*phase (α*(p:ℝ)*n) else 0‖^2) ≤
      (N:ℝ)*P.card*(K/q+1:ℕ)+(P.card:ℝ)^2*((2+4*(N:ℝ)*K/D)/κ) := by
  let b := fun p n => if n<T p then c p*smooth u D (p*(a+n))*phase (α*(p:ℝ)*n) else 0
  let E : ℝ := (2+4*(N:ℝ)*K/D)/κ
  have hE : 0≤E := by dsimp [E]; positivity
  have hb (p n : ℕ) : ‖b p n‖≤1 := by
    dsimp [b]
    split_ifs
    · simp only [norm_mul,norm_phase,mul_one]
      exact (mul_le_of_le_one_left (norm_nonneg _) (hc p)).trans (smooth_bound u hu D _)
    · simp
  have hd (p r : ℕ) : ‖∑n∈range N,b p n*star (b r n)‖≤(N:ℝ) := by
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑n∈range N,(1:ℝ) := by
        apply sum_le_sum
        intro n hn
        rw [norm_mul,norm_star]
        exact (mul_le_of_le_one_left (norm_nonneg _) (hb p n)).trans (hb r n)
      _ = _ := by simp
  have ho (p : ℕ) (hp : p∈P) (r : ℕ) (hr : r∈P) (hpr : p%q≠r%q) :
      ‖∑n∈range N,b p n*star (b r n)‖≤E := by
    dsimp only [b]
    rw [truncated_pair_sum N (T p) (T r) (hT p hp) (hT r hr)]
    apply (smoothed_pair_bound u hu c hc D p r a (min (T p) (T r)) α
      hκ (hgap p hp r hr hpr)).trans
    have hpk : (p:ℝ)≤K := by exact_mod_cast hP p hp
    have hqk : (r:ℝ)≤K := by exact_mod_cast hP r hr
    have hnk : (min (T p) (T r):ℝ)≤N := by
      exact_mod_cast le_trans (min_le_left (T p) (T r)) (hT p hp)
    apply div_le_div_of_nonneg_right _ hκ.le
    calc
      _ ≤ 2+(N:ℝ)*((2*(K:ℝ))*(2/(D:ℝ))) := by
        gcongr
        · exact le_trans (min_le_left (T p) (T r)) (hT p hp)
        · linarith
      _ = _ := by ring
  have hr (p : ℕ) (hp : p∈P) :
      ∑r∈P,‖∑n∈range N,b p n*star (b r n)‖≤
        (N:ℝ)*(K/q+1:ℕ)+(P.card:ℝ)*E := by
    calc
      _ ≤ ∑r∈P,((if r%q=p%q then (N:ℝ) else 0)+E) := by
        apply sum_le_sum
        intro r hr
        by_cases he : r%q=p%q
        · simpa [he] using (hd p r).trans (le_add_of_nonneg_right hE)
        · simpa [he] using ho p hp r hr (Ne.symm he)
      _ = (N:ℝ)*((P.filter (fun r=>r%q=p%q)).card:ℝ)+(P.card:ℝ)*E := by
        simp [sum_add_distrib,←sum_filter,mul_comm]
      _ ≤ _ := by
        gcongr
        exact OrdinaryRationalResonance.residue_fiber_card P K q p hq hP
  calc
    _ ≤ ∑p∈P,∑r∈P,‖∑n∈range N,b p n*star (b r n)‖ := energy_le_gram P b N
    _ ≤ ∑p∈P,((N:ℝ)*(K/q+1:ℕ)+(P.card:ℝ)*E) := sum_le_sum hr
    _ = _ := by simp [E]; ring

theorem resonant_weighted_packet (P : Finset ℕ) (u w c : ℕ → ℂ)
    (hu : ∀n,‖u n‖≤1) (hc : ∀p,‖c p‖≤1)
    (T : ℕ → ℕ) (D a N K : ℕ) (hT : ∀p∈P,T p≤N) (α : ℝ)
    (hP : ∀p∈P,p≤K) (q : ℕ) (hq : 0<q) {κ : ℝ} (hκ : 0<κ)
    (hgap : ∀p∈P,∀r∈P,p%q≠r%q → κ≤‖1-phase (α*((p:ℝ)-r))‖) :
    ‖∑p∈P,c p*∑n∈range (T p),w (a+n)*smooth u D (p*(a+n))*
      phase (α*(p:ℝ)*(a+n))‖^2 ≤
      (∑n∈range N,‖w (a+n)‖^2)*
        ((N:ℝ)*P.card*(K/q+1:ℕ)+(P.card:ℝ)^2*((2+4*(N:ℝ)*K/D)/κ)) := by
  let c' := fun p => c p*phase (α*(p:ℝ)*a)
  have hc' (p : ℕ) : ‖c' p‖≤1 := by simpa [c',norm_mul,norm_phase] using hc p
  let b := fun n => ∑p∈P,if n<T p then
    c' p*smooth u D (p*(a+n))*phase (α*(p:ℝ)*n) else 0
  have hi : (∑p∈P,c p*∑n∈range (T p),w (a+n)*smooth u D (p*(a+n))*
      phase (α*(p:ℝ)*(a+n))) = ∑n∈range N,w (a+n)*b n := by
    calc
      _ = ∑p∈P,∑n∈range N,if n<T p then
          c p*(w (a+n)*smooth u D (p*(a+n))*phase (α*(p:ℝ)*(a+n))) else 0 := by
        apply sum_congr rfl
        intro p hp
        rw [sum_range_cut _ N (T p) (hT p hp),mul_sum]
      _ = _ := by
        rw [sum_comm]
        apply sum_congr rfl
        intro n hn
        simp only [b,mul_sum]
        apply sum_congr rfl
        intro p hp
        split_ifs
        · have he : α*(p:ℝ)*(a+n)=α*(p:ℝ)*a+α*(p:ℝ)*n := by ring
          rw [he,phase_add]
          dsimp [c']
          ring
        · simp
  rw [hi]
  apply (weighted_packet_sq (range N) (fun n => w (a+n)) b).trans
  exact mul_le_mul_of_nonneg_left
    (resonant_truncated_energy P u hu c' hc' T D a N K hT α hP q hq hκ hgap)
    (sum_nonneg (fun n hn => sq_nonneg _))

theorem near_rational_weighted_packet (P : Finset ℕ) (u w c : ℕ → ℂ)
    (hu : ∀n,‖u n‖≤1) (hc : ∀p,‖c p‖≤1)
    (T : ℕ → ℕ) (D b N K : ℕ) (hK : 0<K) (hT : ∀p∈P,T p≤N)
    (α : ℝ) (a : ℤ) (q : ℕ) (hq : 0<q) (haq : Int.gcd a q=1)
    (hP : ∀p∈P,p≤K) (hα : |α-(a:ℝ)/q|≤1/(2*(q:ℝ)*K)) :
    ‖∑p∈P,c p*∑n∈range (T p),w (b+n)*smooth u D (p*(b+n))*
      phase (α*(p:ℝ)*(b+n))‖^2 ≤
      (∑n∈range N,‖w (b+n)‖^2)*
        ((N:ℝ)*P.card*(K/q+1:ℕ)+(P.card:ℝ)^2*(q:ℝ)*(2+4*(N:ℝ)*K/D)) := by
  have hg : ∀p∈P,∀r∈P,p%q≠r%q → 1/(q:ℝ)≤‖1-phase (α*((p:ℝ)-r))‖ := by
    intro p hp r hr hpr
    exact near_rational_phase_gap α a q K p r hq hK haq (hP p hp) (hP r hr) hpr hα
  have hh := resonant_weighted_packet P u w c hu hc T D b N K hT α hP q hq
    (κ := 1/(q:ℝ)) (by positivity) hg
  simp only [div_eq_mul_inv,one_mul,inv_inv] at hh
  convert hh using 1; ring

end OrdinaryAdditiveBilinear

end

end OAI
