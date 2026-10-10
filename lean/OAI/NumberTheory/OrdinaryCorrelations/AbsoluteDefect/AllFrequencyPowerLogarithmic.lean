import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.MajorArcsEvenPowerLogarithmic
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.RationalApproximation
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.MinorDyadicWidth

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

namespace OrdinaryUniformWidth
open OrdinaryCorrelations OrdinaryMellinModulus
open OrdinaryLocalAdditive OrdinarySharpWindow Finset Filter MeasureTheory

theorem all_frequency_power_logarithmic :
    ∃ v : ℕ, ∀ m : ℕ,
    ∀ {f : ℕ→ℂ}, OneBounded f → Multiplicative f → UniformlyNonpretentious f →
    ∀ᶠ X : ℕ in atTop,
    ∀ D : ℝ, ((2:ℕ)^(2^(1800*m+v)):ℝ)≤D → ∀α : ℝ,
      (∫x : ℝ,‖sharpWindow (Ioc X (2*X))
        (fun n=>f n*phase (α*n)) (fun n=>(n:ℝ)) D x‖)
      ≤100*(1/2:ℝ)^(2*m)*D*X := by
  obtain ⟨A,c,k,v,hMajor⟩ := major_arcs_even_power_logarithmic
  obtain ⟨t,hPacket⟩ := choose_prime_packet
  obtain ⟨n0,hn0⟩ := eventually_atTop.mp (resonance_small t)
  obtain ⟨g,hg⟩ := longGate_wide A c k v t
  refine ⟨1800*n0+g,?_⟩
  intro m f hf hm hNP
  let n := m+n0
  let S := shortWidth A c k v t n
  let ε := accuracy n
  have hε : 0<ε := accuracy_pos n
  have hS : (0:ℝ)<S := by dsimp only [S];exact_mod_cast shortWidth_pos A c k v t n
  have hp := hPacket n
  have hres := hn0 n (by dsimp [n];omega)
  have hMj := hMajor n hf hm hNP
  have hMn := minor_dyadic_width A c k v t n hp.1 hp.2 hres hf hm
  have hGate : longGate A c k v t n≤((2:ℕ)^(2^(1800*m+(1800*n0+g))):ℝ) := by
    have hn : 1800*n+g=1800*m+(1800*n0+g) := by dsimp [n];omega
    simpa only [hn,Nat.cast_pow,Nat.cast_ofNat] using hg n
  filter_upwards [hMj,hMn] with X hMX hNX
  intro D hD α
  have hDgate := hGate.trans hD
  have hD0 : 0<D := (show 0<longGate A c k v t n by unfold longGate;positivity).trans_le hDgate
  obtain ⟨q,hq,hqN,a,ha,haL,haU,hα⟩ := rational_approximation α (approxBound_pos A c k v t n)
  have hshort : (∫x : ℝ,‖sharpWindow (Ioc X (2*X))
      (fun j=>f j*phase (Int.fract α*j)) (fun j=>(j:ℝ)) (S:ℝ) x‖)≤55*ε*S*X := by
    by_cases hqQ : q≤2^(10*n)
    · have haQ : a∈Finset.Icc (-(2^(10*n):ℕ):ℤ) (2*(2^(10*n):ℕ):ℤ) := by
        have hqQ' : (q:ℤ)≤(2^(10*n):ℕ) := by exact_mod_cast hqQ
        apply Finset.mem_Icc.mpr;constructor <;> omega
      have hh := hMX (S:ℝ) (shortWidth_large_H A c k v t n) q hq hqQ a haQ
        (Int.fract α) (hα.trans (major_radius A c k v t n hq))
      have hnon : 0≤ε*(S:ℝ)*X := by positivity
      change _≤3*ε*S*X at hh
      nlinarith only [hh,hnon]
    · exact hNX q (by omega) hqN a ha (Int.fract α)
        (hα.trans (minor_radius A c k v t n hq))
  have he : (fun j : ℕ=>f j*phase (Int.fract α*j))=(fun j : ℕ=>f j*phase (α*j)) := by
    funext j;rw [phase_fract α j]
  rw [he] at hshort
  have hlong := sharpWindow_long_from_short (Ioc X (2*X))
    (fun j=>f j*phase (α*j)) (fun j=>(j:ℝ)) hS hD0.le
  have hmass := mul_le_mul_of_nonneg_left (dyadic_phase_mass hf α X) hS.le
  have hs := mul_le_mul_of_nonneg_left hshort (div_nonneg hD0.le hS.le)
  have hid : D/(S:ℝ)*(55*ε*S*X)=55*ε*D*X := by field_simp
  rw [hid] at hs
  have hSD : (S:ℝ)≤ε*D := by
    have hh := mul_le_mul_of_nonneg_left hDgate hε.le
    change ε*((2:ℝ)^(2*n)*S)≤ε*D at hh
    rw [←mul_assoc,mul_comm ε,accuracy_cancel,one_mul] at hh
    exact hh
  have hr := mul_le_mul_of_nonneg_right hSD (Nat.cast_nonneg X)
  have hεm : ε≤(1/2:ℝ)^(2*m) := by
    apply pow_le_pow_of_le_one (by norm_num) (by norm_num)
    dsimp [n];omega
  have hem := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hεm hD0.le) (Nat.cast_nonneg X)
  have hnn : 0≤(1/2:ℝ)^(2*m)*D*X := by positivity
  nlinarith only [hlong,hmass,hs,hr,hem,hnn]

end OrdinaryUniformWidth

end

end OAI
