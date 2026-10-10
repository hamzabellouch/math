import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.DyadicPhaseMass
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.PeriodicEvenBoundFromNP

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

namespace OrdinaryMellinModulus
open OrdinaryCorrelations OrdinaryLocalAdditive OrdinarySharpWindow OrdinaryChainScales Finset Filter MeasureTheory

theorem major_arcs_even_power_logarithmic :
    ∃ A c k v : ℕ, ∀ m : ℕ,
    ∀ {f : ℕ→ℂ}, OneBounded f → Multiplicative f → UniformlyNonpretentious f →
    let H := 2*sharpLogGate A c k (30*m+v)
    ∀ᶠ X : ℕ in atTop,
    ∀ D : ℝ, (2:ℝ)^(2*m)*H≤D →
    ∀q : ℕ, 0<q → q≤2^(10*m) →
    ∀a : ℤ, a∈Finset.Icc (-(2^(10*m):ℕ):ℤ) (2*(2^(10*m):ℕ):ℤ) →
    ∀α : ℝ, |α-(a:ℝ)/q|≤(1/2:ℝ)^(2*m)/(2*Real.pi*H) →
    (∫x : ℝ,‖sharpWindow (Ioc X (2*X))
      (fun n=>f n*phase (α*n)) (fun n=>(n:ℝ)) D x‖)
        ≤3*(1/2:ℝ)^(2*m)*D*X := by
  obtain ⟨A,c,k,v,hP⟩ := periodic_even_power_logarithmic
  refine ⟨A,c,k,v,?_⟩
  intro m f hf hm hNP
  let H := 2*sharpLogGate A c k (30*m+v)
  have hH : 0<H := mul_pos (by norm_num) (sharpLogGate_pos A c k _)
  let ε : ℝ := (1/2:ℝ)^(2*m)
  have hε : 0<ε := by dsimp [ε]; positivity
  let Q : ℕ := 2^(10*m)
  have hcenter (q : ℕ) (hq : q∈Finset.Icc 1 Q) (a : ℤ) :
      ∀ᶠ X : ℕ in atTop,
      (∫x : ℝ,‖sharpWindow (Ioc X (2*X))
        (fun n=>f n*phase ((a:ℝ)/q*n)) (fun n=>(n:ℝ)) H x‖)≤ε*H*X := by
    have hqp : 0<q := (Finset.mem_Icc.mp hq).1
    have ht := hP m hf hm hNP hqp (Finset.mem_Icc.mp hq).2
      (fun n=>phase ((a:ℝ)/q*n)) (fun n=>le_of_eq (norm_phase _)) H le_rfl
    have he : (fun n=>f n*phase ((a:ℝ)/q*(n%q:ℕ)))=
        (fun n=>f n*phase ((a:ℝ)/q*n)) := by
      funext n
      rw [phase_rational_mod a hqp n]
    simpa only [he] using ht
  have hall : ∀ᶠ X : ℕ in atTop, ∀q∈Finset.Icc 1 Q,
      ∀a∈Finset.Icc (-(Q:ℤ)) (2*(Q:ℤ)),
      (∫x : ℝ,‖sharpWindow (Ioc X (2*X))
        (fun n=>f n*phase ((a:ℝ)/q*n)) (fun n=>(n:ℝ)) H x‖)≤ε*H*X := by
    apply (eventually_all_finset (Icc 1 Q)).mpr
    intro q hq
    exact (eventually_all_finset (Icc (-(Q:ℤ)) (2*(Q:ℤ)))).mpr (fun a _=>hcenter q hq a)
  filter_upwards [hall] with X hX
  intro D hD q hq hqQ a ha α hα
  have hD0 : 0<D := (mul_pos (by positivity : 0<(2:ℝ)^(2*m)) hH).trans_le hD
  have hc := hX q (Finset.mem_Icc.mpr ⟨hq,hqQ⟩) a ha
  have hmass := dyadic_mass hf X
  have hphase := sharp_phase_l1 (Ioc X (2*X)) f (fun n=>(n:ℝ)) hH.le α ((a:ℝ)/q)
  have herr : 2*Real.pi*|α-(a:ℝ)/q| *H^2*(∑n∈Ioc X (2*X),‖f n‖)≤ε*H*X := by
    calc
      _ ≤2*Real.pi*(ε/(2*Real.pi*H))*H^2*(X:ℝ) := by gcongr
      _ = _ := by field_simp
  have hshort : (∫x : ℝ,‖sharpWindow (Ioc X (2*X))
      (fun n=>f n*phase (α*n)) (fun n=>(n:ℝ)) H x‖)≤2*ε*H*X := by
    nlinarith only [hc,hphase,herr]
  have hlong := sharpWindow_long_from_short (Ioc X (2*X))
    (fun n=>f n*phase (α*n)) (fun n=>(n:ℝ)) hH hD0.le
  have hm' := mul_le_mul_of_nonneg_left (dyadic_phase_mass hf α X) hH.le
  have hs := mul_le_mul_of_nonneg_left hshort (div_nonneg hD0.le hH.le)
  have he : D/H*(2*ε*H*X)=2*ε*D*X := by field_simp
  rw [he] at hs
  have hHle : H≤ε*D := by
    have ht := mul_le_mul_of_nonneg_left hD hε.le
    have hp : ε*(2:ℝ)^(2*m)=1 := by dsimp [ε]; rw [←mul_pow]; norm_num
    simpa only [←mul_assoc,hp,one_mul] using ht
  have hrem := mul_le_mul_of_nonneg_right hHle (Nat.cast_nonneg X)
  change _≤3*ε*D*X
  nlinarith only [hlong,hm',hs,hrem]

end OrdinaryMellinModulus

end

end OAI
