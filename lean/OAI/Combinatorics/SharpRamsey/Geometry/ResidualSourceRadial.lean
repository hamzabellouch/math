import Mathlib
import OAI.Combinatorics.SharpRamsey.Geometry.SourceStrongRadial

namespace OAI

section
namespace SharpLogRamsey.PreparedRadialResidual
open Finset Filter Real PreparedProjectiveGeometry SourceRadialTests
open scoped Classical BigOperators Topology
noncomputable section

theorem source_residual_radial (δ C : ℝ) (hδ : 0<δ) :
    ∀ᶠ σ : ℝ in atTop,∀ (q : ℕ) [Fact q.Prime],3≤q → exp σ=(q:ℝ) →
    ∀ (S : Finset (Projectivization (ZMod q) (Fin 4→ZMod q))),S.Nonempty →
    ∀ (X : Projectivization (ZMod q) (Fin 4→ZMod q)→Finset (Projectivization (ZMod q) (Fin 4→ZMod q))),
    (∀ x,X x⊆S) → ∀ (P g : ℝ) (Kp p : ℕ),
    σ^δ≤P → P≤σ/40 → g≤σ/2+C → 0<p → (p:ℝ)≤σ^2 →
    exp (3*σ/2+g)/2≤(S.card:ℝ) → (S.card:ℝ)≤exp (3*σ/2+g) →
    (Kp:ℝ)≤2*exp (σ+17*g/15) →
    (∀ f : (Fin 4→ZMod q)→ₗ[ZMod q] ZMod q,f≠0 →
       (S.filter (fun x => f x.rep=0)).card≤Kp) →
    let c := exp σ/(S.card:ℝ)
    let K₀ := exp (σ+P/100-2*g)
    ∃ D₀ D₁ : Finset (Projectivization (ZMod q) (Fin 4→ZMod q)),
      (D₀.card:ℝ)≤S.card*exp (-P/200) ∧
      (D₁.card:ℝ)≤S.card*exp (5*P) ∧
      (∀ x,x∉D₀ → ∀ i∈range (Nat.log 2 S.card+2),
        ((richRadials (X x) x c (DyadicGrid.value i)).card:ℝ)*(DyadicGrid.value i)^100≤K₀) ∧
      (∀ x,x∉D₁ → (richRadials (X x) x c (1/(100*(p:ℝ)))).card=0 ∨
        2*(exp σ+1)/(1/(100*(p:ℝ)))≤(exp (3*σ)/S.card)*exp (-3*P)) := by
  have hpbound := ScaleSelection.eventually_polynomial_le_exp_rpow 400000000 4 δ 1 hδ (by norm_num)
  simp only [one_mul,rpow_ofNat] at hpbound
  filter_upwards [eventually_activated_tests δ C hδ,eventually_radial_loss δ C hδ,
    eventually_strong_tests δ C hδ,hpbound,eventually_ge_atTop (1:ℝ)]
    with σ htests hloss hstrong hpoly hσ q _ hq heq S hS X hX P g Kp p hP hPu hgu hp hpu hNl hNu hK hcap
  let c := exp σ/(S.card:ℝ)
  let K₀ := exp (σ+P/100-2*g)
  have hN : (0:ℝ)<S.card := Nat.cast_pos.mpr (card_pos.mpr hS)
  have hc : 0<c := div_pos (exp_pos _) hN
  have hcN : c*S.card=exp σ := div_mul_cancel₀ _ hN.ne'
  have hceil (a : ℝ) : ⌈a/c⌉₊=⌈a*(S.card:ℝ)/exp σ⌉₊ := by
    dsimp [c]
    congr 1
    field_simp
  obtain ⟨D₀,hD₀,hr⟩ := residual_radial_exceptions hq S hS X hX c K₀ hc (exp_pos _).le Kp hcap
    (range (Nat.log 2 S.card+2)) DyadicGrid.value
    (fun i _ => DyadicGrid.value_pos i) (fun i _ => (DyadicGrid.value_le_one i).trans (by norm_num))
    (by
      intro i hi hh
      rw [hcN] at hh
      have ht := htests P g (DyadicGrid.value i) S.card Kp hP hgu
        (DyadicGrid.value_pos i).le ((DyadicGrid.value_le_one i).trans (by norm_num)) hNl hNu hK hh
      simpa only [hceil,heq] using ht)
  have hradial : (D₀.card:ℝ)≤S.card*exp (-P/200) := by
    apply hloss P g S.card D₀.card hP hNl hgu
    have hs := DyadicGrid.sum_pow_le_two (Nat.log 2 S.card+2) 98 (by norm_num)
    rw [←heq,hcN] at hD₀
    have hq1 : 1≤exp σ := one_le_exp_iff.mpr (by linarith)
    have hd : (D₀.card:ℝ)*K₀≤69744*(exp σ)^2 := by
      calc
        _ ≤ 17436*(exp σ+1)*exp σ*2 := mul_le_mul_of_nonneg_left hs (by positivity) |>.trans' hD₀
        _ ≤ _ := by nlinarith [sq_nonneg (exp σ-1)]
    have hsq : (exp σ)^2=exp (2*σ) := by rw [←exp_nat_mul]; norm_num
    rw [hsq] at hd
    exact hd.trans (mul_le_mul_of_nonneg_right (by norm_num) (exp_pos _).le)
  have hp' : (0:ℝ)<p := Nat.cast_pos.mpr hp
  have hp1 : (1:ℝ)≤p := by exact_mod_cast hp
  have hpolyp : 400000000*(p:ℝ)^2≤exp P := by
    calc
      _ ≤ 400000000*(σ^2)^2 := by gcongr
      _ = 400000000*σ^4 := by ring
      _ ≤ exp (σ^δ) := hpoly
      _ ≤ _ := exp_le_exp.mpr hP
  by_cases hsmall : (S.card:ℝ)≤exp (2*σ-4*P)
  · refine ⟨D₀,∅,hradial,by simp; positivity,hr,?_⟩
    intro x _
    right
    exact strong_small_support (by linarith) hN hsmall hp'
      (le_trans (by nlinarith : 400*(p:ℝ)≤400000000*(p:ℝ)^2) hpolyp)
  · have hgl : σ/2-4*P≤g := by
      have hh := (lt_of_not_ge hsmall).trans_le hNu
      have hh' := exp_lt_exp.mp hh
      linarith
    have ht := hstrong P g S.card Kp p hP hPu hgl hgu hp hpu hNl hNu hK
    let a : ℝ := 1/(100*(p:ℝ))
    have ha : 0<a := by dsimp [a]; positivity
    have ha1 : a≤1 := by dsimp [a]; apply (div_le_iff₀ (by positivity : (0:ℝ)<100*(p:ℝ))).mpr; linarith
    have ht' : 4≤⌈a/c⌉₊ ∧ ⌈a/c⌉₊≤S.card ∧
        198*sqrt ((S.card:ℝ)/⌈a/c⌉₊)<⌈a/c⌉₊ ∧
        33*sqrt ((S.card:ℝ)/⌈a/c⌉₊)<q ∧
        (S.card:ℝ)^2*exp (-5*sqrt ((S.card:ℝ)/⌈a/c⌉₊))<1/2 ∧ 8*Kp≤⌈a/c⌉₊^2 := by
      simpa only [hceil,heq] using ht
    obtain ⟨D₁,hD₁,hzero⟩ := residual_strong_exceptions hq S hS X hX c a hc ha.le Kp
      (by omega) ht'.2.1 hcap ht'.2.2.1 ht'.2.2.2.1 ht'.2.2.2.2.1 ht'.2.2.2.2.2
    have hsize : (D₁.card:ℝ)≤S.card*exp (5*P) := by
      have hNl' : exp (2*σ-4*P)/2≤(S.card:ℝ) :=
        (half_le_self (exp_pos _).le).trans (le_of_not_ge hsmall)
      refine strong_exception_scale hp' hNl' ?_ hpolyp
      rw [←heq,hcN] at hD₁
      have hq1 : 1≤exp σ := one_le_exp_iff.mpr (by linarith)
      calc
        _ ≤ 8718*(exp σ+1)*exp σ*a := hD₁
        _ ≤ 8718*(exp σ+1)*exp σ := mul_le_of_le_one_right (by positivity) ha1
        _ ≤ 20000*(exp σ)^2 := by nlinarith [sq_nonneg (exp σ-1)]
        _ = _ := by rw [←exp_nat_mul]; norm_num
    exact ⟨D₀,D₁,hradial,hsize,hr,fun x hx => Or.inl (hzero x hx)⟩

end
end SharpLogRamsey.PreparedRadialResidual

end

end OAI
