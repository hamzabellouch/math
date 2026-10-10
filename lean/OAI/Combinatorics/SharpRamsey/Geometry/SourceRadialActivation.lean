import Mathlib
import OAI.Combinatorics.SharpRamsey.Spatial.PreparedSpatialRadial

namespace OAI

section
namespace SharpLogRamsey.SourceRadialTests
open Filter Real
open scoped Topology
noncomputable section

theorem radial_activation {σ P g a : ℝ}
    (hP : 10000*(2:ℝ)^99 ≤ P) (ha : 0≤a) (ha2 : a≤2)
    (hk : exp (σ+P/100-2*g)<exp σ*a^99) :
    P/10000<g ∧ exp (-g/20)<a := by
  have he : exp (P/100-2*g)<a^99 := by
    apply (mul_lt_mul_iff_right₀ (exp_pos σ)).mp
    simpa only [←exp_add,show σ+(P/100-2*g)=σ+P/100-2*g by ring] using hk
  have hP0 : 0≤P := (by positivity : (0:ℝ)≤10000*(2:ℝ)^99).trans hP
  have hg : P/10000<g := by
    by_contra hh
    have hgg : g≤P/10000 := le_of_not_gt hh
    have hex : (2:ℝ)^99≤exp (P/100-2*g) := by
      have ht : (2:ℝ)^99≤P/100-2*g+1 := by nlinarith only [hP,hgg]
      exact ht.trans (add_one_le_exp _)
    have haa : a^99≤(2:ℝ)^99 := pow_le_pow_left₀ ha ha2 99
    linarith
  refine ⟨hg,?_⟩
  by_contra hh
  have haa : a≤exp (-g/20) := le_of_not_gt hh
  have hgg : 0≤g := by linarith
  have hpow : a^99≤exp (-99*g/20) := by
    calc
      _ ≤ (exp (-g/20))^99 := pow_le_pow_left₀ ha haa 99
      _ = exp (-99*g/20) := by rw [←exp_nat_mul]; congr 1; norm_num; ring
  have hh' : exp (-99*g/20)≤exp (P/100-2*g) := exp_le_exp.mpr (by linarith)
  exact (not_lt_of_ge (hpow.trans hh')) he

theorem eventually_activated_tests (δ C : ℝ) (hδ : 0<δ) :
    ∀ᶠ σ : ℝ in atTop, ∀ (P g a : ℝ) (N Kp : ℕ),
    σ^δ≤P → g≤σ/2+C → 0≤a → a≤2 →
    exp (3*σ/2+g)/2≤(N:ℝ) → (N:ℝ)≤exp (3*σ/2+g) →
    (Kp:ℝ)≤2*exp (σ+17*g/15) →
    exp (σ+P/100-2*g)<exp σ*a^99 →
    let M := ⌈a*(N:ℝ)/exp σ⌉₊
    4≤M ∧ M≤N ∧
    198*sqrt ((N:ℝ)/(M:ℝ))<(M:ℝ) ∧
    33*sqrt ((N:ℝ)/(M:ℝ))<exp σ ∧
    (N:ℝ)^2*exp (-5*sqrt ((N:ℝ)/(M:ℝ)))<1/2 ∧ 8*Kp≤M^2 := by
  filter_upwards [eventually_rich_tests δ C hδ,
    (tendsto_rpow_atTop hδ).eventually_ge_atTop (10000*(2:ℝ)^99)]
    with σ ht hp P g a N Kp hP hgu ha ha2 hN hN' hK hk
  have hh := radial_activation (hp.trans hP) ha ha2 hk
  exact ht g a N Kp ((div_le_div_of_nonneg_right hP (by norm_num)).trans hh.1.le)
    hgu hh.2.le ha2 hN hN' hK

theorem eventually_activated_list (δ : ℝ) (hδ : 0<δ) :
    ∀ᶠ σ : ℝ in atTop, ∀ (P g a : ℝ) (N J : ℕ),
    σ^δ≤P → 0≤a → a≤2 →
    exp (3*σ/2+g)/2≤(N:ℝ) → (J:ℝ)≤exp (σ/2-2*g/15) →
    exp (σ+P/100-2*g)<exp σ*a^99 →
    2*J≤⌈a*(N:ℝ)/exp σ⌉₊ := by
  have ht := (tendsto_rpow_atTop hδ).eventually_ge_atTop (10000*(2:ℝ)^99)
  filter_upwards [ht,eventually_ge_atTop (2:ℝ)] with σ hp hσ P g a N J hP ha ha2 hN hJ hk
  have hh := radial_activation (hp.trans hP) ha ha2 hk
  have hg : 100000≤g := by
    have hc : (100000:ℝ)≤(2:ℝ)^99 := by norm_num
    have hp' := hp.trans hP
    linarith only [hh.1,hp',hc]
  exact list_threshold hσ hg hh.2.le ha2 hN hJ

end
end SharpLogRamsey.SourceRadialTests

end

end OAI
