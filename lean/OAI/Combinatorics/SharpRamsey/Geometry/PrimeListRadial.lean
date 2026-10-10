import Mathlib
import OAI.Combinatorics.SharpRamsey.Spatial.SpatialCertificates

namespace OAI

section
namespace SharpLogRamsey.PreparedProjectiveGeometry
open Finset Filter Real SourceRadialTests GreedyPreparation
open scoped Classical BigOperators Topology
noncomputable section

theorem prime_list_radial (δ C : ℝ) (hδ : 0<δ) :
    ∀ᶠ σ : ℝ in atTop,∀ (q : ℕ) [Fact q.Prime],∀ (F : Finset (Submodule (ZMod q) (Fin 4→ZMod q))) (m : ℕ)
    (S : Finset (Projectivization (ZMod q) (Fin 4→ZMod q))) (bs : List (Submodule (ZMod q) (Fin 4→ZMod q))),
    Complete F planePoints m S bs → (removed S planePoints bs).Nonempty →
    ∀ (P g : ℝ) (p : ℕ),σ^δ≤P → P≤σ/40 → g≤σ/2+C → 0<p → (p:ℝ)≤σ^2 →
    exp (3*σ/2+g)/2≤((removed S planePoints bs).card:ℝ) →
    ((removed S planePoints bs).card:ℝ)≤exp (3*σ/2+g) →
    (bs.length:ℝ)≤exp (σ/2-2*g/15) →
    let N := (removed S planePoints bs).card
    let c := exp σ/(N:ℝ)
    let X := fun x => removed S planePoints bs \ (own S planePoints bs x∪{x})
    let K₀ := exp (σ+P/100-2*g)
    ∃ D₀ D₁ : Finset (Projectivization (ZMod q) (Fin 4→ZMod q)),
      (D₀.card:ℝ)≤N*exp (-P/200) ∧ (D₁.card:ℝ)≤N*exp (5*P) ∧
      (∀ x,x∉D₀ → ∀ i∈range (Nat.log 2 N+2),
        ((richRadials (X x) x c (DyadicGrid.value i)).card:ℝ)*(DyadicGrid.value i)^100≤K₀) ∧
      (∀ x,x∉D₁ → (richRadials (X x) x c (1/(100*(p:ℝ)))).card=0 ∨
        2*(exp σ+1)/(1/(100*(p:ℝ)))≤(exp (3*σ)/N)*exp (-3*P)) := by
  have hpbound := ScaleSelection.eventually_polynomial_le_exp_rpow 400000000 4 δ 1 hδ (by norm_num)
  simp only [one_mul,rpow_ofNat] at hpbound
  filter_upwards [eventually_activated_tests δ C hδ,eventually_activated_list δ hδ,
    eventually_radial_loss δ C hδ,eventually_strong_tests δ C hδ,eventually_strong_list,
    hpbound,eventually_ge_atTop (1:ℝ)]
    with σ htests hlist hloss hstrong hstronglist hpoly hσ q _ F m S bs hprep hnon P g p hP hPu hgu hp hpu hNl hNu hJ
  let N := (removed S planePoints bs).card
  let c := exp σ/(N:ℝ)
  let K₀ := exp (σ+P/100-2*g)
  have hN : (0:ℝ)<N := Nat.cast_pos.mpr (card_pos.mpr hnon)
  have hc : 0<c := div_pos (exp_pos _) hN
  have hcN : c*N=exp σ := div_mul_cancel₀ _ hN.ne'
  have hceil (a : ℝ) : ⌈a/c⌉₊=⌈a*(N:ℝ)/exp σ⌉₊ := by
    dsimp [c]
    congr 1
    field_simp
  have ha i : DyadicGrid.value i≤2 := (DyadicGrid.value_le_one i).trans (by norm_num)
  obtain ⟨D₀,hD₀,hr⟩ := list_radial_exceptions F m S bs hprep c K₀ hc (exp_pos _).le
    (range (Nat.log 2 N+2)) DyadicGrid.value (fun i _ => DyadicGrid.value_pos i)
    (by
      intro i hi hh
      change K₀<c*N*(DyadicGrid.value i)^99 at hh
      rw [hcN] at hh
      rw [hceil]
      exact hlist P g (DyadicGrid.value i) N bs.length hP (DyadicGrid.value_pos i).le (ha i) hNl hJ hh)
    (by
      intro i hi hh
      change K₀<c*N*(DyadicGrid.value i)^99 at hh
      rw [hcN] at hh
      rw [hceil]
      exact (htests P g (DyadicGrid.value i) N 0 hP hgu (DyadicGrid.value_pos i).le (ha i) hNl hNu
        (by simp; positivity) hh).1)
  have hradial : (D₀.card:ℝ)≤N*exp (-P/200) := by
    apply hloss P g N D₀.card hP hNl hgu
    have hs := DyadicGrid.sum_pow_le_two (Nat.log 2 N+2) 98 (by norm_num)
    change (D₀.card:ℝ)*K₀≤8*(c*N)^2*∑ i∈range (Nat.log 2 N+2),(DyadicGrid.value i)^98 at hD₀
    rw [hcN] at hD₀
    calc
      _ ≤ 8*(exp σ)^2*2 := hD₀.trans (mul_le_mul_of_nonneg_left hs (by positivity))
      _ ≤ 70000*(exp σ)^2 := by nlinarith [sq_nonneg (exp σ)]
      _ = _ := by rw [←exp_nat_mul]; norm_num
  have hp' : (0:ℝ)<p := Nat.cast_pos.mpr hp
  have hp1 : (1:ℝ)≤p := by exact_mod_cast hp
  have hpolyp : 400000000*(p:ℝ)^2≤exp P := by
    calc
      _ ≤ 400000000*(σ^2)^2 := by gcongr
      _ = 400000000*σ^4 := by ring
      _ ≤ exp (σ^δ) := hpoly
      _ ≤ _ := exp_le_exp.mpr hP
  by_cases hsmall : (N:ℝ)≤exp (2*σ-4*P)
  · refine ⟨D₀,∅,hradial,by simp; positivity,hr,?_⟩
    intro x _
    right
    exact strong_small_support (by linarith) hN hsmall hp'
      (le_trans (by nlinarith : 400*(p:ℝ)≤400000000*(p:ℝ)^2) hpolyp)
  · have hgl : σ/2-4*P≤g := by
      have hh := (lt_of_not_ge hsmall).trans_le hNu
      have hh' := exp_lt_exp.mp hh
      linarith
    have ht := hstrong P g N 0 p hP hPu hgl hgu hp hpu hNl hNu (by simp; positivity)
    have hJ' := hstronglist P g N bs.length p hPu hgl hp hpu hNl hJ
    obtain ⟨D₁,hD₁,hzero⟩ := list_strong_exceptions F m S bs hprep c (1/(100*(p:ℝ))) hc
      (by positivity) (by simpa only [hceil] using hJ') (by simpa only [hceil] using ht.1)
    have hsize : (D₁.card:ℝ)≤N*exp (5*P) := by
      have hNl' : exp (2*σ-4*P)/2≤(N:ℝ) :=
        (half_le_self (exp_pos _).le).trans (le_of_not_ge hsmall)
      refine strong_exception_scale hp' hNl' ?_ hpolyp
      change (D₁.card:ℝ)*(1/(100*(p:ℝ)))^2≤8*(c*N)^2 at hD₁
      rw [hcN] at hD₁
      calc
        _ ≤ 8*(exp σ)^2 := hD₁
        _ ≤ 20000*(exp σ)^2 := by nlinarith [sq_nonneg (exp σ)]
        _ = _ := by rw [←exp_nat_mul]; norm_num
    exact ⟨D₀,D₁,hradial,hsize,hr,fun x hx => Or.inl (hzero x hx)⟩

end
end SharpLogRamsey.PreparedProjectiveGeometry

end

end OAI
