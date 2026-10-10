import Mathlib
import OAI.Combinatorics.SharpRamsey.Spatial.SpatialGreedy
import OAI.Combinatorics.SharpRamsey.Geometry.PrimeListRadial

namespace OAI

section
namespace SharpLogRamsey.SpatialLearning
open Finset Real Filter PreparedProjectiveGeometry GreedyPreparation
open scoped Classical BigOperators Topology
noncomputable section

theorem prepared_input (δ C : ℝ) (hδ : 0<δ) :
    ∀ᶠ σ : ℝ in atTop,∀ (q : ℕ) [Fact q.Prime],3≤q → exp σ=(q:ℝ) →
    ∀ (S : Finset (Projectivization (ZMod q) (Fin 4→ZMod q))),S.Nonempty →
    ∀ (P g : ℝ) (p : ℕ),σ^δ≤P → P≤σ/40 → g≤σ/2+C → 0<p → (p:ℝ)≤σ^2 →
    (S.card:ℝ)=exp (3*σ/2+g) →
    (∃ W : Submodule (ZMod q) (Fin 4→ZMod q),Module.finrank (ZMod q) W=3 ∧
      (S.card:ℝ)/50≤(S∩planePoints W).card) ∨
    (∃ (S' : Finset (Projectivization (ZMod q) (Fin 4→ZMod q)))
      (bs : List (Submodule (ZMod q) (Fin 4→ZMod q))),
      S'⊆S ∧ S'.Nonempty ∧ S.card≤2*S'.card ∧
      (bs.length:ℝ)≤exp (σ/2-2*g/15) ∧
      (∀ W∈bs,Module.finrank (ZMod q) W=3) ∧
      (∀ i : Fin bs.length,((indexedCell S' planePoints bs i).card:ℝ)/(S'.card:ℝ)≤1/25) ∧
      ∃ D₀ D₁ : Finset (Projectivization (ZMod q) (Fin 4→ZMod q)),
        (D₀.card:ℝ)≤S'.card*exp (-P/200) ∧ (D₁.card:ℝ)≤S'.card*exp (5*P) ∧
        (∀ x,x∉D₀ → ∀ i∈range (Nat.log 2 S'.card+2),
          ((richRadials (S'\(own S' planePoints bs x∪{x})) x (exp σ/(S'.card:ℝ))
            (DyadicGrid.value i)).card:ℝ)*(DyadicGrid.value i)^100≤exp (σ+P/100-2*g)) ∧
        (∀ x,x∉D₁ →
          (richRadials (S'\(own S' planePoints bs x∪{x})) x (exp σ/(S'.card:ℝ))
            (1/(100*(p:ℝ)))).card=0 ∨
          2*(exp σ+1)/(1/(100*(p:ℝ)))≤(exp (3*σ)/S'.card)*exp (-3*P))) := by
  have hpoly := ScaleSelection.eventually_polynomial_le_exp_rpow 400 2 δ 1 hδ (by norm_num)
  simp only [one_mul,rpow_ofNat] at hpoly
  filter_upwards [PreparedRadialResidual.source_residual_radial δ C hδ,
    prime_list_radial δ C hδ,hpoly,eventually_ge_atTop (1:ℝ)] with σ hres hlist hpol hσ
  intro q _ hq heq S hS P g p hP hPu hgu hp hpu hN
  have hdim : Module.finrank (ZMod q) (Fin 4→ZMod q)=4 := by simp
  have hP0 : 0≤P := (rpow_nonneg (by linarith : 0≤σ) δ).trans hP
  have hNl : exp (3*σ/2+g)/2≤(S.card:ℝ) := by rw [hN]; exact half_le_self (exp_pos _).le
  by_cases hg : g≤P/10000
  · right
    refine ⟨S,[],Subset.rfl,hS,by omega,by simp; positivity,by simp,by simp,∅,∅,?_,?_,?_,?_⟩
    · simp; positivity
    · simp; positivity
    · have hh := low_radial S hS (fun x => S\(own S planePoints [] x∪{x}))
        (fun _ => sdiff_subset) σ P g p (by linarith) hP0 hPu hg hp
        ((mul_le_mul_of_nonneg_left hpu (by norm_num)).trans (hpol.trans (exp_le_exp.mpr hP))) hN.le
      exact fun x _ => hh.1 x
    · have hh := low_radial S hS (fun x => S\(own S planePoints [] x∪{x}))
        (fun _ => sdiff_subset) σ P g p (by linarith) hP0 hPu hg hp
        ((mul_le_mul_of_nonneg_left hpu (by norm_num)).trans (hpol.trans (exp_le_exp.mpr hP))) hN.le
      exact fun _ _ => Or.inr hh.2
  · have hg0 : 0≤g := by linarith
    rcases greedy hdim S hS σ g (by linarith) hg0 hN with hh|⟨S',hsub,hn,hhalf,hm,hcap⟩|⟨bs,hbs,hn,hhalf,hJ,hcell⟩
    · exact Or.inl hh
    · right
      have hNu' : (S'.card:ℝ)≤exp (3*σ/2+g) := (Nat.cast_le.mpr (card_le_card hsub)).trans hN.le
      have hNl' : exp (3*σ/2+g)/2≤(S'.card:ℝ) := by
        have hh : (S.card:ℝ)≤2*S'.card := by exact_mod_cast hhalf
        rw [hN] at hh
        linarith
      refine ⟨S',[],hsub,hn,hhalf,by simp; positivity,by simp,by simp,?_⟩
      exact hres q hq heq S' hn (fun x => S'\(own S' planePoints [] x∪{x}))
        (fun _ => sdiff_subset) P g _ p hP hPu hgu hp hpu hNl' hNu' hm (by
          intro f hf
          convert hcap f hf using 1
          congr 1
          ext x
          simp only [mem_filter])
    · right
      have hNu' : ((removed S planePoints bs).card:ℝ)≤exp (3*σ/2+g) :=
        (Nat.cast_le.mpr (card_le_card (removed_subset S planePoints bs))).trans hN.le
      have hNl' : exp (3*σ/2+g)/2≤((removed S planePoints bs).card:ℝ) := by
        have hh : (S.card:ℝ)≤2*(removed S planePoints bs).card := by exact_mod_cast hhalf
        rw [hN] at hh
        linarith
      refine ⟨removed S planePoints bs,bs,removed_subset S planePoints bs,hn,hhalf,hJ,?_,hcell,?_⟩
      · intro W hW
        exact (mem_filter.mp (complete_members hbs W hW)).2
      · simpa only [own_removed] using hlist q _ _ S bs hbs hn P g p hP hPu hgu hp hpu hNl' hNu' hJ

end
end SharpLogRamsey.SpatialLearning

end

end OAI
