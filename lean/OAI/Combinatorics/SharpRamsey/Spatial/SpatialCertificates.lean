import Mathlib
import OAI.Combinatorics.SharpRamsey.Spatial.SpatialRow

namespace OAI

section
namespace SharpLogRamsey.SpatialLearning
open Finset Real Filter PreparedProjectiveGeometry GreedyPreparation
open scoped Classical BigOperators Topology
noncomputable section
variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
local instance flat_JoinedSpatialCertificates_1 : Finite (Projectivization K V) := by
  let : Finite V := Module.finite_of_finite K
  infer_instance
local instance flat_JoinedSpatialCertificates_2 : Fintype (Projectivization K V) := Fintype.ofFinite _

theorem low_radial (S : Finset (Projectivization K V)) (hS : S.Nonempty)
    (X : Projectivization K V→Finset (Projectivization K V)) (hX : ∀ x,X x⊆S)
    (σ P g : ℝ) (p : ℕ) (hσ : 0≤σ) (hP : 0≤P) (hPu : P≤σ/40)
    (hg : g≤P/10000) (hp : 0<p) (hpoly : 400*(p:ℝ)≤exp P)
    (hNup : (S.card:ℝ)≤exp (3*σ/2+g)) :
    let c := exp σ/(S.card:ℝ)
    (∀ x,∀ i∈range (Nat.log 2 S.card+2),
      ((richRadials (X x) x c (DyadicGrid.value i)).card:ℝ)*(DyadicGrid.value i)^100≤
        exp (σ+P/100-2*g)) ∧
    2*(exp σ+1)/(1/(100*(p:ℝ)))≤(exp (3*σ)/S.card)*exp (-3*P) := by
  dsimp only
  have hN : (0:ℝ)<S.card := by exact_mod_cast card_pos.mpr hS
  have hsmall : (S.card:ℝ)≤exp (2*σ-4*P) := hNup.trans (exp_le_exp.mpr (by linarith))
  refine ⟨?_,SourceRadialTests.strong_small_support hσ hN hsmall (by exact_mod_cast hp) hpoly⟩
  intro x i _
  have hc : 0≤exp σ/(S.card:ℝ) := by positivity
  have ht := richRadials_mul_le (X x) x (exp σ/(S.card:ℝ)) (DyadicGrid.value i) hc
  have ht' : ((richRadials (X x) x (exp σ/(S.card:ℝ)) (DyadicGrid.value i)).card:ℝ)*
      DyadicGrid.value i≤exp σ := by
    apply ht.trans
    calc
      _ ≤ (exp σ/(S.card:ℝ))*(S.card:ℝ) :=
        mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (card_le_card (hX x))) hc
      _ = exp σ := div_mul_cancel₀ _ hN.ne'
  calc
    _ = (((richRadials (X x) x (exp σ/(S.card:ℝ)) (DyadicGrid.value i)).card:ℝ)*
        DyadicGrid.value i)*(DyadicGrid.value i)^99 := by ring
    _ ≤ exp σ*(DyadicGrid.value i)^99 := mul_le_mul_of_nonneg_right ht' (pow_nonneg (DyadicGrid.value_pos i).le _)
    _ ≤ exp σ*1 := mul_le_mul_of_nonneg_left
      (pow_le_one₀ (DyadicGrid.value_pos i).le (DyadicGrid.value_le_one i)) (exp_pos _).le
    _ ≤ exp (σ+P/100-2*g) := by rw [mul_one]; exact exp_le_exp.mpr (by linarith)

theorem list_radial (δ C : ℝ) (hδ : 0<δ) :
    ∀ᶠ σ : ℝ in atTop,∀ (F : Finset (Submodule K V)) (m : ℕ)
    (S : Finset (Projectivization K V)) (bs : List (Submodule K V)),
    Complete F planePoints m S bs → (removed S planePoints bs).Nonempty →
    ∀ (P g : ℝ) (p : ℕ),σ^δ≤P → P≤σ/40 → g≤σ/2+C → 0<p → (p:ℝ)≤σ^2 →
    exp (3*σ/2+g)/2≤((removed S planePoints bs).card:ℝ) →
    ((removed S planePoints bs).card:ℝ)≤exp (3*σ/2+g) →
    (bs.length:ℝ)≤exp (σ/2-2*g/15) →
    let S' := removed S planePoints bs
    let c := exp σ/(S'.card:ℝ)
    ∃ D₀ D₁ : Finset (Projectivization K V),
      (D₀.card:ℝ)≤S'.card*exp (-P/200) ∧ (D₁.card:ℝ)≤S'.card*exp (5*P) ∧
      (∀ x,x∉D₀ → ∀ i∈range (Nat.log 2 S'.card+2),
        ((richRadials (S'\(own S' planePoints bs x∪{x})) x c (DyadicGrid.value i)).card:ℝ)*
          (DyadicGrid.value i)^100≤exp (σ+P/100-2*g)) ∧
      (∀ x,x∉D₁ → (richRadials (S'\(own S' planePoints bs x∪{x})) x c (1/(100*(p:ℝ)))).card=0 ∨
        2*(exp σ+1)/(1/(100*(p:ℝ)))≤(exp (3*σ)/S'.card)*exp (-3*P)) := by
  filter_upwards [source_list_radial (K:=K) (V:=V) δ C hδ] with σ hs
  intro F m S bs hbs hn P g p hP hPu hg hp hpu hNl hNu hJ
  simpa only [own_removed] using hs F m S bs hbs hn P g p hP hPu hg hp hpu hNl hNu hJ

end
end SharpLogRamsey.SpatialLearning

end

end OAI
