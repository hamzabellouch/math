import OAI.Geometry.NodalSets.Elliptic.LocalJetAlgebra

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set
open scoped ContDiff
noncomputable section

lemma near_one_product_jet_bound {U : Set Coord} (hU : IsOpen U)
    (A B : Coord → ℂ) (hA : ContDiffOn ℝ ∞ A U) (hB : ContDiffOn ℝ ∞ B U)
    {x : Coord} (hx : x ∈ U) (d : ℕ) {delta : ℝ} (hd0 : 0 ≤ delta) (hd1 : delta ≤ 1)
    (ha : ∀ j, j ≤ d → ‖iteratedFDeriv ℝ j (fun z ↦ A z-1) x‖ ≤ delta)
    (hb : ∀ j, j ≤ d → ‖iteratedFDeriv ℝ j (fun z ↦ B z-1) x‖ ≤ delta)
    (k : ℕ) (hk : k ≤ d) :
    ‖iteratedFDeriv ℝ k (fun z ↦ A z*B z-1) x‖ ≤ (2^d+2)*delta := by
  let f : Coord → ℂ := fun z ↦ A z-1
  let g : Coord → ℂ := fun z ↦ B z-1
  have hf : ContDiffOn ℝ ∞ f U := hA.sub contDiffOn_const
  have hg : ContDiffOn ℝ ∞ g U := hB.sub contDiffOn_const
  have hp := local_mul_jet_bound hU f g hf hg hx k hd0
    (fun j hj ↦ ha j (hj.trans hk)) (fun j hj ↦ hb j (hj.trans hk))
  have he : (fun z ↦ A z*B z-1) = ((fun z ↦ f z*g z)+f)+g := by
    funext z; dsimp [f,g]; ring
  have hs : (k:ℕ∞ω) ≤ ∞ := by exact_mod_cast (show (k:ℕ∞) ≤ ⊤ from le_top)
  have hfx := hf.contDiffAt (hU.mem_nhds hx)
  have hgx := hg.contDiffAt (hU.mem_nhds hx)
  rw [he,iteratedFDeriv_add_apply (f := (fun z ↦ f z*g z)+f) (g := g) (((hfx.mul hgx).add hfx).of_le hs) (hgx.of_le hs),
    iteratedFDeriv_add_apply (f := fun z ↦ f z*g z) (g := f) ((hfx.mul hgx).of_le hs) (hfx.of_le hs)]
  apply (norm_add_le _ _).trans
  apply (add_le_add (norm_add_le _ _) le_rfl).trans
  have hpow : (2:ℝ)^k ≤ 2^d := pow_le_pow_right₀ (by norm_num) hk
  have hsmall : 2^k*delta*delta ≤ 2^d*delta := by
    calc
      _ ≤ 2^d*delta*1 := mul_le_mul (mul_le_mul_of_nonneg_right hpow hd0) hd1 hd0 (by positivity)
      _ = _ := by ring
  exact (add_le_add (add_le_add (hp.trans hsmall) (ha k hk)) (hb k hk)).trans_eq (by ring)

end
end Yau.Geometry

end OAI
