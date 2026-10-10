import OAI.NumberTheory.Ostmann.Preliminaries.WindowTestStability

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters
open Ostmann.Preliminaries Filter

theorem eventually_subset_A_test_stability (d:Decomposition) (k:ℕ) (hk:4≤k) :
    ∀ᶠ X:ℕ in atTop, ∀ S:Finset ℕ, S⊆upperWindow d.A X →
      Real.sqrt X/Real.log (X:ℝ)^k≤(S.card:ℝ) →
      ∀ f:(p:PrimeUpTo (collisionScale k X))→ZMod p.val→ℂ,
      (∀p,∑r,‖f p r‖^2≤p.val) →
      (∑p:PrimeUpTo (collisionScale k X), (Real.log p.val/p.val)*
        ‖(∑a∈S,f p (a:ZMod p.val))/(S.card:ℂ)-
          (∑r∈d.residueSupport p.val,f p r)/((d.residueSupport p.val).card:ℂ)‖^2)
        ≤collisionConstant k*Real.log (Real.log (X:ℝ)) := by
  classical
  filter_upwards [eventually_upperWindow_mass_cap d,
    eventually_upperWindow_large d.cutoff, eventually_collision_bound_conditions k]
    with X hcap hlarge hcond
  intro S hS hcard f hf
  have hxr : (0:ℝ)<X := by exact_mod_cast hcond.1
  have hsqrt : 0<Real.sqrt X := Real.sqrt_pos.mpr hxr
  have hlog : 0<Real.log (X:ℝ) := lt_of_lt_of_le (by norm_num) hcond.2.1
  have hSpos : (0:ℝ)<S.card := (div_pos hsqrt (pow_pos hlog _)).trans_le hcard
  have hSnz : (S.card:ℝ)≠0 := hSpos.ne'
  let μ : S→ℝ := fun _ => (S.card:ℝ)⁻¹
  have hμ0 : ∀i,0≤μ i := fun _ => by dsimp [μ]; positivity
  have hμsum : ∑i:S,μ i=1 := by simp [μ,hSnz]
  have hμcap : ∀i,μ i≤collisionMassCap k X := by
    intro i
    change (S.card:ℝ)⁻¹≤Real.log (X:ℝ)^k/Real.sqrt X
    rw [inv_eq_one_div]
    apply (div_le_div_iff₀ hSpos hsqrt).mpr
    have hh := (div_le_iff₀ (pow_pos hlog k)).mp hcard
    nlinarith
  have hνcap : ∀i:upperWindow d.B X,
      uniformWindowMass d.B X i≤collisionMassCap k X := by
    intro i
    apply (hcap.2.2.2 i).trans
    exact div_le_div_of_nonneg_right
      (pow_le_pow_right₀ hcond.2.1 hk) hsqrt.le
  have hcoll := collisionStability_le_loglog d k X hcond.1 hcond.2.1
    hcond.2.2.1 hcond.2.2.2 (fun i:S=>i.val) μ
    (fun i:upperWindow d.B X=>i.val) (uniformWindowMass d.B X)
    Subtype.val_injective Subtype.val_injective
    (fun i=>(mem_upperWindow.mp (hS i.property)).2.1)
    (fun i=>(mem_upperWindow.mp i.property).2.1)
    hμ0 (uniformWindowMass_nonneg d.B X) hμsum (uniformWindowMass_sum d.B X hcap.2.1)
    (fun i _=>(mem_upperWindow.mp (hS i.property)).1)
    (fun i _=>(mem_upperWindow.mp i.property).1)
    (fun i _=>hlarge.trans_le (mem_upperWindow.mp (hS i.property)).2.2)
    (fun i _=>hlarge.trans_le (mem_upperWindow.mp i.property).2.2) hμcap hνcap
  have htest := (weighted_A_test_error_le d (collisionScale k X)
    (fun i:S=>i.val) μ (fun i:upperWindow d.B X=>i.val)
    (uniformWindowMass d.B X) f hf).trans hcoll
  have hav (p:PrimeUpTo (collisionScale k X)) :
      (∑i:S,(μ i:ℂ)*f p (i.val:ZMod p.val))=
        (∑a∈S,f p (a:ZMod p.val))/(S.card:ℂ) := by
    have hsum : (∑i:S,f p (i.val:ZMod p.val))=∑a∈S,f p (a:ZMod p.val) :=
      Finset.sum_coe_sort S (fun a:ℕ=>f p (a:ZMod p.val))
    simp only [μ, Complex.ofReal_inv, Complex.ofReal_natCast,
      ← Finset.mul_sum, hsum, div_eq_mul_inv]
    ring
  simpa only [hav, uniformMass_complex_average] using htest

end Ostmann.Characters

end

end OAI
