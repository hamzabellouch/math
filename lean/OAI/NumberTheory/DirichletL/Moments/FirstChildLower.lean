import OAI.NumberTheory.DirichletL.Moments.AmplificationChildSourceCaps
import OAI.NumberTheory.DirichletL.Moments.CommonExceptionalGates

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentFirstChildLower
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentCommonExceptionalGates CenteredMomentCommonAllocationSum
open CenteredMomentCommonProfile
local notation "O"=>HeckeFamily.O
variable {ι:Type*}[Fintype ι]
local instance {κ:Type*}:DecidableEq κ:=Classical.decEq _

theorem child_lower (s:Input ι)(C R:Ideal O)(hC:C≠0)
    (B:actualAllocations s.pools C)(τ:Character)(t Z r:ℝ)(hZ:1<Z)
    (hX₁:Z^r≤s.X₁)(hX₂:Z^r≤s.X₂)(hY₁:Z^r≤s.Y₁)(hY₂:Z^r≤s.Y₂):
    let d:=child s C R B τ t
    Z^(r-Real.logb Z (C.absNorm:ℝ))≤d.X₁ ∧
    Z^(r-Real.logb Z (C.absNorm:ℝ))≤d.X₂ ∧
    Z^(r-Real.logb Z (C.absNorm:ℝ))≤d.Y₁ ∧
    Z^(r-Real.logb Z (C.absNorm:ℝ))≤d.Y₂:=by
  exact ⟨extracted_lower s C hC B (Sum.inr 0) Z r s.X₁ hZ hX₁,
    extracted_lower s C hC B (Sum.inr 1) Z r s.X₂ hZ hX₂,
    extracted_lower s C hC B (Sum.inr 0) Z r s.Y₁ hZ hY₁,
    extracted_lower s C hC B (Sum.inr 1) Z r s.Y₂ hZ hY₂⟩

theorem twice_lower (s:Input ι)(C R:Ideal O)(hC:C≠0)
    (B:actualAllocations s.pools C)(τ:Character)(t:ℝ)
    (Q:Ideal O)(hQ:Q≠0)(k:ℕ)
    (Bp:actualAllocations (child s C R B τ t).pools (Q^k))
    (υ:Character)(v Z r:ℝ)(hZ:1<Z)
    (hX₁:Z^r≤s.X₁)(hX₂:Z^r≤s.X₂)(hY₁:Z^r≤s.Y₁)(hY₂:Z^r≤s.Y₂):
    let d:=twiceChild s C R B τ t Q k Bp υ v
    let r':=r-Real.logb Z (C.absNorm:ℝ)-(k:ℝ)*Real.logb Z (Q.absNorm:ℝ)
    Z^r'≤d.X₁ ∧ Z^r'≤d.X₂ ∧ Z^r'≤d.Y₁ ∧ Z^r'≤d.Y₂:=by
  have hc:=child_lower s C R hC B τ t Z r hZ hX₁ hX₂ hY₁ hY₂
  have hp:=child_lower (child s C R B τ t) (Q^k) (R*C) (pow_ne_zero k hQ)
    Bp υ v Z (r-Real.logb Z (C.absNorm:ℝ)) hZ hc.1 hc.2.1 hc.2.2.1 hc.2.2.2
  have hnorm:(Q.absNorm:ℝ)>0:=by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hQ)
  have he:Real.logb Z ((Q^k).absNorm:ℝ)=(k:ℝ)*Real.logb Z (Q.absNorm:ℝ):=by
    rw [map_pow,Nat.cast_pow,Real.logb_pow]
  simpa only [he,twiceChild] using hp

theorem removed_width_cap (L c w:ℝ):
    (2/3:ℝ)*(c+w)+(2/3:ℝ)*max (L-c-w) 0≥(2/3:ℝ)*L:=by
  have h:=le_max_left (L-c-w) 0
  linarith

theorem paired_removed_width_cap (L c₁ w₁ c₂ w₂:ℝ):
    ((c₁+w₁)+(c₂+w₂))/3+
      (max (L-c₁-w₁) 0+max (L-c₂-w₂) 0)/3≥(2/3:ℝ)*L:=by
  have h₁:=le_max_left (L-c₁-w₁) 0
  have h₂:=le_max_left (L-c₂-w₂) 0
  linarith

end SevenEighths.CenteredMomentFirstChildLower

end

end OAI
