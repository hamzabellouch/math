import OAI.NumberTheory.DirichletL.Moments.FirstExceptionalPaidScales
import OAI.NumberTheory.DirichletL.Moments.FirstChildLower

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentFirstExceptionalChildPaid
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentAmplificationChildInput CenteredMomentFirstChildLower
open CenteredMomentAmplificationChildSourceCaps
open CenteredMomentFirstExceptionalPaidScales CenteredMomentCompleteCommon
local notation "O"=>HeckeFamily.O
variable {ι:Type*}[Fintype ι]
local instance {κ:Type*}:DecidableEq κ:=Classical.decEq _

def inputCap (Z:ℝ)(s:Input ι):ℝ:=
  min (min (Real.logb Z s.X₁) (Real.logb Z s.X₂))
    (min (Real.logb Z s.Y₁) (Real.logb Z s.Y₂))

lemma input_cap_lower (Z r:ℝ)(hZ:1<Z)(s:Input ι)
    (hX₁:Z^r≤s.X₁)(hX₂:Z^r≤s.X₂)(hY₁:Z^r≤s.Y₁)(hY₂:Z^r≤s.Y₂):
    r ≤ inputCap Z s:=by
  have h (x:ℝ)(hx:Z^r≤x):r≤Real.logb Z x:=by
    have hh:=Real.logb_le_logb_of_le hZ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) r) hx
    simpa only [Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne'] using hh
  exact le_min (le_min (h _ hX₁) (h _ hX₂)) (le_min (h _ hY₁) (h _ hY₂))

lemma input_cap_scales (Z:ℝ)(hZ:1<Z)(s:Input ι):
    Z^(inputCap Z s)≤s.X₁ ∧ Z^(inputCap Z s)≤s.X₂ ∧
      Z^(inputCap Z s)≤s.Y₁ ∧ Z^(inputCap Z s)≤s.Y₂:=by
  have hz:0<Z:=zero_lt_one.trans hZ
  have h (x:ℝ)(hx:0<x)(hl:inputCap Z s≤Real.logb Z x):Z^(inputCap Z s)≤x:=by
    calc
      _≤Z^(Real.logb Z x):=Real.rpow_le_rpow_of_exponent_le hZ.le hl
      _=x:=Real.rpow_logb hz hZ.ne' hx
  refine ⟨h _ s.X₁_pos ?_,h _ s.X₂_pos ?_,h _ s.Y₁_pos ?_,h _ s.Y₂_pos ?_⟩
  · exact (min_le_left _ _).trans (min_le_left _ _)
  · exact (min_le_left _ _).trans (min_le_right _ _)
  · exact (min_le_right _ _).trans (min_le_left _ _)
  · exact (min_le_right _ _).trans (min_le_right _ _)

theorem main_child_stage (Z A M:ℝ)(hZ:1<Z)(b:Branch Z)(hb:b.w=0)
    (s:Input ι)(R:Ideal O)
    (B:actualAllocations s.pools (commonPart b.I b.J))(τ:Character)(t:ℝ)
    (hX₁:Z^(M/4)≤s.X₁)(hX₂:Z^(M/4)≤s.X₂)
    (hY₁:Z^(M/4)≤s.Y₁)(hY₂:Z^(M/4)≤s.Y₂):
    let d:=child s (commonPart b.I b.J) R B τ t
    A-5*M/6-saving b-2*max (inputCap Z d) 0/3≤A-M+loss b:=by
  have hh:=child_lower s (commonPart b.I b.J) R (commonPart_ne_zero b.I b.J)
    B τ t Z (M/4) hZ hX₁ hX₂ hY₁ hY₂
  have hr:=input_cap_lower Z _ hZ _ hh.1 hh.2.1 hh.2.2.1 hh.2.2.2
  have hs:=actual_saving hZ b
  have hm:=le_max_left (inputCap Z (child s (commonPart b.I b.J) R B τ t)) (0:ℝ)
  dsimp only [removedWidth] at hs
  rw [hb] at hs
  dsimp only
  linarith

theorem error_child_stage (Z A M:ℝ)(hZ:1<Z)(b:Branch Z)
    (s:Input ι)(R:Ideal O)
    (B:actualAllocations s.pools (commonPart b.I b.J))(τ:Character)(t:ℝ)
    (Q:Ideal O)(hQ:Q≠0)(k:ℕ)
    (Bp:actualAllocations (child s (commonPart b.I b.J) R B τ t).pools (Q^k))
    (υ:Character)(v:ℝ)(hw:b.w=(k:ℝ)*Real.logb Z (Q.absNorm:ℝ))
    (hX₁:Z^(M/4)≤s.X₁)(hX₂:Z^(M/4)≤s.X₂)
    (hY₁:Z^(M/4)≤s.Y₁)(hY₂:Z^(M/4)≤s.Y₂):
    let d:=twiceChild s (commonPart b.I b.J) R B τ t Q k Bp υ v
    A-5*M/6-saving b-2*max (inputCap Z d) 0/3≤A-M+loss b:=by
  have hh:=twice_lower s (commonPart b.I b.J) R (commonPart_ne_zero b.I b.J)
    B τ t Q hQ k Bp υ v Z (M/4) hZ hX₁ hX₂ hY₁ hY₂
  have hr:=input_cap_lower Z _ hZ _ hh.1 hh.2.1 hh.2.2.1 hh.2.2.2
  have hs:=actual_saving hZ b
  have hm:=le_max_left (inputCap Z (twiceChild s (commonPart b.I b.J) R B τ t Q k Bp υ v)) (0:ℝ)
  dsimp only [removedWidth] at hs
  rw [hw] at hs
  dsimp only at hr ⊢
  linarith

theorem actual_error_pair (Z A M:ℝ)(hZ:1<Z)(b:Fin 2→Branch Z)
    (s:Input ι)(R:Ideal O)
    (B:∀j,actualAllocations s.pools (commonPart (b j).I (b j).J))
    (τ:Fin 2→Character)(t:Fin 2→ℝ)(Q:Fin 2→Ideal O)(hQ:∀j,Q j≠0)(k:Fin 2→ℕ)
    (Bp:∀j,actualAllocations
      (child s (commonPart (b j).I (b j).J) R (B j) (τ j) (t j)).pools ((Q j)^(k j)))
    (υ:Fin 2→Character)(v:Fin 2→ℝ)
    (hw:∀j,(b j).w=(k j:ℝ)*Real.logb Z ((Q j).absNorm:ℝ))
    (hX₁:Z^(M/4)≤s.X₁)(hX₂:Z^(M/4)≤s.X₂)
    (hY₁:Z^(M/4)≤s.Y₁)(hY₂:Z^(M/4)≤s.Y₂):
    let d:=fun j=>twiceChild s (commonPart (b j).I (b j).J) R
      (B j) (τ j) (t j) (Q j) (k j) (Bp j) (υ j) (v j)
    A-5*M/6-(saving (b 0)+saving (b 1))/2-
      (max (inputCap Z (d 0)) 0+max (inputCap Z (d 1)) 0)/3≤
      max (A-M) 0+(loss (b 0)+loss (b 1))/2:=by
  have h₀:=error_child_stage Z A M hZ (b 0) s R (B 0) (τ 0) (t 0) (Q 0) (hQ 0)
    (k 0) (Bp 0) (υ 0) (v 0) (hw 0) hX₁ hX₂ hY₁ hY₂
  have h₁:=error_child_stage Z A M hZ (b 1) s R (B 1) (τ 1) (t 1) (Q 1) (hQ 1)
    (k 1) (Bp 1) (υ 1) (v 1) (hw 1) hX₁ hX₂ hY₁ hY₂
  have hm:=le_max_left (A-M) (0:ℝ)
  dsimp only at h₀ h₁ ⊢
  linarith

end SevenEighths.CenteredMomentFirstExceptionalChildPaid

end

end OAI
