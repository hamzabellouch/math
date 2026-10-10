import Mathlib
import OAI.Combinatorics.KMedian.Preparation.RationalRepresentatives

namespace OAI


                                         
section
namespace MetricKMedian.Preparation
open Finset

structure RationalUnitInput (f j : ℕ) where
  y : Fin f → ℚ
  F : Fin j → Finset (Fin f)
  dc : Fin j → Fin f → ℚ
  dd : Fin j → Fin j → ℚ
  df : Fin f → Fin f → ℚ
  hy : ∀ a, 0<y a
  hy1 : ∀ a, y a≤1
  hu : ∀ c, ∑ a ∈ F c, y a=1
  hdc : ∀ c a, 0≤dc c a
  hdd : ∀ c, dd c c=0
  hsymm : ∀ c c', dd c c'=dd c' c
  hnear : ∀ c, ∀ a ∈ F c, ∀ b ∉ F c, dc c a≤dc c b

namespace RationalUnitInput
variable {f j : ℕ} (U : RationalUnitInput f j)

def V (c : Fin j) : ℚ := ∑ a ∈ U.F c, U.y a*U.dc c a

theorem V_nonneg (c : Fin j) : 0≤U.V c :=
  sum_nonneg (fun a _ => mul_nonneg (U.hy a).le (U.hdc c a))

def representatives (M : ℚ) := RationalRepresentatives.representatives U.dd U.V M

def ridx (M : ℚ) : Fin (U.representatives M).card → Fin j :=
  (U.representatives M).orderEmbOfFin rfl

theorem representative_separation (M : ℚ) (hM : 0≤M) :
    ∀ t u, t≠u → M*max (U.V (U.ridx M t)) (U.V (U.ridx M u)) <
      U.dd (U.ridx M t) (U.ridx M u) := by
  intro t u htu
  have hh := (RationalRepresentatives.representatives_spec U.dd U.V M U.hdd U.hsymm hM U.V_nonneg).1
  exact hh ((U.representatives M).orderEmbOfFin_mem rfl t)
    ((U.representatives M).orderEmbOfFin_mem rfl u)
    (fun h => htu ((U.representatives M).orderEmbOfFin rfl |>.injective h))

theorem representative_cover (M : ℚ) (hM : 0≤M) (c : Fin j) :
    ∃ t, U.V (U.ridx M t)≤U.V c ∧ U.dd c (U.ridx M t)≤M*U.V c := by
  obtain ⟨s,hs,hV,hd⟩ :=
    (RationalRepresentatives.representatives_spec U.dd U.V M U.hdd U.hsymm hM U.V_nonneg).2 c
  let t := ((U.representatives M).orderIsoOfFin rfl).symm ⟨s,hs⟩
  have ht : U.ridx M t=s := congrArg Subtype.val
    (((U.representatives M).orderIsoOfFin rfl).apply_symm_apply ⟨s,hs⟩)
  exact ⟨t,ht ▸ hV,ht ▸ hd⟩

structure Realization (X : Type) [PseudoMetricSpace X] where
  i : Fin f → X
  c : Fin j → X
  hdf : ∀ a b, dist (i a) (i b)=(U.df a b:ℝ)
  hdc : ∀ c' a, dist (c c') (i a)=(U.dc c' a:ℝ)
  hdd : ∀ c' c'', dist (c c') (c c'')=(U.dd c' c'':ℝ)

end RationalUnitInput
end MetricKMedian.Preparation
end

end OAI
