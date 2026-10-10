import Mathlib
import OAI.Combinatorics.UniformKServer.ComputedSuffix

namespace OAI

section
namespace UniformKServer.ComputedInstance
open EffectiveLP EpochShadow EpochPartition

variable {n k : ℕ}

def allDistances (d : RationalMetric n) : Finset ℚ :=
  Finset.univ.image (fun p : Fin n × Fin n => d.distance p.1 p.2)

def positiveDistances (d : RationalMetric n) : Finset ℚ :=
  (allDistances d).filter (0 < ·)

theorem allDistances_nonempty (hn : 2 ≤ n) (d : RationalMetric n) :
    (allDistances d).Nonempty := by
  exact ⟨d.distance ⟨0,by omega⟩ ⟨1,by omega⟩,
    Finset.mem_image.mpr ⟨(⟨0,by omega⟩,⟨1,by omega⟩), Finset.mem_univ _, rfl⟩⟩

theorem positiveDistances_nonempty (hn : 2 ≤ n) (d : RationalMetric n) :
    (positiveDistances d).Nonempty := by
  let x : Fin n := ⟨0,by omega⟩
  let y : Fin n := ⟨1,by omega⟩
  have hxy : x ≠ y := by intro h; have := congrArg Fin.val h; simp [x,y] at this
  have hp : 0 < d.distance x y := lt_of_le_of_ne (d.nonneg x y)
    (Ne.symm (fun h => hxy ((d.eq_zero x y).mp h)))
  exact ⟨d.distance x y, Finset.mem_filter.mpr
    ⟨Finset.mem_image.mpr ⟨(x,y), Finset.mem_univ _, rfl⟩, hp⟩⟩

def diameter (hn : 2 ≤ n) (d : RationalMetric n) : ℚ :=
  (allDistances d).max' (allDistances_nonempty hn d)

def separation (hn : 2 ≤ n) (d : RationalMetric n) : ℚ :=
  (positiveDistances d).min' (positiveDistances_nonempty hn d)

def canonical (hkn : k ≤ n) : Config n k :=
  ⟨Fin.castLE hkn, Fin.castLE_injective hkn⟩

def restart (hn : 2 ≤ n) (d : RationalMetric n) (k : ℕ) : ℕ :=
  ⌈(k:ℚ)*diameter hn d / separation hn d⌉₊

def cap (hn : 2 ≤ n) (d : RationalMetric n) (k : ℕ) : ℕ :=
  ⌈(restart hn d k : ℚ)*(k+1)*diameter hn d / separation hn d⌉₊

/-- Exact instance parameters and canonical start in the manuscript. -/
theorem parameters (hn : 2 ≤ n) (hk : 0 < k) (d : RationalMetric n) :
    0 ≤ (diameter hn d : ℝ) ∧ 0 < (separation hn d : ℝ) ∧
    (∀ x y, (d.distance x y : ℝ) ≤ diameter hn d) ∧
    (∀ x y, x ≠ y → (separation hn d : ℝ) ≤ d.distance x y) ∧
    0 < restart hn d k ∧
    (k:ℝ)*diameter hn d ≤ (restart hn d k : ℝ)*separation hn d ∧
    (restart hn d k : ℝ)*(k+1)*diameter hn d ≤
      ((cap hn d k : ℝ)+1)*separation hn d := by
  have hsQ : 0 < separation hn d :=
    (Finset.mem_filter.mp (Finset.min'_mem _ (positiveDistances_nonempty hn d))).2
  have hdiamQ : ∀ x y, d.distance x y ≤ diameter hn d := by
    intro x y
    exact Finset.le_max' (allDistances d) (d.distance x y)
      (Finset.mem_image.mpr ⟨(x,y),Finset.mem_univ _,rfl⟩)
  have hsepQ : ∀ x y, x ≠ y → separation hn d ≤ d.distance x y := by
    intro x y hxy
    apply Finset.min'_le
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_image.mpr ⟨(x,y),Finset.mem_univ _,rfl⟩, ?_⟩
    exact lt_of_le_of_ne (d.nonneg x y)
      (Ne.symm (fun h => hxy ((d.eq_zero x y).mp h)))
  have hsd : separation hn d ≤ diameter hn d := by
    obtain ⟨p,hp⟩ := positiveDistances_nonempty hn d
    have hm := Finset.min'_le _ p hp
    have hx : p ≤ diameter hn d :=
      Finset.le_max' _ _ (Finset.mem_filter.mp hp).1
    exact hm.trans hx
  have hdQ : 0 < diameter hn d := hsQ.trans_le hsd
  have hR : 0 < restart hn d k := by
    apply Nat.ceil_pos.mpr
    exact div_pos (mul_pos (by exact_mod_cast hk) hdQ) hsQ
  have hRDQ : (k:ℚ)*diameter hn d ≤ (restart hn d k : ℚ)*separation hn d := by
    apply (div_le_iff₀ hsQ).mp
    exact Nat.le_ceil _
  have hMQ : (restart hn d k : ℚ)*(k+1)*diameter hn d ≤
      (cap hn d k : ℚ)*separation hn d := by
    apply (div_le_iff₀ hsQ).mp
    exact Nat.le_ceil _
  have hcapQ : (restart hn d k : ℚ)*(k+1)*diameter hn d ≤
      ((cap hn d k : ℚ)+1)*separation hn d := by nlinarith
  refine ⟨?_, ?_, ?_, ?_, hR, ?_, ?_⟩
  · exact_mod_cast hdQ.le
  · exact_mod_cast hsQ
  · intro x y; exact_mod_cast hdiamQ x y
  · intro x y hxy; exact_mod_cast hsepQ x y hxy
  · exact_mod_cast hRDQ
  · exact_mod_cast hcapQ

/-- Prefix requests before deterministic activation use source label 1
(zero in Fin k); the raw suffix then uses the computed exact-bit epochs. -/
def prefixTrace [NeZero k] (w : List (Fin n)) : History n k :=
  w.map (fun r => (r,⟨0,NeZero.pos k⟩))

noncomputable def expected [NeZero k] (hn : 2 ≤ n) (hk : 0 < k) (hkn : k ≤ n)
    (d : RationalMetric n) (s : Configuration n k) (activation : ℕ)
    (w : List (Fin n)) : ℝ :=
  let pre := w.take (activation-1)
  let raw := w.drop (activation-1)
  let gp := prefixTrace pre
  costAlong d s gp +
    ComputedSuffix.expected d (canonical hkn) (cap hn d k) (finish s gp)
      (epochs k (restart hn d k) (parameters hn hk d).2.2.2.2.1 raw)

def coefficient [NeZero k] (hn : 2 ≤ n) (hkn : k ≤ n) (d : RationalMetric n) : ℚ :=
  AutomaticTable.coefficient d (canonical hkn) (horizon k (cap hn d k))

/-- The source full-movement estimate with the actually computed coefficient;
no unknown existence result or competitive coefficient is supplied as input. -/
theorem full_movement [NeZero k] (hn : 2 ≤ n) (hk : 2 ≤ k) (hkn : k ≤ n)
    (d : RationalMetric n) (s : Configuration n k) (activation : ℕ)
    (w : List (Fin n)) :
    expected hn (by omega) hkn d s activation w ≤
      (4*(coefficient hn hkn d : ℝ)+2)*offlineCost d s w +
      (activation-1 : ℕ)*(diameter hn d : ℝ) +
      (2*(coefficient hn hkn d : ℝ)+2)*k*(diameter hn d : ℝ) := by
  rcases parameters hn (show 0 < k by omega) d with
    ⟨hD,hδ,hdiam,hsep,hR,hRD,hcap⟩
  let pre := w.take (activation-1)
  let raw := w.drop (activation-1)
  let gp : History n k := prefixTrace pre
  have hcost : costAlong d s gp ≤ (pre.length : ℝ)*(diameter hn d : ℝ) := by
    change costAlong d s (prefixTrace pre) ≤ _
    induction pre generalizing s with
    | nil => simp [prefixTrace,costAlong]
    | cons r pre ih =>
      simp only [prefixTrace,List.map_cons,costAlong,List.length_cons,Nat.cast_add,Nat.cast_one]
      have ht := ih (serve s r ⟨0,NeZero.pos k⟩)
      have hd := hdiam (s ⟨0,NeZero.pos k⟩) r
      calc
        _ ≤ (diameter hn d : ℝ) + (pre.length : ℝ)*(diameter hn d : ℝ) :=
          add_le_add hd ht
        _ = _ := by ring
  have hlen : pre.length ≤ activation-1 := List.length_take_le _ _
  have hlenc : (pre.length : ℝ) ≤ (activation-1 : ℕ) := by exact_mod_cast hlen
  have hpre := hcost.trans (mul_le_mul_of_nonneg_right hlenc hD)
  have he := ComputedSuffix.suffix hk d (canonical hkn) (cap hn d k) (restart hn d k)
    hR (diameter hn d) (separation hn d) hD hδ.le hdiam hsep hcap hRD
    pre raw s (finish s gp)
  have hw : pre++raw = w := List.take_append_drop _ _
  rw [hw] at he
  change costAlong d s gp + ComputedSuffix.expected d (canonical hkn) (cap hn d k)
    (finish s gp) (epochs k (restart hn d k) hR raw) ≤ _
  change ComputedSuffix.expected d (canonical hkn) (cap hn d k)
    (finish s gp) (epochs k (restart hn d k) hR raw) ≤
    (4*(coefficient hn hkn d : ℝ)+2)*offlineCost d s w +
    (2*(coefficient hn hkn d : ℝ)+2)*k*(diameter hn d : ℝ) at he
  linarith

end UniformKServer.ComputedInstance

end



end OAI
