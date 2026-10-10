import Mathlib
import OAI.Combinatorics.UniformKServer.AdaptiveAlpha
import OAI.Combinatorics.UniformKServer.EpochParameters

namespace OAI

                                 
section

/-! Source logarithmic configurations are built on the actual active-size
 domain, including the automatic one-point domain. -/
noncomputable section
namespace UniformKServer.EpochAlpha
open Finset
open scoped Classical
variable {ι : Type*} [Fintype ι]

def ell (k : ℕ) : ℝ := 1+Real.log (k+1)

theorem ell_one (k : ℕ) : 1 ≤ ell k := by
  unfold ell
  have h : (1:ℝ) ≤ k+1 := by linarith [Nat.cast_nonneg (α:=ℝ) k]
  linarith [Real.log_nonneg h]

theorem height_upper {A ai : ℝ} {k : ℕ} (hA : 0 < A)
    (hAk : A ≤ 2*k) (hai : (9/100000:ℝ) ≤ ai) :
    SideParameters.height A ai ≤ 50000*ell k := by
  have hkp : (0:ℝ) < k+1 := by positivity
  have hip : 0 < ai := by linarith
  have hrat : A/ai ≤ 40000*(k+1) := by
    apply (div_le_iff₀ hip).mpr
    have hkn : (0:ℝ) ≤ k := by positivity
    have hmul := mul_le_mul_of_nonneg_left hai (show 0 ≤ 40000*((k:ℝ)+1) by positivity)
    nlinarith
  have hlog := Real.log_le_log (div_pos hA hip) hrat
  rw [Real.log_mul (by norm_num : (40000:ℝ) ≠ 0) hkp.ne'] at hlog
  have hc := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<40000)
  have hl := Real.log_nonneg (show (1:ℝ) ≤ k+1 by linarith [Nat.cast_nonneg (α:=ℝ) k])
  unfold SideParameters.height ell
  linarith

/-- Exact h on all regular coordinates; no clamped-log discrepancy occurs
 because the epoch geometry proves ai < A. -/
def regular (a : ι → ℝ) (A ell ct C : ℝ) : AdaptiveAlpha.Config ι where
  active := EpochParameters.active a
  param := ⟨.regular,fun i => SideParameters.height A (a i),ell,ct,C⟩

def marked (a : ι → ℝ) (A U ell ct C : ℝ) (o : EpochParameters.active a) :
    AdaptiveAlpha.Config ι := by
  exact ⟨EpochParameters.active a,
    ⟨.marked o (U/A),fun i => if i=o then U/A else SideParameters.height A (a i),ell,ct,C⟩⟩

def singleton (a : ι → ℝ) (ell ct C : ℝ) (o : EpochParameters.active a) :
    AdaptiveAlpha.Config ι where
  active := EpochParameters.active a
  param := ⟨.singleton o,fun _ => 0,ell,ct,C⟩

theorem eta_bound {ct h ell : ℝ} (hc : 0 < ct) (hl : 0 < ell)
    (hct : ct*50000 ≤ 1) (hh : h ≤ 50000*ell) : ct*h/ell ≤ 1 := by
  apply (div_le_iff₀ hl).mpr
  have hm := mul_le_mul_of_nonneg_left hh hc.le
  have hm' := mul_le_mul_of_nonneg_right hct hl.le
  nlinarith

theorem regular_valid {a : ι → ℝ} {s : EpochGeometry.State ι}
    (hs : EpochGeometry.valid a s) (ha : ∀ i, 0 ≤ a i)
    (hne : (EpochParameters.active a).Nonempty) (ho : EpochGeometry.dominant s=none)
    {ell ct C : ℝ} (hl : 0 < ell) (hc : 0 < ct) (hct : ct*50000 ≤ 1)
    (hC : 1000 < C*ct)
    (hheight : ∀ i : EpochParameters.active a,
      SideParameters.height (EpochGeometry.total s.base) (a i) ≤ 50000*ell) :
    AdaptiveAlpha.valid (regular a (EpochGeometry.total s.base) ell ct C) := by
  have hA : 0 < EpochGeometry.total s.base := by
    obtain ⟨i,hi⟩ := hne
    exact EpochParameters.active_total_pos hs (EpochParameters.mem_active.mp hi)
  refine ⟨hne,hl,hc,hC,?_,?_,?_⟩
  · intro i
    exact eta_bound hc hl hct (hheight i)
  · intro i
    exact EpochParameters.regular_height hs (EpochParameters.mem_active.mp i.property) (by simp [ho])
  · exact EpochParameters.regular_exponential_sum hs ha hA

theorem marked_valid {a : ι → ℝ} {s : EpochGeometry.State ι}
    (hs : EpochGeometry.valid a s) (ha : ∀ i, 0 ≤ a i)
    (o : EpochParameters.active a) (ho : EpochGeometry.dominant s=some o.val)
    {U ell ct C : ℝ} (hU : EpochParameters.sideReference a o U) (hUp : 0 < U)
    (hl : 1 ≤ ell) (hc : 0 < ct) (hct : ct*50000 ≤ 1) (hC : 1000 < C*ct)
    (hheight : ∀ i : EpochParameters.active a,
      SideParameters.height (EpochGeometry.total s.base) (a i) ≤ 50000*ell) :
    AdaptiveAlpha.valid (marked a (EpochGeometry.total s.base) U ell ct C o) := by
  have hA := (EpochGeometry.dominant_spec ho).1
  have hu := EpochParameters.marked_u_upper hs ho hU
  have hu' : U/EpochGeometry.total s.base ≤ 1 := by linarith
  have hlp : 0 < ell := by linarith
  refine ⟨⟨o,o.property⟩,hlp,hc,hC,?_,div_pos hUp hA,hu',?_,?_,?_,?_⟩
  · intro i
    apply eta_bound hc hlp hct
    unfold marked
    dsimp only
    split_ifs
    · linarith
    · exact hheight i
  · simp [marked]
  · intro i hi
    have hio : (i:ι) ≠ o.val := fun h => hi (Subtype.ext h)
    have hh := EpochParameters.regular_height hs (EpochParameters.mem_active.mp i.property)
      (by simpa only [ho,ne_eq,Option.some.injEq] using hio.symm)
    unfold marked
    dsimp only
    split_ifs with he
    · exact False.elim (hi he)
    · exact hh
  · intro i hi
    have hio : (i:ι) ≠ o.val := fun h => hi (Subtype.ext h)
    have haiU := (EpochParameters.side_coordinate ha hio).trans hU.2.2
    have hh := EpochParameters.marked_height_lower hA (EpochParameters.mem_active.mp i.property)
      haiU hu' hUp
    unfold marked
    dsimp only
    split_ifs with he
    · exact False.elim (hi he)
    · exact hh
  · let : DecidableEq (EpochParameters.active a) := fun i j => Classical.propDecidable (i=j)
    have hsum := EpochParameters.side_exp_sum ha hA hU
    have he : (∑ i ∈ univ.erase o,
        Real.exp (- (if i=o then U/EpochGeometry.total s.base else
          SideParameters.height (EpochGeometry.total s.base) (a i)))) =
        ∑ i : {i : EpochParameters.active a // (i : ι) ≠ o.val},
          Real.exp (-SideParameters.height (EpochGeometry.total s.base) (a i.1)) := by
      have hmem (i : EpochParameters.active a) : i ∈ univ.erase o ↔ (i:ι) ≠ o.val := by
        simp only [mem_erase,mem_univ,and_true]
        exact not_congr Subtype.ext_iff
      rw [←Finset.sum_subtype (univ.erase o) hmem (fun i : EpochParameters.active a =>
          Real.exp (-SideParameters.height (EpochGeometry.total s.base) (a i)))]
      apply sum_congr rfl
      intro i hi
      rw [ite_eq_right (mem_erase.mp hi).1]
    apply le_trans (le_of_eq ?_) (he.le.trans hsum)
    apply sum_congr rfl
    intro i _
    unfold marked
    dsimp only
    split_ifs <;> rfl

theorem singleton_valid {a : ι → ℝ} (o : EpochParameters.active a)
    (ha : ∀ i : EpochParameters.active a, i=o) {ell ct C : ℝ}
    (hl : 0 < ell) (hc : 0 < ct) (hC : 1000 < C*ct) :
    AdaptiveAlpha.valid (singleton a ell ct C o) := by
  refine ⟨⟨o,o.property⟩,hl,hc,hC,?_,ha,fun _ => rfl⟩
  intro i
  change ct*0/ell ≤ 1
  norm_num

theorem side_zero_singleton {a : ι → ℝ} (ha : ∀ i, 0 ≤ a i)
    (o : EpochParameters.active a) {U : ℝ} (hU : EpochParameters.sideReference a o U)
    (hzero : U=0) : ∀ i : EpochParameters.active a, i=o := by
  intro i
  by_contra hi
  have hio : (i:ι) ≠ o.val := fun h => hi (Subtype.ext h)
  have hside := EpochParameters.side_coordinate ha hio
  have hsize := EpochParameters.mem_active.mp i.property
  have hupp := hU.2.2
  rw [hzero,mul_zero] at hupp
  linarith

end UniformKServer.EpochAlpha

end


end

end OAI
