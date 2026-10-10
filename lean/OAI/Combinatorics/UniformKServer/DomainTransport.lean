import Mathlib
import OAI.Combinatorics.UniformKServer.AlphaTracker
import OAI.Combinatorics.UniformKServer.SideTracker

namespace OAI

                                      
section

/-! Zero-extension and the exact prepared domain-change operation in companion
 §04. Departing coordinates are NOT erased until the minimizing feasibility
 inequalities have been obtained for the synthetic common-core input. -/
noncomputable section
namespace UniformKServer.DomainTransport
open Finset
open scoped Classical
variable {ι : Type*} [Fintype ι]

def Supported (I : Finset ι) (a : ι → ℝ) : Prop := ∀ i, i ∉ I → a i=0

def extend (I : Finset ι) (a : I → ℝ) (i : ι) : ℝ := if h : i ∈ I then a ⟨i,h⟩ else 0

def simplex (I : Finset ι) (a : ι → ℝ) : Prop :=
  (∀ i, 0 ≤ a i) ∧ Supported I a ∧ ∑ i, a i=1

def domain (I : Finset ι) (W : ℝ) (w : ι → ℝ) : Prop :=
  (∀ i, 0 ≤ w i) ∧ Supported I w ∧ ∑ i, w i ≤ W

theorem sum_restrict {I : Finset ι} {a : ι → ℝ} (ha : Supported I a) :
    (∑ i : I, a i)=∑ i, a i := by
  rw [sum_coe_sort]
  exact sum_subset (subset_univ I) (fun i _ hi => ha i hi)

omit [Fintype ι] in
theorem extend_supported (I : Finset ι) (a : I → ℝ) : Supported I (extend I a) := by
  intro i hi
  simp [extend,hi]

omit [Fintype ι] in
theorem extend_apply (I : Finset ι) (a : I → ℝ) (i : I) : extend I a i=a i := by
  simp [extend,i.property]

theorem extend_sum (I : Finset ι) (a : I → ℝ) : (∑ i, extend I a i)=∑ i : I, a i := by
  rw [←sum_restrict (extend_supported I a)]
  apply sum_congr rfl
  intro i _
  exact extend_apply I a i

theorem restrict_simplex {I : Finset ι} {a : ι → ℝ} (ha : simplex I a) :
    SimplexTracker.simplex (fun i : I => a i) := by
  refine ⟨fun i => ha.1 i,?_⟩
  rw [sum_restrict ha.2.1,ha.2.2]

theorem extend_simplex {I : Finset ι} {a : I → ℝ} (ha : SimplexTracker.simplex a) :
    simplex I (extend I a) := by
  refine ⟨?_,extend_supported I a,?_⟩
  · intro i
    unfold extend
    split_ifs with h
    · exact ha.1 ⟨i,h⟩
    · rfl
  · rw [extend_sum]
    exact ha.2

theorem exists_simplex {I : Finset ι} (hI : I.Nonempty) : ∃ a, simplex I a := by
  obtain ⟨i,hi⟩ := hI
  refine ⟨fun j => if j=i then 1 else 0,?_,?_,?_⟩
  · intro j; dsimp; split_ifs <;> norm_num
  · intro j hj
    have hji : j ≠ i := by rintro rfl; exact hj hi
    simp [hji]
  · simp

theorem potential_extend (I : Finset ι) (g : ι → ℝ → ℝ) (a : I → ℝ)
    (hg : ∀ i, i ∉ I → g i 0=0) :
    (∑ i, g i (extend I a i))=∑ i : I, g i (a i) := by
  have hsup : Supported I (fun i => g i (extend I a i)) := by
    intro i hi
    dsimp
    rw [extend_supported I a i hi,hg i hi]
  rw [←sum_restrict hsup]
  apply sum_congr rfl
  intro i _
  rw [extend_apply]

theorem potential_restrict {I : Finset ι} (g : ι → ℝ → ℝ) {a : ι → ℝ}
    (ha : Supported I a) (hg : ∀ i, i ∉ I → g i 0=0) :
    (∑ i : I, g i (a i))=∑ i, g i (a i) :=
  sum_restrict (a:=fun i => g i (a i)) (fun i hi => by dsimp; rw [ha i hi,hg i hi])

theorem movement_extend (I : Finset ι) (a : I → ℝ) {b : ι → ℝ} (hb : Supported I b) :
    SimplexTracker.movement (extend I a) b =
      SimplexTracker.movement a (fun i : I => b i) := by
  unfold SimplexTracker.movement
  have hs : Supported I (fun i => |extend I a i-b i|) := by
    intro i hi
    dsimp
    rw [extend_supported I a i hi,hb i hi,sub_self,abs_zero]
  rw [←sum_restrict hs]
  apply sum_congr rfl
  intro i _
  rw [extend_apply]

/-- Lift an actual compact minimizing update; no conclusion is assumed about
 the full-domain state. The premise is the already-proved subtype update. -/
theorem lift_update {I : Finset ι} {g : ι → ℝ → ℝ} {B h a₀ : ι → ℝ} {ell ct : ℝ}
    (hB : Supported I B) (ha₀ : simplex I a₀) (hg : ∀ i, i ∉ I → g i 0=0)
    (hu : AlphaTracker.UpdateConclusion (fun i : I => g i) (fun i : I => B i)
      (fun i : I => h i) ell ct (fun i : I => a₀ i)) :
    ∃ a, simplex I a ∧ (∀ i, (∑ j, B j)*a i ≤ (1+ct*h i/ell)*B i) ∧
      (∑ j, B j)*SimplexTracker.movement a a₀ ≤
        (∑ i, g i (a₀ i))-(∑ i, g i (a i)) := by
  obtain ⟨a,ha,_,hf,hm⟩ := hu
  refine ⟨extend I a,extend_simplex ha,?_,?_⟩
  · intro i
    by_cases hi : i ∈ I
    · have hx := hf ⟨i,hi⟩
      rw [sum_restrict hB] at hx
      simpa only [extend,hi,dite_true] using hx
    · rw [extend_supported I a i hi,hB i hi,mul_zero,mul_zero]
  · rw [sum_restrict hB,potential_restrict g ha₀.2.1 hg] at hm
    rw [movement_extend I a ha₀.2.1,potential_extend I g a hg]
    exact hm

/-- Preparation with common-core input makes deletion and zero insertion free.
At zero common input the entire alpha primitive is zero, so redistribution
on the new nonempty domain does not spend weighted movement or potential. -/
theorem prepared_alpha {I J : Finset ι} {a B : ι → ℝ} {S : ℝ}
    (ha : simplex I a) (hJ : J.Nonempty) (hS : 0 ≤ S)
    (hf : ∀ i, i ∉ J → S*a i ≤ B i) (hB : Supported J B)
    (g : ι → ℝ → ℝ) (hg : S=0 → ∀ i x, g i x=0) :
    ∃ b, simplex J b ∧ S*SimplexTracker.movement b a=0 ∧
      (∑ i, g i (b i))=∑ i, g i (a i) := by
  rcases hS.eq_or_lt with hzero | hpos
  · obtain ⟨b,hb⟩ := exists_simplex hJ
    refine ⟨b,hb,?_,?_⟩
    · rw [←hzero,zero_mul]
    · simp only [hg hzero.symm,sum_const_zero]
  · have hs : Supported J a := by
      intro i hi
      have hu := hf i hi
      rw [hB i hi] at hu
      exact le_antisymm (by nlinarith : a i ≤ 0) (ha.1 i)
    refine ⟨a,⟨ha.1,hs,ha.2.2⟩,?_,rfl⟩
    simp [SimplexTracker.movement]

def delete (J : Finset ι) (w : ι → ℝ) (i : ι) : ℝ := if i ∈ J then w i else 0

theorem delete_domain {I J : Finset ι} {w : ι → ℝ} {W : ℝ} (hw : domain I W w) :
    domain J W (delete J w) := by
  refine ⟨?_,?_,?_⟩
  · intro i; unfold delete; split_ifs; exact hw.1 i; rfl
  · intro i hi; simp [delete,hi]
  · refine (sum_le_sum fun i _ => ?_).trans hw.2.2
    unfold delete
    split_ifs
    · rfl
    · exact hw.1 i

/-- Exact side primitive is unchanged by prepared deletion, including D=0. -/
theorem prepared_side {I J : Finset ι} {w B θ z : ι → ℝ} {W D b C : ℝ}
    (hw : domain I W w) (hD : 0 ≤ D) (hB : Supported J B)
    (hf : ∀ i, i ∉ J → D*w i ≤ (b+θ i)*B i) :
    domain J W (delete J w) ∧ D*SideTracker.movement (delete J w) w=0 ∧
      SideTracker.potential b C D θ z B (delete J w)=SideTracker.potential b C D θ z B w := by
  refine ⟨delete_domain hw,?_,?_⟩
  · rcases hD.eq_or_lt with he | hp
    · rw [←he,zero_mul]
    · have hd : delete J w=w := by
        funext i
        unfold delete
        split_ifs with hi
        · rfl
        · have h := hf i hi
          rw [hB i hi,mul_zero] at h
          exact (le_antisymm (by nlinarith : w i ≤ 0) (hw.1 i)).symm
      simp [hd,SideTracker.movement]
  · unfold SideTracker.potential
    apply sum_congr rfl
    intro i _
    by_cases hi : i ∈ J
    · simp [delete,hi]
    · rcases hD.eq_or_lt with he | hp
      · simp [delete,hi,hB i hi,←he,SideTracker.coordinate]
      · have h := hf i hi
        rw [hB i hi,mul_zero] at h
        have hz : w i=0 := le_antisymm (by nlinarith : w i ≤ 0) (hw.1 i)
        simp [delete,hi,hz]

end UniformKServer.DomainTransport

end


end

end OAI
