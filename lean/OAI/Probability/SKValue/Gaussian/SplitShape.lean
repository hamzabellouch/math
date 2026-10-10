import Mathlib
import OAI.Probability.SKValue.Gaussian.SplitConvergence

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal
namespace SKValue
noncomputable def splitTerminal (γ:OrderParameter) (t:Ioo (0:ℝ) 1) (n:ℕ) : ℝ → ℝ :=
  profileValue (logCoshTerminal (splitSmoothParameter γ t n))
    (γ.splitSegment t 1 t.property.2.le n) 0
lemma splitTerminal_eq (γ:OrderParameter) (t:Ioo (0:ℝ) 1) (n:ℕ) :
    splitTerminal γ t n=splitSmooth γ t n t := by
  unfold splitSmooth OrderParameter.splitGrid
  rw [profileValue_append_before _ _ _ ⟨t.property.1.le,by rw [γ.splitSegment_time,sub_zero]⟩]
  have he:profileTime (γ.splitSegment 0 t t.property.1.le n)=(t:ℝ) := by rw [γ.splitSegment_time,sub_zero]
  exact (by simpa only [he,splitTerminal] using
    (profileValue_terminal (splitTerminal γ t n) (γ.splitSegment 0 t t.property.1.le n)).symm)
lemma splitTerminal_smooth (γ:OrderParameter) (t:Ioo (0:ℝ) 1) (n:ℕ) :
    SmoothTerminal (splitTerminal γ t n) := by
  rw [splitTerminal_eq]
  exact (splitSmooth_evolution γ t n).slices t ⟨t.property.1.le,t.property.2.le⟩
lemma OrderParameter.splitSegment_coeff (γ:OrderParameter) {a b:ℝ}
    (ha:0 ≤ a) (hab:a<b) (hb:b ≤ 1) (n:ℕ) {p:ℝ≥0 × ℝ≥0}
    (hp:p∈γ.splitSegment a b hab.le n) :
    ∃ r∈Ico (0:ℝ) 1,a ≤ r ∧ r<b ∧ (p.2:ℝ)=γ.coeff r+(gridDelta n:ℝ) := by
  obtain ⟨i,_,hi,rfl⟩:=gridProfile_mem hp
  have hr:=split_sample_mem ha hab hb (show i<n+1 by omega)
  have hd:0<(splitLength a b hab.le n:ℝ) := div_pos (sub_pos.mpr hab) (by positivity)
  have hi':(i:ℝ)<(n+1:ℕ) := by exact_mod_cast (show i<n+1 by omega)
  have hit:=mul_lt_mul_of_pos_right hi' hd
  rw [splitLength_mul] at hit
  refine ⟨_,hr,le_add_of_nonneg_right (by positivity),by linarith,?_⟩
  simp only [NNReal.coe_add,Real.coe_toNNReal _ (γ.nonneg _ hr)]
lemma splitCut_le_parameter (γ:OrderParameter) (t:Ioo (0:ℝ) 1) (n:ℕ) :
    γ.coeff t+(gridDelta n:ℝ) ≤ splitSmoothParameter γ t n := by
  let p:ℝ≥0 × ℝ≥0 := (splitLength t 1 t.property.2.le n,(γ.coeff t).toNNReal+gridDelta n)
  have hp:p∈γ.splitGrid t n := by
    apply List.mem_append_right
    change p∈gridProfile _ _ 0 (n+1)
    simp only [gridProfile,List.mem_cons,zero_add,zero_mul,Nat.cast_zero,add_zero]
    exact Or.inl rfl
  have hh:=profileHeight_mem hp
  have he:(p.2:ℝ)=γ.coeff t+(gridDelta n:ℝ) := by
    simp only [p,NNReal.coe_add,Real.coe_toNNReal _ (γ.nonneg _ ⟨t.property.1.le,t.property.2⟩)]
  rw [he] at hh
  exact hh.trans (le_add_of_nonneg_left (by positivity : (0:ℝ) ≤ n+1))
lemma splitTerminal_shape (γ:OrderParameter) (t:Ioo (0:ℝ) 1) (n:ℕ) :
    BackwardShape (γ.coeff t+(gridDelta n:ℝ)) (splitTerminal γ t n) := by
  have hM:=splitSmoothParameter_pos γ t n
  have hC:0<γ.coeff t+(gridDelta n:ℝ) := add_pos_of_nonneg_of_pos
    (γ.nonneg _ ⟨t.property.1.le,t.property.2⟩) (by change 0<1/(n+1:ℝ);positivity)
  apply (logCoshTerminal_backwardShape hM hM le_rfl).profile
    (logCoshTerminal_smoothTerminal hM) hM hC (splitCut_le_parameter γ t n)
    (γ.splitSegment_mono t.property.1.le t.property.2 le_rfl n)
  · intro p hp
    obtain ⟨r,hr,htr,_,he⟩:=γ.splitSegment_coeff t.property.1.le t.property.2 le_rfl n hp
    rw [he]
    exact add_le_add (γ.monotone ⟨t.property.1.le,t.property.2⟩ hr htr) le_rfl
  · intro p hp
    exact (profileHeight_mem (List.mem_append_right _ hp)).trans
      (le_add_of_nonneg_left (by positivity : (0:ℝ) ≤ n+1))
lemma split_profile_coercivity (γ:OrderParameter) (t:Ioo (0:ℝ) 1) (n:ℕ) :
    let A:=splitTerminal γ t n
    let C:=γ.coeff t+(gridDelta n:ℝ)
    let l:=γ.splitSegment 0 t t.property.1.le n
    (1/1000:ℝ)*profileResponse A (fun x ↦ (spatialJet C A 1 x)^4) l 0 0 ≤
      profileResponse A (fun x ↦ (spatialJet C A 3 x)^2-
        12*spatialJet C A 1 x*(spatialJet C A 2 x)^2+6*(spatialJet C A 1 x)^4) l 0 0 := by
  dsimp only
  have hleft:∀ p∈γ.splitSegment 0 t t.property.1.le n,(p.2:ℝ) ≤ γ.coeff t+(gridDelta n:ℝ) := by
    intro p hp
    obtain ⟨r,hr,_,hrt,he⟩:=γ.splitSegment_coeff le_rfl t.property.1 t.property.2.le n hp
    rw [he]
    exact add_le_add (γ.monotone hr ⟨t.property.1.le,t.property.2⟩ hrt.le) le_rfl
  simp only [OrderParameter.splitSegment,gridProfile,Nat.cast_zero,zero_mul,zero_add]
  apply (splitTerminal_shape γ t n).profile_coercivity (splitTerminal_smooth γ t n)
    (p:=(splitLength 0 t t.property.1.le n,(γ.coeff 0).toNNReal+gridDelta n))
  · change 0<((γ.coeff 0).toNNReal:ℝ)+(gridDelta n:ℝ)
    exact add_pos_of_nonneg_of_pos (by positivity) (by change 0<1/(n+1:ℝ);positivity)
  · change 0<((t:ℝ)-0)/(n+1:ℝ)
    exact div_pos (by simpa only [sub_zero] using t.property.1) (by positivity)
  · simpa only [OrderParameter.splitSegment,gridProfile,Nat.cast_zero,zero_mul,zero_add] using
      γ.splitSegment_mono le_rfl t.property.1 t.property.2.le n
  · simpa only [OrderParameter.splitSegment,gridProfile,Nat.cast_zero,zero_mul,zero_add] using hleft
end SKValue

end

end OAI
