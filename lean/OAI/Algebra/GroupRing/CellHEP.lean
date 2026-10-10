import Mathlib
import OAI.Algebra.GroupRing.PartialLift

namespace OAI



section
namespace TorsionFreeZeroDivisors.CellHEP
open Set Metric Topology GroupRingTopology GroupRingTopology.Cellular
open scoped unitInterval
noncomputable section
variable {n : ℕ}
abbrev Cylinder (n : ℕ) := unitInterval × Disk n
def denom (q : Cylinder n) : ℝ := max (2-q.1.1) (2*‖q.2.1‖)
lemma denom_pos (q : Cylinder n) : 0<denom q :=
  lt_of_lt_of_le (by linarith [q.1.2.2] : 0<2-q.1.1) (le_max_left _ _)
lemma denom_le_two (q : Cylinder n) : denom q ≤ 2 := by
  have h := mem_closedBall_zero_iff.mp q.2.2
  exact max_le (by linarith [q.1.2.1]) (by linarith)
def scale (q : Cylinder n) : ℝ := 2/denom q
lemma scale_nonneg (q : Cylinder n) : 0 ≤ scale q := div_nonneg (by norm_num) (denom_pos q).le
lemma scale_ge_one (q : Cylinder n) : 1 ≤ scale q := by
  rw [scale,le_div_iff₀ (denom_pos q)]
  simpa using denom_le_two q
lemma scale_time (q : Cylinder n) : scale q*(2-q.1.1) ≤ 2 := by
  dsimp [scale]
  rw [div_mul_eq_mul_div,div_le_iff₀ (denom_pos q)]
  have h : 2-q.1.1 ≤ denom q := le_max_left _ _
  nlinarith
lemma scale_norm (q : Cylinder n) : scale q*‖q.2.1‖ ≤ 1 := by
  dsimp [scale]
  rw [div_mul_eq_mul_div,div_le_iff₀ (denom_pos q)]
  simpa only [one_mul,denom] using le_max_right (2-q.1.1) (2*‖q.2.1‖)
def retract (q : Cylinder n) : Cylinder n :=
  (⟨2-scale q*(2-q.1.1),by
      constructor
      · linarith [scale_time q]
      · have h := mul_le_mul_of_nonneg_right (scale_ge_one q) (by linarith [q.1.2.2] : 0 ≤ 2-q.1.1)
        linarith [q.1.2.2]⟩,
   ⟨scale q • q.2.1,by
      rw [mem_closedBall_zero_iff,norm_smul,Real.norm_eq_abs,abs_of_nonneg (scale_nonneg q)]
      exact scale_norm q⟩)
lemma continuous_retract : Continuous (@retract n) := by
  have hd : Continuous (@denom n) := by unfold denom;fun_prop
  have hs : Continuous (@scale n) := continuous_const.div hd (fun q=>(denom_pos q).ne')
  exact (Continuous.subtype_mk ((continuous_const.sub (hs.mul
    (continuous_const.sub (continuous_subtype_val.comp continuous_fst))))) _).prodMk
    (Continuous.subtype_mk (hs.smul (continuous_subtype_val.comp continuous_snd)) _)
def Rim (n : ℕ) : Set (Cylinder n) := {q | q.1=0 ∨ q.2.1 ∈ sphere 0 1}
lemma retract_mem (q : Cylinder n) : retract q∈Rim n := by
  rcases le_total (2*‖q.2.1‖) (2-q.1.1) with h|h
  · left
    apply Subtype.ext
    change 2-scale q*(2-q.1.1)=0
    have he : denom q=2-q.1.1 := max_eq_left h
    rw [scale,←he,div_mul_cancel₀ _ (denom_pos q).ne']
    ring
  · right
    rw [mem_sphere_zero_iff_norm]
    change ‖scale q • q.2.1‖=1
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (scale_nonneg q)]
    have he : denom q=2*‖q.2.1‖ := max_eq_right h
    rw [scale,div_mul_eq_mul_div]
    change (2*‖q.2.1‖)/denom q=1
    rw [←he,div_self (denom_pos q).ne']
lemma retract_eq (q : Cylinder n) (h : q∈Rim n) : retract q=q := by
  have hm : denom q=2 := by
    apply le_antisymm (denom_le_two q)
    rcases h with h|h
    · have ht : q.1.1=0 := congrArg Subtype.val h
      simp [denom,ht]
    · have hn : ‖q.2.1‖=1 := mem_sphere_zero_iff_norm.mp h
      simp [denom,hn]
  have hs : scale q=1 := by simp [scale,hm]
  apply Prod.ext
  · apply Subtype.ext
    change 2-scale q*(2-q.1.1)=q.1.1
    rw [hs];ring
  · apply Subtype.ext
    change scale q • q.2.1=q.2.1
    rw [hs,one_smul]

def retraction : C(Cylinder n,Rim n) := ⟨fun q=>⟨retract q,retract_mem q⟩,
  continuous_retract.subtype_mk _⟩
variable {Y : Type*} [TopologicalSpace Y]
def face (n : ℕ) : Bool → Set (Rim n)
  | false => {z | z.1.1=0}
  | true => {z | z.1.2.1∈sphere 0 1}
lemma face_closed (b : Bool) : IsClosed (face n b) := by
  cases b
  · exact isClosed_eq (continuous_fst.comp continuous_subtype_val) continuous_const
  · exact isClosed_sphere.preimage (continuous_subtype_val.comp
      (continuous_snd.comp continuous_subtype_val))
lemma face_cover : ⋃b,face n b=univ := by
  apply eq_univ_of_forall
  rintro ⟨q,hq⟩
  rcases hq with hq|hq
  · exact mem_iUnion.mpr ⟨false,hq⟩
  · exact mem_iUnion.mpr ⟨true,hq⟩
variable (f : C(Disk n,Y)) (H : C(unitInterval × Sphere n,Y))
  (h : ∀x,H (0,x)=f (boundary n x))
def faceMap : ∀ b : Bool,C(face n b,Y)
  | false => ⟨fun z=>f z.1.1.2,
      f.continuous.comp (continuous_snd.comp (continuous_subtype_val.comp continuous_subtype_val))⟩
  | true => ⟨fun z=>H (z.1.1.1,⟨z.1.1.2.1,z.2⟩),H.continuous.comp
      ((continuous_fst.comp (continuous_subtype_val.comp continuous_subtype_val)).prodMk
        ((continuous_subtype_val.comp (continuous_snd.comp
          (continuous_subtype_val.comp continuous_subtype_val))).subtype_mk _))⟩
include h in
lemma faceMap_compat (b c : Bool) (z : Rim n) (hb : z∈face n b) (hc : z∈face n c) :
    faceMap f H b ⟨z,hb⟩=faceMap f H c ⟨z,hc⟩ := by
  have cross (hb : z∈face n false) (hc : z∈face n true) :
      faceMap f H false ⟨z,hb⟩=faceMap f H true ⟨z,hc⟩ := by
    change f z.1.2=H (z.1.1,⟨z.1.2.1,hc⟩)
    change z.1.1=0 at hb
    rw [hb,h]
    rfl
  cases b <;> cases c
  · rfl
  · exact cross hb hc
  · exact (cross hc hb).symm
  · rfl
def rimMap : C(Rim n,Y) := ⟨Set.liftCover (face n) (fun b=>faceMap f H b)
  (faceMap_compat f H h) face_cover,
  continuous_liftCover _ _ _ _ face_closed⟩
lemma rimMap_face (b : Bool) (z : face n b) :
    rimMap f H h z.1=faceMap f H b z := by
  apply Set.liftCover_coe (S:=face n) (f:=fun b=>faceMap f H b)
    (hf:=faceMap_compat f H h) (hS:=face_cover)
/-- Literal homotopy extension for a cell, with no fibrancy premise. -/
def extension : C(Cylinder n,Y) := (rimMap f H h).comp retraction
lemma extension_zero (x : Disk n) : extension f H h (0,x)=f x := by
  have hr : retract (0,x)=(0,x) := retract_eq _ (Or.inl rfl)
  change rimMap f H h ⟨retract (0,x),retract_mem (0,x)⟩=f x
  simp only [hr]
  exact rimMap_face f H h false ⟨⟨(0,x),Or.inl rfl⟩,rfl⟩
lemma extension_boundary (t : unitInterval) (x : Sphere n) :
    extension f H h (t,boundary n x)=H (t,x) := by
  have hr : retract (t,boundary n x)=(t,boundary n x) := retract_eq _ (Or.inr x.2)
  change rimMap f H h ⟨retract (t,boundary n x),retract_mem (t,boundary n x)⟩=H (t,x)
  simp only [hr]
  exact rimMap_face f H h true ⟨⟨(t,boundary n x),Or.inr x.2⟩,x.2⟩

end
end TorsionFreeZeroDivisors.CellHEP


end



end OAI
