import Mathlib
import OAI.Combinatorics.UniformKServer.RealFlowMixture

namespace OAI

noncomputable section
                                     
section

namespace UniformKServer.RealFlow
open Finset
variable {R C J : Type*} [Fintype C] [Fintype J] [DecidableEq C]
  {F : Data R C J} {T : C→R→J→C} {allowed : C→R→J→Prop} {s : C} {H : ℕ}

theorem mass_le_one (hF : Valid F T allowed s H) (w : List R) (hw : w.length≤H) (c : C) :
    F.mass w c≤1 := by
  have h := single_le_sum (fun c _=>hF.mass_nonneg w hw c) (mem_univ c)
  rw [hF.mass_total w hw] at h
  exact h

theorem flow_le_one (hF : Valid F T allowed s H) (w : List R) (hw : w.length<H) (r : R) (c : C) (j : J) :
    F.flow w r c j≤1 := by
  have h := single_le_sum (fun j _=>hF.flow_nonneg w hw r c j) (mem_univ j)
  rw [hF.outflow w hw r c] at h
  exact h.trans (mass_le_one hF w hw.le c)

theorem flowCost_nonneg (hF : Valid F T allowed s H) (d : C→R→J→ℝ)
    (hd : ∀c r j,0≤d c r j) (w u : List R) (hu : w.length+u.length≤H) :
    0≤flowCost F d w u := by
  induction u generalizing w with
  | nil => exact le_rfl
  | cons r u ih =>
    apply add_nonneg
    · exact sum_nonneg fun c _=>sum_nonneg fun j _=>
        mul_nonneg (hF.flow_nonneg w (by simp only [List.length_cons] at hu; omega) r c j) (hd c r j)
    · exact ih _ (by simp only [List.length_append,List.length_cons,List.length_nil] at *; omega)

theorem flowCost_prefix (hF : Valid F T allowed s H) (d : C→R→J→ℝ)
    (hd : ∀c r j,0≤d c r j) (u v : List R) (hv : v.length≤H) (hu : u.IsPrefix v) :
    flowCost F d [] u≤flowCost F d [] v := by
  obtain ⟨a,rfl⟩ := hu
  rw [flowCost_append]
  apply le_add_of_nonneg_right
  apply flowCost_nonneg hF d hd
  simpa only [List.length_append,List.nil_append] using hv

end UniformKServer.RealFlow

end


end

end OAI
