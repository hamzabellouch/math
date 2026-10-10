import OAI.Analysis.FourierLLogL.Assembly.Weighted

/-!
# The grid bound
-/

open Function Set Filter
open scoped Topology BigOperators ComplexConjugate
noncomputable section
namespace OAI

namespace FourierLLogL.Dyadic
open Law Node Real Period Compress.Params Thermal
open Procedure Procedure.Scene Procedure.Paths Procedure.Paths.Troupe Procedure.Paths.CastShow
variable {M J j : ℕ} {s : Scene M} {f : Grid M → ℝ}
open scoped Classical

theorem gridProof : GridBound := by
  refine ⟨10^222,by positivity,?_⟩
  filter_upwards [grossDry,grossOur,plant,annual_valid] with j h1 h2 hp h J
  filter_upwards [eventually_ge_atTop (J+20)] with M hM f hF hm hG
  let m := expU f
  let b := decide (1/Thermal.H j ≤ m)
  let s := beginPlay f b
  have he : J ≤ M := by omega
  obtain ⟨t,ht⟩ := hp M J he f hF hm hG b
  let W (x : Grid M) := annual x t
  have hX (x : Grid M) : x ∈ s.here.block M := (mem_group _ _).mp
    (by change x∈root.group M; rw [group_top]; simp)
  refine ⟨W,fun x => ?_, ?_,?_⟩
  · exact le_trans (norm_nonneg _) (h M J he s f t ht 0 x (hX x))
  · rw [← top_avg W,avg_ex (root_ok M)]
    change yieldA t ≤ _
    suffices H : ∀ b : Bool, decide (1/Thermal.H j ≤ m)=b → ∀ t : Play j M (beginPlay f b), t.Follows J f → yieldA t ≤ (10:ℝ)^222*height j from H b rfl t ht
    intro b ha t ht
    have hd := d_pos j
    cases b
    · have hh := le_of_not_ge (of_decide_eq_false ha)
      exact le_trans (h1 M J f hG t ht (by rw [show (beginPlay f false).mass=m from top_avg _]; exact hh
       )) (by linarith)
    · have hh := of_decide_eq_true ha
      have HE : 1000*(2:ℝ)^J ≤ 2^M := by
        apply le_trans _ (pow_le_pow_right₀ (by norm_num) hM)
        rw [pow_add]
        nlinarith [show 0 < (2:ℝ)^J by positivity]
      have HX : (beginPlay f true).mass=m := top_avg f
      have HV := h2 M J HE f hG t ht (HX.symm ▸ hh)
      rw [HX] at HV
      have hc : m ≤ 2 := hm
      change _ ≤ (10:ℝ)^222* height j
      nlinarith
  intro x hx u
  have HE := stage_shift s t u x ht (hX x) hx
  have HI : tailE s J x u=FinShift J (finMod f u) x := by
    unfold tailE; rw [show s.here.lev=0 from rfl,Nat.Ico_zero_eq_range]
    rfl
  rw [HI,ordinary,show s.norm=0 from rfl,Complex.ofReal_zero,zero_mul,zero_add] at HE
  rw [HE]; exact h M J he s f t ht u x (hX x)

end FourierLLogL.Dyadic

end OAI
