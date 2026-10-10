import Mathlib
import OAI.Analysis.FreeWords.AsymptoticBlockTransportDefinitions

namespace OAI

noncomputable section

namespace KKAsymptoticTransport

noncomputable section

open Filter

open scoped Topology

variable {I A:Type*} [NormedRing A] [NormedAlgebra ℂ A]

omit [NormedAlgebra ℂ A] in
theorem NetBound.const (a:A) : NetBound (fun _:I => a) := ⟨‖a‖,norm_nonneg _,fun _ => le_rfl⟩

omit [NormedAlgebra ℂ A] in
theorem NetBound.mul {f g:I → A} (hf:NetBound f) (hg:NetBound g) :
    NetBound (fun j => f j*g j) := by
  obtain ⟨C,hC,hf⟩ := hf
  obtain ⟨D,hD,hg⟩ := hg
  exact ⟨C*D,mul_nonneg hC hD,fun j => (norm_mul_le _ _).trans
    (mul_le_mul (hf j) (hg j) (norm_nonneg _) hC)⟩

omit [NormedAlgebra ℂ A] in
theorem NetBound.sub {f g:I → A} (hf:NetBound f) (hg:NetBound g) :
    NetBound (fun j => f j-g j) := by
  obtain ⟨C,hC,hf⟩ := hf
  obtain ⟨D,hD,hg⟩ := hg
  exact ⟨C+D,add_nonneg hC hD,fun j => (norm_sub_le _ _).trans (add_le_add (hf j) (hg j))⟩

theorem NetBound.map (E:A →L[ℂ] A) {f:I → A} (hf:NetBound f) :
    NetBound (fun j => E (f j)) := by
  obtain ⟨C,hC,hf⟩ := hf
  exact ⟨‖E‖*C,mul_nonneg (norm_nonneg _) hC,fun j => (E.le_opNorm _).trans
    (mul_le_mul_of_nonneg_left (hf j) (norm_nonneg _))⟩

theorem NetBound.center (E:A →L[ℂ] A) {f:I → A} (hf:NetBound f) :
    NetBound (centerNet E f) := hf.sub (hf.map E)

omit [NormedAlgebra ℂ A] in
theorem NetBound.isBoundedUnder {L:Filter I} {f:I → A} (hf:NetBound f) :
    IsBoundedUnder (·≤·) L (norm ∘ f) := by
  obtain ⟨C,_,hf⟩ := hf
  exact isBoundedUnder_of ⟨C,hf⟩

omit [NormedAlgebra ℂ A] in
theorem NetBound.netPair (w:List ((I → A)×A))
    (h:∀z∈w,NetBound z.1) : NetBound (netPair w) := by
  induction w with
  | nil => exact NetBound.const 1
  | cons z w ih =>
    exact ((h z List.mem_cons_self).mul (NetBound.const z.2)).mul
      (ih (fun a ha => h a (List.mem_cons_of_mem _ ha)))

omit [NormedAlgebra ℂ A] in
theorem null_mul {L:Filter I} {f g:I → A}
    (hf:Tendsto f L (𝓝 0)) (hg:NetBound g) :
    Tendsto (fun j => f j*g j) L (𝓝 0) := hf.zero_mul_isBoundedUnder_le hg.isBoundedUnder

omit [NormedAlgebra ℂ A] in
theorem mul_null {L:Filter I} {f g:I → A}
    (hf:NetBound f) (hg:Tendsto g L (𝓝 0)) :
    Tendsto (fun j => f j*g j) L (𝓝 0) := isBoundedUnder_le_mul_tendsto_zero hf.isBoundedUnder hg

omit [NormedAlgebra ℂ A] in
theorem asymp_mul {L:Filter I} {f f' g g':I → A}
    (hf:Tendsto (fun j => f j-f' j) L (𝓝 0))
    (hg:Tendsto (fun j => g j-g' j) L (𝓝 0))
    (hf':NetBound f') (hgb:NetBound g) :
    Tendsto (fun j => f j*g j-f' j*g' j) L (𝓝 0) := by
  have hh := (null_mul hf hgb).add (mul_null hf' hg)
  simpa only [sub_mul,mul_sub,sub_add_sub_cancel,add_zero] using hh

theorem asymp_center {L:Filter I} (E:A →L[ℂ] A) {c:I → A}
    (hc:Tendsto (fun j => E (c j)) L (𝓝 0)) :
    Tendsto (fun j => c j-centerNet E c j) L (𝓝 0) := by
  simpa only [centerNet,sub_sub_cancel] using hc

theorem pair_center_difference {L:Filter I} (E:A →L[ℂ] A)
    (w:List ((I → A)×A))
    (hb:∀z∈w,NetBound z.1)
    (hz:∀z∈w,Tendsto (fun j => E (z.1 j)) L (𝓝 0)) :
    Tendsto (fun j => netPair w j-netPair (centeredWord E w) j) L (𝓝 0) := by
  induction w with
  | nil => simpa [netPair,centeredWord] using (tendsto_const_nhds : Tendsto (fun _:I => (0:A)) L (𝓝 0))
  | cons z w ih =>
    have hd := null_mul (asymp_center E (hz z List.mem_cons_self)) (NetBound.const z.2)
    have hd' : Tendsto (fun j => z.1 j*z.2-centerNet E z.1 j*z.2) L (𝓝 0) := by
      simpa only [sub_mul] using hd
    exact asymp_mul hd'
      (ih (fun a ha => hb a (List.mem_cons_of_mem _ ha))
        (fun a ha => hz a (List.mem_cons_of_mem _ ha)))
      (((hb z List.mem_cons_self).center E).mul (NetBound.const z.2))
      (NetBound.netPair w (fun a ha => hb a (List.mem_cons_of_mem _ ha)))

theorem tendsto_E_of_difference {L:Filter I} (E:A →L[ℂ] A) {f g:I → A}
    (hd:Tendsto (fun j => f j-g j) L (𝓝 0))
    (hg:Tendsto (fun j => E (g j)) L (𝓝 0)) :
    Tendsto (fun j => E (f j)) L (𝓝 0) := by
  have hd' := E.continuous.tendsto 0 |>.comp hd
  have hh := hd'.add hg
  simpa only [Function.comp_def,map_sub,map_zero,sub_add_cancel,add_zero] using hh

end

end KKAsymptoticTransport
end

end OAI
