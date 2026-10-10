import Mathlib
import OAI.Combinatorics.Chromatic.Walls.SectionGenericPerturbation

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries PowerSeriesAdjoint PowerSeriesSplit FiniteRayGeometry FiniteEventTraversal LaurentPositive WallUnits
open scoped BigOperators
open Classical
noncomputable section
variable {M E I : Type*} [AddCommGroup M] [AddCommGroup E] [Module ℝ E] [Fintype I]
variable (Ω:M →+ M →+ ℤ) (C:(I → ℤ) →+ M)
variable (e:M →+ E) (he:Function.Injective e)
variable (B:E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hB:∀x,B x x=0)
variable (hcomp:∀a b,B (e a) (e b)=(Ω a b:ℝ))
variable (L:Module.Dual ℝ E) (hdeg:∀n m,HasRootDegree C n m → L (e m)=(n:ℝ))
include he hB hcomp hdeg in

lemma section_line_program (F:CompletedPositive LaurentRay.vUnit Ω C)
    (N:ℕ) (walls:WallsPositiveThrough Ω C e N F) (h:Module.Dual ℝ E) (r:M) :
    ∃ts:List (LineTransfer E),
      (∀t∈ts,t.PositiveThrough Ω C e F N r) ∧
      ∀b (X:PowerSeries (Torus LaurentRay.vUnit Ω)),ShiftGraded LaurentRay.vUnit Ω C b X →
        coeff N (sectionValue LaurentRay.vUnit Ω C F (h.toAddMonoidHom.comp e) X) r =
        coeff N (sectionValue LaurentRay.vUnit Ω C F (incomingCovector Ω r) X) r +
          (ts.map (fun t=>t.delta Ω C e F b X N r)).sum := by
  have hΩ:∀m,Ω m m=0:=by
    intro m; have HH:=hB (e m); rw [hcomp] at HH; exact_mod_cast HH
  obtain ⟨k,Hk,Heq⟩:=uniform_section_generic_offset LaurentRay.vUnit Ω C e L hdeg N h (B.flip (e r))
  let dir:=B.flip (e r)
  let S:=realRootsThrough e C N
  let events:=lineEvents S dir k
  let P (a:ℝ):Prop:=∃ts:List (LineTransfer E),
    (∀t∈ts,t.PositiveThrough Ω C e F N r) ∧
    ∀b (X:PowerSeries (Torus LaurentRay.vUnit Ω)),ShiftGraded LaurentRay.vUnit Ω C b X →
      coeff N (sectionValue LaurentRay.vUnit Ω C F ((k+a • dir).toAddMonoidHom.comp e) X) r =
      coeff N (sectionValue LaurentRay.vUnit Ω C F (incomingCovector Ω r) X) r+
        (ts.map (fun t=>t.delta Ω C e F b X N r)).sum
  have h0:(0:ℝ)∉events:=section_line_zero_not_event C e N dir k Hk
  have hstart:∃a,0≤a ∧ (∀z∈events,z<a) ∧ P a:=by
    obtain ⟨a,ha,Hbound⟩:=finite_upper_bound events
    refine ⟨a,ha.le,Hbound,[],by simp,?_⟩
    intro b X hX
    simp only [List.map_nil,List.sum_nil,add_zero]
    exact section_incoming_perturbation LaurentRay.vUnit Ω C hΩ r
      (k.toAddMonoidHom.comp e) ((k+a • dir).toAddMonoidHom.comp e) F X N (by
        intro n hn m hm
        have HH:=far_line_lex S dir k a Hbound (e m) (realRoot_mem e C N n hn m hm)
        simp only [dir,LinearMap.flip_apply,hcomp] at HH
        exact HH)
  have hcell:∀a a',0≤a → 0≤a' → a∉events → a'∉events →
      (∀z∈events,a<z ↔ a'<z) → P a → P a':=by
    intro a a' ha ha' hna hna' Hside hpa
    obtain ⟨ts,hpos,hid⟩:=hpa
    refine ⟨ts,hpos,?_⟩
    intro b X hX
    have HH:=section_sign_congr_through LaurentRay.vUnit Ω C
      ((k+a • dir).toAddMonoidHom.comp e) ((k+a' • dir).toAddMonoidHom.comp e) F X N (by
        intro n hn hnN m hm
        exact line_cell_signs S dir k a a' hna hna' Hside (e m) (realRoot_mem e C N n hnN m hm))
    rw [←HH N le_rfl]
    exact hid b X hX
  have hstep:∀a∈events,0<a → ∃ε>0,∀δ:ℝ,0<δ → δ<ε → P (a+δ) → P (a-δ):=by
    intro a ha ha0
    obtain ⟨ε,he,Hε⟩:=section_line_transfer Ω C e he B hB hcomp L hdeg N r F walls k Hk a ha
    refine ⟨ε,he,?_⟩
    intro δ hd hδε HP
    obtain ⟨t,ht,Ht⟩:=Hε δ hd hδε
    obtain ⟨ts,hpos,hid⟩:=HP
    refine ⟨t::ts,?_,?_⟩
    · intro t' ht'
      rcases List.mem_cons.mp ht' with rfl|ht'
      · exact ht
      · exact hpos t' ht'
    · intro b X hX
      rw [Ht b X hX,hid b X hX]
      simp only [List.map_cons,List.sum_cons]
      ac_rfl
  obtain ⟨ts,hpos,hid⟩:=descend events P hstart hcell hstep 0 (le_refl 0) h0
  refine ⟨ts,hpos,?_⟩
  intro b X hX
  rw [←Heq F X N le_rfl]
  simpa only [zero_smul,add_zero] using hid b X hX
end
end ElementaryPositivity.QuantumTorus

end

end OAI
