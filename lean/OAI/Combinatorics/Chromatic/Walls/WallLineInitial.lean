import Mathlib
import OAI.Combinatorics.Chromatic.Walls.FiniteRayGeometry

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries FiniteRayGeometry WallUnits
noncomputable section
variable {M E I : Type*} [AddCommGroup M] [AddCommGroup E] [Module ℝ E] [Fintype I]
variable (Ω : M →+ M →+ ℤ) (C : (I → ℤ) →+ M)
variable (e : M →+ E) (he : Function.Injective e)
variable (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hB : ∀x,B x x=0)
variable (hcomp : ∀a b,B (e a) (e b)=(Ω a b:ℝ))
variable (L : Module.Dual ℝ E) (hdeg : ∀n m,HasRootDegree C n m → L (e m)=(n:ℝ))
lemma finite_upper_bound (S : Finset ℝ) : ∃b,0 < b ∧ ∀a∈S,a < b := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1,one_pos,by simp⟩
  | @insert a S ha ih =>
    obtain ⟨b,hb,H⟩:=ih
    refine ⟨max b (a+1),lt_of_lt_of_le hb (le_max_left _ _),?_⟩
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl|hz
    · exact lt_of_lt_of_le (by linarith : z < z+1) (le_max_right _ _)
    · exact lt_of_lt_of_le (H z hz) (le_max_left _ _)
lemma far_line_lex (S : Finset E) (v h : Module.Dual ℝ E) (b : ℝ)
    (hb : ∀a∈lineEvents S v h,a < b) (s : E) (hs : s∈S) :
    (0 < v s → 0 < (h+b • v) s) ∧ (v s < 0 → (h+b • v) s < 0) ∧
    (v s=0 → (0 < h s → 0 < (h+b • v) s) ∧ (h s=0 → (h+b • v) s=0) ∧
      (h s < 0 → (h+b • v) s < 0)) := by
  classical
  simp only [LinearMap.add_apply,LinearMap.smul_apply,smul_eq_mul]
  have HB : v s≠0 → -h s/v s < b:=fun hv => hb _
    (Finset.mem_image.mpr ⟨s,Finset.mem_filter.mpr ⟨hs,hv⟩,rfl⟩)
  constructor
  · intro hh
    have H:=HB (ne_of_gt hh)
    have hz : h s+(-h s/v s)*v s=0:=by field_simp [ne_of_gt hh]; ring
    nlinarith
  constructor
  · intro hh
    have H:=HB (ne_of_lt hh)
    have hz : h s+(-h s/v s)*v s=0:=by field_simp [ne_of_lt hh]; ring
    nlinarith
  · intro hz
    simp only [hz,mul_zero,add_zero]
    exact ⟨id,id,id⟩
include he hdeg in
lemma offset_ray_generic (N d : ℕ) (r : M) (hd : 0 < d) (hr : HasRootDegree C d r)
    (v h : Module.Dual ℝ E)
    (H : GenericOffset (realRootsThrough e C N) (e r) v h) :
    RayGeneric C N r (h.toAddMonoidHom.comp e) := by
  refine ⟨H.on_ray,?_⟩
  intro n hn hnN m hm hm0
  apply positive_ray_of_mem_span e he C L hdeg r m d n hd hn hr hm
  by_contra hP
  exact H.avoid _ (realRoot_mem e C N n hnN m hm) hP hm0
include he hB hcomp hdeg in
theorem incoming_positive_at_far (N d : ℕ) (r : M) (hd : 0 < d) (hr : HasRootDegree C d r)
    (k : Module.Dual ℝ E)
    (H : GenericOffset (realRootsThrough e C N) (e r) (B.flip (e r)) k)
    (F D : CompletedPositive LaurentRay.vUnit Ω C)
    (hD : ∀n m,coeff (n+1) D.val m≠0 → OnPositiveRay r m)
    (hpos : RootClosedThrough LaurentRay.vUnit Ω N (literalRootProducts Ω C (OnPositiveRay r)) D.val)
    (hprescribed : ∀n ≤ N,∀m,OnPositiveRay r m →
      coeff n (FormalLog.log (chartZero LaurentRay.vUnit Ω C (incomingCovector Ω m) F).val) m=
        coeff n (FormalLog.log D.val) m) :
    ∃b,0 < b ∧ (∀a∈lineEvents (realRootsThrough e C N) (B.flip (e r)) k,a < b) ∧
      RootClosedThrough LaurentRay.vUnit Ω N (literalRootProducts Ω C (OnPositiveRay r))
        (chartZero LaurentRay.vUnit Ω C ((k+b • B.flip (e r)).toAddMonoidHom.comp e) F).val := by
  have hΩ : ∀m,Ω m m=0:=by
    intro m; have HH:=hB (e m); rw [hcomp] at HH; exact_mod_cast HH
  obtain ⟨b,hb,hbound⟩:=finite_upper_bound (lineEvents (realRootsThrough e C N) (B.flip (e r)) k)
  refine ⟨b,hb,hbound,?_⟩
  have Hgen:=offset_ray_generic C e he L hdeg N d r hd hr (B.flip (e r)) k H
  have Hinc:=incoming_ray_element_through LaurentRay.vUnit Ω C hΩ r (k.toAddMonoidHom.comp e)
    H.on_ray F D N (fun n hn hnN m hm hΩm hkm => Hgen.2 n hn hnN m hm hkm) hD hprescribed
  have Href:=chart_zero_refinement LaurentRay.vUnit Ω C (incomingCovector Ω r)
    (k.toAddMonoidHom.comp e) ((k+b • B.flip (e r)).toAddMonoidHom.comp e) F N (by
      intro n hn m hm
      have HH:=far_line_lex (realRootsThrough e C N) (B.flip (e r)) k b hbound
        (e m) (realRoot_mem e C N n hn m hm)
      simp only [LinearMap.flip_apply,hcomp] at HH
      exact HH)
  apply hpos.congr LaurentRay.vUnit Ω
  intro n hn
  exact (Href n hn |>.trans (Hinc n hn)).symm
end
end ElementaryPositivity.QuantumTorus

end
section
namespace ElementaryPositivity.FiniteEventTraversal
noncomputable section
lemma finite_gap (S : Finset ℝ) (a : ℝ) :
    ∃ε > 0,∀s∈S,s≠a  →  ε < |s-a| := by
  classical
  induction S using Finset.induction_on with
  | empty=>exact ⟨1,one_pos,by simp⟩
  | @insert s S hs ih=>
    obtain ⟨ε,he,H⟩:=ih
    by_cases hsa : s=a
    · refine ⟨ε,he,?_⟩
      intro x hx hn
      rcases Finset.mem_insert.mp hx with rfl|hx
      · exact False.elim (hn hsa)
      · exact H x hx hn
    · refine ⟨min ε (|s-a|/2),lt_min he (by have := abs_pos.mpr (sub_ne_zero.mpr hsa); positivity),?_⟩
      intro x hx hn
      rcases Finset.mem_insert.mp hx with rfl|hx
      · exact lt_of_le_of_lt (min_le_right _ _) (by have := abs_pos.mpr (sub_ne_zero.mpr hsa); linarith)
      · exact lt_of_le_of_lt (min_le_left _ _) (H x hx hn)
lemma near_not_mem (S : Finset ℝ) (a δ ε : ℝ) (hd : 0 < δ) (hde : δ < ε)
    (H : ∀s∈S,s≠a  →  ε < |s-a|) : a+δ∉S ∧ a-δ∉S := by
  constructor
  · intro hs
    have hx:=H (a+δ) hs (by linarith)
    rw [add_sub_cancel_left,abs_of_pos hd] at hx
    linarith
  · intro hs
    have hx:=H (a-δ) hs (by linarith)
    have he : a-δ-a= -δ:=by ring
    rw [he,abs_neg,abs_of_pos hd] at hx
    linarith

theorem descend (S : Finset ℝ) (P : ℝ → Prop)
    (initial : ∃b,0 ≤ b ∧ (∀s∈S,s < b) ∧ P b)
    (cell : ∀a b,0 ≤ a  →  0 ≤ b  →  a∉S  →  b∉S  →
      (∀s∈S,a < s↔b < s)  →  P a  →  P b)
    (step : ∀a∈S,0 < a  →  ∃ε > 0,∀δ,0 < δ  →  δ < ε  →  P (a+δ)  →  P (a-δ))
    (t : ℝ) (ht : 0 ≤ t) (htS : t∉S) : P t := by
  classical
  suffices ∀k,∀t:ℝ,0 ≤ t  →  t∉S  →  (S.filter (fun s=>t < s)).card=k  →  P t from
    this _ t ht htS rfl
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih=>
    intro t ht htS hk
    let U:=S.filter (fun s=>t < s)
    by_cases hU : U.Nonempty
    · let a:=U.min' hU
      have haU : a∈U:=Finset.min'_mem _ _
      have haS : a∈S:=(Finset.mem_filter.mp haU).1
      have hta : t < a:=(Finset.mem_filter.mp haU).2
      obtain ⟨ε,he,Hε⟩:=step a haS (lt_of_le_of_lt ht hta)
      obtain ⟨η,hh,Hη⟩:=finite_gap S a
      let δ:=min (min ε η) (a-t)/2
      have hd : 0 < δ:=by dsimp [δ]; exact div_pos (lt_min (lt_min he hh) (sub_pos.mpr hta)) (by norm_num)
      have hδsmall : δ < min (min ε η) (a-t):=by
        have hp : 0 < min (min ε η) (a-t):=lt_min (lt_min he hh) (sub_pos.mpr hta)
        dsimp [δ]; linarith
      have hδε : δ < ε:=lt_of_lt_of_le hδsmall ((min_le_left _ _).trans (min_le_left _ _))
      have hδη : δ < η:=lt_of_lt_of_le hδsmall ((min_le_left _ _).trans (min_le_right _ _))
      have hδt : δ < a-t:=lt_of_lt_of_le hδsmall (min_le_right _ _)
      have hnS:=near_not_mem S a δ η hd hδη Hη
      have hsub : S.filter (fun s=>a+δ < s) ⊂ U:=by
        apply Finset.ssubset_iff_subset_ne.mpr
        constructor
        · intro x hx
          obtain ⟨hx,hxx⟩:=Finset.mem_filter.mp hx
          exact Finset.mem_filter.mpr ⟨hx,by linarith⟩
        · intro heq
          have hx : a∈S.filter (fun s=>a+δ < s):=heq.symm ▸ haU
          have := (Finset.mem_filter.mp hx).2
          linarith
      have hcard : (S.filter (fun s=>a+δ < s)).card < k:=by
        rw [←hk]; exact Finset.card_lt_card hsub
      have hb : P (a+δ):=ih _ hcard (a+δ) (by linarith) hnS.1 rfl
      have hc : P (a-δ):=Hε δ hd hδε hb
      apply cell (a-δ) t (by linarith) ht hnS.2 htS _ hc
      intro s hs
      constructor
      · intro hcs
        by_contra hts
        linarith
      · intro hts
        have hsu : s∈U:=Finset.mem_filter.mpr ⟨hs,hts⟩
        have has : a ≤ s:=Finset.min'_le _ _ hsu
        linarith
    · obtain ⟨b,hb,hbS,hPb⟩:=initial
      have hbN : b∉S:=fun hbmem=>lt_irrefl b (hbS b hbmem)
      apply cell b t hb ht hbN htS _ hPb
      intro s hs
      have hts : ¬t < s:=fun h=>hU ⟨s,Finset.mem_filter.mpr ⟨hs,h⟩⟩
      exact iff_of_false (not_lt_of_ge (hbS s hs).le) hts
end
end ElementaryPositivity.FiniteEventTraversal

end

end OAI
