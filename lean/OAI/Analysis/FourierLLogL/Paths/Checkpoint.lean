import OAI.Analysis.FourierLLogL.Paths.Chief
/-! # The uniform output path -/

open Function Set Filter
open scoped Topology BigOperators ComplexConjugate
noncomputable section

namespace OAI

namespace FourierLLogL.Dyadic.Procedure.Paths
open Law Node Real Period Compress.Params Thermal Fund Scene Fork Road Event Journal Wire Pulse Thread Capture Chart Snapshot
variable {M j J : ℕ} {s q : Scene M} {f : Grid M → ℝ}
open scoped Classical


namespace Run.Streak
open Beam

def wave (e : Streak M) (t : Tide) : Path M → Tide
| [] => t
| b::l => wave e (e.rightNow b.post t).next l
lemma wave_combine (e : Streak M) (t : Tide) (l r : Path M) :
    e.wave t (l++r)=e.wave (e.wave t l) r := by
  induction l generalizing t with
  | nil => rfl
  | cons b l ih => exact ih _

lemma wave_bling (e : Streak M) (t : Tide) (l r : Path M) :
    e.sumbling (e.wave t l) r ≤ e.sumbling t (l++r) := by
  induction l generalizing t with
  | nil => exact le_rfl
  | cons b l ih =>
    change _ ≤ sumbling e t (b::(l++r))
    rw [sumbling]
    apply le_trans (ih _)
    apply le_add_of_nonneg_left
    split; linarith [(bling_share e (b::(l++r))).1]
    exact le_rfl

lemma holds_tail (e : Streak M) (p r : Path M) (n : ℝ) (hp : e.wave none p=some n) :
    ∃ v w : Path M, p=v++w ∧ (∀ b∈w,e.outer b.post) ∧
      fullFax w=n ∧ e.bling (w++r) ≤ e.sumbling none (p++r) := by
  induction p using List.reverseRecOn generalizing n r with
  | nil => cases hp
  | append_singleton p b ih =>
    rw [wave_combine] at hp
    let t := e.wave none p; let k := e.rightNow b.post t
    let a := b.post
    change k.next=some n at hp
    have hx : e.sumbling t ([b]++r) ≤ e.sumbling none ((p++[b])++r) := by
      rw [List.append_assoc]
      exact wave_bling e none p _
    have HH (ha : k.alpha ∨ k.tick) (h : fax a=n) (hF : outer e a) :
        ∃ v w : Path M,p++[b]=v++w ∧ (∀ z∈w,e.outer z.post) ∧
          fullFax w=n ∧ e.bling (w++r) ≤ e.sumbling none ((p++[b])++r) := by
      refine ⟨p,[b],rfl,by simpa using hF,?_,?_⟩
      · change fax a+0=_; simpa only [add_zero] using h
      · apply le_trans _ hx; change bling _ _ ≤ sumbling e t (b::r); rw [sumbling,ite_eq_left ha]
        apply le_add_of_nonneg_right; linarith [sumbling_one e (rightNow e b.post t).next r]
    cases ht : t with
    | none =>
      by_cases hV : innerV e b.post
      · have hi : k=going true false (fax b.post) := by unfold k; rw [ht]; exact ite_eq_left hV
        rw [hi] at hp
        exact HH (by rw [hi]; exact Or.inl rfl) (Option.some.inj hp) (inner_outer e _ hV)
      · have hi : k=idle := by unfold k; rw [ht]; exact ite_eq_right hV
        rw [hi] at hp; cases hp
    | some x =>
      by_cases hV : outer e b.post
      · by_cases hz : 1 ≤ x
        · have hi : k=going false true (fax b.post) := by simp only [k,ht,rightNow,hV,hz, ↓reduceIte]
          rw [hi] at hp
          exact HH (by rw [hi]; exact Or.inr rfl) (Option.some.inj hp) hV
        have hi : k=going false false (x+fax b.post) := by simp only [k,ht,rightNow,hV,hz, ↓reduceIte]
        rw [hi] at hp
        obtain ⟨v,w,hw,h1,h2,h3⟩ := ih (b::r) x ht
        refine ⟨v,w++[b],by rw [hw,List.append_assoc],?_,?_,?_⟩
        · intro z hz; simp only [List.mem_append,List.mem_singleton] at hz
          exact hz.elim (fun hh => h1 z hh) (fun h => h ▸ hV)
        · unfold fullFax; rw [subtotal_app]
          change fullFax w+(fax b.post+0)=n
          rw [h2,add_zero]; exact Option.some.inj hp
        simp only [List.append_assoc, List.singleton_append]
        exact h3
      · have hi : k=idle := by unfold k; rw [ht]; exact ite_eq_right hV
        rw [hi] at hp; cases hp

lemma holds_inner (e : Streak M) (p l m : Path M) (h : ∀ b∈l,e.innerV b.post) (hh : l ≠ []) :
    ∃ v w : Path M, p=v++w ∧ (∀ b∈w++l,e.outer b.post) ∧ fullFax w ≤ 1 ∧
      e.bling (w++(l++m)) ≤ e.sumbling none (p++(l++m)) := by
  cases l with
  | nil => exact (hh rfl).elim
  | cons b l =>
    let r := b::l; let t := e.wave none p; let k := e.rightNow b.post t
    have hv : ∀ b ∈ r,e.outer b.post := fun b hi => inner_outer e b.post (h b hi)
    have hh' : innerV e b.post := h b List.mem_cons_self
    have ho : outer e b.post := inner_outer e _ hh'
    by_cases ha : k.alpha=true ∨ k.tick=true
    · refine ⟨p,[],(by simp),hv,(by change (0:ℝ) ≤ 1; norm_num),?_⟩
      apply le_trans _ (wave_bling e none p (r++m))
      change bling e (b::(l++m)) ≤ sumbling e t (b::(l++m)); rw [sumbling,ite_eq_left ha]
      apply le_add_of_nonneg_right; linarith [sumbling_one e (rightNow e b.post t).next (l++m)]
    · cases hx : t with
      | none =>
        apply (ha ?_).elim
        apply Or.inl; unfold k; rw [hx]
        rw [rightNow,ite_eq_left hh']; rfl
      | some x =>
        have he : x < 1 := by
          by_contra! he
          apply ha; apply Or.inr; unfold k; rw [hx]
          simp [rightNow,ho,he,going]
        obtain ⟨v,w,hq,h₁,h₂,h₃⟩ := holds_tail e p (r++m) x hx
        refine ⟨v,w,hq,?_,(h₂.le.trans he.le),h₃⟩
        intro c hc; rw [List.mem_append] at hc
        exact hc.elim (h₁ c) (hv c)

lemma possible (e : Streak M) {x : Grid M} (p l m : Path M)
    (h : Trip x s (p++(l++m))) (hp : ∀ b∈l,e.innerV b.post)
    (t : ℝ) (ht : 2*log (sumbling e none (p++(l++m))) ≤ t) :

      let L := p++(l++m); yieldW (subtotal (duties x e.u) l) ≤
      10^15*(fullFax l+(1+fullKills L+e.flagged L)/e.thick+e.thick*t) := by
  intro L
  let a := e.thick; let F := duties x e.u
  have ha : 0 < a := e.thick_rate.1
  have hi : a ≤ 1 := e.thick_rate.2.1
  have hT : 0 ≤ t := le_trans (mul_nonneg (by norm_num)
    (log_nonneg (sumbling_one e none L))) ht
  have hL : 0 ≤ fullKills L := trip_K h; have hE : 0 ≤ flagged e L := flagged_pos e h
  by_cases H : l=[]
  · rw [H,subtotal_nil,yield_zero]
    change (0:ℝ) ≤ 10^15*(0+(1+fullKills L+flagged e L)/a+a*t)
    positivity
  obtain ⟨v,w,hv,hq,hf,hB⟩ := holds_inner e p l m hp H
  have HE : L=v++((w++l)++m) := by unfold L; simp [hv]
  have H0 : Trip x s (v++((w++l)++m)) := HE ▸ h
  obtain ⟨h₁,s',hh⟩ := trip_cut H0
  obtain ⟨h₂,q,h₄⟩ := trip_cut hh
  obtain ⟨h₃,r,h₅⟩ := trip_cut h₂
  have HX : 2*log (bling e (w++(l++m))) ≤ t :=
    le_trans (mul_le_mul_of_nonneg_left (log_le_log
      (by linarith [(bling_share e (w++(l++m))).1]) hB) (by norm_num)) ht
  rw [show subtotal (duties x e.u) l=subtotal F (w++l)-subtotal F w by rw [subtotal_app]; unfold F; abel]
  apply (yield_sub _ _).trans
  apply le_trans (add_le_add
    (ribbon_bound e _ _ h₂ hq t (show 2*log (e.bling ((w++l)++m)) ≤ t from by rwa [List.append_assoc]))
    (ribbon_bound e _ _ h₃ (fun b hb => hq b (List.mem_append_left _ hb)) t HX))
  have hiP (g : Beat M → ℝ) :
      subtotal g L=subtotal g v+subtotal g (w++l)+subtotal g m := by
    rw [HE,subtotal_app,subtotal_app]; linarith
  have H₁ (p l : Path M) : fullKills (p++l)=fullKills p+fullKills l := subtotal_app _ _ _
  have H₂ (p l : Path M) : flagged e (p++l)=flagged e p+flagged e l := subtotal_app _ _ _
  have hk : fullKills w ≤ fullKills (w++l) ∧ fullKills (w++l) ≤ fullKills L := by
    have H : fullKills L=fullKills v+fullKills (w++l)+fullKills m := hiP killed
    constructor <;> linarith [trip_K h₁,trip_K h₄,trip_K h₅,H₁ w l]
  have he : flagged e w ≤ flagged e (w++l) ∧ flagged e (w++l) ≤ flagged e L := by
    have H : flagged e L=flagged e v+flagged e (w++l)+flagged e m := hiP _
    constructor <;> linarith [flagged_pos e h₁,flagged_pos e h₄,flagged_pos e h₅,H₂ w l]
  rw [show fullFax (w++l)=fullFax w+fullFax l from subtotal_app _ w l]
  have hY : 1 ≤ (e.thick)⁻¹ := (one_le_inv₀ ha).mpr hi
  unfold a at *
  simp_rw [div_eq_mul_inv]
  nlinarith [trip_fax h₅]

end Run.Streak


end FourierLLogL.Dyadic.Procedure.Paths

end OAI
