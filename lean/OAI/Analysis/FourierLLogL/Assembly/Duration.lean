import OAI.Analysis.FourierLLogL.Assembly.Slab
/-! # The uniform output path -/

open Function Set Filter
open scoped Topology BigOperators ComplexConjugate
noncomputable section

namespace OAI

namespace FourierLLogL.Dyadic.Procedure.Paths
open Law Node Real Period Compress.Params Thermal Fund Scene Fork Road Event Journal Wire Pulse Thread Capture Chart Snapshot
variable {M j J : ℕ} {s q : Scene M} {f : Grid M → ℝ}
open scoped Classical


namespace Troupe
open Plot Run Streak Beam

def tagM (i : ℕ) : Grade := ⟨true,i⟩
def tagL (i : ℕ) : Grade := ⟨false,i⟩
def depthRate (i : ℕ) := √(side i)
def mainRatio (i : ℕ) (j : ℕ) (L : Path M) :=
    let g := tagM i
    (1+fullKills L+ (rose g 0).flagged L) / depthRate i +
      depthRate i*timex g j L
def mainSticker (i : ℕ) (j : ℕ) (L : Path M) :=
    mainRatio i j L+(billWait (tagM (i-1)) j L:ℝ)
def scalarSticker (i : ℕ) (j : ℕ) (L : Path M) :=
    let g := tagL i
    depthRate i*(1+fullKills L+timex g j L)

lemma rate_easy (i) : 0 < depthRate i ∧ depthRate i ≤ 1 ∧ (depthRate i)^2=side i :=
    thick_rate (M:=0) (rose (tagM i) 0)
lemma mainRatio_one (i j : ℕ) {L : Path M} {x : Grid M} {s : Scene M}
    (h : Trip x s L) : 1 ≤ mainRatio i j L := by
  let g := tagM i; let p : Streak M := rose g 0
  have hv := trip_K h; have ht := flagged_pos p h
  have hi := (timex_scores g j L).1
  let a := depthRate i; have hx : 0 < a ∧ a ≤ 1 := ⟨(rate_easy _).1,(rate_easy i).2.1⟩
  change 1 ≤ (1+fullKills L+p.flagged L)/a+a*_
  exact le_trans ((one_le_div hx.1).mpr (by linarith))
    (le_add_of_nonneg_right (mul_nonneg hx.1.le hi))
lemma mainSticker_pos (i j : ℕ) {L : Path M} {x : Grid M} {s : Scene M}
    (h : Trip x s L) : 0 ≤ mainSticker i j L :=
    add_nonneg (le_trans (by norm_num) (mainRatio_one i j h)) (by positivity)
lemma scalarSticker_pos (i j : ℕ) {L : Path M} {x : Grid M} {s : Scene M}
    (h : Trip x s L) : 0 ≤ scalarSticker i j L :=
    mul_nonneg (rate_easy i).1.le
      (add_nonneg (add_nonneg (by norm_num) (trip_K h)) (timex_scores (tagL i) j L).1)

/-- Bounding a suffix without bigger main activations. -/
lemma ride :
    ∀ᶠ j : ℕ in atTop,
      ∀ M J i : ℕ, ∀ s : Scene M, ∀ f : Grid M → ℝ, ∀ l r m : Path M,
        ∀ (b : Beat M) (x u : Grid M),
          let g := tagM i
          let D := b::r
          let L := l++(D++m)
          let p := heroPlot g L
          Cast j J f s L → Trip x s L → entitled g s j →
            ringing u p j l b →
              (0 < i → stall u (tagM (i-1)) j L (l++D)) →
            ‖subtotal (proceeds x u) D‖ ≤ 10^20*(fullFax D+mainSticker i j L) := by
  filter_upwards [live_rec,channel_inner,near_size] with j h₁ h₂ h₃
    M J i s f l r m b x u g D L p hh he hg hp hf
  let g' := tagM (i-1)
  let n := billWait g' j L
  obtain ⟨z,hz⟩ := bound_stage (u:=u) L hh g'
  obtain ⟨v,hA,l₀,l₁,hL,hT⟩ := h₁ M J s f u g l (r++m) b hh hg hp
  let t := timex g j L
  let S := rose g v
  have HT : 2*log (sumbling S none (l₁++(b::(r++m)))) ≤ t := by
    apply le_trans _ hT
    unfold S g Troupe.rose Troupe.tagM recital
    simp
    exact le_rfl
  have hI : i ≤ mainIx j := (hg rfl).1
  have H : ∃ k, delta (dye b.post) k ≤ sepRad j ∧ rad (u-v-k) ≤ 2*spotLimit b.post j i true := by
    change aligned p b.post j u v at hA
    unfold aligned at hA
    rw [ite_eq_left (show p.main=true from rfl)] at hA; exact hA
  obtain ⟨k,hK,hD⟩ := H
  let a := depthRate i
  obtain ⟨_,q,hq⟩ := trip_cut (show Trip x s (l++(D++m)) from he)
  obtain ⟨hX,_,_⟩ := trip_cut hq
  have hY : b.post.here=q.here := hX.2.1.lower.here.trans (congrArg Scene.here hX.1)
  have hy : dye b.post=dye q := (trip_attend hX b List.mem_cons_self).2.2.2.2
  have HV (c : Beat M) (hc : c∈D) (hA : ¬betweenS z n c) :
      innerV S c.post := by
    have hr := trip_attend hX c hc
    refine h₂ i hI M b.post c.post (by rw [hY]; exact hr.2.2.2.1)
      (hr.2.2.2.2.trans hy.symm) hr.1.climb u v k hK hD ?_
    intro hi hx
    have HX := hf hi
    exact hA (hz (l++D) m (by unfold L; rw [List.append_assoc]) HX c (by simp [hc]) hx)
  let P := proceeds x u
  have HA : 1 ≤ mainRatio i j L := mainRatio_one i j he
  have hc (v' w q' : Path M) (hiD : D=v'++(w++q')) (hiA : ∀ b∈w, ¬betweenS z n b) :
      ‖subtotal P w‖ ≤ 10^16*(fullFax w+mainRatio i j L) := by
    have hp₁ : Trip x q (v'++(w++q')) := hiD ▸ hX
    have hp₂ : L=l₀++(((l₁++v')++(w++(q'++m)))) := by
      unfold L; rw [hL,hiD]; simp only [List.append_assoc]
    have hp₃ : l₁++(b::(r++m))=(l₁++v')++(w++(q'++m)) := by
      change l₁++(D++m)=_
      rw [hiD]; simp only [List.append_assoc]
    let K := (l₁++v')++(w++(q'++m))
    obtain ⟨hU,c₀,hc₀⟩ := trip_cut (show Trip x s (l₀++K) from hp₂ ▸ he)
    have hi₁ := possible S (l₁++v') w (q'++m) hc₀
      (fun b hb => HV b (by rw [hiD]; simp [hb]) (hiA b hb)) t (hp₃ ▸ HT)
    have hi₂ : yieldW (subtotal (duties x v) w) ≤ 10^15*(fullFax w + mainRatio i j L) := by
      apply hi₁.trans; unfold mainRatio
      change 10^15*(fullFax w+(1+fullKills K+flagged S K)/a+a*t) ≤
        10^15*(fullFax w+((1+fullKills L+flagged S L)/a+a*t))
      have ht₁ : fullKills K ≤ fullKills L := by
        rw [hp₂,show fullKills (l₀++K)=fullKills l₀+fullKills K from subtotal_app killed _ _]
        exact le_add_of_nonneg_left (trip_K hU)
      have ht₂ : flagged S K ≤ flagged S L := by
        rw [hp₂,show flagged S (l₀++K)=flagged S l₀+flagged S K from subtotal_app _ _ _]
        exact le_add_of_nonneg_left (flagged_pos S hU)
      have ha : 0 < a := (rate_easy i).1
      have HE : (1+fullKills K+flagged S K)/a ≤ (1+fullKills L+flagged S L)/a :=
        div_le_div_of_nonneg_right (by linarith) ha.le
      linarith
    have hi₃ := h₃ i hI
    have hga : 64*q.here.len*rad (u-v-k) ≤ 4 := by
      have HE : b.post.here.len*rad (u-v-k) ≤ 2*sig j :=
        halo_limit b.post j i true _ (below_refl _) hD
      rw [←hY]; nlinarith [hi₃.2, side_le i, side_pos i]
    have HB := below_decode u v k x (dye b.post) v' w q' hp₁ hy (hK.trans (hi₃.1.trans (side_le i)))
    apply HB.trans
    obtain ⟨_,C,Hc⟩ := trip_cut hp₁
    linarith [trip_fax (trip_cut Hc).1]
  obtain ⟨w,v,q,hD',hw,hp,hq⟩ := slab_on _ _ (matrix_trip D hX) z n
  let K := mainRatio i j L
  have Heq : mainSticker i j L=K+(n:ℝ) := rfl
  have HW : D=w++(v++q) := by rw [hD',List.append_assoc]
  have HA₁ := hc [] w (v++q) (by simpa using HW) hw
  have HA₂ := hc (w++v) q [] (by simpa using hD') hp
  obtain ⟨hw',q₀,Hh⟩ := trip_cut (show Trip x _ (w++(v++q)) from HW ▸ hX)
  obtain ⟨hv',q₁,hq₁⟩ := trip_cut Hh
  rw [Heq,hD',subtotal_app,subtotal_app]
  change ‖subtotal P w + subtotal P v + subtotal P q‖ ≤ _
  apply (norm_add_le _ _).trans
  have he' : (v.length:ℝ) ≤ n := by exact_mod_cast hq
  have HE := straight_fee u v hv'
  change ‖subtotal P v‖ ≤ _ at HE
  change 1 ≤ K at HA
  change _ ≤ 10^16* (fullFax w+K) at HA₁
  change _ ≤ 10^16*(fullFax q+K) at HA₂
  have HE : fullFax (w++v++q)=fullFax w+fullFax v+fullFax q := by
    rw [fullFax,subtotal_app,subtotal_app]; rfl
  rw [HE]
  linarith [norm_add_le (subtotal P w) (subtotal P v),trip_fax hw',trip_fax hv',trip_fax hq₁]

/-- Scalar suffix exact part with mask specified by chosen representative. -/
def guardedV (i : ℕ) (v : Grid M) (b : Beat M) := guarded v (side i) b.post

def ampU (s : Scene M) (u : Grid M) :=
    max ‖scalar (s.smaller false) u‖ ‖scalar (s.smaller true) u‖

lemma mask_estimate :
    ∀ᶠ j : ℕ in atTop, ∀ M J i : ℕ, ∀ s : Scene M, ∀ f : Grid M → ℝ,
      ∀ l r m : Path M, ∀ b : Beat M, ∀ x u : Grid M,
        let g := tagL i
        let D := b::r
        let L := l++(D++m)
        let p := heroPlot g L
        Cast j J f s L → Trip x s L → ringing u p j l b →
          ∃ v : Grid M, let μ := guardedV i v
            ‖subtotal (aired μ x u) D‖ ≤ 20000*scalarSticker i j L ∧
            ∀ z∈D, ¬μ z → 4*side i < ampU z.post u := by
  filter_upwards [live_rec] with j hj M J i s f l r m b x u g D L p h ht hp
  let y := side i
  have Hg : entitled g s j := fun H => False.elim (Bool.noConfusion H)
  obtain ⟨v,hA,l₀,l₁,hL,hT⟩ := hj M J s f u g l (r++m) b h Hg hp
  have HK : rad (u-v) ≤ 2*spotLimit b.post j i false := by
    change aligned p b.post j u v at hA
    unfold aligned at hA; rw [ite_eq_right (show p.main ≠ true from Bool.false_ne_true)] at hA; exact hA
  obtain ⟨_,q,hq⟩ := trip_cut (show Trip x s (l++(D++m)) from ht)
  have HX := (trip_cut hq).1
  have HE : b.post.here=q.here := HX.2.1.lower.here.trans (congrArg Scene.here HX.1)
  have hb : b.post.here.len*rad (u-v) ≤ 2*(y^4/65536) := halo_limit _ j i false _ (below_refl _) HK
  let a := depthRate i
  have ha : 0 < a ∧ a ≤ 1 ∧ a^2=y := rate_easy i
  have hy : 0 < y := side_pos i
  have hf : y^4 ≤ y := by simpa using pow_le_pow_of_le_one hy.le (side_le i) (by omega : 1≤4)
  refine ⟨v,?_⟩
  intro μ
  let t := timex g j L
  have hp₂ : L=l₀++(l₁++(D++m)) := by unfold L; rw [hL,List.append_assoc]
  constructor
  · have ht₀ : 2*log (coldScore v y (l₁++D++m)) ≤ t := by
      apply le_trans _ hT
      simp only [g,tagL,recital,Bool.false_eq_true,↓reduceIte,List.append_assoc]
      exact le_rfl
    obtain ⟨hU,c₀,hc₀⟩ := trip_cut (show Trip x s (l₀++(l₁++(D++m))) from hp₂ ▸ ht)
    have He : Trip x c₀ (l₁++D++m) := by rwa [List.append_assoc]
    have HR : aired μ x v = frosty x v y := by
      funext b; unfold aired frosty prize
      split_ifs with h1 h2 h2
      · rfl
      · exact (h2 h1).elim
      · exact (h1 h2).elim
      simp
    have Hx := rail_fee u v μ [] D [] (s:=q) (by simpa using HX)
    have HV := frosty_portion v hy (side_le i) l₁ D m He t ht₀
    have H := norm_add_le (subtotal (aired μ x u) D-chi (u-v) x*subtotal (aired μ x v) D)
      (chi (u-v) x*subtotal (aired μ x v) D)
    rw [sub_add_cancel,norm_mul,norm_chi,one_mul,HR] at H
    have hE' : fullKills (l₁++D++m) ≤ fullKills L := by
      rw [hp₂,List.append_assoc,show fullKills (l₀++(l₁++(D++m)))=fullKills l₀+fullKills (l₁++(D++m)) from subtotal_app killed _ _]
      exact le_add_of_nonneg_left (trip_K hU)
    have hV : 0 ≤ fullKills L := trip_K ht
    have hY : 0 ≤ t := (timex_scores g j _).1
    apply H.trans
    rw [HR,← HE] at Hx
    change _ ≤ 12000*a*_ at HV
    change _ ≤ 20000*(a*(1+fullKills L+t))
    nlinarith
  · intro z hz hμ
    obtain ⟨hz₁,hz₂,hz₃,hz₄,hz₅⟩ := trip_attend HX z hz
    rw [←HE] at hz₄
    change ¬∀ k, ‖scalar (z.post.smaller k) v‖ ≤ 10*y at hμ
    push Not at hμ
    obtain ⟨c,hc⟩ := hμ
    let d := z.post.smaller c
    have H1 := hz₁.climb.child c
    have H2 := scalar_compare d u v H1.ready H1.pos.le 4 H1.lift
    have H3 : d.here.len ≤ b.post.here.len :=
      node_compress (below_trans (child_below _ _) hz₄)
    have HH' : ‖scalar d u‖ ≤ ampU z.post u := by unfold d ampU; cases c; exact le_max_left _ _; exact le_max_right _ _
    change _ < ‖scalar d v‖ at hc
    change 4*y < _
    nlinarith [(abs_le.mp H2).1,rad_nonneg (u-v)]

end Troupe


end FourierLLogL.Dyadic.Procedure.Paths

end OAI
