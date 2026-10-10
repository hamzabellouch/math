import OAI.Analysis.FourierLLogL.Assembly.Tokens
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

lemma masked_split (m : Beat M → Prop) (x u : Grid M) (l : Path M) :
    subtotal (proceeds x u) l=subtotal (aired m x u) l+subtotal (aired (fun b => ¬m b) x u) l := by
  induction l with
  | nil => simp [subtotal]
  | cons b l ih =>
    simp only [subtotal_cons,ih]
    by_cases h : m b <;> unfold aired <;> simp only [h,not_false_eq_true,ite_false,ite_true,zero_add,not_true]
    all_goals abel

lemma subt_le {l : Path M} {f g : Beat M → ℝ} (h : ∀ b∈l, f b ≤ g b) :
    subtotal f l ≤ subtotal g l := by
  induction l with
  | nil => exact le_rfl
  | cons b l ih =>
    exact add_le_add (h b List.mem_cons_self)
      (ih (fun i hi => h i (List.mem_cons_of_mem _ hi)))

def crumb (n T j : ℕ) (L : Path M) :=
    20000*∑ i∈Finset.Ico n T, scalarSticker i j L

lemma start_ico (t n : ℕ) (h : n < t) (f : ℕ → ℝ) :
    ∑ i∈Finset.Ico n t,f i = f n+∑ i∈Finset.Ico (n+1) t,f i := by
  have he : Finset.Ico n t=insert n (Finset.Ico (n+1) t) := by
    ext i; simp only [Finset.mem_insert, Finset.mem_Ico]; omega
  rw [he, Finset.sum_insert (by simp)]

lemma scalar_stage :
    ∀ᶠ j : ℕ in atTop,
      ∀ (M J : ℕ) (s : Scene M) (c : Bool) (f : Grid M → ℝ) (x u : Grid M),
      let t := lowI j c
      let T := highI j M c
      ∀ (L : Path M) (a : Grade → ℕ), Cast j J f s L → Trip x s L → shades a u L j →
        ∀ (l r : Path M), L=l++r → (c=true→stall u (tagM (mainIx j)) j L l) →
          ‖subtotal (proceeds x u) l‖ ≤
            subtotal (token a L j c) l + crumb t T j L := by
  filter_upwards [mask_estimate] with j hj M J s c f x u t T L a h hh hV
  let P := proceeds x u
  let q := token a L j c
  suffices HE : ∀ k n : ℕ, t ≤ n → n+k=T → ∀ l r : Path M, L=l++r →
      (c=true → stall u (tagM (mainIx j)) j L l) →
      (∀ i∈Finset.Ico t n, stall u (tagL i) j L l) →
      ‖subtotal P l‖ ≤ subtotal q l+crumb n T j L by
    intro l r hx hf
    have hT : t ≤ T := Nat.le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _)
    exact HE (T-t) t (le_refl _) (by omega) l r hx hf (by simp)
  intro k
  induction k with
  | zero =>
    intro n hn hE l r hl hf he
    obtain rfl := (show T=n by omega)
    rw [show crumb T T j L=0 by simp [crumb],add_zero]
    apply (subt_norm l P).trans
    exact subt_le (fun b hb => direct_point hh j c a hV T l r b hf he ⟨hn,le_rfl⟩ hl hb (by omega))
  | succ k ih =>
    intro n hn hE l r hl hf he
    have hT : n < T := by omega
    have HV : crumb n T j L = 20000*scalarSticker n j L + crumb (n+1) T j L := by
      rw [crumb, start_ico T n hT,mul_add]; rfl
    rw [HV]
    let g := tagL n
    have HP (p w : Path M) (hL : l=p++w) (hh : stall u g j L p) :
        ‖subtotal P p‖ ≤ subtotal q p + crumb (n+1) T j L := by
      have hx (g) (hh : stall u g j L l) : stall u g j L p := by
        rw [hL] at hh
        exact ((mute_cat _ _ _ _ _ _).1 hh).1
      apply ih (n+1) (hn.trans (Nat.le_add_right n 1)) (by omega) p (w++r) ?_
        (fun H => hx _ (hf H))
      · intro i hi
        obtain ⟨h₁,h₂⟩ := Finset.mem_Ico.mp hi
        by_cases heq : i=n
        · subst heq; exact hh
        · exact hx _ (he _ (Finset.mem_Ico.mpr ⟨h₁,by omega⟩))
      rw [hl,hL,List.append_assoc]
    let p := heroPlot g L
    rcases first_on u p (vacant M) j l with H|⟨d,b,m,H,h₁,h₂⟩
    · have Hx := HP l [] (by simp) H
      have HE := scalarSticker_pos n j hh; linarith
    · let w := b::m
      let L' := d++(w++r)
      have HB : L=L' := by unfold L' w; rw [hl,H,List.append_assoc]
      have HC : ringing u (heroPlot g L') j d b := HB ▸ h₂
      have Hw : l=d++w := H
      obtain ⟨v,hX⟩ := hj M J n s f d m r b x u (show Cast j J f s L' from HB ▸ h) (show Trip x s L' from HB ▸ hh) HC
      let μ := guardedV n v; let Q := aired μ x u; let R := aired (fun z => ¬μ z) x u
      change ‖subtotal Q w‖ ≤ _*scalarSticker n j L' ∧ _ at hX
      have hx₁ : ‖subtotal Q w‖ ≤ 20000* scalarSticker n j L := by rw [HB]; exact hX.1
      have hx₂ : ‖subtotal R w‖ ≤ subtotal q w := by
        apply (subt_norm w R).trans; apply subt_le
        intro z hz
        unfold R aired; split
        · rename_i HH
          apply direct_point hh j c a hV n l r z hf he ⟨hn,hT.le⟩ hl (by rw [Hw]; simp [hz])
          intro _; exact hX.2 z hz HH
        · rw [norm_zero]; exact tokens_nonneg a L z j c
      rw [Hw,subtotal_app,subtotal_app,
        show subtotal P w=subtotal Q w+subtotal R w from masked_split μ x u w]
      apply (norm_add_le _ _).trans
      linarith [HP d w Hw h₁,norm_add_le (subtotal Q w) (subtotal R w)]

def bigCrumb (n t j : ℕ) (L : Path M) :=
    10^20* ∑ i∈Finset.Ico n t, mainSticker i j L

/-- Main handles a contour interval, consuming the small leading prefix only once. -/
lemma main_stage :
    ∀ᶠ j : ℕ in atTop, ∀ (M J : ℕ) (s : Scene M) (f : Grid M → ℝ) (x u : Grid M)
      (L : Path M), s.live=true → Cast j J f s L → Trip x s L →
        ∀ (v : ℝ),
          (∀ l r : Path M, L=l++r → (∀ i, i ≤ mainIx j → stall u (tagM i) j L l) →
            ‖subtotal (proceeds x u) l‖ ≤ v) →
          ‖subtotal (proceeds x u) L‖ ≤ v+10^20*fullFax L+
            bigCrumb 0 (mainIx j+1) j L := by
  filter_upwards [ride] with j hj M J s f x u L hs hc ht v hv
  let P := proceeds x u
  let T := mainIx j+1
  suffices H : ∀ k n : ℕ, n+k=T → ∀ (l r : Path M), L=l++r →
      (∀ i, i < n → stall u (tagM i) j L l) →
        ‖subtotal P l‖ ≤ v+10^20*fullFax l+bigCrumb n T j L from
    H T 0 (by omega) L [] (by simp) (by omega)
  intro k; induction k with
  | zero =>
    intro n hh l r he hf
    have HX : Trip x s (l++r) := he ▸ ht
    have hT : n=T := by omega
    cases hT
    have HH := hv l r he (fun i hi => hf i (Nat.lt_succ_of_le hi))
    have HJ := trip_fax (trip_cut HX).1
    simp only [bigCrumb,Finset.Ico_self,Finset.sum_empty,mul_zero,add_zero]
    unfold P; linarith
  | succ k ih =>
    intro n hn l r hl hf
    let g := tagM n; let p := heroPlot g L
    have hE : n < mainIx j+1 := Nat.lt_of_lt_of_le (by omega : n < T) (le_refl _)
    have hX : Cast j J f s (l++r) := hl ▸ hc
    have hY : Trip x s (l++r) := hl ▸ ht
    have HI (d w : Path M) (hD : l=d++w) (hh : stall u g j L d) :
        ‖subtotal P d‖ ≤ v+10^20*fullFax d+bigCrumb (n+1) T j L := by
      apply ih _ (by omega) d (w++r) ?_
      · intro i hi
        by_cases he : i=n; subst i; exact hh
        have H := hf i (by omega)
        rw [hD] at H
        exact ((mute_cat _ _ _ _ _ _).1 H).1
      rw [hl,hD,List.append_assoc]
    rw [show bigCrumb n T j L=10^20*mainSticker n j L+bigCrumb (n+1) T j L by
      unfold bigCrumb; rw [start_ico _ n hE,mul_add]]
    rcases first_on u p (vacant M) j l with H|⟨d,b,w,hD,hp,ha⟩
    · have HE := HI l [] (by simp) H
      linarith [mainSticker_pos n j ht]
    · let D := b::w; let X := d++(D++r)
      have heq : X = L := by unfold X D; rw [hl,hD,List.append_assoc]
      have H : Cast j J f s X := heq.symm ▸ hc; have HR : Trip x s X := heq.symm ▸ ht
      have HF : ringing u (heroPlot g X) j d b := by rw [heq]; exact ha
      have Ht (hh : 0 < n) : stall u (tagM (n-1)) j X (d++D) := by rw [heq]; exact (hD ▸ hf (n-1) (by omega))
      have HH := hj M J n s f d w r b x u H HR (fun _ => ⟨by change n ≤ mainIx j; omega,hs⟩) HF Ht
      change ‖subtotal P D‖ ≤ _*(fullFax D+mainSticker n j X) at HH
      rw [heq] at HH
      rw [show l=d++D from hD,subtotal_app,show fullFax (d++D)=fullFax d+fullFax D from subtotal_app billFax d D]
      apply (norm_add_le _ _).trans; linarith [HI d D hD hp]

def souvenir (c : Bool) (j : ℕ) (L : Path M) :=
    let t := lowI j c; let T := highI j M c
    tokenCost j c L+crumb t T j L+
      (if c then 10^20*fullFax L+bigCrumb 0 (mainIx j+1) j L else 0)

lemma gala :
    ∀ᶠ j : ℕ in atTop, ∀ (M J : ℕ), J ≤ M → ∀ s : Scene M, ∀ f : Grid M → ℝ,
      ∀ x u : Grid M, ∀ L : Path M, Cast j J f s L → Trip x s L →
        ‖subtotal (proceeds x u) L‖ ≤ souvenir s.live j L := by
  filter_upwards [scalar_stage, main_stage] with j hs hm M J hJ s f x u L h hh
  obtain ⟨a,ha⟩ := sheds h u
  let V (c : Bool) := tokenCost j c L+ crumb (lowI j c) (highI j M c) j L
  have HV (b : Bool) (l r : Path M) (he : L=l++r) (ht : b=true→stall u (tagM (mainIx j)) j L l) :
      ‖subtotal (proceeds x u) l‖ ≤ V b := by
    apply (hs M J s b f x u L a h hh ha l r he ht).trans
    apply add_le_add_left
    have hM : L.length ≤ M := by have HE := trip_depth_limit h; omega
    apply le_trans _ (max_tokens L hh a j b hM)
    obtain ⟨hx,V,hR⟩ := trip_cut (show Trip x s (l++r) from he ▸ hh)
    nth_rw 3 [he]
    exact le_trans (le_add_of_nonneg_right (trip_nonneg hR (f:=token a L j b)
      (fun i _ => tokens_nonneg _ _ _ _ _))) (le_of_eq (subtotal_app _ l r).symm)
  unfold souvenir
  by_cases HB : s.live=true
  · have HH := hm M J s f x u L HB h hh (V true) (fun l r hL he =>
      HV _ _ _ hL (fun _ => he _ (le_refl _)))
    rw [HB,ite_eq_left rfl]
    unfold V at HH; linarith
  rw [show s.live=false from Bool.eq_false_iff.mpr HB,ite_eq_right (by simp),add_zero]
  exact HV false L [] (by simp) fun h => Bool.noConfusion h

end Troupe


end FourierLLogL.Dyadic.Procedure.Paths

end OAI
