import OAI.Analysis.Kaplansky.Main
import OAI.Analysis.Kaplansky.Ultrapower.ApproxPolar

namespace OAI

noncomputable section

namespace KaplanskyConsequences.QuasiValue

open scoped ComplexOrder
open PolarScalar
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
variable {A : Type*} [CStarAlgebra A]

lemma polarCut_defect_square (x : A) {r : ℝ} (hr : 0 < r) :
    star (polarCut x r*star (polarCut x r)*polarCut x r-polarCut x r)*
      (polarCut x r*star (polarCut x r)*polarCut x r-polarCut x r) =
        cfc (fun t => cut r t*(cut r t-1)^2) (star x*x) := by
  let v := polarCut x r
  let e := spectralCut x r
  have hv : star v*v=e := polarCut_square x hr
  have he : IsSelfAdjoint e := (spectralCut_nonneg x hr).isSelfAdjoint
  have hf := (continuous_cut hr).continuousOn (s:=spectrum ℝ (star x*x))
  have hb : IsSelfAdjoint (star x*x) := (star_mul_self_nonneg x).isSelfAdjoint
  calc
    star (v*star v*v-v)*(v*star v*v-v) = (e-1)*e*(e-1) := by
      have h : v*star v*v-v=v*(e-1) := by rw [← hv]; noncomm_ring
      rw [h,star_mul,star_sub,he.star_eq,star_one]
      calc
        (e-1)*star v*(v*(e-1)) = (e-1)*(star v*v)*(e-1) := by noncomm_ring
        _ = _ := by rw [hv]
    _ = cfc (fun t => (cut r t-1)*cut r t*(cut r t-1)) (star x*x) := by
      rw [cfc_mul (fun t => (cut r t-1)*cut r t) (fun t => cut r t-1) _
        ((hf.sub continuousOn_const).mul hf) (hf.sub continuousOn_const),
        cfc_mul (fun t => cut r t-1) (cut r) _ (hf.sub continuousOn_const) hf,
        cfc_sub (cut r) (fun _ => 1) _ hf continuousOn_const,cfc_const_one ℝ (star x*x)]
      rfl
    _ = _ := by congr 1; funext t; ring

lemma val_sub_commute (V : QuasiValue A) {a b : A} (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b)
    (hc : Commute a b) : V.val (a-b)=V.val a-V.val b := by
  have hn := V.smul (-1) b
  simp only [neg_one_smul,neg_mul,one_mul] at hn
  rw [sub_eq_add_neg,V.add_commute ha hb.neg hc.neg_right,hn,sub_eq_add_neg]

lemma spectralCut_commute (x : A) (r s : ℝ) : Commute (spectralCut x r) (spectralCut x s) :=
  (((Commute.refl (star x*x)).cfc_real (cut r)).symm.cfc_real (cut s)).symm

lemma polarCut_q_defect (V : QuasiValue A) (x : A) {r : ℝ} (hr : 0 < r) :
    V.q (polarCut x r*star (polarCut x r)*polarCut x r-polarCut x r) ≤
      V.val (spectralCut x (r/2))-V.val (spectralCut x r) := by
  have hf := (continuous_cut hr).continuousOn (s:=spectrum ℝ (star x*x))
  have hg := (continuous_cut (half_pos hr)).continuousOn (s:=spectrum ℝ (star x*x))
  have hc := spectralCut_commute x (r/2) r
  rw [← V.val_sub_commute (spectralCut_nonneg x (half_pos hr)).isSelfAdjoint
    (spectralCut_nonneg x hr).isSelfAdjoint hc]
  apply V.mono (star_mul_self_nonneg _)
  rw [polarCut_defect_square x hr]
  change _ ≤ cfc (cut (r/2)) (star x*x)-cfc (cut r) (star x*x)
  rw [← cfc_sub (cut (r/2)) (cut r) _ hg hf]
  apply (cfc_le_iff _ _ _ (hf.mul ((hf.sub continuousOn_const).pow 2)) (hg.sub hf)
    (star_mul_self_nonneg x).isSelfAdjoint).mpr
  intro t ht
  exact cut_gap hr (spectrum_nonneg_of_nonneg (star_mul_self_nonneg x) ht)

lemma spectralCut_val_bound (V : QuasiValue A) (x : A) {r : ℝ} (hr : 0 < r) :
    0 ≤ V.val (spectralCut x r) ∧ V.val (spectralCut x r) ≤ 1 :=
  ⟨V.nonneg (spectralCut_nonneg x hr),
    (le_abs_self _).trans ((V.bound _).trans (spectralCut_norm x hr))⟩

lemma spectralCut_val_mono (V : QuasiValue A) (x : A) {r s : ℝ}
    (hr : 0 < r) (hs : 0 < s) (hrs : r ≤ s) :
    V.val (spectralCut x s) ≤ V.val (spectralCut x r) := by
  apply V.mono (spectralCut_nonneg x hs)
  apply (cfc_le_iff _ _ _ (continuous_cut hs).continuousOn (continuous_cut hr).continuousOn
    (star_mul_self_nonneg x).isSelfAdjoint).mpr
  intro t ht
  exact cut_mono hr hs (spectrum_nonneg_of_nonneg (star_mul_self_nonneg x) ht) hrs

lemma exists_good_polarCut (V : QuasiValue A) (x : A) {ε : ℝ} (hε : 0 < ε) :
    ∃ r : ℝ, 0 < r ∧ V.q (polarCut x r*star (polarCut x r)*polarCut x r-polarCut x r) < ε ∧
      ‖polarCut x r*CFC.sqrt (star x*x)-x‖^2 ≤ ε := by
  let S : Set ℝ := {t | ∃ r : ℝ, 0 < r ∧ t=V.val (spectralCut x r)}
  have hS : S.Nonempty := ⟨_,1,zero_lt_one,rfl⟩
  have hb : BddAbove S := ⟨1,by rintro t ⟨r,hr,rfl⟩; exact (spectralCut_val_bound V x hr).2⟩
  obtain ⟨_,⟨s,hs,rfl⟩,hlt⟩ := exists_lt_of_lt_csSup hS (sub_lt_self (sSup S) hε)
  let r := min s ε
  have hr : 0 < r := lt_min hs hε
  have hsup : V.val (spectralCut x (r/2)) ≤ sSup S :=
    le_csSup hb ⟨r/2,half_pos hr,rfl⟩
  have hmono := spectralCut_val_mono V x hr hs (min_le_left s ε)
  refine ⟨r,hr,?_,(polarCut_error_norm x hr).trans (min_le_right s ε)⟩
  have hq := polarCut_q_defect V x hr
  linarith

lemma exists_approx_polar (V : QuasiValue A) (x : A) {ε : ℝ} (hε : 0 < ε) :
    ∃ v : A, ‖v‖ ≤ 1 ∧ V.q (v*star v*v-v) < ε ∧
      ‖v*CFC.sqrt (star x*x)-x‖^2 ≤ ε := by
  obtain ⟨r,hr,hq,hn⟩ := exists_good_polarCut V x hε
  exact ⟨polarCut x r,polarCut_norm x hr,hq,hn⟩


end KaplanskyConsequences.QuasiValue

end

end OAI
