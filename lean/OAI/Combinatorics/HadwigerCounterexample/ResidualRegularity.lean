import OAI.Combinatorics.HadwigerCounterexample.RectangleRegularity

namespace OAI

/-! # Residual Regularity -/

noncomputable section
namespace HadwigerCounterexample
open Finset Matrix LinearMap Function Filter Real
open scoped BigOperators
variable {A B I : Type} [Fintype A] [Fintype B] [Fintype I]

def wanes (u : Wgt I) (w : Wgt A) (f : I→Wgt A) (p : A→B) (ε : ℝ) :=
  ∀ h : Wgt A,(∀ x,|h x| ≤ 1) →
    avg u (fun i => |dip w (fun x=> f i x - banner w p (f i) x) h|) ≤ ε
def hits (u : Wgt I) (w : Wgt A) (f : I→ Wgt A) (p : A→ B) :=
  avg u (fun i => ode w (banner w p (f i)))

private def twistSign (b : ℝ) := decide (0≤ b)
private theorem twistabs (b : ℝ) : b*swab (twistSign b)=|b| := by
  classical by_cases h : 0≤b <;> simp [swab,twistSign,h,abs_of_nonneg,abs_of_neg,lt_of_not_ge]

set_option maxHeartbeats 600000 in
theorem tilt_test (w : Wgt A) (u : Wgt I) (hu : ∀ i,0 ≤ u i) (f : I → Wgt A) (h : Wgt A)
    (hh : ∀ x,|h x|≤1) :
    ∃ p : A→Bool, avg u (fun i=>|dip w (f i) h|) ≤ avg u (fun i => |dip w (f i) (swab∘ p)|) := by
  classical
  let q (i:I) := swab (twistSign (dip w (f i) h))
  let V (x) := avg u (fun i=> f i x * q i)
  have hx (h : Wgt A) :
      avg u (fun i=> dip w (f i) h * q i)=dip w V h := by
    unfold V dip; simp_rw [← avg_mul]
    rw [avg_avg]
    refine avg_congr fun i _=> avg_congr fun j _=>by ring
  let p (x:A) := twistSign (w x*V x)
  refine ⟨p,?_⟩
  have hV : dip w V h ≤ dip w V (swab ∘ p) := by
    unfold dip avg; refine Finset.sum_le_sum fun i _=> ?_
    dsimp only [Function.comp_apply,p]
    set t := w i*V i with ht
    rw [←mul_assoc,←mul_assoc,←ht,twistabs]
    refine (le_abs_self _).trans ?_
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left (hh _) (abs_nonneg _)).trans_eq (mul_one _)
  have h0 i :
      |dip w (f i) h|=dip w (f i) h*q i := (twistabs ..).symm
  simp_rw [h0,hx]; rw [←hx (swab ∘ p)] at hV
  apply le_trans hV
  apply avg_mono hu
  intro i
  rw [← show |dip w (f i) (swab∘p)* q i|=|dip w (f i) (swab∘p)| by rw [abs_mul,swab_abs,mul_one]]
  exact le_abs_self _

theorem mean_sq (u : Wgt I) (hu : IsLaw u) (f : Wgt I) :
    avg u f ^ 2 ≤ avg u (fun i=> f i^2) := by
  simpa only [mul_one,one_pow, hu.avg_const] using avg_CS hu.nz f (fun _=>1)

set_option maxHeartbeats 800000 in
theorem erosive (M ε : ℝ) (hM : 0≤M) (hε : 0<ε) :
    ∃ k:ℕ,∀ (A I : Type) [Fintype A] [Fintype I]
      (u : Wgt I) (w : Wgt A) (f : I→Wgt A),
      IsLaw u → IsLaw w → (∀ i j,|f i j|≤ M) →
      ∃ l:ℕ,l≤ k∧∃ p:A→Fin l,wanes u w f p ε := by
  classical
  obtain ⟨n,hn⟩:=exists_nat_gt (M^2/ε^2)
  rw [div_lt_iff₀ (by positivity)] at hn
  refine ⟨2^n,fun A I _ _ u w f hu hw hf =>?_⟩
  by_contra! h
  have hh (i:ℕ) (hi : i≤ n) :
      ∃ p : A→ Fin (2^i),i*ε^2 ≤ hits u w f p := by
    induction i with
    | zero => exact ⟨fun _=>0,(by simp only [Nat.cast_zero,zero_mul,hits]; exact avg_nonneg hu.nz (fun i=>ode_nonneg hw.nz _))⟩
    | succ i ih =>
      obtain ⟨p,hp⟩:=ih (by omega)
      obtain h := h (2^i) (Nat.pow_le_pow_right (by decide) (by omega)) p
      let T (i:I) (x:A) := f i x-banner w p (f i) x
      unfold wanes at h; push Not at h; obtain ⟨a,ha,h⟩:=h
      obtain ⟨s,hs⟩:=tilt_test w u hu.nz T a ha
      let q:= swab∘s
      let e : (Fin (2^i) × Bool)≃ Fin (2^(i+1)) := Fintype.equivFinOfCardEq (by simp [pow_succ])
      let b x := e (p x,s x)
      let P := Prod.fst ∘ e.symm; let Q:= swab ∘ Prod.snd ∘ e.symm
      have hP : P∘b=p := by funext i; simp [P,b]
      have hQ : Q∘b=q := by funext i; simp [q,Q,b]
      have he x : ode w (banner w p (f x)) + dip w (T x) q ^2 ≤ ode w (banner w b (f x)) := by
        have he := archive_gain hw.sub (f x) b P Q (fun i=>by unfold Q; simp [swab_abs])
        rw [hP,hQ] at he
        change ode _ _+dip w (fun i=> f x i-banner w p (f x) i) q ^2≤_
        linarith only [he]
      let V i:= |dip w (T i) q|
      have hz : ε ≤ avg u V := h.le.trans hs
      have hb := (pow_le_pow_left₀ hε.le hz 2).trans (mean_sq u hu V)
      have hh := avg_mono hu.nz he
      rw [avg_add] at hh
      change hits u w f p + _ ≤ hits u w f b at hh
      unfold V at hb; simp_rw [sq_abs] at hb
      refine ⟨b,?_⟩
      push_cast; linarith only [hp,hb,hh]
  obtain ⟨p,hp⟩ := hh n le_rfl
  have h (i:I) : ∀ x:A,|banner w p (f i) x|≤ M :=
    fun i'=> cashbook_bound w hw.nz p _ _ hM (hf i) (p i')
  exact not_lt_of_ge (hp.trans (hu.avg_le (fun i=> ode_upper hw.sub _ M (h i)))) hn
end HadwigerCounterexample

end

end OAI
