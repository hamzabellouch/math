import OAI.Combinatorics.HadwigerCounterexample.HistogramBounds

namespace OAI

/-! # Conditional Projection -/

noncomputable section
namespace HadwigerCounterexample
open Finset Real Function
open scoped BigOperators
variable {A B C K : Type} [Fintype A] [Fintype B] [Fintype C]

def dip (μ f g : Wgt A) := avg μ (fun i => f i*g i)
def ode (μ f : Wgt A) := dip μ f f
def cashbook (μ : Wgt A) (f : A→B) (g : Wgt A) :=
  fun i => mapW (fun x => μ x*g x) f i / mapW μ f i
def banner (μ : Wgt A) (f : A→B) (g : Wgt A) := cashbook μ f g ∘ f

theorem ode_nonneg {μ : Wgt A} (hμ : ∀ i,0 ≤ μ i) (f : Wgt A) : 0≤ ode μ f :=
  avg_nonneg hμ (fun _ => mul_self_nonneg _)
theorem ode_upper {μ : Wgt A} (hμ : SubLaw μ) (f : Wgt A) (B : ℝ)
    (hf : ∀ i,|f i|≤B) : ode μ f ≤ B^2 := by
  apply hμ.avg_le (sq_nonneg _)
  intro i
  exact (le_of_eq (Eq.symm (pow_two _))).trans
    ((le_of_eq (sq_abs (f i)).symm).trans (pow_le_pow_left₀ (abs_nonneg _) (hf i) 2))

theorem dip_sym (μ f g : Wgt A) : dip μ f g=dip μ g f := by unfold dip; simp only [mul_comm]
theorem dip_sub (μ f g h : Wgt A) :
    dip μ (fun i=> f i-g i) h=dip μ f h-dip μ g h := by
  unfold dip; simp only [sub_mul,avg_sub]

omit [Fintype B] in
theorem cashbook_bound (μ : Wgt A) (hμ : ∀ i,0≤ μ i) (f : A→B) (g : Wgt A)
    (b : ℝ) (hb : 0≤b) (h : ∀ i,|g i|≤b) (i) : |cashbook μ f g i| ≤ b := by
  have he : cashbook μ f g i=avg (onW μ (fun x=>f x=i)) g := by
    unfold cashbook onW
    rw [avg_norm,subW_tot]
    unfold mapW pr avg subW; congr 1
    exact Finset.sum_congr rfl fun j _ => by ring
  have hw : SubLaw (onW μ (fun x=>f x=i)) := normW_subLaw (subW_nonneg hμ _)
  rw [he]
  exact (abs_avg_le hw.nz).trans (hw.avg_le hb h)

theorem cash_orth (μ : Wgt A) (hμ : ∀ i,0≤ μ i) (f : A→B) (g : Wgt A) (h : Wgt B) :
    dip μ (banner μ f g) (h ∘ f)=dip μ g (h ∘ f) := by
  classical
  let w := fun x=> μ x*g x
  have he : pour μ f (mapW w f) = fun i => μ i*banner μ f g i := rfl
  have hz : lsupp w μ := fun _ hi => left_ne_zero_of_mul hi
  have ht := map_pour μ f _ (hz.map hμ f)
  rw [he] at ht
  have hi := congrArg (fun w' => avg w' h) ht
  simp_rw [mapW_avg] at hi
  simpa only [w,dip,avg,mul_assoc,Function.comp_apply] using hi

theorem ode_step (μ : Wgt A) (hμ : ∀ i,0≤ μ i) (f : Wgt A)
    (p : A→B) (q : B→C) :
    ode μ (banner μ p f)=ode μ (banner μ (q∘p) f)+
      ode μ (fun i => banner μ p f i - banner μ (q∘p) f i) := by
  classical
  let g := banner μ p f; let h := banner μ (q ∘ p) f
  have hh : ode μ h=dip μ g h :=
    (cash_orth μ hμ (q∘p) f (cashbook μ (q∘p) f)).trans
      (cash_orth μ hμ p f (cashbook μ (q∘p) f ∘ q)).symm
  have hi i : (g i - h i)*(g i-h i)=g i*g i - 2*(g i*h i)+h i*h i := by ring
  change ode μ g=ode μ h+dip μ (fun i => g i-h i) (fun i=>g i-h i)
  unfold dip
  simp_rw [hi,avg_add,avg_sub,avg_mul']
  change ode μ g=ode μ h+(ode μ g-2*dip μ g h + ode μ h)
  linarith only [hh]

theorem archive_gain {μ : Wgt A} (hw : SubLaw μ) (f : Wgt A)
    (p : A→B) (q : B→ C)
    (h : Wgt B) (hh : ∀ i:A,|h (p i)| ≤1) :
    (dip μ (fun i => f i - banner μ (q∘p) f i) (h ∘ p))^2 ≤
      ode μ (banner μ p f)-ode μ (banner μ (q∘p) f) := by
  let u := banner μ p f; let v := banner μ (q∘p) f
  let w i := u i-v i
  rw [ode_step μ hw.nz f p q]
  have he : dip μ (fun i=> f i - banner μ (q∘p) f i) (h∘p)=dip μ w (h∘p) := by
    unfold w
    rw [dip_sub,dip_sub,cash_orth μ hw.nz p f h]
  have ht : ode μ (h∘p) ≤ 1 := (ode_upper hw (h∘p) 1 hh).trans_eq (by ring)
  have hq : dip μ w (h∘p)^2≤ode μ w*ode μ (h∘p) := by
    simpa only [ode,dip,pow_two] using avg_CS hw.nz w (h∘p)
  rw [he]
  apply le_trans hq
  refine (mul_le_mul_of_nonneg_left ht (ode_nonneg hw.nz w)).trans_eq ?_
  unfold w u v
  ring
end HadwigerCounterexample

end

end OAI
