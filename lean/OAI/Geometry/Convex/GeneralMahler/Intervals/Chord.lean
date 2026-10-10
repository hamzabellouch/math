import OAI.Geometry.Convex.GeneralMahler.Intervals.JCalc

namespace OAI
/-! Interpolation/range certificate through second derivatives. -/
open Set Filter Real
namespace GeneralMahler
namespace Jet
variable {f g h:ℝ→ℝ}
def mix (x y a:ℝ):=(1-a)*x+a*y

lemma convex_err_upper (hf:∀ x,HasDerivAt f (g x) x)
    (hg:∀ x,HasDerivAt g (h x) x) {x y a:ℝ} (hm:x≤y) (ha:a∈Set.Icc (0:ℝ) 1)
    (K:ℝ) (hK:0≤K) (he:∀ z∈Set.Icc x y,-K ≤ h z):
    f (mix x y a)-mix (f x) (f y) a≤K/8*(y-x)^2 := by
  let b := fun x=> K/2*x*x
  let u := fun x=> f x+b x
  let v := fun x=> g x+K*x
  have h₁(x:ℝ): HasDerivAt u (v x) x := by
    apply (hf x).fun_add
    convert ((((hasDerivAt_id' x).const_mul (K/2)).mul (hasDerivAt_id' x))) using 1
    all_goals first|rfl|ring
  have h₂(x:ℝ): HasDerivAt v (h x+K) x := by
    apply (hg x).fun_add
    convert ((hasDerivAt_id' x).const_mul K) using 1; first|rfl|ring
  have hu := convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc x y)
    (f:=u) (f':=v) (f'':=fun x=>h x+K) (fun x _=> (h₁ x).continuousAt.continuousWithinAt)
    (fun x _=> (h₁ x).hasDerivWithinAt) (fun x _=> (h₂ x).hasDerivWithinAt)
    (fun z hz=> by linarith [he z (interior_subset hz)])
  have ht:= hu.2 (show x∈Set.Icc x y from ⟨le_rfl,hm⟩) (show y∈Set.Icc x y from ⟨hm,le_rfl⟩)
    (sub_nonneg.mpr ha.2) ha.1 (sub_add_cancel 1 a)
  change u (mix x y a) ≤ mix (u x) (u y) a at ht
  have hv : mix (u x) (u y) a = mix (f x) (f y) a+mix (b x) (b y) a := by unfold mix u;ring
  rw [hv] at ht
  have hh : mix (b x) (b y) a-b (mix x y a)=K/2*(y-x)^2*(a*(1-a)):=by unfold mix b; ring
  have hp:= mul_le_mul_of_nonneg_left (show a*(1-a) ≤ 1/4 from by nlinarith [sq_nonneg (a-1/2)])
    (show 0≤ K/2*(y-x)^2 from by positivity)
  change f (mix x y a)+ _≤ _ at ht
  linarith

lemma chord_error (hf:∀ x,HasDerivAt f (g x) x)
    (hg:∀ x,HasDerivAt g (h x) x) {x y a:ℝ} (hm:x≤y) (ha:a∈Set.Icc (0:ℝ) 1)
    (K:ℝ) (hK:0≤K) (he:∀ z∈Set.Icc x y,|h z| ≤ K):
    |f (mix x y a)-mix (f x) (f y) a|≤K/8*(y-x)^2 := by
  have h:= convex_err_upper hf hg hm ha K hK fun z hz=> (abs_le.mp (he z hz)).1
  have h₁:= convex_err_upper (fun x=>(hf x).neg) (fun x=>(hg x).neg) hm ha K hK (fun z hz=> neg_le_neg (le_of_abs_le (he z hz)))
  apply abs_le.mpr
  refine ⟨?_,h⟩
  change -f _-mix (-f x) (-f y) _≤_ at h₁; unfold mix at *; linarith
lemma mix_exists {x y z:ℝ} (h:x≤z) (he:z≤y) :
    ∃ a∈Set.Icc (0:ℝ) 1,z=mix x y a := by
  rcases lt_or_eq_of_le (h.trans he) with ht|ht
  · refine ⟨(z-x)/(y-x),⟨div_nonneg (by linarith) (by linarith),
      (div_le_one (by linarith)).mpr (by linarith)⟩,?_⟩
    unfold mix; field_simp; ring
  have hz:= le_antisymm h (he.trans ht.symm.le)
  exact ⟨0,⟨le_rfl,zero_le_one⟩,by simp [mix,hz]⟩
end Jet
namespace Cert.IV
open Jet
-- largest norm limit as point
def limK : IV→IV
  | unk=>unk
  | box a b=>let c:=max (-a) (max 0 b); box c c
def Radius (D W:IV) := limK W/c 8 * sq D
def bcChord (D V W F:IV):=
  let R:=Radius D F
  IV.span V W+IV.span (-R) R

lemma box_mix {A B:IV} {x y:ℝ} (h:x∈A) (hh:y∈B) {c:ℝ} (hc:c∈Set.Icc (0:ℝ) 1):
    mix x y c∈ IV.span A B := by
  rcases le_total x y with he|he
  · apply span_conv h hh
    all_goals unfold mix; nlinarith [hc.1,hc.2]
  have hx : IV.span A B= IV.span B A := by cases A <;> cases B <;> simp [IV.span,max_comm,min_comm]
  rw [hx]
  apply span_conv hh h
  all_goals unfold mix; nlinarith [hc.1,hc.2]

private lemma lk_pos (a b:Int) : 0≤ w (max (-a) (max 0 b)) :=
  w0 ▸ (w_mono ((le_max_left ..).trans (le_max_right ..)))
private lemma lk_e (a b:Int) {x:ℝ} (ha:x∈box a b): |x|≤ w (max (-a) (max 0 b)) := by
  rw [w_max,w_max,w_neg,w0]
  rw [abs_le]; constructor
  · have hx:w a≤ x:=ha.1
    have hi: -w a ≤ max (-w a) (max 0 (w b)) := le_max_left ..
    linarith
  exact ha.2.trans ((le_max_right ..).trans (le_max_right ..))

lemma mcChord (X:RF) (h:TW univ X) (n:ℕ) (x y z:ℝ) (hx:x ≤ z)
    (hy:z≤y) (A B D F:IV)
    (ha:X x n∈A) (hb:X y n∈B) (hd:y-x∈D)
    (hf:∀ z∈Set.Icc x y,X z (n+2) ∈ F):
    X z n∈ bcChord D A B F := by
  cases F
  · cases D <;> cases A <;> cases B <;> trivial -- IV.mul on sq etc defeq maybe
  rename_i a b
  let K:= w (max (-a) (max 0 b))
  have hm : K∈limK (box a b):= ⟨le_rfl,le_rfl⟩
  have he8: (8:ℝ)∈ IV.c 8 := mc 8
  have hr:=mmul (mdiv hm he8) (msq hd)
  let r:= Radius D (box a b)
  obtain ⟨c,hc,hcx⟩:= mix_exists hx hy
  have he:= chord_error (fun t=>h n t (mem_univ _)) (fun t=>h (n+1) t (mem_univ _)) (hx.trans hy)
    hc K (lk_pos _ _) (fun t ht=> lk_e a b (hf t ht))
  change |X _ n-_| ≤ _ at he
  rw [← hcx] at he
  have hi:= abs_le.mp he
  have hh:= madd (box_mix ha hb hc) (span_conv (mneg hr) hr hi.1 hi.2)
  exact (show mix (X x n) (X y n) c + (X z n - mix (X x n) (X y n) c) = X z n by ring) ▸ hh
end Cert.IV
end GeneralMahler

end OAI
