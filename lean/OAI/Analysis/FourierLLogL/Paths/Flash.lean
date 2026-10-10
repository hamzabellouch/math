import OAI.Analysis.FourierLLogL.Paths.Bridge
/-! # The uniform output path -/

open Function Set Filter
open scoped Topology BigOperators ComplexConjugate
noncomputable section

namespace OAI

namespace FourierLLogL.Dyadic.Procedure.Paths
open Law Node Real Period Compress.Params Thermal Fund Scene Fork Road Event Journal Wire Pulse Thread Capture Chart Snapshot
variable {M j J : ℕ} {s q : Scene M} {f : Grid M → ℝ}
open scoped Classical


namespace Beam

/-- Camera anchored at a jumping post. -/
structure Lamp (M : ℕ) where
  u : Grid M
  width : ℝ
  W : Paths.Vector M
  site : Scene M

namespace Lamp
def glint (e : Lamp M) (z : Grid M) :=
    glow (e.W z) (letter e.site e.u z) (e.width*matter e.site z)
def first (e : Lamp M) (z : Grid M) :=
    e.glint z 0 (factor e.site e.u z) (e.width*shell e.site z)
def second (e : Lamp M) (r : Bool) (q : Scene M) (z : Grid M) :=
    e.glint z ((curl r:ℂ)*factor e.site e.u z) (factor q e.u z) (e.width*shell q z)
def start (e : Lamp M) := ∑ z, first e z
def delayed (e : Lamp M) (r : Bool) (q : Scene M) := ∑ z, second e r q z

/-- update of accumulated same-parity output. -/
def carry (e : Lamp M) (r t : Bool) (z : Grid M) :=
    e.W z + (curl t:ℂ)*((curl r:ℂ)*factor e.site e.u z)

lemma flash_cell (e : Lamp M) (h : Climb e.site) (r t : Bool) (q : Scene M)
    (hq : Ideal (e.site.smaller r) q) (ha : 0 < e.width) (he : e.width ≤ 1)
    (z : Grid M) :
    let u := e.u
    let a := e.width
    let s := e.site
    let k := matter (s.smaller r) z-matter q z
    let C := 20*(pierce s z+pierce q z) + 400*((k+dew u s z+dew u q z)/a)
    prism (q.smaller t) u (e.carry r t) a z ≤
      prism s u e.W a z + curl r * e.first z + curl t * e.second r q z + 2*k+4*C := by
  intro u a s k C
  let w := s.smaller r; let y := q.smaller t
  let R := prism s u e.W a z
  let f (s) := letter s u z; let m (s) := matter s z
  let P (s) := factor s u z; let D (s : Scene M) := a*shell s z
  let X := curl r; let Y := curl t; let A := e.W z
  let F (x : Scene M) := a*m x
  let kill : ℂ := f q-f w; let lost : ℝ := F q-F w
  let g₀ := (↑X:ℂ)*P s; let g₁ := (↑Y:ℂ)*P q
  let gain := (↑Y:ℂ)*g₀; let plusf := g₀+kill+g₁
  let plusm := X*D s + lost + Y*D q
  have hk : ‖kill‖ ≤ k := by unfold kill; rw [norm_sub_rev]; exact matter_drain hq u z
  have hl : lost= -(a*k) := by unfold lost k F w m; ring
  have hp := (norm_nonneg kill).trans hk
  have hm : |lost|=a*k := by rw [hl,abs_neg,abs_of_nonneg (mul_nonneg ha.le hp)]
  have hs : |lost| ≤ k := by rw [hm]; nlinarith
  have hA : f y=f s+plusf := by
    have h1 : f w=f s+g₀ := letter_jump h r u z
    have h2 : f y=f q+g₁ := letter_jump hq.climb t u z
    rw [h2]; unfold plusf kill; rw [h1]; ring
  have hB : F y=F s+plusm := by
    have h1 : m w=m s+X*shell s z := matter_jump h r z
    have h2 : m y=m q+Y*shell q z := matter_jump hq.climb t z
    unfold F plusm lost D; unfold F; rw [h1,h2]; ring
  have h0 : 0 ≤ R := ray_pos _ _ _
  have hC : 0 ≤ C := by
    have h1 := pierce_nonneg h.fit z
    have h2 := pierce_nonneg hq.climb.fit z
    have h3 : 0 ≤ k+dew u s z+dew u q z := add_nonneg
      (add_nonneg hp (dew_nonneg u h z)) (dew_nonneg u hq.climb z)
    exact add_nonneg (mul_nonneg (by norm_num) (add_nonneg h1 h2))
      (mul_nonneg (by norm_num) (div_nonneg h3 ha.le))
  have hx : |X|=1 := curl_unit _; have hy : |Y|=1 := curl_unit _
  have HG : content gain plusf plusm ≤ R*(4*C) := by
    have HH := contest g₀ kill g₁ (X*D s) lost (Y*D q)
    have Heq : ‖g₀‖=‖P s‖ := by unfold g₀; rw [norm_scaleC,hx,one_mul]
    have Hf : ‖gain‖=‖g₀‖ := by unfold gain; rw [norm_scaleC,hy,one_mul]
    have Hf' : ‖g₁‖=‖P q‖ := by unfold g₁; rw [norm_scaleC,hy,one_mul]
    have HV : ‖P s‖^2+‖P q‖^2+D s^2+D q^2+
        ‖kill‖^2+(a*k)^2 ≤ R*C := by
      have H := extra_joints h u z r hq a ha he e.W
      unfold kill; rw [norm_sub_rev]; exact H
    rw [show content gain plusf plusm=‖gain‖^2+(‖plusf‖^2+plusm^2) by unfold content; ring,Hf,Heq]
    change ‖plusf‖^2 + plusm^2 ≤ _ at HH
    rw [Heq,Hf',mul_pow X (D s),mul_pow Y (D q),show X^2=1 from curl_sq _,show Y^2=1 from curl_sq _,hl] at HH
    nlinarith [sq_nonneg (D s),sq_nonneg (D q),sq_nonneg ‖P q‖,sq_nonneg ‖kill‖,sq_nonneg (a*k)]
  let glow' := glow A (f s) (F s)
  have HL : glow' gain plusf plusm =
      X*e.first z+glow' 0 kill lost+Y*e.second r q z := by
    unfold gain plusf plusm g₀ g₁ first second glint X Y glow'
    let F' := factor e.site e.u z
    let a' := curl r; let k' := curl t

    let L := e.glint z
    change L ((k':ℂ)*((a':ℂ)*F')) ((a':ℂ)*F'+kill+(k':ℂ)*P q)
      (a'*D s+lost+k'*D q)=a'*L 0 F' (D s)+L 0 kill lost+k'*L ((a':ℂ)*F') (P q) (D q)
    have h1 (v w p i : ℂ) (u y : ℝ) :
        L (v+p) (w+i) (u+y)=L v w u+L p i y := glow_add _ _ _ _ _ _ _ _ _
    have h2 (v : ℝ) (y : ℝ) (q w : ℂ) :
        L ((v:ℂ)*q) ((v:ℂ)*w) (v*y)=v*L q w y := glow_scale _ _ _ _ _ _ _
    rw [← h2,← h2,← h1,← h1]
    congr 1; ring
  have Hpill : glow' 0 kill lost ≤ 2*k := by
    apply le_trans (le_abs_self _); apply le_trans (glow_limit _ _ _ _ _ _)
    rw [norm_zero]; linarith
  change ray (A+gain) (f y) (F y) ≤ ray A (f s) (F s)+X*e.first z+Y*e.second r q z+2*k+4*C
  rw [hA,hB]
  apply (ray_shift A (f s) gain plusf (F s) plusm _ (by positivity) HG).trans
  change ray A _ _+glow' gain plusf plusm+_ ≤ _
  rw [HL]; linarith

lemma flash (e : Lamp M) (h : Climb e.site) (r : Bool) (b : Beat M)
    (hb : b.pre=e.site.smaller r) (hq : Ideal b.pre b.post)
    (ha : 0 < e.width) (he : e.width ≤ 1) :
    let s := e.site
    let u := e.u
    let a := e.width
    let q := b.post
    let t := b.bit
    let k := killed b
    let C := 20*(fax s+fax q)+400*((k+shower u s+shower u q)/a)
    watt (winds b) u (carry e r t) a ≤ watt s u e.W a + curl r *start e +
      curl t *delayed e r q + 2*k + 4*C := by
  intro s u a q t k C
  let K z := matter (s.smaller r) z - matter q z
  have hK : k=∑ z,K z := by
    unfold K k; rw [hq.kill_eq]; rw [← matter_sum hq.fit, ← matter_sum hq.climb.fit,
      Finset.sum_sub_distrib]
    rw [hb]
  let B z := 20*(pierce s z+pierce q z)+400*((K z+dew u s z+dew u q z)/a)
  have hC : C=∑ z,B z := by
    unfold C B fax shower
    rw [hK]
    rw [Finset.sum_add_distrib,←Finset.mul_sum,←Finset.mul_sum,← Finset.sum_div]; simp_rw [Finset.sum_add_distrib]
    rfl
  rw [hK,hC,watt,watt,start,delayed, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,Finset.mul_sum,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,← Finset.sum_add_distrib,← Finset.sum_add_distrib]
  apply Finset.sum_le_sum; intro i _
  exact flash_cell e h r t q (hb ▸ hq) ha he i

def lit (e : Lamp M) (s : Scene M) := (energy s e.u + e.width^2)*fax s + shower e.u s

lemma start_cost (e : Lamp M) (h : Climb e.site) (ha : 0 ≤ e.width) :
    start e^2 ≤ 100*lit e e.site := by
  let a := e.width; let W := e.W; let s := e.site; let u := e.u
  let x := ∑ z,‖factor s u z‖; let y := ∑ z, |shell s z|
  have H : |start e| ≤ x + a*y := by
    apply le_trans (Finset.abs_sum_le_sum_abs _ _)
    unfold x y; rw [Finset.mul_sum,← Finset.sum_add_distrib]
    apply Finset.sum_le_sum; intro i _
    apply (glow_limit _ _ _ _ _ _).trans
    rw [norm_zero,zero_add,abs_mul,abs_of_nonneg ha]
  have hX : x^2 ≤ _ := factor_bill _ h u
  have hY : y^2 ≤ _ := shell_bill _ h
  have hT : (start e)^2 ≤ (x+a*y)^2 := by
    rw [←sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) H _
  have hV : (a*y)^2 ≤ a^2*(2*fax s) := by rw [mul_pow]; gcongr
  change _ ≤ 100*((energy s u+a^2)*fax s+shower u s)
  nlinarith [mul_nonneg (energy_small h.fit u).1 (fax_floor h).1,shower_nonneg (u:=u) h,sq_nonneg (x-a*y),
    mul_nonneg (sq_nonneg a) (fax_floor h).1]

lemma delayed_cost (e : Lamp M) (h : Climb e.site) {q : Scene M} (hq : Climb q)
    (ha : 0 ≤ e.width) (r : Bool) :
    delayed e r q^2 ≤ 100*(lit e e.site+lit e q) := by
  let a := e.width; let W := e.W; let s := e.site; let u := e.u
  let x (s : Scene M) := ∑ z,‖factor s u z‖
  let y := ∑ z, |shell q z|
  have H : |delayed e r q| ≤ x s+x q + a*y := by
    apply le_trans (Finset.abs_sum_le_sum_abs _ _)
    unfold x y; rw [Finset.mul_sum,← Finset.sum_add_distrib,← Finset.sum_add_distrib]
    apply Finset.sum_le_sum; intro i _
    apply (glow_limit _ _ _ _ _ _).trans
    rw [norm_scaleC,curl_unit,one_mul,abs_mul,abs_of_nonneg ha]
  have hX₁ : x s^2 ≤ _ := factor_bill _ h u
  have hX₂ : x q^2 ≤ _ := factor_bill _ hq u
  have hY : y^2 ≤ _ := shell_bill _ hq
  have hT : delayed e r q^2 ≤ (x s+x q+a*y)^2 := by
    rw [←sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) H _
  have hV : (a*y)^2 ≤ a^2*(2*fax q) := by rw [mul_pow]; gcongr
  let A (s : Scene M) := (energy s u+a^2)*fax s+shower u s
  have HI (w : Scene M) (hw : Climb w) : 0 ≤ energy w u*fax w ∧ 0 ≤ a^2*fax w :=
    ⟨mul_nonneg (energy_small hw.fit u).1 (fax_floor hw).1,mul_nonneg (sq_nonneg a) (fax_floor hw).1⟩
  have h1 := HI s h; have h2 := HI q hq
  change _ ≤ 100*((energy s u+a^2)*fax s+shower u s+((energy q u+a^2)*fax q+shower u q))
  nlinarith [shower_nonneg (u:=u) h, shower_nonneg (u:=u) hq,sq_nonneg (x s-x q),sq_nonneg (x q-a*y),sq_nonneg (x s-a*y)]

end Lamp
end Beam


end FourierLLogL.Dyadic.Procedure.Paths

end OAI
