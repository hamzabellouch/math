import Mathlib
import OAI.Probability.SKValue.Evolution.BoundedSmooth

namespace OAI

section

open Set Filter
open scoped Topology
namespace SKValue

lemma localMin_second_deriv_nonneg {f : ℝ → ℝ} {x : ℝ}
    (hm : IsLocalMin f x) (hc : ContinuousAt f x) : 0≤deriv (deriv f) x := by
  by_contra hn
  have hn := lt_of_not_ge hn
  have hmax := isLocalMax_of_deriv_deriv_neg hn hm.deriv_eq_zero hc
  have he : f=ᶠ[𝓝 x] fun _ ↦ f x := by
    filter_upwards [hm,hmax] with y hy hy'
    exact le_antisymm hy' hy
  have hz := he.deriv.deriv_eq
  simp only [deriv_const',deriv_const] at hz
  linarith

lemma time_min_deriv_nonpos {f : ℝ → ℝ} {T t d : ℝ} (ht : 0<t)
    (htT : t≤T) (hm : IsMinOn f (Icc (0 : ℝ) T) t) (hd : HasDerivAt f d t) : d≤0 := by
  have hdir : (0 : ℝ)-t∈posTangentConeAt (Icc (0 : ℝ) T) t :=
    sub_mem_posTangentConeAt_of_segment_subset
      ((convex_Icc (0 : ℝ) T).segment_subset ⟨ht.le,htT⟩ ⟨le_rfl,ht.le.trans htT⟩)
  have hh := hm.isLocalMinOn.hasFDerivWithinAt_nonneg hd.hasFDerivAt.hasFDerivWithinAt hdir
  have hh' : 0≤(0-t)*d := by simpa using hh
  nlinarith

lemma parabolic_nonneg_of_negative_zeroth {T a b : ℝ}
    (hT : 0≤T) (hab : a≤b) {u ut ux uxx β c : ℝ → ℝ → ℝ}
    (hc : ContinuousOn (fun p : ℝ×ℝ ↦ u p.1 p.2) ((Icc 0 T)×ˢ(Icc a b)))
    (hdt : ∀ t∈Ioc (0 : ℝ) T, ∀ x∈Ioo a b, HasDerivAt (u · x) (ut t x) t)
    (hdx : ∀ t∈Ioc (0 : ℝ) T, ∀ x∈Ioo a b, HasDerivAt (u t) (ux t x) x)
    (hdxx : ∀ t∈Ioc (0 : ℝ) T, ∀ x∈Ioo a b,
      HasDerivAt (deriv (u t)) (uxx t x) x)
    (hinit : ∀ x∈Icc a b, 0≤u 0 x)
    (hleft : ∀ t∈Icc (0 : ℝ) T, 0≤u t a)
    (hright : ∀ t∈Icc (0 : ℝ) T, 0≤u t b)
    (hcneg : ∀ t∈Ioc (0 : ℝ) T, ∀ x∈Ioo a b, c t x<0)
    (hpde : ∀ t∈Ioc (0 : ℝ) T, ∀ x∈Ioo a b,
      0≤ut t x-(1/2 : ℝ)*uxx t x-β t x*ux t x-c t x*u t x) :
    ∀ t∈Icc (0 : ℝ) T, ∀ x∈Icc a b, 0≤u t x := by
  obtain ⟨⟨s,y⟩,⟨hs,hy⟩,hmin⟩ := (isCompact_Icc.prod isCompact_Icc).exists_isMinOn
    (show (((Icc (0 : ℝ) T)×ˢ(Icc a b))).Nonempty from ⟨(0,a),⟨⟨le_rfl,hT⟩,⟨le_rfl,hab⟩⟩⟩) hc
  suffices hm : 0≤u s y by
    intro t ht x hx
    exact hm.trans (@hmin (t,x) ⟨ht,hx⟩)
  by_contra hn
  have hn : u s y<0 := lt_of_not_ge hn
  have hs0 : 0<s := lt_of_le_of_ne hs.1 (by intro he; subst s; exact (not_lt_of_ge (hinit y hy)) hn)
  have hya : a<y := lt_of_le_of_ne hy.1 (by intro he; subst y; exact (not_lt_of_ge (hleft s hs)) hn)
  have hyb : y<b := lt_of_le_of_ne hy.2 (by intro he; subst y; exact (not_lt_of_ge (hright s hs)) hn)
  have hst : s∈Ioc (0 : ℝ) T := ⟨hs0,hs.2⟩
  have hyi : y∈Ioo a b := ⟨hya,hyb⟩
  have hmt : IsMinOn (u · y) (Icc (0 : ℝ) T) s := fun t ht ↦ @hmin (t,y) ⟨ht,hy⟩
  have hmx : IsLocalMin (u s) y :=
    (show IsMinOn (u s) (Icc a b) y from fun x hx ↦ @hmin (s,x) ⟨hs,hx⟩).isLocalMin (Icc_mem_nhds hya hyb)
  have htime := time_min_deriv_nonpos hs0 hs.2 hmt (hdt s hst y hyi)
  have hxzero := hmx.hasDerivAt_eq_zero (hdx s hst y hyi)
  have hxxpos := localMin_second_deriv_nonneg hmx (hdx s hst y hyi).continuousAt
  rw [(hdxx s hst y hyi).deriv] at hxxpos
  have hcc := mul_pos_of_neg_of_neg (hcneg s hst y hyi) hn
  have hp := hpde s hst y hyi
  rw [hxzero,mul_zero] at hp
  linarith

lemma parabolic_barrier {T a b C ε : ℝ}
    (hT : 0≤T) (hab : a≤b) (hε : 0≤ε) {u ut ux uxx β c : ℝ → ℝ → ℝ}
    (hc : ContinuousOn (fun p : ℝ×ℝ ↦ u p.1 p.2) ((Icc 0 T)×ˢ(Icc a b)))
    (hdt : ∀ t∈Ioc (0 : ℝ) T, ∀ x∈Ioo a b, HasDerivAt (u · x) (ut t x) t)
    (hdx : ∀ t∈Ioc (0 : ℝ) T, ∀ x∈Ioo a b, HasDerivAt (u t) (ux t x) x)
    (hdxx : ∀ t∈Ioc (0 : ℝ) T, ∀ x∈Ioo a b,
      HasDerivAt (deriv (u t)) (uxx t x) x)
    (hinit : ∀ x∈Icc a b, 0≤u 0 x)
    (hleft : ∀ t∈Icc (0 : ℝ) T, -ε≤u t a)
    (hright : ∀ t∈Icc (0 : ℝ) T, -ε≤u t b)
    (hcbd : ∀ t∈Ioc (0 : ℝ) T, ∀ x∈Ioo a b, c t x≤C)
    (hpde : ∀ t∈Ioc (0 : ℝ) T, ∀ x∈Ioo a b,
      0≤ut t x-(1/2 : ℝ)*uxx t x-β t x*ux t x-c t x*u t x) :
    ∀ t∈Icc (0 : ℝ) T, ∀ x∈Icc a b,
      -ε*Real.exp ((max C 0+1)*t)≤u t x := by
  let k := max C 0+1
  let e := fun t : ℝ ↦ Real.exp (-k*t)
  have hk : 0<k := by dsimp [k]; linarith [le_max_right C 0]
  have hepos : ∀ t,0<e t := fun t ↦ Real.exp_pos _
  have heder : ∀ t,HasDerivAt e (-k*e t) t := by
    intro t
    convert ((hasDerivAt_id t).const_mul (-k)).exp using 1 <;> dsimp [e]
    ring
  have hecont : Continuous e := by fun_prop
  have hbound : ∀ t∈Icc (0 : ℝ) T, 0≤e t ∧ e t≤1 := by
    intro t ht
    refine ⟨(hepos t).le,Real.exp_le_one_iff.mpr ?_⟩
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hk.le) ht.1
  have hlbound {t v : ℝ} (ht : t∈Icc (0 : ℝ) T) (hv : -ε≤v) : 0≤e t*v+ε := by
    have hh := mul_le_mul_of_nonneg_left hv (hepos t).le
    have hh' := mul_le_mul_of_nonneg_left (hbound t ht).2 hε
    nlinarith
  have hh := parabolic_nonneg_of_negative_zeroth hT hab
    (u := fun t x ↦ e t*u t x+ε)
    (ut := fun t x ↦ e t*(ut t x-k*u t x))
    (ux := fun t x ↦ e t*ux t x) (uxx := fun t x ↦ e t*uxx t x)
    (β := β) (c := fun t x ↦ c t x-k)
    (((hecont.comp continuous_fst).continuousOn.mul hc).add continuousOn_const)
    (by
      intro t ht x hx
      have hd : HasDerivAt (fun s : ℝ ↦ e s*u s x+ε)
          ((-k*e t)*u t x+e t*ut t x) t :=
        ((heder t).mul (hdt t ht x hx)).add_const ε
      convert hd using 1
      ring)
    (by
      intro t ht x hx
      exact ((hdx t ht x hx).const_mul (e t)).add_const ε)
    (by
      intro t ht x hx
      have heq : (deriv (fun y ↦ e t*u t y+ε))=fun y ↦ e t*deriv (u t) y := by
        funext y
        rw [deriv_add_const,deriv_const_mul_field]
      rw [heq]
      exact (hdxx t ht x hx).const_mul (e t))
    (by intro x hx; simpa only [e,mul_zero,Real.exp_zero,one_mul] using add_nonneg (hinit x hx) hε)
    (by intro t ht; exact hlbound ht (hleft t ht))
    (by intro t ht; exact hlbound ht (hright t ht))
    (by intro t ht x hx; have hb := hcbd t ht x hx; dsimp [k]; linarith [le_max_left C 0])
    (by
      intro t ht x hx
      have hp := mul_nonneg (hepos t).le (hpde t ht x hx)
      have hb : c t x-k≤0 := by have hb := hcbd t ht x hx; dsimp [k]; linarith [le_max_left C 0]
      have hbε := mul_nonpos_of_nonpos_of_nonneg hb hε
      nlinarith only [hp,hbε])
  intro t ht x hx
  have hn := hh t ht x hx
  have heinv : e t*Real.exp (k*t)=1 := by
    dsimp [e]
    rw [←Real.exp_add, neg_mul, neg_add_cancel, Real.exp_zero]
  have hmul : 0≤Real.exp (k*t)*(e t*u t x+ε) := mul_nonneg (Real.exp_pos _).le hn
  have heq : Real.exp (k*t)*(e t*u t x+ε)=u t x+ε*Real.exp (k*t) := by
    calc
      _ = (e t*Real.exp (k*t))*u t x+ε*Real.exp (k*t) := by ring
      _ = _ := by rw [heinv,one_mul]
  rw [heq] at hmul
  change -ε*Real.exp (k*t)≤u t x
  linarith

end SKValue

end

end OAI
