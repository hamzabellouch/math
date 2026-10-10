import OAI.Combinatorics.ThinTrees.PartialFractions

namespace OAI

universe uI uR uR2 uR3 uR4 uS uR5 uS2 uR6

section

noncomputable section
open Polynomial Finset Filter
open scoped Topology
namespace StrongThinTree.MSS

variable {I : Type uI} [DecidableEq I]

def ray {R : Type uR} [CommRing R] (p : MvPolynomial I R) (z : I → R) (i : I) : R[X] :=
  MvPolynomial.eval₂ Polynomial.C (fun j => Polynomial.C (z j)+if j=i then Polynomial.X else 0) p

lemma ray_eval {R : Type uR2} [CommRing R] (p : MvPolynomial I R) (z : I → R) (i : I) (t : R) :
    (ray p z i).eval t=MvPolynomial.eval (Function.update z i (z i+t)) p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [ray]
  | add p q hp hq => simpa [ray,MvPolynomial.eval₂_add] using congrArg₂ (·+·) hp hq
  | mul_X p j hp =>
    simp only [ray] at hp
    by_cases hji : j=i
    · subst j
      simp [ray,MvPolynomial.eval₂_mul,hp]
    · simp [ray,MvPolynomial.eval₂_mul,hji,hp]

lemma ray_derivative {R : Type uR3} [CommRing R] (p : MvPolynomial I R) (z : I → R) (i : I) :
    (ray p z i).derivative=ray (MvPolynomial.pderiv i p) z i := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [ray]
  | add p q hp hq =>
    simp only [ray] at hp hq
    simp [ray,MvPolynomial.eval₂_add,hp,hq]
  | mul_X p j hp =>
    simp only [ray] at hp
    rw [MvPolynomial.pderiv_mul]
    by_cases hji : j=i
    · subst j
      simp [ray,MvPolynomial.eval₂_mul,MvPolynomial.eval₂_add,Polynomial.derivative_mul,hp]
    · simp [ray,MvPolynomial.eval₂_mul,Polynomial.derivative_mul,MvPolynomial.pderiv_X,hji,hp]

lemma ray_map {R : Type uR4} {S : Type uS} [CommRing R] [CommRing S] (f : R →+* S)
    (p : MvPolynomial I R) (z : I → R) (i : I) :
    (ray p z i).map f=ray (p.map f) (fun j => f (z j)) i := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [ray]
  | add p q hp hq => simpa [ray,MvPolynomial.eval₂_add] using congrArg₂ (·+·) hp hq
  | mul_X p j hp =>
    simp only [ray] at hp
    by_cases hji : j=i
    · subst j
      simp [ray,MvPolynomial.eval₂_mul,hp]
    · simp [ray,MvPolynomial.eval₂_mul,hp,hji]

omit [DecidableEq I] in
lemma eval_map_between {R : Type uR5} {S : Type uS2} [CommRing R] [CommRing S] (f : R →+* S)
    (p : MvPolynomial I R) (z : I → R) :
    MvPolynomial.eval (fun j => f (z j)) (p.map f)=f (MvPolynomial.eval z p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp,hq]
  | mul_X p j hp => simp [hp]

def RealStable (p : MvPolynomial I ℝ) : Prop := Stable (p.map (algebraMap ℝ ℂ))
def Above (p : MvPolynomial I ℝ) (z : I → ℝ) : Prop :=
  ∀s : I → ℝ, (∀i, 0 ≤ s i) → 0 < MvPolynomial.eval (z+s) p

def barrier (p : MvPolynomial I ℝ) (z : I → ℝ) (i : I) : ℝ :=
  MvPolynomial.eval z (MvPolynomial.pderiv i p)/MvPolynomial.eval z p

omit [DecidableEq I] in
lemma Above.pos {p : MvPolynomial I ℝ} {z : I → ℝ} (hz : Above p z) :
    0 < MvPolynomial.eval z p := by
  simpa using hz 0 (fun _ => le_rfl)

omit [DecidableEq I] in
lemma Above.add {p : MvPolynomial I ℝ} {z s : I → ℝ} (hz : Above p z) (hs : ∀i, 0 ≤ s i) :
    Above p (z+s) := by
  intro t ht
  simpa [add_assoc] using hz (s+t) (fun i => add_nonneg (hs i) (ht i))

lemma Above.update {p : MvPolynomial I ℝ} {z : I → ℝ} (hz : Above p z) (i : I) {t : ℝ} (ht : 0 ≤ t) :
    Above p (Function.update z i (z i+t)) := by
  have he : Function.update z i (z i+t)=z+Pi.single i t := by
    ext j
    by_cases hj : j=i
    · subst j; simp
    · simp [Function.update_of_ne hj,Pi.single_eq_of_ne hj]
  rw [he]
  exact hz.add (fun j => by by_cases hj : j=i; subst j; simp [ht]; simp [Pi.single_eq_of_ne hj])

lemma ray_zero (p : MvPolynomial I ℝ) (z : I → ℝ) (i : I) :
    (ray p z i).eval 0=MvPolynomial.eval z p := by simp [ray_eval]

lemma real_ray_upper {p : MvPolynomial I ℝ} (hp : RealStable p) {z : I → ℝ}
    (hz : Above p z) (i : I) :
    ∀w : ℂ, 0 < w.im → Rational.cval (ray p z i) w ≠ 0 := by
  have hs0 : slice (p.map (algebraMap ℝ ℂ)) (fun j => (z j:ℂ)) i ≠ 0 := by
    intro he
    have hh := slice_eval_self (p.map (algebraMap ℝ ℂ)) (fun j => (z j:ℂ)) i
    rw [he] at hh
    have hm := eval_map_between (algebraMap ℝ ℂ) p z
    change MvPolynomial.eval (fun j => (z j:ℂ)) (p.map (algebraMap ℝ ℂ))=(MvPolynomial.eval z p:ℂ) at hm
    rw [hm] at hh
    simp only [Polynomial.eval_zero] at hh
    exact hz.pos.ne' (by exact_mod_cast hh.symm)
  intro w hw
  have hh := hp.slice_boundary (fun j => (z j:ℂ)) (fun _ => by simp) i hs0 ((z i:ℂ)+w)
    (by simpa using hw)
  rw [slice_eval] at hh
  unfold Rational.cval
  rw [ray_map,ray_eval]
  exact hh

lemma real_ray_splits {p : MvPolynomial I ℝ} (hp : RealStable p) {z : I → ℝ}
    (hz : Above p z) (i : I) : (ray p z i).Splits :=
  splits_of_upper_half_plane _ (real_ray_upper hp hz i)

lemma barrier_nonneg {p : MvPolynomial I ℝ} (hp : RealStable p) {z : I → ℝ}
    (hz : Above p z) (i : I) : 0 ≤ barrier p z i := by
  let g := ray p z i
  have hg0 : g.eval 0 ≠ 0 := by simpa [g,ray_zero] using hz.pos.ne'
  have hg : g.Splits := real_ray_splits hp hz i
  have hgroot : ∀x ∈ g.roots, x < 0 := by
    intro x hx
    by_contra hx0
    have he : g.eval x=0 := (mem_roots (by intro h0; simp [h0] at hg0)).mp hx
    have hp0 := (hz.update i (le_of_not_gt hx0)).pos
    rw [←ray_eval] at hp0
    exact hp0.ne' he
  have he : barrier p z i=g.derivative.eval 0/g.eval 0 := by
    simp [g,ray_derivative,ray_zero,barrier]
  rw [he,hg.eval_derivative_div_eval_of_ne_zero hg0]
  apply Multiset.sum_nonneg
  intro r hr
  obtain ⟨x,hx,rfl⟩ := Multiset.mem_map.mp hr
  exact div_nonneg zero_le_one (by linarith [hgroot x hx])

lemma Stable.log_derivative_im {p : MvPolynomial I ℂ} (hp : Stable p)
    (z : I → ℂ) (hz : ∀j, 0 < (z j).im) (i : I) :
    (MvPolynomial.eval z (MvPolynomial.pderiv i p)/MvPolynomial.eval z p).im ≤ 0 := by
  have hs : ∀w : ℂ, 0 < w.im → (slice p z i).eval w ≠ 0 := by
    intro w hw
    rw [slice_eval]
    apply hp
    intro j
    by_cases hji : j=i
    · subst j; simpa using hw
    · simpa [Function.update_of_ne hji] using hz j
  have hh := polynomial_log_derivative (hz i) hs
  rw [slice_derivative_eval_self,slice_eval_self] at hh
  rcases hh with hh | hh
  · simp [hh]
  · exact hh.le

lemma ray_log_derivative_im {p : MvPolynomial I ℝ} (hp : RealStable p) {z : I → ℝ}
    (hz : Above p z) (i j : I) (w : ℂ) (hw : 0 < w.im) :
    (Rational.cval (ray (MvPolynomial.pderiv i p) z j) w/Rational.cval (ray p z j) w).im ≤ 0 := by
  let P := p.map (algebraMap ℝ ℂ)
  let Z : ℝ → I → ℂ := fun t => Function.update (fun k => (z k:ℂ)+(t:ℂ)*Complex.I) j ((z j:ℂ)+w)
  have hZ : Continuous Z := by
    apply continuous_pi
    intro k
    by_cases hkj : k=j
    · subst k; simp only [Z,Function.update_self]; fun_prop
    · simp only [Z,Function.update_of_ne hkj]; fun_prop
  have he (q : MvPolynomial I ℝ) :
      Rational.cval (ray q z j) w=MvPolynomial.eval (Z 0) (q.map (algebraMap ℝ ℂ)) := by
    unfold Rational.cval
    rw [ray_map,ray_eval]
    simp only [Z,Complex.ofReal_zero,zero_mul,add_zero]
    rfl
  have hD : MvPolynomial.eval (Z 0) P ≠ 0 := by
    exact (he p).symm ▸ real_ray_upper hp hz j w hw
  have hA := ((MvPolynomial.continuous_eval (MvPolynomial.pderiv i P)).comp hZ).continuousAt (x:=0)
  have hB := ((MvPolynomial.continuous_eval P).comp hZ).continuousAt (x:=0)
  have hlim := Complex.continuous_im.continuousAt.tendsto.comp (hA.tendsto.div hB.tendsto hD)
  have heq : (MvPolynomial.eval (Z 0) (MvPolynomial.pderiv i P)/MvPolynomial.eval (Z 0) P).im=
      (Rational.cval (ray (MvPolynomial.pderiv i p) z j) w/Rational.cval (ray p z j) w).im := by
    dsimp [P]
    rw [MvPolynomial.pderiv_map,←he,←he]
  dsimp only [Function.comp_apply] at hlim
  rw [heq] at hlim
  apply le_of_tendsto (hlim.mono_left (nhdsWithin_le_nhds (s:=Set.Ioi 0)))
  filter_upwards [self_mem_nhdsWithin] with t ht
  apply hp.log_derivative_im
  intro k
  by_cases hkj : k=j
  · subst k; simpa only [Z,Function.update_self,Complex.add_im,Complex.ofReal_im,zero_add] using hw
  · simpa only [Z,Function.update_of_ne hkj,Complex.add_im,Complex.ofReal_im,Complex.mul_im,
      Complex.ofReal_re,Complex.I_im,mul_one,Complex.I_re,mul_zero,zero_add,add_zero,Set.mem_Ioi] using ht

lemma barrier_ray_representation {p : MvPolynomial I ℝ} (hp : RealStable p) {z : I → ℝ}
    (hz : Above p z) (i j : I) :
    ∃s : Finset ℝ, ∃c : ℝ, ∃d : ℝ → ℝ, 0 ≤ c ∧
      (∀x ∈ s, x < 0 ∧ 0 < d x) ∧
      ∀t : ℝ, 0 ≤ t → barrier p (Function.update z j (z j+t)) i=c+∑x ∈ s, d x/(t-x) := by
  have hb : ray p z j ≠ 0 := by
    intro h0
    have hh := hz.pos
    rw [←ray_zero p z j,h0,Polynomial.eval_zero] at hh
    exact lt_irrefl _ hh
  have hr : ∀t : ℝ, 0 ≤ t → (ray p z j).eval t ≠ 0 := by
    intro t ht
    rw [ray_eval]
    exact (hz.update j ht).pos.ne'
  obtain ⟨s,c,d,hc,hd,he⟩ := Rational.positive_decomposition (ray (MvPolynomial.pderiv i p) z j)
    (ray p z j) hb (real_ray_splits hp hz j) hr (real_ray_upper hp hz j)
    (ray_log_derivative_im hp hz i j) (fun t ht => by
      simpa only [ray_eval,barrier] using barrier_nonneg hp (hz.update j ht) i)
  refine ⟨s,c,d,hc,hd,?_⟩
  intro t ht
  simpa only [barrier,ray_eval] using he t ht

lemma barrier_update_le {p : MvPolynomial I ℝ} (hp : RealStable p) {z : I → ℝ}
    (hz : Above p z) (i j : I) {t : ℝ} (ht : 0 ≤ t) :
    barrier p (Function.update z j (z j+t)) i ≤ barrier p z i := by
  obtain ⟨s,c,d,_,hd,he⟩ := barrier_ray_representation hp hz i j
  have he0 := he 0 le_rfl
  simp only [add_zero,Function.update_eq_self] at he0
  rw [he t ht,he0]
  apply add_le_add le_rfl
  apply Finset.sum_le_sum
  intro x hx
  exact div_le_div_of_nonneg_left (hd x hx).2.le (by linarith [(hd x hx).1]) (by linarith)

lemma update_add_single (z : I → ℝ) (i : I) (t : ℝ) :
    Function.update z i (z i+t)=z+Pi.single i t := by
  ext j
  by_cases hj : j=i
  · subst j; simp
  · simp [Function.update_of_ne hj,Pi.single_eq_of_ne hj]

lemma barrier_add_le [Fintype I] {p : MvPolynomial I ℝ} (hp : RealStable p) {z s : I → ℝ}
    (hz : Above p z) (hs : ∀i, 0 ≤ s i) (i : I) : barrier p (z+s) i ≤ barrier p z i := by
  have hh : ∀T : Finset I, barrier p (z+∑j ∈ T, Pi.single j (s j)) i ≤ barrier p z i := by
    intro T
    induction T using Finset.induction_on with
    | empty => simp
    | @insert j T hj ih =>
      have hn : ∀k, 0 ≤ (∑j ∈ T, Pi.single j (s j)) k := by
        intro k
        rw [Finset.sum_apply]
        exact Finset.sum_nonneg (fun l _ => by by_cases hl : k=l; subst l; simp [hs]; simp [Pi.single_eq_of_ne hl])
      have hu := barrier_update_le hp (hz.add hn) i j (hs j)
      rw [update_add_single] at hu
      rw [Finset.sum_insert hj]
      simpa only [add_left_comm,add_assoc,add_comm] using hu.trans ih
  simpa only [Finset.univ_sum_single] using hh Finset.univ

def crossBarrier (p : MvPolynomial I ℝ) (z : I → ℝ) (i j : I) : ℝ :=
  (MvPolynomial.eval z (MvPolynomial.pderiv j (MvPolynomial.pderiv i p))*MvPolynomial.eval z p-
    MvPolynomial.eval z (MvPolynomial.pderiv i p)*MvPolynomial.eval z (MvPolynomial.pderiv j p))/(MvPolynomial.eval z p)^2

lemma hasDerivAt_barrier_ray (p : MvPolynomial I ℝ) (z : I → ℝ) (i j : I) {t : ℝ}
    (ht : MvPolynomial.eval (Function.update z j (z j+t)) p ≠ 0) :
    HasDerivAt (fun u => barrier p (Function.update z j (z j+u)) i)
      (crossBarrier p (Function.update z j (z j+t)) i j) t := by
  have hh := ((ray (MvPolynomial.pderiv i p) z j).hasDerivAt t).div ((ray p z j).hasDerivAt t)
    (by simpa only [ray_eval] using ht)
  convert hh using 1 <;> first | rfl | (simp [ray_eval,ray_derivative,barrier,crossBarrier] <;> rfl)

lemma fractions_tangent {x d t : ℝ} (hx : x < 0) (hd : 0 ≤ d) (ht : 0 ≤ t) :
    d/(t-x)+t*(d/(t-x)^2) ≤ d/(0-x) := by
  have hb : 0 < t-x := by linarith
  calc
    d/(t-x)+t*(d/(t-x)^2) = d*(t-x+t)/(t-x)^2 := by field_simp
    _ ≤ d/(0-x) := by
      rw [div_le_div_iff₀ (sq_pos_of_pos hb) (by linarith)]
      nlinarith [mul_nonneg hd (sq_nonneg t)]

lemma barrier_ray_tangent {p : MvPolynomial I ℝ} (hp : RealStable p) {z : I → ℝ}
    (hz : Above p z) (i j : I) {t : ℝ} (ht : 0 < t) :
    crossBarrier p (Function.update z j (z j+t)) i j ≤ 0 ∧
      barrier p (Function.update z j (z j+t)) i-t*crossBarrier p (Function.update z j (z j+t)) i j ≤ barrier p z i := by
  obtain ⟨s,c,d,_,hd,he⟩ := barrier_ray_representation hp hz i j
  have hder : HasDerivAt (fun u : ℝ => c+∑x ∈ s, d x/(u-x))
      (-(∑x ∈ s, d x/(t-x)^2)) t := by
    have hh : ∀x ∈ s, HasDerivAt (fun u : ℝ => d x/(u-x)) (-(d x/(t-x)^2)) t := by
      intro x hx
      have hu := (hasDerivAt_const t (d x)).div ((hasDerivAt_id t).sub_const x) (by linarith [(hd x hx).1] : t-x ≠ 0)
      convert hu using 1 <;> first | rfl | simp [neg_div]
    convert (hasDerivAt_const t c).add (HasDerivAt.fun_sum hh) using 1
    first | rfl | simp [Finset.sum_neg_distrib]
  have hder' : HasDerivAt (fun u => barrier p (Function.update z j (z j+u)) i)
      (-(∑x ∈ s, d x/(t-x)^2)) t := by
    apply hder.congr_of_eventuallyEq
    filter_upwards [eventually_gt_nhds ht] with u hu
    exact he u hu.le
  have hdval := (hasDerivAt_barrier_ray p z i j (hz.update j ht.le).pos.ne').unique hder'
  rw [hdval]
  constructor
  · exact neg_nonpos.mpr (Finset.sum_nonneg (fun x hx => div_nonneg (hd x hx).2.le (sq_nonneg _)))
  · have he0 := he 0 le_rfl
    simp only [add_zero,Function.update_eq_self] at he0
    rw [he t ht.le,he0,mul_neg,sub_neg_eq_add,add_assoc,Finset.mul_sum,←Finset.sum_add_distrib]
    exact add_le_add le_rfl (Finset.sum_le_sum (fun x hx => fractions_tangent (hd x hx).1 (hd x hx).2.le ht.le))

lemma pderiv_commute {R : Type uR6} [CommRing R] (p : MvPolynomial I R) (i j : I) :
    MvPolynomial.pderiv i (MvPolynomial.pderiv j p)=MvPolynomial.pderiv j (MvPolynomial.pderiv i p) := by
  by_cases hij : i=j
  · subst j; rfl
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp,hq]
  | mul_X p k hp =>
    by_cases hki : k=i
    · subst k
      simp [MvPolynomial.pderiv_X,hij,hp,add_comm]
    · by_cases hkj : k=j
      · subst k
        simp [MvPolynomial.pderiv_X,Ne.symm hij,hp,add_comm]
      · simp [MvPolynomial.pderiv_X,hki,hkj,hp]

omit [DecidableEq I] in
lemma RealStable.sub_pderiv {p : MvPolynomial I ℝ} (hp : RealStable p) (j : I) :
    RealStable (p-MvPolynomial.pderiv j p) := by
  classical
  simpa only [RealStable,map_sub,MvPolynomial.pderiv_map] using Stable.sub_pderiv hp j

omit [DecidableEq I] in
lemma eval_sub_pderiv {p : MvPolynomial I ℝ} {w : I → ℝ}
    (hw : MvPolynomial.eval w p ≠ 0) (j : I) :
    MvPolynomial.eval w (p-MvPolynomial.pderiv j p)=MvPolynomial.eval w p*(1-barrier p w j) := by
  simp only [map_sub,barrier]
  field_simp

lemma barrier_sub_pderiv {p : MvPolynomial I ℝ} {w : I → ℝ}
    (hw : MvPolynomial.eval w p ≠ 0) (i j : I) (hj : 1-barrier p w j ≠ 0) :
    barrier (p-MvPolynomial.pderiv j p) w i =
      barrier p w i-crossBarrier p w i j/(1-barrier p w j) := by
  have hne : MvPolynomial.eval w p-MvPolynomial.eval w (MvPolynomial.pderiv j p) ≠ 0 := by
    intro he
    have he' := sub_eq_zero.mp he
    apply hj
    simp [barrier,←he',hw]
  simp only [barrier,crossBarrier,map_sub,pderiv_commute p i j]
  field_simp
  ring

lemma barrier_shift [Fintype I] {p : MvPolynomial I ℝ} (hp : RealStable p) {z : I → ℝ}
    (hz : Above p z) (j : I) {δ : ℝ} (hδ : 0 < δ) (hh : barrier p z j+1/δ ≤ 1) :
    Above (p-MvPolynomial.pderiv j p) (Function.update z j (z j+δ)) ∧
      ∀i, barrier (p-MvPolynomial.pderiv j p) (Function.update z j (z j+δ)) i ≤ barrier p z i := by
  have hzq : Above (p-MvPolynomial.pderiv j p) z := by
    intro s hs
    rw [eval_sub_pderiv (hz.add hs).pos.ne']
    apply mul_pos (hz.add hs).pos
    have hm := barrier_add_le hp hz hs j
    have hpos := one_div_pos.mpr hδ
    linarith
  refine ⟨hzq.update j hδ.le,fun i => ?_⟩
  let w := Function.update z j (z j+δ)
  have hw := (hz.update j hδ.le).pos
  have hm : 1/δ ≤ 1-barrier p w j := by
    have hu := barrier_update_le hp hz j j hδ.le
    change barrier p w j ≤ _ at hu
    linarith
  have hpos : 0 < 1-barrier p w j := lt_of_lt_of_le (one_div_pos.mpr hδ) hm
  obtain ⟨hf,ht⟩ := barrier_ray_tangent hp hz i j hδ
  change crossBarrier p w i j ≤ 0 at hf
  change barrier p w i-δ*crossBarrier p w i j ≤ barrier p z i at ht
  rw [barrier_sub_pderiv hw.ne' i j hpos.ne']
  apply le_trans _ ht
  change barrier p w i-crossBarrier p w i j/(1-barrier p w j) ≤ barrier p w i-δ*crossBarrier p w i j
  apply sub_le_sub_left
  rw [le_div_iff₀ hpos]
  have he : 1 ≤ δ*(1-barrier p w j) := by
    simpa only [mul_comm] using (div_le_iff₀ hδ).mp hm
  have hm' := mul_le_mul_of_nonpos_left he hf
  nlinarith

end StrongThinTree.MSS

end
end

end OAI
