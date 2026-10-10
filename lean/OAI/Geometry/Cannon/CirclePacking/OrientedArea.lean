import Mathlib
import OAI.Geometry.Cannon.PlanarGraphs.Next

namespace OAI

section
section
section
noncomputable section
namespace CannonPackingGeometry
open ComplexConjugate

def orientedArea (a b c : ℂ) : ℝ := (conj (b-a)*(c-a)).im

theorem normalize_edge (a b : ℂ) (hab : a≠b) :
    ∃ e : ℂ≃ᵢℂ,e a=0 ∧ e b=(dist a b : ℂ) ∧
      ∀ z,(e z).im=orientedArea a b z/dist a b := by
  let L := dist a b
  have hL : 0<L := dist_pos.mpr hab
  let u : ℂ := conj (b-a)/(L:ℂ)
  have hu : ‖u‖=1 := by
    rw [show u=conj (b-a)/(L:ℂ) from rfl,norm_div,Complex.norm_conj,Complex.norm_real,
      Real.norm_eq_abs,abs_of_pos hL]
    have hn : ‖b-a‖=L := by exact (dist_eq_norm b a).symm.trans (dist_comm b a)
    rw [hn,div_self hL.ne']
  let U : Circle := ⟨u,by simpa [Submonoid.unitSphere] using hu⟩
  let e : ℂ≃ᵢℂ := (IsometryEquiv.vaddConst a).symm.trans (rotation U).toIsometryEquiv
  have he (z:ℂ) : e z=u*(z-a) := rfl
  refine ⟨e,?_,?_,?_⟩
  · rw [he,sub_self,mul_zero]
  · rw [he]
    have hn : (Complex.normSq (b-a) : ℂ)=(L:ℂ)^2 := by
      rw [Complex.normSq_eq_norm_sq]
      have : ‖b-a‖=L := by exact (dist_eq_norm b a).symm.trans (dist_comm b a)
      rw [this,Complex.ofReal_pow]
    dsimp [u]
    rw [div_mul_eq_mul_div,←Complex.normSq_eq_conj_mul_self,hn]
    have hLc : (L:ℂ)≠0 := by exact_mod_cast hL.ne'
    change (L:ℂ)^2/(L:ℂ)=(L:ℂ)
    field_simp
  · intro z
    rw [he]
    change (conj (b-a)/(L:ℂ)*(z-a)).im=_
    rw [div_mul_eq_mul_div,Complex.div_ofReal_im]
    rfl

theorem normalized_two_distances {L : ℝ} (hL : 0<L) {z w : ℂ}
    (h0 : ‖z‖=‖w‖) (h1 : dist (L:ℂ) z=dist (L:ℂ) w) :
    z=w ∨ z=conj w := by
  have hs0 := congrArg (fun t:ℝ=>t^2) h0
  have hs1 := congrArg (fun t:ℝ=>t^2) h1
  simp only [dist_eq_norm,Complex.sq_norm,Complex.normSq_apply,Complex.sub_re,
    Complex.sub_im,Complex.ofReal_re,Complex.ofReal_im] at hs0 hs1
  have hre : z.re=w.re := by nlinarith
  have him : z.im=w.im ∨ z.im= -w.im := by
    have hh : z.im*z.im=w.im*w.im := by nlinarith
    exact mul_self_eq_mul_self_iff.mp hh
  rcases him with h|h
  · exact Or.inl (Complex.ext hre h)
  · exact Or.inr (Complex.ext hre (by simpa using h))

theorem congruent_triangle_isometry (a b c A B C : ℂ) (hab : a≠b)
    (hAB : dist a b=dist A B) (hAC : dist a c=dist A C)
    (hBC : dist b c=dist B C) :
    ∃ e : ℂ≃ᵢℂ,e a=A ∧ e b=B ∧ e c=C := by
  have hAB' : A≠B := by intro h; rw [h,dist_self] at hAB; exact hab (dist_eq_zero.mp hAB)
  obtain ⟨e,hea,heb,-⟩ := normalize_edge a b hab
  obtain ⟨f,hfA,hfB,-⟩ := normalize_edge A B hAB'
  have hz0 : ‖e c‖=‖f C‖ := by
    have h := (e.dist_eq a c).trans (hAC.trans (f.dist_eq A C).symm)
    simpa [hea,hfA] using h
  have hz1 : dist (dist a b : ℂ) (e c)=dist (dist a b : ℂ) (f C) := by
    have h := (e.dist_eq b c).trans (hBC.trans (f.dist_eq B C).symm)
    simpa [heb,hfB,←hAB] using h
  rcases normalized_two_distances (dist_pos.mpr hab) hz0 hz1 with h|h
  · refine ⟨e.trans f.symm,?_,?_,?_⟩
    · apply f.injective; simpa [IsometryEquiv.trans_apply,hea] using hfA.symm
    · apply f.injective; simp [IsometryEquiv.trans_apply,heb,hfB,hAB]
    · apply f.injective; simpa [IsometryEquiv.trans_apply] using h
  · refine ⟨(e.trans Complex.conjLIE.toIsometryEquiv).trans f.symm,?_,?_,?_⟩
    · apply f.injective; simpa [IsometryEquiv.trans_apply,hea] using hfA.symm
    · apply f.injective; simp [IsometryEquiv.trans_apply,heb,hfB,hAB]
    · apply f.injective; simp [IsometryEquiv.trans_apply,h]

theorem point_unique_of_three_distances (a b c x y : ℂ)
    (harea : orientedArea a b c≠0)
    (ha : dist a x=dist a y) (hb : dist b x=dist b y) (hc : dist c x=dist c y) : x=y := by
  have hab : a≠b := by rintro rfl; exact harea (by simp [orientedArea])
  obtain ⟨e,hea,heb,he⟩ := normalize_edge a b hab
  have hz0 : ‖e x‖=‖e y‖ := by
    simpa [hea] using (e.dist_eq a x).trans (ha.trans (e.dist_eq a y).symm)
  have hz1 : dist (dist a b : ℂ) (e x)=dist (dist a b : ℂ) (e y) := by
    simpa [heb] using (e.dist_eq b x).trans (hb.trans (e.dist_eq b y).symm)
  rcases normalized_two_distances (dist_pos.mpr hab) hz0 hz1 with h|h
  · exact e.injective h
  have hcd : dist (e c) (e x)=dist (e c) (e y) :=
    (e.dist_eq c x).trans (hc.trans (e.dist_eq c y).symm)
  have hyim : (e y).im=0 := by
    have hn := congrArg (fun t:ℝ=>t^2) hcd
    rw [h] at hn
    simp only [dist_eq_norm,Complex.sq_norm,Complex.normSq_apply,Complex.sub_re,
      Complex.sub_im,Complex.conj_re,Complex.conj_im] at hn
    have hci : (e c).im≠0 := by rw [he]; exact div_ne_zero harea (dist_pos.mpr hab).ne'
    have hm : (e c).im*(e y).im=0 := by nlinarith
    exact (mul_eq_zero.mp hm).resolve_left hci
  apply e.injective
  rw [h]
  exact Complex.ext (by simp) (by simp [hyim])

 theorem triangle_isometry_unique {a b c : ℂ} (harea : orientedArea a b c≠0)
    {e f : ℂ≃ᵢℂ} (ha : e a=f a) (hb : e b=f b) (hc : e c=f c) : e=f := by
  ext z
  apply e.symm.injective
  apply point_unique_of_three_distances a b c _ _ harea
  · calc
      dist a (e.symm (e z)) = dist (e a) (e z) := by rw [e.symm_apply_apply]; exact (e.dist_eq a z).symm
      _ = dist (f a) (f z) := (e.dist_eq a z).trans (f.dist_eq a z).symm
      _ = dist a (e.symm (f z)) := by rw [←ha,←e.symm.dist_eq]; simp
  · calc
      dist b (e.symm (e z)) = dist (e b) (e z) := by rw [e.symm_apply_apply]; exact (e.dist_eq b z).symm
      _ = dist (f b) (f z) := (e.dist_eq b z).trans (f.dist_eq b z).symm
      _ = dist b (e.symm (f z)) := by rw [←hb,←e.symm.dist_eq]; simp
  · calc
      dist c (e.symm (e z)) = dist (e c) (e z) := by rw [e.symm_apply_apply]; exact (e.dist_eq c z).symm
      _ = dist (f c) (f z) := (e.dist_eq c z).trans (f.dist_eq c z).symm
      _ = dist c (e.symm (f z)) := by rw [←hc,←e.symm.dist_eq]; simp
@[simp] lemma orientedArea_translate (t a b c : ℂ) :
    orientedArea (a+t) (b+t) (c+t)=orientedArea a b c := by
  simp [orientedArea]

lemma orientedArea_rotate (u:Circle) (a b c:ℂ) :
    orientedArea ((u:ℂ)*a) ((u:ℂ)*b) ((u:ℂ)*c)=orientedArea a b c := by
  unfold orientedArea
  rw [←mul_sub,←mul_sub,map_mul]
  have he : conj (u:ℂ)*conj (b-a)*((u:ℂ)*(c-a))=
      (conj (u:ℂ)*(u:ℂ))*(conj (b-a)*(c-a)) := by ring
  rw [he,←Complex.normSq_eq_conj_mul_self,Circle.normSq_coe,Complex.ofReal_one,one_mul]

@[simp] lemma orientedArea_conj (a b c:ℂ) :
    orientedArea (conj a) (conj b) (conj c)= -orientedArea a b c := by
  simp only [orientedArea,←map_sub,Complex.conj_conj,Complex.mul_im,Complex.conj_re,Complex.conj_im]
  ring

theorem isometry_orientedArea_product (e:ℂ≃ᵢℂ) (a b c d:ℂ) :
    orientedArea (e a) (e b) (e c)*orientedArea (e a) (e b) (e d)=
      orientedArea a b c*orientedArea a b d := by
  obtain ⟨u,hu|hu⟩ := linear_isometry_complex e.toRealLinearIsometryEquiv
  · have he (z:ℂ) : e z=(u:ℂ)*z+e 0 := by
      have hh := congrArg (fun f:ℂ≃ₗᵢ[ℝ]ℂ=>f z) hu
      change e z-e 0=(u:ℂ)*z at hh
      exact eq_add_of_sub_eq hh
    rw [he a,he b,he c,he d]
    simp only [orientedArea_translate,orientedArea_rotate]
  · have he (z:ℂ) : e z=(u:ℂ)*conj z+e 0 := by
      have hh := congrArg (fun f:ℂ≃ₗᵢ[ℝ]ℂ=>f z) hu
      simp only [e.toRealLinearIsometryEquiv_apply,LinearIsometryEquiv.trans_apply,
        Complex.conjLIE_apply,rotation_apply] at hh
      exact eq_add_of_sub_eq hh
    rw [he a,he b,he c,he d]
    simp only [orientedArea_translate,orientedArea_rotate,orientedArea_conj,neg_mul_neg]

theorem point_unique_of_two_distances_and_side (a b x y : ℂ) (hab:a≠b) (t:ℝ)
    (ha:dist a x=dist a y) (hb:dist b x=dist b y)
    (hx:orientedArea a b x*t<0) (hy:orientedArea a b y*t<0) : x=y := by
  obtain ⟨e,hea,heb,he⟩ := normalize_edge a b hab
  have hz0 : ‖e x‖=‖e y‖ := by
    simpa [hea] using (e.dist_eq a x).trans (ha.trans (e.dist_eq a y).symm)
  have hz1 : dist (dist a b : ℂ) (e x)=dist (dist a b : ℂ) (e y) := by
    simpa [heb] using (e.dist_eq b x).trans (hb.trans (e.dist_eq b y).symm)
  rcases normalized_two_distances (dist_pos.mpr hab) hz0 hz1 with h|h
  · exact e.injective h
  have him := congrArg Complex.im h
  simp only [Complex.conj_im,he] at him
  have harea : orientedArea a b x= -orientedArea a b y := by
    have hL : dist a b≠0 := (dist_pos.mpr hab).ne'
    field_simp [hL] at him
    linarith
  rw [harea,neg_mul] at hx
  linarith

theorem folded_edge_isometry (a b c A B C : ℂ) (hab:a≠b)
    (hd:dist a b=dist A B) (hs:orientedArea a b c≠0) (hS:orientedArea A B C≠0) :
    ∃! e : ℂ≃ᵢℂ,e a=A ∧ e b=B ∧ orientedArea A B (e c)*orientedArea A B C<0 := by
  have hAB : A≠B := by intro h; rw [h,dist_self] at hd; exact hab (dist_eq_zero.mp hd)
  obtain ⟨n,hna,hnb,hn⟩ := normalize_edge a b hab
  obtain ⟨m,hmA,hmB,hm⟩ := normalize_edge A B hAB
  have hc : (n c).im≠0 := by rw [hn]; exact div_ne_zero hs (dist_pos.mpr hab).ne'
  have hprod : (n c).im*orientedArea A B C≠0 := mul_ne_zero hc hS
  have exist : ∃ e : ℂ≃ᵢℂ,e a=A ∧ e b=B ∧
      orientedArea A B (e c)*orientedArea A B C<0 := by
    by_cases hp : (n c).im*orientedArea A B C<0
    · let e := n.trans m.symm
      have hc' : orientedArea A B (e c)=dist A B*(n c).im := by
        have hh := hm (e c)
        have he : m (e c)=n c := by simp [e]
        rw [he] at hh
        exact (div_eq_iff (dist_pos.mpr hAB).ne').mp hh.symm |>.trans (mul_comm ..)
      refine ⟨e,?_,?_,?_⟩
      · apply m.injective; simp [e,hna,hmA]
      · apply m.injective; simp [e,hnb,hmB,hd]
      · rw [hc',mul_assoc]
        exact mul_neg_of_pos_of_neg (dist_pos.mpr hAB) hp
    · let e := (n.trans Complex.conjLIE.toIsometryEquiv).trans m.symm
      have hc' : orientedArea A B (e c)= -(dist A B*(n c).im) := by
        have hh := hm (e c)
        have he : m (e c)=conj (n c) := by simp [e]
        rw [he,Complex.conj_im] at hh
        have hh' := (div_eq_iff (dist_pos.mpr hAB).ne').mp hh.symm
        rw [hh']; ring
      refine ⟨e,?_,?_,?_⟩
      · apply m.injective; simp [e,hna,hmA]
      · apply m.injective; simp [e,hnb,hmB,hd]
      · rw [hc',neg_mul,mul_assoc]
        exact neg_neg_of_pos (mul_pos (dist_pos.mpr hAB) (lt_of_le_of_ne (le_of_not_gt hp) hprod.symm))
  obtain ⟨e,hea,heb,hec⟩ := exist
  refine ⟨e,⟨hea,heb,hec⟩,?_⟩
  rintro f ⟨hfa,hfb,hfc⟩
  apply triangle_isometry_unique hs (hfa.trans hea.symm) (hfb.trans heb.symm)
  apply point_unique_of_two_distances_and_side A B (f c) (e c) hAB (orientedArea A B C)
  · calc dist A (f c) = dist a c := by rw [←hfa]; exact f.dist_eq a c
         _ = dist A (e c) := by rw [←hea]; exact (e.dist_eq a c).symm
  · calc dist B (f c) = dist b c := by rw [←hfb]; exact f.dist_eq b c
         _ = dist B (e c) := by rw [←heb]; exact (e.dist_eq b c).symm
  · exact hfc
  · exact hec

lemma orientedArea_swap (a b c:ℂ) : orientedArea a b c= -orientedArea a c b := by
  simp only [orientedArea,Complex.mul_im,Complex.conj_re,Complex.conj_im]
  ring

theorem folded_frames_compatible {a b c A B C P Q:ℂ}
    (hab:a≠b) (hd:dist a b=dist A B)
    (hs:orientedArea a b c≠0) (hS:orientedArea A B C≠0)
    (K e f:ℂ≃ᵢℂ) (hKa:K a=A) (hKb:K b=B)
    (hKc:orientedArea A B (K c)*orientedArea A B C<0)
    (hea:e a=P) (heb:e b=Q) (hfA:f A=P) (hfB:f B=Q)
    (hop:orientedArea P Q (e c)*orientedArea P Q (f C)<0) : K*e.symm=f.symm := by
  obtain ⟨g,hg,huniq⟩ := folded_edge_isometry a b c A B C hab hd hs hS
  have hK : K=g := huniq K ⟨hKa,hKb,hKc⟩
  have he : e.trans f.symm=g := by
    apply huniq
    refine ⟨?_,?_,?_⟩
    · apply f.injective; simp [hea,hfA]
    · apply f.injective; simp [heb,hfB]
    · have h := isometry_orientedArea_product f A B ((e.trans f.symm) c) C
      simp only [hfA,hfB,IsometryEquiv.trans_apply,IsometryEquiv.apply_symm_apply] at h
      change orientedArea A B (f.symm (e c))*orientedArea A B C<0
      rw [←h]
      exact hop
  rw [hK,←he]
  ext z
  simp [IsometryEquiv.mul_apply]

end CannonPackingGeometry

end
end
section
noncomputable section
namespace CannonPackingGeometry
open Set ComplexConjugate

theorem positive_radii_triangle (x y z:ℝ) (hx:0<x) (hy:0<y) (hz:0<z) :
    ∃ c:Fin 3→ℂ,(∀ i j,i≠j → dist (c i) (c j)=(![x,y,z] i)+(![x,y,z] j)) ∧
      orientedArea (c 0) (c 1) (c 2)≠0 := by
  let L:=x+y
  let U:=((x+y)^2+(x+z)^2-(y+z)^2)/(2*(x+y))
  let W:=2*Real.sqrt (x*y*z*(x+y+z))/(x+y)
  have hL : 0<L := add_pos hx hy
  have hprod : 0<x*y*z*(x+y+z) := by positivity
  have hW : 0<W := by dsimp [W]; positivity
  have hsq : U^2+W^2=(x+z)^2 := by
    dsimp [U,W]
    simp only [div_pow,mul_pow,Real.sq_sqrt hprod.le]
    field_simp [(add_pos hx hy).ne']
    ring
  have hsq' : (L-U)^2+W^2=(y+z)^2 := by
    have hu : 2*L*U=L^2+(x+z)^2-(y+z)^2 := by
      dsimp [L,U]
      field_simp [(add_pos hx hy).ne']
    nlinarith only [hsq,hu]
  let c:Fin 3→ℂ := ![0,(L:ℂ),⟨U,W⟩]
  have h01:dist (c 0) (c 1)=x+y := by
    change dist (0:ℂ) (L:ℂ)=L
    rw [dist_zero_left,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hL]
  have h02:dist (c 0) (c 2)=x+z := by
    have hh:‖c 2‖^2=(x+z)^2 := by
      rw [Complex.sq_norm]
      simpa [c,Complex.normSq_apply,pow_two] using hsq
    simp only [c,Matrix.cons_val_zero,Matrix.cons_val_two,dist_zero_left]
    change ‖(⟨U,W⟩:ℂ)‖=x+z
    change ‖(⟨U,W⟩:ℂ)‖^2=(x+z)^2 at hh
    nlinarith [norm_nonneg (⟨U,W⟩:ℂ)]
  have h12:dist (c 1) (c 2)=y+z := by
    have hh:dist (c 1) (c 2)^2=(y+z)^2 := by
      rw [dist_eq_norm,Complex.sq_norm]
      simpa [c,Complex.normSq_apply,Complex.sub_re,Complex.sub_im,L,pow_two] using hsq'
    nlinarith [dist_nonneg (x:=c 1) (y:=c 2)]
  refine ⟨c,?_,?_⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [dist_comm,add_comm]
    all_goals rw [dist_comm]; exact h01

  · have he:orientedArea (c 0) (c 1) (c 2)=L*W := by
      simp [c,orientedArea,Complex.mul_im,Complex.conj_ofReal]
    rw [he]
    exact (mul_pos hL hW).ne'

lemma orientedArea_ne_zero_of_strict {a b c:ℂ}
    (h1:dist a b<dist a c+dist b c)
    (h2:dist a c<dist a b+dist b c)
    (h3:dist b c<dist a b+dist a c) : orientedArea a b c≠0 := by
  have hab:a≠b := by intro h; simp only [h,dist_self,zero_add] at h2; exact lt_irrefl _ h2
  obtain ⟨e,hea,heb,he⟩ := normalize_edge a b hab
  intro hz
  have him:(e c).im=0 := by rw [he,hz,zero_div]
  have hec:e c=((e c).re:ℂ) := by apply Complex.ext <;> simp [him]
  have h0:dist a c=|(e c).re| := by
    rw [←e.dist_eq,hea,hec,dist_zero_left,Complex.norm_real,Real.norm_eq_abs]
    simp only [Complex.ofReal_re]
  have hL:dist b c=|dist a b-(e c).re| := by
    rw [←e.dist_eq,heb,hec,dist_eq_norm,←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
    simp only [Complex.ofReal_re]
  rw [h0,hL] at h1 h2 h3
  by_cases hc:0≤(e c).re
  · rw [abs_of_nonneg hc] at h1 h2 h3
    by_cases hl:0≤dist a b-(e c).re
    · rw [abs_of_nonneg hl] at h1; linarith
    · rw [abs_of_neg (lt_of_not_ge hl)] at h2; linarith
  · rw [abs_of_neg (lt_of_not_ge hc),abs_of_nonneg (by linarith [dist_nonneg (x:=a) (y:=b)])] at h3
    linarith

lemma triangle_third_unique {V:Type*} [DecidableEq V] {S:Finset V}
    (hS:S.card=3) {u v:V} (hu:u∈S) (hv:v∈S) (huv:u≠v) :
    ∃ w∈S,w≠u ∧ w≠v ∧ ∀ z∈S,z≠u → z≠v → z=w := by
  have hsub:({u,v}:Finset V)⊆S := by intro z hz; simp only [Finset.mem_insert,Finset.mem_singleton] at hz; rcases hz with rfl|rfl <;> assumption
  have hcard:(S\{u,v}).card=1 := by rw [Finset.card_sdiff_of_subset hsub,hS]; simp [huv]
  obtain ⟨w,hw⟩ := Finset.card_eq_one.mp hcard
  have hw':w∈S\{u,v} := by rw [hw]; simp
  simp only [Finset.mem_sdiff,Finset.mem_insert,Finset.mem_singleton,not_or] at hw'
  refine ⟨w,hw'.1,hw'.2.1,hw'.2.2,?_⟩
  intro z hz hzu hzv
  have hh:z∈S\{u,v} := by simp [hz,hzu,hzv]
  simpa only [hw,Finset.mem_singleton] using hh

theorem triangle_chart {V:Type*} [DecidableEq V] (S:Finset V) (hS:S.card=3)
    (r:V→ℝ) (hr:∀v,0<r v) :
    ∃ c:V→ℂ,∀ u∈S,∀ v∈S,u≠v → dist (c u) (c v)=r u+r v := by
  classical
  let en:Fin 3≃S := (Finset.equivFinOfCardEq hS).symm
  obtain ⟨z,hz,-⟩ := positive_radii_triangle (r (en 0)) (r (en 1)) (r (en 2)) (hr _) (hr _) (hr _)
  let c:V→ℂ := fun v=>if h:v∈S then z (en.symm ⟨v,h⟩) else 0
  have hval (i:Fin 3): ![r (en 0),r (en 1),r (en 2)] i=r (en i) := by fin_cases i <;> rfl
  refine ⟨c,fun u hu v hv huv=>?_⟩
  dsimp [c]
  rw [dite_eq_left hu,dite_eq_left hv,hz]
  · rw [hval,hval]; simp
  · intro hh
    have he:=congrArg (fun k=>(en k).val) hh
    exact huv (by simpa using he)

end CannonPackingGeometry

end
end
section
noncomputable section
namespace CannonPackingGeometry
open Set ComplexConjugate

lemma orientedArea_swap_edge (a b c:ℂ) : orientedArea b a c= -orientedArea a b c := by
  simp only [orientedArea,Complex.mul_im,Complex.conj_re,Complex.conj_im,Complex.sub_re,Complex.sub_im]
  ring

lemma chart_area_ne_zero {V:Type*} [DecidableEq V] {S:Finset V} {r:V→ℝ}
    (hr:∀v,0<r v) {c:V→ℂ}
    (hc:∀u∈S,∀v∈S,u≠v → dist (c u) (c v)=r u+r v)
    {u v w:V} (hu:u∈S) (hv:v∈S) (hw:w∈S) (huv:u≠v) (huw:u≠w) (hvw:v≠w) :
    orientedArea (c u) (c v) (c w)≠0 := by
  apply orientedArea_ne_zero_of_strict <;> rw [hc _ hu _ hv huv,hc _ hu _ hw huw,hc _ hv _ hw hvw]
  · linarith [hr w]
  · linarith [hr v]
  · linarith [hr u]

def Folds {V:Type*} (K:ℂ≃ᵢℂ) (c d:V→ℂ) (S T:Set V) (u v:V) : Prop :=
  K (c u)=d u ∧ K (c v)=d v ∧
    ∀ w∈S,w≠u → w≠v → ∀ z∈T,z≠u → z≠v →
      orientedArea (d u) (d v) (K (c w))*orientedArea (d u) (d v) (d z)<0

lemma Folds.swap {V:Type*} {K:ℂ≃ᵢℂ} {c d:V→ℂ} {S T:Set V} {u v:V}
    (h:Folds K c d S T u v) : Folds K c d S T v u := by
  refine ⟨h.2.1,h.1,fun w hw hwv hwu z hz hzv hzu=>?_⟩
  simp only [orientedArea_swap_edge (d u) (d v),neg_mul_neg]
  exact h.2.2 w hw hwu hwv z hz hzu hzv

lemma Folds.symm {V:Type*} {K:ℂ≃ᵢℂ} {c d:V→ℂ} {S T:Set V} {u v:V}
    (h:Folds K c d S T u v) : Folds K.symm d c T S u v := by
  refine ⟨?_,?_,fun z hz hzu hzv w hw hwu hwv=>?_⟩
  · exact K.symm_apply_eq.mpr h.1.symm
  · exact K.symm_apply_eq.mpr h.2.1.symm
  · have hh := isometry_orientedArea_product K (c u) (c v) (K.symm (d z)) (c w)
    rw [h.1,h.2.1,K.apply_symm_apply] at hh
    rw [←hh,mul_comm]
    exact h.2.2 w hw hwu hwv z hz hzu hzv

theorem exists_fold {V:Type*} [DecidableEq V] {S T:Finset V}
    (hS:S.card=3) (hT:T.card=3) {r:V→ℝ} (hr:∀v,0<r v)
    {c d:V→ℂ} (hc:∀u∈S,∀v∈S,u≠v → dist (c u) (c v)=r u+r v)
    (hd:∀u∈T,∀v∈T,u≠v → dist (d u) (d v)=r u+r v)
    {u v:V} (hu:u∈S) (hv:v∈S) (hU:u∈T) (hV:v∈T) (huv:u≠v) :
    ∃! K:ℂ≃ᵢℂ,Folds K c d S T u v := by
  obtain ⟨w,hw,hwu,hwv,hwuniq⟩ := triangle_third_unique hS hu hv huv
  obtain ⟨z,hz,hzu,hzv,hzuniq⟩ := triangle_third_unique hT hU hV huv
  have hcu:c u≠c v := by
    intro he
    have hh := hc u hu v hv huv
    rw [he,dist_self] at hh
    linarith [hr u,hr v]
  have hlen:dist (c u) (c v)=dist (d u) (d v) := (hc _ hu _ hv huv).trans (hd _ hU _ hV huv).symm
  have hcw:=chart_area_ne_zero hr hc hu hv hw huv hwu.symm hwv.symm
  have hdz:=chart_area_ne_zero hr hd hU hV hz huv hzu.symm hzv.symm
  obtain ⟨K,hK,huniq⟩ := folded_edge_isometry (c u) (c v) (c w) (d u) (d v) (d z) hcu hlen hcw hdz
  refine ⟨K,⟨hK.1,hK.2.1,?_⟩,?_⟩
  · intro w' hw' hw'u hw'v z' hz' hz'u hz'v
    rw [hwuniq w' hw' hw'u hw'v,hzuniq z' hz' hz'u hz'v]
    exact hK.2.2
  · intro J hJ
    exact huniq J ⟨hJ.1,hJ.2.1,hJ.2.2 w hw hwu hwv z hz hzu hzv⟩
end CannonPackingGeometry

end
end
section
noncomputable section
namespace CannonPackingGeometry
open Set ComplexConjugate

def fanRay (L α:ℕ→ℝ) (k:ℕ) : ℂ := (L k:ℂ)*(Circle.exp (∑ j∈Finset.range k,α j):ℂ)

lemma rotate_polar_dist (x y t a:ℝ) :
    dist ((x:ℂ)*(Circle.exp t:ℂ)) ((y:ℂ)*(Circle.exp (t+a):ℂ))=
      dist (x:ℂ) ((y:ℂ)*(Circle.exp a:ℂ)) := by
  rw [Circle.exp_add,Circle.coe_mul]
  convert (rotation (Circle.exp t)).dist_map (x:ℂ) ((y:ℂ)*(Circle.exp a:ℂ)) using 1
  simp only [rotation_apply]
  congr 1 <;> ring

lemma polar_distance_sq (x y a:ℝ) :
    dist (x:ℂ) ((y:ℂ)*(Circle.exp a:ℂ))^2=x^2+y^2-2*x*y*Real.cos a := by
  rw [dist_eq_norm,Complex.sq_norm]
  simp only [Complex.normSq_apply,Circle.coe_exp,Complex.exp_mul_I,←Complex.ofReal_cos,←Complex.ofReal_sin,Complex.sub_re,
    Complex.sub_im,Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
    Complex.add_re,Complex.add_im,Complex.I_re,Complex.I_im]
  nlinarith only [Real.sin_sq_add_cos_sq a]

lemma polar_orientedArea (x y a:ℝ) :
    orientedArea 0 (x:ℂ) ((y:ℂ)*(Circle.exp a:ℂ))=x*y*Real.sin a := by
  simp only [orientedArea,sub_zero,Complex.conj_ofReal,Circle.coe_exp,Complex.exp_mul_I,←Complex.ofReal_cos,←Complex.ofReal_sin,
    Complex.mul_im,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    Complex.add_re,Complex.add_im,Complex.I_re,Complex.I_im]
  ring

lemma rotated_polar_orientedArea (x y t a:ℝ) :
    orientedArea 0 ((x:ℂ)*(Circle.exp t:ℂ)) ((y:ℂ)*(Circle.exp (t+a):ℂ))=
      x*y*Real.sin a := by
  rw [Circle.exp_add,Circle.coe_mul]
  have h := orientedArea_rotate (Circle.exp t) 0 (x:ℂ) ((y:ℂ)*(Circle.exp a:ℂ))
  rw [mul_zero,polar_orientedArea] at h
  convert h using 1
  congr 1 <;> ring

@[simp] lemma fanRay_zero (L α:ℕ→ℝ) : fanRay L α 0=(L 0:ℂ) := by
  simp [fanRay]

lemma fanRay_norm {L α:ℕ→ℝ} {k:ℕ} (hk:0≤L k) : ‖fanRay L α k‖=L k := by
  rw [fanRay,norm_mul,Circle.norm_coe,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hk,mul_one]

lemma fanRay_dist_sq (L α:ℕ→ℝ) (k:ℕ) :
    dist (fanRay L α k) (fanRay L α (k+1))^2=
      (L k)^2+(L (k+1))^2-2*L k*L (k+1)*Real.cos (α k) := by
  simp only [fanRay,Finset.sum_range_succ]
  rw [rotate_polar_dist,polar_distance_sq]

lemma fanRay_orientedArea (L α:ℕ→ℝ) (k:ℕ) :
    orientedArea 0 (fanRay L α k) (fanRay L α (k+1))=L k*L (k+1)*Real.sin (α k) := by
  simp only [fanRay,Finset.sum_range_succ]
  rw [rotated_polar_orientedArea]

theorem closed_euclidean_fan (n:ℕ) (L α d:ℕ→ℝ)
    (hL:∀ k≤n,0<L k) (hd:∀ k<n,0<d k)
    (hα:∀ k<n,α k∈Ioo (0:ℝ) Real.pi)
    (hs:∑ k∈Finset.range n,α k=2*Real.pi) (hp:L n=L 0)
    (hcos:∀ k<n,2*L k*L (k+1)*Real.cos (α k)=(L k)^2+(L (k+1))^2-(d k)^2) :
    fanRay L α n=fanRay L α 0 ∧
    (∀ k≤n,dist (0:ℂ) (fanRay L α k)=L k) ∧
    ∀ k<n,dist (fanRay L α k) (fanRay L α (k+1))=d k ∧
      0<orientedArea 0 (fanRay L α k) (fanRay L α (k+1)) := by
  refine ⟨?_,?_,?_⟩
  · simp [fanRay,hs,hp,Circle.exp_two_pi]
  · intro k hk; rw [dist_zero_left]; exact fanRay_norm (hL k hk).le
  · intro k hk
    constructor
    · have he := fanRay_dist_sq L α k
      rw [hcos k hk] at he
      nlinarith [dist_nonneg (x:=fanRay L α k) (y:=fanRay L α (k+1)),hd k hk]
    · rw [fanRay_orientedArea]
      exact mul_pos (mul_pos (hL k (by omega)) (hL (k+1) (by omega)))
        (Real.sin_pos_of_pos_of_lt_pi (hα k hk).1 (hα k hk).2)

theorem fan_triangle_frames (n:ℕ) (L α d:ℕ→ℝ)
    (hL:∀ k≤n,0<L k) (hd:∀ k<n,0<d k)
    (hα:∀ k<n,α k∈Ioo (0:ℝ) Real.pi)
    (hs:∑ k∈Finset.range n,α k=2*Real.pi) (hp:L n=L 0)
    (hcos:∀ k<n,2*L k*L (k+1)*Real.cos (α k)=(L k)^2+(L (k+1))^2-(d k)^2)
    (A B C:Fin n→ℂ)
    (hAB:∀ i,dist (A i) (B i)=L i.val)
    (hAC:∀ i,dist (A i) (C i)=L (i.val+1))
    (hBC:∀ i,dist (B i) (C i)=d i.val) :
    ∃ e:Fin n→(ℂ≃ᵢℂ),∀ i,e i (A i)=0 ∧ e i (B i)=fanRay L α i.val ∧
      e i (C i)=fanRay L α (i.val+1) := by
  classical
  obtain ⟨_,hR,hD⟩ := closed_euclidean_fan n L α d hL hd hα hs hp hcos
  have h (i:Fin n) : ∃ e:ℂ≃ᵢℂ,e (A i)=0 ∧ e (B i)=fanRay L α i.val ∧
      e (C i)=fanRay L α (i.val+1) := by
    apply congruent_triangle_isometry
    · intro he
      have hh := hAB i
      rw [he,dist_self] at hh
      exact (hL i.val (by omega)).ne' hh.symm
    · exact (hAB i).trans (hR _ (by omega)).symm
    · exact (hAC i).trans (hR _ (by omega)).symm
    · exact (hBC i).trans (hD _ i.isLt).1.symm
  choose e he using h
  exact ⟨e,he⟩
def fanSucc {n:ℕ} (hn:0<n) (i:Fin n) : Fin n :=
  if h:i.val+1<n then ⟨i.val+1,h⟩ else ⟨0,hn⟩

lemma fanRay_succ {n:ℕ} (hn:0<n) (L α:ℕ→ℝ)
    (hclose:fanRay L α n=fanRay L α 0) (i:Fin n) :
    fanRay L α (i.val+1)=fanRay L α (fanSucc hn i).val := by
  unfold fanSucc
  split_ifs with h
  · rfl
  · have he : i.val+1=n := by omega
    simpa only [he] using hclose

theorem cyclic_folded_frames (n:ℕ) (hn:0<n) (L α d:ℕ→ℝ)
    (hL:∀ k≤n,0<L k) (hd:∀ k<n,0<d k)
    (hα:∀ k<n,α k∈Ioo (0:ℝ) Real.pi)
    (hs:∑ k∈Finset.range n,α k=2*Real.pi) (hp:L n=L 0)
    (hcos:∀ k<n,2*L k*L (k+1)*Real.cos (α k)=(L k)^2+(L (k+1))^2-(d k)^2)
    (A B C:Fin n→ℂ)
    (hAB:∀ i,dist (A i) (B i)=L i.val)
    (hAC:∀ i,dist (A i) (C i)=L (i.val+1))
    (hBC:∀ i,dist (B i) (C i)=d i.val)
    (K:Fin n→(ℂ≃ᵢℂ))
    (hKA:∀ i,K i (A i)=A (fanSucc hn i))
    (hKC:∀ i,K i (C i)=B (fanSucc hn i))
    (hKB:∀ i,orientedArea (A (fanSucc hn i)) (B (fanSucc hn i)) (K i (B i))*
      orientedArea (A (fanSucc hn i)) (B (fanSucc hn i)) (C (fanSucc hn i))<0) :
    ∃ t:Fin n→(ℂ≃ᵢℂ),∀ i,K i*t i=t (fanSucc hn i) := by
  obtain ⟨hclose,hR,hD⟩ := closed_euclidean_fan n L α d hL hd hα hs hp hcos
  obtain ⟨e,he⟩ := fan_triangle_frames n L α d hL hd hα hs hp hcos A B C hAB hAC hBC
  have harea (i:Fin n) : orientedArea (A i) (B i) (C i)≠0 := by
    have hh := isometry_orientedArea_product (e i) (A i) (B i) (C i) (C i)
    rw [(he i).1,(he i).2.1,(he i).2.2] at hh
    intro hz
    rw [hz,mul_zero] at hh
    exact mul_ne_zero (hD i.val i.isLt).2.ne' (hD i.val i.isLt).2.ne' hh
  refine ⟨fun i=>(e i).symm,fun i=>?_⟩
  let j := fanSucc hn i
  have hray : fanRay L α (i.val+1)=fanRay L α j.val := fanRay_succ hn L α hclose i
  apply folded_frames_compatible (a:=A i) (b:=C i) (c:=B i)
    (A:=A j) (B:=B j) (C:=C j) (P:=0) (Q:=fanRay L α j.val)
    (e:=e i) (f:=e j)
  · intro hh
    have hh' := hAC i
    rw [hh,dist_self] at hh'
    exact (hL (i.val+1) (by omega)).ne' hh'.symm
  · calc dist (A i) (C i) = dist ((e i) (A i)) ((e i) (C i)) :=
          ((e i).dist_eq _ _).symm
         _ = dist ((e j) (A j)) ((e j) (B j)) := by
          rw [(he i).1,(he i).2.2,(he j).1,(he j).2.1,hray]
         _ = dist (A j) (B j) := (e j).dist_eq _ _
  · rw [orientedArea_swap]
    exact neg_ne_zero.mpr (harea i)
  · exact harea j
  · exact hKA i
  · exact hKC i
  · exact hKB i
  · exact (he i).1
  · exact (he i).2.2.trans hray
  · exact (he j).1
  · exact (he j).2.1
  · rw [(he i).2.1,(he j).2.2,←hray,orientedArea_swap 0 (fanRay L α (i.val+1))]
    exact mul_neg_of_neg_of_pos (neg_neg_of_pos (hD i.val i.isLt).2)
      (by rw [hray]; exact (hD j.val j.isLt).2)

end CannonPackingGeometry

end
end
section
noncomputable section
namespace CannonPackingGeometry
open Set

theorem finite_cyclic_folded_frames {n:ℕ} (hn:0<n) (L α d:Fin n→ℝ)
    (hL:∀ i,0<L i) (hd:∀ i,0<d i) (hα:∀ i,α i∈Ioo (0:ℝ) Real.pi)
    (hs:∑ i,α i=2*Real.pi)
    (hcos:∀ i,2*L i*L (CannonCycleOrder.next hn i)*Real.cos (α i)=
      (L i)^2+(L (CannonCycleOrder.next hn i))^2-(d i)^2)
    (A B C:Fin n→ℂ)
    (hAB:∀ i,dist (A i) (B i)=L i)
    (hAC:∀ i,dist (A i) (C i)=L (CannonCycleOrder.next hn i))
    (hBC:∀ i,dist (B i) (C i)=d i)
    (K:Fin n→(ℂ≃ᵢℂ))
    (hKA:∀ i,K i (A i)=A (CannonCycleOrder.next hn i))
    (hKC:∀ i,K i (C i)=B (CannonCycleOrder.next hn i))
    (hKB:∀ i,orientedArea (A (CannonCycleOrder.next hn i)) (B (CannonCycleOrder.next hn i)) (K i (B i))*
      orientedArea (A (CannonCycleOrder.next hn i)) (B (CannonCycleOrder.next hn i)) (C (CannonCycleOrder.next hn i))<0) :
    ∃ t:Fin n→(ℂ≃ᵢℂ),∀ i,K i*t i=t (CannonCycleOrder.next hn i) := by
  let atN (k:ℕ):Fin n := ⟨k%n,Nat.mod_lt _ hn⟩
  have hat (i:Fin n):atN i.val=i := Fin.ext (Nat.mod_eq_of_lt i.isLt)
  have hat' (i:Fin n):atN (i.val+1)=CannonCycleOrder.next hn i :=
    Fin.ext (CannonCycleOrder.next_mod hn i).symm
  have htotal:∑ k∈Finset.range n,α (atN k)=2*Real.pi := by
    rw [Finset.sum_range]
    simpa only [hat] using hs
  apply cyclic_folded_frames n hn (L∘atN) (α∘atN) (d∘atN)
    (fun k hk=>hL (atN k)) (fun k hk=>hd (atN k)) (fun k hk=>hα (atN k)) htotal
    (by simp [atN]) ?_ A B C ?_ ?_ ?_ K hKA hKC hKB
  · intro k hk
    have hh := hcos ⟨k,hk⟩
    have h0:=hat ⟨k,hk⟩
    have h1:=hat' ⟨k,hk⟩
    simpa only [Function.comp_def,h0,h1] using hh
  · intro i; simpa only [Function.comp_def,hat] using hAB i
  · intro i; simpa only [Function.comp_def,hat'] using hAC i
  · intro i; simpa only [Function.comp_def,hat] using hBC i
end CannonPackingGeometry

end
end
end
end

end OAI
