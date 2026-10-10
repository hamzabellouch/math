import OAI.Dynamics.StandardMap.EntropyEndpoint
import OAI.Dynamics.StandardMap.Stable.SmoothRemainder

namespace OAI

section
section
namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped BigOperators ENNReal Topology

noncomputable def gridIntIndex (Q : ℕ) (hQ : 0<Q) (i : ℤ) : Fin Q :=
  ⟨(i%(Q : ℤ)).toNat,by
    have h0 := Int.emod_nonneg i (show (Q : ℤ)≠0 by omega)
    have h1 := Int.emod_lt_of_pos i (show (0 : ℤ)<Q by omega)
    omega⟩
lemma gridIndex_coe_int (Q : ℕ) (hQ : 0<Q) (y : ℝ) :
    gridIndex Q hQ (y : Circle)=gridIntIndex Q hQ ⌊(Q : ℝ)*y⌋ := by
  have hb : ((gridIndex Q hQ (y : Circle)).val : ℤ)=⌊(Q : ℝ)*y⌋-⌊y⌋*(Q : ℤ) := by
    change (⌊(Q : ℝ)*circleRep (y : Circle)⌋₊ : ℤ)=_
    rw [Int.natCast_floor_eq_floor (mul_nonneg (Nat.cast_nonneg Q) (circleRep_mem (y : Circle)).1),circleRep_coe]
    have he : (Q : ℝ)*Int.fract y=(Q : ℝ)*y-((⌊y⌋*(Q : ℤ) : ℤ) : ℝ) := by
      simp only [Int.fract,Int.cast_mul,Int.cast_natCast]
      ring
    rw [he,Int.floor_sub_intCast]
  have hm : ⌊(Q : ℝ)*y⌋%(Q : ℤ)=((gridIndex Q hQ (y : Circle)).val : ℤ) := by
    rw [←Int.sub_mul_emod_self_right ⌊(Q : ℝ)*y⌋ ⌊y⌋ (Q : ℤ),←hb]
    exact Int.emod_eq_of_lt (by omega) (by exact_mod_cast (gridIndex Q hQ (y : Circle)).isLt)
  apply Fin.ext
  simp only [gridIntIndex]
  rw [hm,Int.toNat_natCast]

noncomputable def gridIntLabel (Q : ℕ) (hQ : 0<Q) (v : ℤ×ℤ) : Fin (Q*Q+1) :=
  (finProdFinEquiv (gridIntIndex Q hQ v.1,gridIntIndex Q hQ v.2)).castSucc
lemma gridLabel_complex_lift (Q : ℕ) (hQ : 0<Q) (w : ℂ) :
    gridLabel Q hQ (complexProjection w)=gridIntLabel Q hQ (⌊(Q : ℝ)*w.re⌋,⌊(Q : ℝ)*w.im⌋) := by
  simp only [gridLabel,complexProjection,gridIndex_coe_int,gridIntLabel]
lemma floor_close_int {x y : ℝ} {M : ℕ} (h : |x-y|≤M) :
    ⌊x⌋∈Finset.Icc (⌊y⌋-(M : ℤ)-1) (⌊y⌋+(M : ℤ)+1) := by
  have hx0 := Int.floor_le x
  have hx1 := Int.lt_floor_add_one x
  have hy0 := Int.floor_le y
  have hy1 := Int.lt_floor_add_one y
  have hl := (abs_le.mp h).1
  have hu := (abs_le.mp h).2
  apply Finset.mem_Icc.mpr
  constructor
  · have hh : ((⌊y⌋-(M : ℤ)-1 : ℤ) : ℝ)≤(⌊x⌋ : ℝ) := by push_cast; linarith
    exact_mod_cast hh
  · have hh : (⌊x⌋ : ℝ)≤((⌊y⌋+(M : ℤ)+1 : ℤ) : ℝ) := by push_cast; linarith
    exact_mod_cast hh
noncomputable def liftGridCover (Q : ℕ) (hQ : 0<Q) (c : ℂ) (M : ℕ) : Finset (Fin (Q*Q+1)) :=
  ((Finset.Icc (⌊(Q : ℝ)*c.re⌋-(M : ℤ)-1) (⌊(Q : ℝ)*c.re⌋+(M : ℤ)+1)).product
    (Finset.Icc (⌊(Q : ℝ)*c.im⌋-(M : ℤ)-1) (⌊(Q : ℝ)*c.im⌋+(M : ℤ)+1))).image (gridIntLabel Q hQ)
lemma liftGridCover_card (Q : ℕ) (hQ : 0<Q) (c : ℂ) (M : ℕ) :
    (liftGridCover Q hQ c M).card≤(2*M+3)^2 := by
  apply (Finset.card_image_le).trans
  simp only [Finset.card,Finset.product,Multiset.card_product]
  change (Finset.Icc (⌊(Q : ℝ)*c.re⌋-(M : ℤ)-1) (⌊(Q : ℝ)*c.re⌋+(M : ℤ)+1)).card *
    (Finset.Icc (⌊(Q : ℝ)*c.im⌋-(M : ℤ)-1) (⌊(Q : ℝ)*c.im⌋+(M : ℤ)+1)).card ≤ _
  rw [Int.card_Icc,Int.card_Icc]
  have h1 : (⌊(Q : ℝ)*c.re⌋+(M : ℤ)+1+1-(⌊(Q : ℝ)*c.re⌋-(M : ℤ)-1)).toNat=2*M+3 := by omega
  have h2 : (⌊(Q : ℝ)*c.im⌋+(M : ℤ)+1+1-(⌊(Q : ℝ)*c.im⌋-(M : ℤ)-1)).toNat=2*M+3 := by omega
  rw [h1,h2,pow_two]
lemma liftGridCover_mem (Q : ℕ) (hQ : 0<Q) (c w : ℂ) (M : ℕ)
    (hw : ‖w-c‖≤(M : ℝ)/(Q : ℝ)) : gridLabel Q hQ (complexProjection w)∈liftGridCover Q hQ c M := by
  have hQpos : (0 : ℝ)<Q := Nat.cast_pos.mpr hQ
  have hr : |(Q : ℝ)*w.re-(Q : ℝ)*c.re|≤M := by
    rw [←mul_sub,abs_mul,abs_of_pos hQpos]
    have h := (Complex.abs_re_le_norm (w-c)).trans hw
    exact (mul_le_mul_of_nonneg_left h hQpos.le).trans_eq (mul_div_cancel₀ _ hQpos.ne')
  have hi : |(Q : ℝ)*w.im-(Q : ℝ)*c.im|≤M := by
    rw [←mul_sub,abs_mul,abs_of_pos hQpos]
    have h := (Complex.abs_im_le_norm (w-c)).trans hw
    exact (mul_le_mul_of_nonneg_left h hQpos.le).trans_eq (mul_div_cancel₀ _ hQpos.ne')
  rw [gridLabel_complex_lift]
  apply Finset.mem_image.mpr
  refine ⟨(⌊(Q : ℝ)*w.re⌋,⌊(Q : ℝ)*w.im⌋),?_,rfl⟩
  exact Finset.mem_product.mpr ⟨floor_close_int hr,floor_close_int hi⟩

end StandardMapEntropy

end
section
namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped BigOperators ENNReal Topology

lemma PlaneAreaPreserving.thin_cover {A : ℂ →L[ℝ] ℂ} (hA : PlaneAreaPreserving A) :
    ∃ (a : ℂ) (J : Finset ℤ),‖a‖=1 ∧ (J.card : ℝ)≤7*‖A‖ ∧
      ∀ v y : ℂ,‖v‖≤2 → ‖y-A v‖≤1 →
      ∃ j∈J,‖y-((j : ℝ)/‖A‖) • A a‖≤4 := by
  obtain ⟨a,ha,hAa,_,hAb,hL⟩ := hA.singular_pair
  have hLp : 0<‖A‖ := lt_of_lt_of_le zero_lt_one hL
  let N := ⌈2*‖A‖⌉₊
  have hN : 2*‖A‖≤(N : ℝ) := Nat.le_ceil _
  have hNb : (N : ℝ)<2*‖A‖+1 := Nat.ceil_lt_add_one (by positivity)
  let J := Finset.Icc (-(N : ℤ)) (N : ℤ)
  have hc : (J.card : ℝ)≤7*‖A‖ := by
    have hj : J.card=2*N+1 := by dsimp [J]; rw [Int.card_Icc]; omega
    rw [hj]
    push_cast
    nlinarith
  refine ⟨a,J,ha,hc,?_⟩
  intro v y hv hy
  have hd : |dot a v|≤2 := by simpa only [ha,one_mul] using (abs_dot_le_norm_mul a v).trans (by simpa [ha] using hv)
  have hw : |wedge a v|≤2 := by simpa only [ha,one_mul] using (abs_wedge_le_norm_mul a v).trans (by simpa [ha] using hv)
  let t := dot a v*‖A‖
  have ht : |t|≤(N : ℝ) := by
    dsimp [t]
    rw [abs_mul,abs_of_pos hLp]
    exact (mul_le_mul_of_nonneg_right hd hLp.le).trans hN
  have hj : ⌊t⌋∈J := by
    apply Finset.mem_Icc.mpr
    constructor
    · apply Int.le_floor.mpr
      simpa only [Int.cast_neg,Int.cast_natCast] using (abs_le.mp ht).1
    · apply Int.floor_le_iff.mpr
      simpa only [Int.cast_natCast] using lt_of_le_of_lt (abs_le.mp ht).2 (lt_add_one _)
  have hmajor : ‖(dot a v-(⌊t⌋ : ℝ)/‖A‖) • A a‖≤1 := by
    rw [norm_smul,Real.norm_eq_abs,hAa]
    have he : |dot a v-(⌊t⌋ : ℝ)/‖A‖| *‖A‖=|t-(⌊t⌋ : ℝ)| := by
      rw [←abs_of_pos hLp,←abs_mul]
      congr 1
      dsimp only [t]
      rw [abs_of_pos hLp]
      field_simp
    rw [he]
    exact abs_le.mpr ⟨by linarith [Int.floor_le t],by linarith [Int.lt_floor_add_one t]⟩
  have hminor : ‖(wedge a v) • A (quarterTurn a)‖≤2 := by
    rw [norm_smul,Real.norm_eq_abs,hAb]
    exact (mul_le_mul hw ((inv_le_one₀ hLp).mpr hL) (inv_nonneg.mpr hLp.le) (by norm_num)).trans_eq (mul_one _)
  have he : A v-((⌊t⌋ : ℝ)/‖A‖) • A a=
      (dot a v-(⌊t⌋ : ℝ)/‖A‖) • A a+(wedge a v) • A (quarterTurn a) := by
    conv_lhs => rw [unit_expansion a v ha]
    rw [map_add,map_smul,map_smul,sub_smul]
    abel
  refine ⟨⌊t⌋,hj,?_⟩
  have hn : ‖y-(((⌊t⌋ : ℝ)/‖A‖) • A a)‖≤‖y-A v‖+‖A v-(((⌊t⌋ : ℝ)/‖A‖) • A a)‖ := by
    simpa only [sub_add_sub_cancel] using norm_add_le (y-A v) (A v-(((⌊t⌋ : ℝ)/‖A‖) • A a))
  rw [he] at hn
  have hab := norm_add_le ((dot a v-(⌊t⌋ : ℝ)/‖A‖) • A a) ((wedge a v) • A (quarterTurn a))
  linarith

lemma PlaneAreaPreserving.grid_cover {A : ℂ →L[ℝ] ℂ} (hA : PlaneAreaPreserving A)
    (Q : ℕ) (hQ : 0<Q) (c : ℂ) :
    ∃ S : Finset (Fin (Q*Q+1)),(S.card : ℝ)≤1000*‖A‖ ∧
      ∀ v w : ℂ,‖v‖≤2/(Q : ℝ) → ‖w-c-A v‖≤1/(Q : ℝ) →
        gridLabel Q hQ (complexProjection w)∈S := by
  obtain ⟨a,J,ha,hJ,hcover⟩ := hA.thin_cover
  have hQp : (0 : ℝ)<Q := Nat.cast_pos.mpr hQ
  have hAp : 0<‖A‖ := lt_of_lt_of_le zero_lt_one hA.singular_pair.choose_spec.2.2.2.2
  let center : ℤ → ℂ := fun j => c+((j : ℝ)/((Q : ℝ)*‖A‖)) • A a
  let S : Finset (Fin (Q*Q+1)) := J.biUnion (fun j => liftGridCover Q hQ (center j) 4)
  have hcard : (S.card : ℝ)≤1000*‖A‖ := by
    have hn : S.card≤J.card*121 := calc
      _ ≤ ∑ j∈J,(liftGridCover Q hQ (center j) 4).card := Finset.card_biUnion_le
      _ ≤ ∑ _j∈J,121 := Finset.sum_le_sum (fun j _ => by simpa using liftGridCover_card Q hQ (center j) 4)
      _ = _ := by simp
    have hr : (S.card : ℝ)≤(J.card : ℝ)*121 := by exact_mod_cast hn
    nlinarith [norm_nonneg A]
  refine ⟨S,hcard,?_⟩
  intro v w hv hw
  have hv' : ‖(Q : ℝ) • v‖≤2 := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos hQp]
    exact (mul_le_mul_of_nonneg_left hv hQp.le).trans_eq (mul_div_cancel₀ _ hQp.ne')
  have hw' : ‖(Q : ℝ) • (w-c)-A ((Q : ℝ) • v)‖≤1 := by
    rw [map_smul,←smul_sub,norm_smul,Real.norm_eq_abs,abs_of_pos hQp]
    exact (mul_le_mul_of_nonneg_left hw hQp.le).trans_eq (mul_div_cancel₀ _ hQp.ne')
  obtain ⟨j,hj,hij⟩ := hcover ((Q : ℝ) • v) ((Q : ℝ) • (w-c)) hv' hw'
  have he : (Q : ℝ) • (w-center j)=(Q : ℝ) • (w-c)-((j : ℝ)/‖A‖) • A a := by
    simp only [center]
    rw [show w-(c+((j : ℝ)/((Q : ℝ)*‖A‖)) • A a)=
      (w-c)-((j : ℝ)/((Q : ℝ)*‖A‖)) • A a by abel,
      smul_sub,smul_smul]
    congr 2
    field_simp
  rw [←he,norm_smul,Real.norm_eq_abs,abs_of_pos hQp] at hij
  have hclose : ‖w-center j‖≤(4 : ℝ)/(Q : ℝ) := by
    apply (le_div_iff₀ hQp).mpr
    simpa only [mul_comm] using hij
  exact Finset.mem_biUnion.mpr ⟨j,hj,liftGridCover_mem Q hQ (center j) w 4 hclose⟩

end StandardMapEntropy

end
section
namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology ENNReal

lemma norm_sub_le_of_derivative_bound {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (D : E → E →L[ℝ] F) (hD : ∀ x,HasFDerivAt f (D x) x)
    {B : ℝ} (hB : ∀ x,‖D x‖≤B) (x y : E) : ‖f x-f y‖≤B*‖x-y‖ := by
  exact (convex_univ : Convex ℝ (Set.univ : Set E)).norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun z _ => (hD z).hasFDerivWithinAt) (fun z _ => hB z) (Set.mem_univ y) (Set.mem_univ x)

lemma standardLift_iterate_control (k : ℝ) (hk : 0≤k) (n : ℕ) :
    ∃ B C : ℝ,0<B ∧ 0≤C ∧
      (∀ z : ℂ,‖standardDerivativeProduct k (complexProjection z) n‖≤B) ∧
      (∀ z w : ℂ,‖standardDerivativeProduct k (complexProjection z) n-
         standardDerivativeProduct k (complexProjection w) n‖≤C*‖z-w‖) := by
  induction n with
  | zero =>
    refine ⟨1,0,zero_lt_one,le_rfl,?_,?_⟩
    · intro z
      simp only [standardDerivativeProduct_zero,ContinuousLinearMap.norm_id,le_refl]
    · intro z w
      simp only [standardDerivativeProduct_zero,sub_self,norm_zero,zero_mul,le_refl]
  | succ n ih =>
    obtain ⟨B,C,hB,hC,hbound,hLip⟩ := ih
    let D := 9*growthBase k
    have hD : 0<D := by
      have hg := growthBase_ge_four k hk
      dsimp [D]
      linarith
    have hf : ∀ z w : ℂ,‖(standardLift k)^[n] z-(standardLift k)^[n] w‖≤B*‖z-w‖ :=
      norm_sub_le_of_derivative_bound _ _ (hasFDerivAt_standardLift_iterate k n) hbound
    refine ⟨D*B,derivativeVariationBound k*B^2+D*C,mul_pos hD hB,
      add_nonneg (mul_nonneg (derivativeVariationBound_nonneg k) (sq_nonneg B)) (mul_nonneg hD.le hC),?_,?_⟩
    · intro z
      exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul (standardDerivative_norm_bound k hk _) (hbound z) (norm_nonneg _) hD.le)
    · intro z w
      let Az := standardDerivative k ((standardMap k)^[n] (complexProjection z))
      let Aw := standardDerivative k ((standardMap k)^[n] (complexProjection w))
      let Pz := standardDerivativeProduct k (complexProjection z) n
      let Pw := standardDerivativeProduct k (complexProjection w) n
      have he : Az.comp Pz-Aw.comp Pw=(Az-Aw).comp Pz+Aw.comp (Pz-Pw) := by
        ext v
        simp only [sub_apply,add_apply,ContinuousLinearMap.comp_apply,map_sub]
        abel
      have hdiff : ‖Az-Aw‖≤derivativeVariationBound k*(B*‖z-w‖) := by
        have hh := standardDerivative_lift_sub_bound k ((standardLift k)^[n] z) ((standardLift k)^[n] w)
        rw [complexProjection_iterate,complexProjection_iterate] at hh
        exact hh.trans (mul_le_mul_of_nonneg_left (hf z w) (derivativeVariationBound_nonneg k))
      change ‖Az.comp Pz-Aw.comp Pw‖≤_
      rw [he]
      calc
        _ ≤ ‖(Az-Aw).comp Pz‖+‖Aw.comp (Pz-Pw)‖ := norm_add_le _ _
        _ ≤ ‖Az-Aw‖*‖Pz‖+‖Aw‖*‖Pz-Pw‖ :=
          add_le_add (ContinuousLinearMap.opNorm_comp_le _ _) (ContinuousLinearMap.opNorm_comp_le _ _)
        _ ≤ (derivativeVariationBound k*(B*‖z-w‖))*B+D*(C*‖z-w‖) := by
          apply add_le_add
          · exact mul_le_mul hdiff (hbound z) (norm_nonneg _) (mul_nonneg (derivativeVariationBound_nonneg k) (mul_nonneg hB.le (norm_nonneg _)))
          · exact mul_le_mul (standardDerivative_norm_bound k hk _) (hLip z w) (norm_nonneg _) hD.le
        _ = _ := by ring

lemma log_norm_sub_le_of_one_le {E : Type*} [SeminormedAddCommGroup E] {a b : E}
    (ha : 1≤‖a‖) (hb : 1≤‖b‖) : |Real.log ‖a‖-Real.log ‖b‖|≤‖a-b‖ := by
  have ha0 : 0<‖a‖ := lt_of_lt_of_le zero_lt_one ha
  have hb0 : 0<‖b‖ := lt_of_lt_of_le zero_lt_one hb
  have hab := Real.log_le_sub_one_of_pos (div_pos ha0 hb0)
  have hba := Real.log_le_sub_one_of_pos (div_pos hb0 ha0)
  rw [Real.log_div ha0.ne' hb0.ne'] at hab
  rw [Real.log_div hb0.ne' ha0.ne'] at hba
  have hd := norm_sub_norm_le a b
  have hd' := norm_sub_norm_le b a
  rw [norm_sub_rev b a] at hd'
  apply abs_le.mpr
  constructor
  · have hh : ‖b‖/‖a‖-1≤‖a-b‖ := by
      apply (sub_le_iff_le_add).mpr
      apply (div_le_iff₀ ha0).mpr
      nlinarith [norm_nonneg (a-b)]
    linarith
  · have hh : ‖a‖/‖b‖-1≤‖a-b‖ := by
      apply (sub_le_iff_le_add).mpr
      apply (div_le_iff₀ hb0).mpr
      nlinarith [norm_nonneg (a-b)]
    exact hab.trans hh

end StandardMapEntropy

end
section
namespace StandardMapEntropy.Entropy
open Set Finset
open scoped BigOperators

noncomputable def shannon {α : Type*} [Fintype α] (p : α → ℝ) : ℝ :=
  ∑ a, Real.negMulLog (p a)

lemma negMulLog_le_cross {p q : ℝ} (hp : 0≤p) (hq : 0≤q) (hs : p≠0 → q≠0) :
    Real.negMulLog p≤ -p*Real.log q+q-p := by
  by_cases he : p=0
  · simp only [he,Real.negMulLog_zero,neg_zero,zero_mul,sub_zero,zero_add]
    exact hq
  have hp' : 0<p := lt_of_le_of_ne hp (Ne.symm he)
  have hq' : 0<q := lt_of_le_of_ne hq (Ne.symm (hs he))
  have hh := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos (div_pos hq' hp')) hp
  rw [Real.log_div hq'.ne' hp'.ne'] at hh
  have hc : p*(q/p-1)=q-p := by field_simp
  rw [hc] at hh
  dsimp [Real.negMulLog]
  nlinarith

lemma shannon_le_cross {α : Type*} [Fintype α] (p q : α → ℝ)
    (hp : ∀ a, 0≤p a) (hq : ∀ a, 0≤q a) (hs : ∀ a, p a≠0 → q a≠0)
    (hm : ∑ a,q a≤∑ a,p a) :
    shannon p≤ -∑ a,p a*Real.log (q a) := by
  have hh := Finset.sum_le_sum (s:=Finset.univ) (fun a _ => negMulLog_le_cross (hp a) (hq a) (hs a))
  simp only [Finset.sum_sub_distrib,Finset.sum_add_distrib,neg_mul,Finset.sum_neg_distrib] at hh
  dsimp [shannon]
  linarith

lemma shannon_nonneg {α : Type*} [Fintype α] (p : α → ℝ)
    (hp : ∀ a, 0≤p a) (hm : ∑ a,p a≤1) : 0 ≤ shannon p := by
  apply Finset.sum_nonneg
  intro a _
  exact Real.negMulLog_nonneg (hp a) ((Finset.single_le_sum (fun b _ => hp b) (Finset.mem_univ a)).trans hm)

lemma shannon_scale {α : Type*} [Fintype α] (p : α → ℝ) (c : ℝ) :
    shannon (fun a => c*p a)=c*shannon p+(∑ a,p a)*Real.negMulLog c := by
  simp only [shannon,Real.negMulLog_mul,Finset.sum_add_distrib,←Finset.mul_sum,←Finset.sum_mul]
  ring

lemma shannon_bound {α : Type*} [Fintype α] [Nonempty α] (p : α → ℝ)
    (hp : ∀ a, 0≤p a) (hm : ∑ a,p a=1) : shannon p≤Real.log (Fintype.card α) := by
  have hc : 0<(Fintype.card α : ℝ) := by exact_mod_cast Fintype.card_pos
  have hh := shannon_le_cross p (fun _ => (Fintype.card α : ℝ)⁻¹) hp
    (fun _ => (inv_pos.mpr hc).le) (fun _ _ => inv_ne_zero hc.ne') (by simp [hm,hc.ne'])
  rw [←Finset.sum_mul,hm,one_mul,Real.log_inv,neg_neg] at hh
  exact hh

lemma matrix_row_nonneg {α β : Type*} [Fintype α] [Fintype β]
    (p : α → β → ℝ) (hp : ∀ a b, 0≤p a b) (a : α) : 0≤∑ b,p a b :=
  Finset.sum_nonneg (fun b _ => hp a b)
lemma matrix_col_nonneg {α β : Type*} [Fintype α] [Fintype β]
    (p : α → β → ℝ) (hp : ∀ a b, 0≤p a b) (b : β) : 0≤∑ a,p a b :=
  Finset.sum_nonneg (fun a _ => hp a b)
lemma matrix_le_row {α β : Type*} [Fintype α] [Fintype β]
    (p : α → β → ℝ) (hp : ∀ a b, 0≤p a b) (a : α) (b : β) : p a b≤∑ j,p a j :=
  Finset.single_le_sum (fun j _ => hp a j) (Finset.mem_univ b)
lemma matrix_le_col {α β : Type*} [Fintype α] [Fintype β]
    (p : α → β → ℝ) (hp : ∀ a b, 0≤p a b) (a : α) (b : β) : p a b≤∑ i,p i b :=
  Finset.single_le_sum (fun i _ => hp i b) (Finset.mem_univ a)

lemma matrix_subadd {α β : Type*} [Fintype α] [Fintype β]
    (p : α → β → ℝ) (hp : ∀ a b, 0≤p a b) :
    shannon (fun ab : α×β => p ab.1 ab.2)≤
      shannon (fun a => ∑ b,p a b)+shannon (fun b => ∑ a,p a b)-
        Real.negMulLog (∑ a,∑ b,p a b) := by
  let A : α → ℝ := fun a => ∑ b,p a b
  let B : β → ℝ := fun b => ∑ a,p a b
  let T : ℝ := ∑ a,∑ b,p a b
  have hA := matrix_row_nonneg p hp
  have hB := matrix_col_nonneg p hp
  have hT : 0≤T := Finset.sum_nonneg (fun a _ => hA a)
  have hpT (a : α) (b : β) : p a b≤T := (matrix_le_row p hp a b).trans
    (Finset.single_le_sum (fun i _ => hA i) (Finset.mem_univ a))
  by_cases he : T=0
  · have hz (a : α) (b : β) : p a b=0 := le_antisymm (by simpa only [he] using hpT a b) (hp a b)
    simp only [shannon,hz,Finset.sum_const_zero,Real.negMulLog_zero,add_zero,sub_zero,le_refl]
  have hT' : 0<T := lt_of_le_of_ne hT (Ne.symm he)
  let q : α×β → ℝ := fun ab => A ab.1*B ab.2/T
  have hq (ab : α×β) : 0≤q ab := div_nonneg (mul_nonneg (hA ab.1) (hB ab.2)) hT
  have hs (ab : α×β) (hh : p ab.1 ab.2≠0) : q ab≠0 := by
    have hpos : 0<p ab.1 ab.2 := lt_of_le_of_ne (hp _ _) (Ne.symm hh)
    exact div_ne_zero (mul_ne_zero (ne_of_gt (hpos.trans_le (matrix_le_row p hp _ _)))
      (ne_of_gt (hpos.trans_le (matrix_le_col p hp _ _)))) he
  have hmass : ∑ ab : α×β,q ab=∑ ab : α×β,p ab.1 ab.2 := by
    simp only [q,Fintype.sum_prod_type,←Finset.sum_div,←Finset.mul_sum,←Finset.sum_mul]
    have hsumA : ∑ a,A a=T := rfl
    have hsumB : ∑ b,B b=T := by dsimp [B,T]; exact Finset.sum_comm
    rw [hsumA,hsumB,mul_div_cancel_right₀ _ he]
  have hh := shannon_le_cross (fun ab : α×β => p ab.1 ab.2) q (fun ab => hp ab.1 ab.2) hq hs hmass.le
  have hlog (a : α) (b : β) : p a b*Real.log (q (a,b))=
      p a b*Real.log (A a)+p a b*Real.log (B b)-p a b*Real.log T := by
    by_cases hz : p a b=0
    · simp only [hz,zero_mul,add_zero,sub_zero]
    have hpos : 0<p a b := lt_of_le_of_ne (hp a b) (Ne.symm hz)
    have ha : A a≠0 := ne_of_gt (hpos.trans_le (matrix_le_row p hp a b))
    have hb : B b≠0 := ne_of_gt (hpos.trans_le (matrix_le_col p hp a b))
    rw [show q (a,b)=A a*B b/T from rfl,Real.log_div (mul_ne_zero ha hb) he,Real.log_mul ha hb]
    ring
  have hsum1 : ∑ a,∑ b,p a b*Real.log (A a)=∑ a,A a*Real.log (A a) := by
    apply Finset.sum_congr rfl
    intro a _
    rw [←Finset.sum_mul]
  have hsum2 : ∑ a,∑ b,p a b*Real.log (B b)=∑ b,B b*Real.log (B b) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro b _
    rw [←Finset.sum_mul]
  have hsum3 : ∑ a,∑ b,p a b*Real.log T=T*Real.log T := by simp only [←Finset.sum_mul]; rfl
  simp only [Fintype.sum_prod_type,hlog,Finset.sum_sub_distrib,Finset.sum_add_distrib] at hh
  rw [hsum1,hsum2,hsum3] at hh
  dsimp only [shannon,Real.negMulLog] at hh ⊢
  simp only [neg_mul,Finset.sum_neg_distrib] at hh ⊢
  change _≤ -(∑ a,A a*Real.log (A a)) + -(∑ b,B b*Real.log (B b)) - (-(T*Real.log T))
  linarith

lemma shannon_total_bound {α : Type*} [Fintype α] (p : α → ℝ)
    (hp : ∀ a, 0≤p a) : shannon p≤Real.negMulLog (∑ a,p a)+(∑ a,p a)*Real.log (Fintype.card α) := by
  let T : ℝ := ∑ a,p a
  have hT : 0≤T := Finset.sum_nonneg (fun a _ => hp a)
  by_cases he : T=0
  · have hz (a : α) : p a=0 := le_antisymm
      ((Finset.single_le_sum (fun b _ => hp b) (Finset.mem_univ a) : p a≤T).trans_eq he) (hp a)
    simp only [shannon,hz,Finset.sum_const_zero,Real.negMulLog_zero,zero_mul,add_zero,le_refl]
  have hT' : 0<T := lt_of_le_of_ne hT (Ne.symm he)
  have : Nonempty α := by
    by_contra h
    have : IsEmpty α := not_nonempty_iff.mp h
    exact he (by dsimp [T]; simp)
  let q : α → ℝ := fun a => p a/T
  have hq (a : α) : 0≤q a := div_nonneg (hp a) hT
  have hmass : ∑ a,q a=1 := by dsimp [q]; rw [←Finset.sum_div]; exact div_self he
  have hb := mul_le_mul_of_nonneg_left (shannon_bound q hq hmass) hT
  have hs := shannon_scale q T
  have heq : (fun a => T*q a)=p := by funext a; dsimp [q]; field_simp
  rw [heq,hmass,one_mul] at hs
  change shannon p≤Real.negMulLog T+T*Real.log (Fintype.card α)
  linarith

lemma matrix_super_row {α β : Type*} [Fintype α] [Fintype β]
    (p : α → β → ℝ) (hp : ∀ a b, 0≤p a b) :
    shannon (fun a => ∑ b,p a b)≤ shannon (fun ab : α×β => p ab.1 ab.2) := by
  have hh (a : α) (b : β) : -p a b*Real.log (∑ j,p a j)≤Real.negMulLog (p a b) := by
    by_cases he : p a b=0
    · simp [he]
    have hpos : 0<p a b := lt_of_le_of_ne (hp a b) (Ne.symm he)
    have hlog := Real.log_le_log hpos (matrix_le_row p hp a b)
    exact mul_le_mul_of_nonpos_left hlog (neg_nonpos.mpr (hp a b))
  have hs := Finset.sum_le_sum (s:=Finset.univ) (fun a _ => Finset.sum_le_sum (s:=Finset.univ) (fun b _ => hh a b))
  simp only [neg_mul,←Finset.sum_mul,Finset.sum_neg_distrib] at hs
  simpa only [shannon,Fintype.sum_prod_type,Real.negMulLog,neg_mul,Finset.sum_neg_distrib] using hs

end StandardMapEntropy.Entropy

end
end

end OAI
