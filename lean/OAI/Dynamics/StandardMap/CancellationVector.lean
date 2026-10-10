import OAI.Dynamics.StandardMap.CancellationScalar

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology
namespace StandardMapEntropy
lemma torus_reverse_operator (k : ℝ) (z : Torus) (n : ℕ) :
    (planeSwap.comp (torusSegmentTransfer k z.swap 0 n)).comp planeSwap=
      transferProductInv (torusSegmentCoefficient k z (-(n:ℤ))) n := by
  ext u
  apply (show Function.Injective (torusSegmentTransfer k z (-(n:ℤ)) n) from fun x y hxy => by
    have := congrArg (transferProductInv (torusSegmentCoefficient k z (-(n:ℤ))) n) hxy
    simpa only [torusSegmentTransfer,transferProductInv_inverse] using this)
  exact (torusSegmentTransfer_reverse_identity k z n u).trans (transferProduct_inverse _ _ _).symm
lemma small_vector_of_cancellation (M : ℝ) (hM : 1 < M) (δ : ℝ) (hδ : 0 ≤ δ)
    (A B : ℂ →L[ℝ] ℂ) (hA : PlaneAreaPreserving A) (n : ℕ)
    (ha : M^((1-δ)*(n:ℝ)) ≤ ‖A‖) (hab : ‖B‖ ≤ M^(δ*(n:ℝ))) :
    ∃ u : ℂ, ‖u‖=1 ∧ ‖A u‖ ≤ M^(-((1-2*δ)*(n:ℝ))) ∧
      ‖B (A u)‖ ≤ M^(-((1-2*δ)*(n:ℝ))) := by
  obtain ⟨a,ha1,_,_,hsmall,hAn⟩ := hA.singular_pair
  have hMp : 0 < M := by linarith
  have hneg : ‖A (quarterTurn a)‖ ≤ M^(-((1-δ)*(n:ℝ))) := by
    rw [hsmall,Real.rpow_neg hMp.le]
    exact (inv_le_inv₀ (by linarith : 0 < ‖A‖) (Real.rpow_pos_of_pos hMp _)).mpr ha
  refine ⟨quarterTurn a,by simpa [norm_quarterTurn] using ha1,?_,?_⟩
  · exact hneg.trans (Real.rpow_le_rpow_of_exponent_le hM.le (by nlinarith [Nat.cast_nonneg (α:=ℝ) n]))
  · calc
      _ ≤ ‖B‖*‖A (quarterTurn a)‖ := B.le_opNorm _
      _ ≤ M^(δ*(n:ℝ))*M^(-((1-δ)*(n:ℝ))) := mul_le_mul hab hneg (norm_nonneg _) (Real.rpow_nonneg hMp.le _)
      _ = _ := by rw [← Real.rpow_add hMp]; congr 1; ring
lemma torus_cancellation_vector (k : ℝ) (hk : 0 ≤ k) (n : ℕ) (δ : ℝ) (hδ : 0 ≤ δ)
    (z : Torus)
    (hback : growthBase k^((1-δ)*(n:ℝ)) ≤ ‖torusSegmentTransfer k z (-(n:ℤ)) n‖)
    (hfull : ‖torusSegmentTransfer k z (-(n:ℤ)) (n+n)‖ ≤ growthBase k^(δ*(n:ℝ))) :
    ∃ u : ℂ, ‖u‖=1 ∧
      ‖torusSegmentTransfer k z.swap 0 n (planeSwap u)‖ ≤ growthBase k^(-((1-2*δ)*(n:ℝ))) ∧
      ‖torusSegmentTransfer k z 0 n u‖ ≤ growthBase k^(-((1-2*δ)*(n:ℝ))) := by
  let A := transferProductInv (torusSegmentCoefficient k z (-(n:ℤ))) n
  let B := torusSegmentTransfer k z (-(n:ℤ)) (n+n)
  have hM : 1 < growthBase k := by linarith [growthBase_ge_four k hk]
  have ha : growthBase k^((1-δ)*(n:ℝ)) ≤ ‖A‖ := by
    dsimp only [A]
    rw [← transferProduct_norm_inverse]
    exact hback
  obtain ⟨u,hu,hum,hup⟩ := small_vector_of_cancellation (growthBase k) hM δ hδ A B
    (transferProductInv_area _ _) n ha hfull
  refine ⟨u,hu,?_,?_⟩
  · dsimp only [A] at hum
    rw [← torus_reverse_operator,ContinuousLinearMap.comp_apply,ContinuousLinearMap.comp_apply,norm_planeSwap] at hum
    exact hum
  · have he : B (A u)=torusSegmentTransfer k z 0 n u := by
      dsimp only [A,B]
      rw [torusSegmentTransfer_concat,neg_add_cancel,ContinuousLinearMap.comp_apply]
      simp only [torusSegmentTransfer,transferProduct_inverse]
    rwa [he] at hup
noncomputable def torusSmallEndpoints (k : ℝ) (Np Nm : ℕ) (R : ℝ) (z : Torus) : Prop :=
  ∃ b ∈ Icc (-growthBase k) (growthBase k),
    ‖torusSegmentTransfer k z.swap 0 (Nm-1) ⟨b,1⟩‖ ≤ R ∧
    ‖torusSegmentTransfer k z 0 Np ⟨1,b⟩‖ ≤ R
lemma torusSegmentTransfer_first (k : ℝ) (z : Torus) (n : ℕ) :
    torusSegmentTransfer k z 0 (n+1)=
      (torusSegmentTransfer k (torusStep k z) 0 n).comp (transferStep (torusPotential k z.1)) := by
  rw [show n+1=1+n by omega,torusSegmentTransfer_concat]
  change (torusSegmentTransfer k z 1 n).comp (torusSegmentTransfer k z 0 1)=_
  have hs : torusSegmentTransfer k (torusStep k z) 0 n=torusSegmentTransfer k z 1 n := by
    exact torusSegmentTransfer_shift k z 0 1 n
  rw [hs]
  simp only [torusSegmentTransfer,transferProduct,torusSegmentCoefficient,zero_add,Nat.cast_one,
    sub_self,torusIter_zero,ContinuousLinearMap.comp_id]
lemma torusStep_swap_prev (k : ℝ) (z : Torus) :
    torusStep k z.swap=((torusStep k).symm z).swap := rfl
lemma torusPotential_bound (k : ℝ) (hk : 0 ≤ k) (x : Circle) : |torusPotential k x|+1 ≤ growthBase k := by
  obtain ⟨t,rfl⟩ := Quotient.mk_surjective x
  exact potential_bound k t hk
lemma max_unit_coordinate (u : ℂ) (hu : ‖u‖=1) : 1/2 ≤ max |u.re| |u.im| := by
  have hs : u.re^2+u.im^2=1 := by simpa only [Complex.sq_norm,Complex.normSq_apply,hu,one_pow,pow_two,one_mul] using (Complex.sq_norm u).symm
  by_contra h
  have hr : |u.re| < 1/2 := lt_of_le_of_lt (le_max_left _ _) (lt_of_not_ge h)
  have hi : |u.im| < 1/2 := lt_of_le_of_lt (le_max_right _ _) (lt_of_not_ge h)
  nlinarith [sq_abs u.re,sq_abs u.im,abs_nonneg u.re,abs_nonneg u.im]
lemma normalized_endpoint_norm (A : ℂ →L[ℝ] ℂ) (u : ℂ) (a R : ℝ)
    (ha : 1/2 ≤ |a|) (hR : 0 ≤ R) (h : ‖A u‖ ≤ R) : ‖A (a⁻¹ • u)‖ ≤ 2*R := by
  rw [map_smul,norm_smul,Real.norm_eq_abs,abs_inv]
  have hap : 0 < |a| := by linarith
  have hai : |a|⁻¹ ≤ 2 := (inv_le_iff_one_le_mul₀ hap).mpr (by linarith)
  exact (mul_le_mul_of_nonneg_left h (inv_nonneg.mpr (abs_nonneg a))).trans
    (mul_le_mul_of_nonneg_right hai hR)
lemma torus_small_normalize (k : ℝ) (hk : 0 ≤ k) (n : ℕ) (hn : 1 ≤ n) (R : ℝ) (hR : 0 ≤ R)
    (z : Torus) (u : ℂ) (hu : ‖u‖=1)
    (hm : ‖torusSegmentTransfer k z.swap 0 n (planeSwap u)‖ ≤ R)
    (hp : ‖torusSegmentTransfer k z 0 n u‖ ≤ R) :
    torusSmallEndpoints k n (n+1) (2*R) z ∨
      torusSmallEndpoints k (n+1) n (2*R) ((torusStep k).symm z) := by
  have hM : 1 ≤ growthBase k := by linarith [growthBase_ge_four k hk]
  have hcoord := max_unit_coordinate u hu
  by_cases hdom : |u.im| ≤ |u.re|
  · left
    have hure : 1/2 ≤ |u.re| := by simpa only [max_eq_left hdom] using hcoord
    have hur0 : u.re ≠ 0 := by intro hh; simp [hh] at hure; norm_num at hure
    have hb : |u.im/u.re| ≤ 1 := by rw [abs_div]; exact (div_le_one (by linarith : 0 < |u.re|)).mpr hdom
    refine ⟨u.im/u.re,⟨?_,?_⟩,?_,?_⟩
    · linarith [(abs_le.mp hb).1]
    · linarith [(abs_le.mp hb).2]
    · have he : (u.re⁻¹ : ℝ) • planeSwap u=⟨u.im/u.re,1⟩ := by
        apply Complex.ext <;> simp [div_eq_mul_inv,hur0,mul_comm]
      simpa only [Nat.add_sub_cancel,he] using normalized_endpoint_norm
        (torusSegmentTransfer k z.swap 0 n) (planeSwap u) u.re R hure hR hm
    · have he : (u.re⁻¹ : ℝ) • u=⟨1,u.im/u.re⟩ := by
        apply Complex.ext <;> simp [div_eq_mul_inv,hur0,mul_comm]
      simpa only [he] using normalized_endpoint_norm (torusSegmentTransfer k z 0 n) u u.re R hure hR hp
  · right
    have himdom : |u.re| ≤ |u.im| := le_of_lt (lt_of_not_ge hdom)
    have him : 1/2 ≤ |u.im| := by simpa only [max_eq_right himdom] using hcoord
    have hi0 : u.im ≠ 0 := by intro hh; simp [hh] at him; norm_num at him
    let p := torusPotential k z.2
    let w := transferStepInv p u
    have hwp : torusSegmentTransfer k ((torusStep k).symm z) 0 (n+1) w=torusSegmentTransfer k z 0 n u := by
      rw [torusSegmentTransfer_first,ContinuousLinearMap.comp_apply,Equiv.apply_symm_apply]
      change torusSegmentTransfer k z 0 n (transferStep p (transferStepInv p u))=_
      rw [transferStep_inv]
    have hwm : torusSegmentTransfer k (((torusStep k).symm z).swap) 0 (n-1) (planeSwap w)=
        torusSegmentTransfer k z.swap 0 n (planeSwap u) := by
      conv_rhs => rw [← Nat.sub_add_cancel hn,torusSegmentTransfer_first,ContinuousLinearMap.comp_apply,torusStep_swap_prev]
      congr 1
    have hwre : w.re=u.im := rfl
    have hbr : |w.im/u.im| ≤ growthBase k := by
      have hd : |u.re/u.im| ≤ 1 := by rw [abs_div]; exact (div_le_one (by linarith : 0 < |u.im|)).mpr himdom
      have he : w.im/u.im=p-u.re/u.im := by change (p*u.im-u.re)/u.im=_; field_simp
      rw [he]
      exact (abs_sub _ _).trans ((add_le_add_right hd _).trans (torusPotential_bound k hk z.2))
    refine ⟨w.im/u.im,⟨(abs_le.mp hbr).1,(abs_le.mp hbr).2⟩,?_,?_⟩
    · have he : (u.im⁻¹ : ℝ) • planeSwap w=⟨w.im/u.im,1⟩ := by
        apply Complex.ext <;> simp [hwre,div_eq_mul_inv,hi0,mul_comm]
      have hb := normalized_endpoint_norm (torusSegmentTransfer k (((torusStep k).symm z).swap) 0 (n-1))
        (planeSwap w) u.im R him hR (by rw [hwm]; exact hm)
      simpa only [he] using hb
    · have he : (u.im⁻¹ : ℝ) • w=⟨1,w.im/u.im⟩ := by
        apply Complex.ext <;> simp [hwre,div_eq_mul_inv,hi0,mul_comm]
      have hb := normalized_endpoint_norm (torusSegmentTransfer k ((torusStep k).symm z) 0 (n+1))
        w u.im R him hR (by rw [hwp]; exact hp)
      simpa only [he] using hb
end StandardMapEntropy

end OAI
