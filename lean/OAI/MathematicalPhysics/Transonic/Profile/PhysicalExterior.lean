import OAI.MathematicalPhysics.Transonic.Exterior.Continuation
import OAI.MathematicalPhysics.Transonic.Profile.PhysicalProfile

namespace OAI

section
noncomputable section
namespace SepticProfile.PhysicalExterior
open Set

def field (ell beta : ℝ) (p : ℝ×ℝ) : ℝ :=
  profileNumer ell beta p.1 p.2/profileDenom ell p.1 p.2

lemma exterior_factors {q a m y v : ℝ}
    (hq : 1 < q) (ha : 0 < a) (hm : (-1) < m ∧ m < 1)
    (hfirst : 1-q*a+(q-a)*m < 0) (hsecond : 0 < 1+q*a-(a+q)*m)
    (hy : a ≤ y) (hv : (-1) ≤ v ∧ v ≤ m) :
    1-q*y+(q-y)*v < 0 ∧ 0 < 1+q*y-(y+q)*v := by
  have hyp : 0 < y := ha.trans_le hy
  have hqm : 0 < q+m := by linarith
  constructor
  · by_cases hle : y ≤ q
    · have hvm := mul_le_mul_of_nonneg_left hv.2 (sub_nonneg.mpr hle)
      have ht := mul_nonneg (sub_nonneg.mpr hy) hqm.le
      nlinarith
    · have hh := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (le_of_not_ge hle))
        (by linarith [hv.1] : 0 ≤ v+1)
      have hp := mul_pos (by linarith : 0 < q-1) (by linarith : 0 < 1+y)
      nlinarith
  · have hvm := mul_le_mul_of_nonneg_left hv.2 (by linarith : 0 ≤ y+q)
    have ht := mul_nonneg (sub_nonneg.mpr hy) (by linarith : 0 ≤ q-m)
    nlinarith

lemma denominator_neg {q a m y v : ℝ}
    (hq : 1 < q) (ha : 0 < a) (hm : (-1) < m ∧ m < 1)
    (hfirst : 1-q*a+(q-a)*m < 0) (hsecond : 0 < 1+q*a-(a+q)*m)
    (hy : a ≤ y) (hv : (-1) ≤ v ∧ v ≤ m) :
    profileDenom (q^2) y v < 0 := by
  have hh := exterior_factors hq ha hm hfirst hsecond hy hv
  have he : profileDenom (q^2) y v=
      y*((1-q*y+(q-y)*v)*(1+q*y-(y+q)*v)) := by
    unfold profileDenom;ring
  rw [he]
  exact mul_neg_of_pos_of_neg (ha.trans_le hy) (mul_neg_of_neg_of_pos hh.1 hh.2)

lemma numerator_pos_upper {ell beta a m y : ℝ} (hell : 0 < ell) (hbeta : 0 < beta)
    (hm : (-1) < m ∧ m < 1)
    (hcrit : 0 < beta*ell*(1-m^2)*a-3*m*(1-a*m)) (hy : a ≤ y) :
    0 < profileNumer ell beta y m := by
  have hs : 0 < 1-m^2 := by nlinarith
  have hp : 0 < beta*ell*(1-m^2)+3*m^2 := by
    nlinarith [mul_pos (mul_pos hbeta hell) hs,sq_nonneg m]
  have ht := mul_nonneg (sub_nonneg.mpr hy) hp.le
  unfold profileNumer
  apply mul_pos hs
  nlinarith

lemma field_smooth_on {q beta a b m : ℝ}
    (hq : 1 < q) (ha : 0 < a) (hm : (-1) < m ∧ m < 1)
    (hfirst : 1-q*a+(q-a)*m < 0) (hsecond : 0 < 1+q*a-(a+q)*m) :
    ContDiffOn ℝ 1 (field (q^2) beta) (Icc a b ×ˢ Icc ((-1)) m) := by
  intro p hp
  apply ContDiffAt.contDiffWithinAt
  have hn : profileDenom (q^2) p.1 p.2≠0 :=
    ne_of_lt (denominator_neg hq ha hm hfirst hsecond hp.1.1 hp.2)
  unfold field profileNumer profileDenom at *
  fun_prop

lemma finite_continuation {q beta a b m v0 : ℝ}
    (hq : 1 < q) (hbeta : 0 < beta) (ha : 0 < a) (hab : a ≤ b)
    (hm : (-1) < m ∧ m < 1)
    (hfirst : 1-q*a+(q-a)*m < 0) (hsecond : 0 < 1+q*a-(a+q)*m)
    (hcrit : 0 < beta*q^2*(1-m^2)*a-3*m*(1-a*m))
    (hstart : (-1) < v0 ∧ v0 ≤ m) :
    ∃ v : ℝ → ℝ, v a=v0 ∧ ContinuousOn v (Icc a b) ∧
      (∀ y∈Icc a b, (-1) < v y ∧ v y ≤ m) ∧
      ∀ y∈Icc a b, HasDerivWithinAt v (field (q^2) beta (y,v y)) (Icc a b) y := by
  let f : ℝ×ℝ → ℝ := fun p => -field (q^2) beta (p.1,-p.2)
  have hf : ContDiffOn ℝ 1 f (Icc a b ×ˢ Icc (-m) 1) := by
    apply ContDiffOn.neg
    apply (field_smooth_on hq ha hm hfirst hsecond).comp
      (contDiffOn_fst.prodMk contDiffOn_snd.neg)
    intro p hp
    exact ⟨hp.1,⟨by linarith [hp.2.2],by linarith [hp.2.1]⟩⟩
  have hl : ∀ y∈Icc a b, 0 < f (y,-m) := by
    intro y hy
    dsimp [f,field]
    rw [neg_neg]
    have hn := numerator_pos_upper (sq_pos_of_pos (by linarith : 0 < q)) hbeta hm hcrit hy.1
    have hd := denominator_neg hq ha hm hfirst hsecond hy.1 ⟨hm.1.le,le_rfl⟩
    exact neg_pos.mpr (div_neg_of_pos_of_neg hn hd)
  have heq : ∀ y∈Icc a b, f (y,1)=0 := by
    intro y hy
    simp [f,field,profileNumer]
  obtain ⟨u,hu,huc,hbound,hder⟩ := RegularContinuation.exists_between_lower_equilibrium hab
    (by linarith : -m ≤ 1) hf (fun _ => -m) (fun _ => 0)
    (fun y _ => hasDerivAt_const y (-m))
    (fun y _ => ⟨le_rfl,by linarith⟩) hl heq
    (show -m ≤ -v0 by linarith [hstart.2]) (show -v0 < 1 by linarith [hstart.1])
  refine ⟨fun y => -u y,?_,huc.neg,?_,?_⟩
  · dsimp; rw [hu,neg_neg]
  · intro y hy
    have h := hbound y hy
    constructor <;> dsimp <;> linarith
  · intro y hy
    convert (hder y hy).neg using 1 ; first | rfl | simp [f]

end SepticProfile.PhysicalExterior

end
end

end OAI
