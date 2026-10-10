import OAI.Analysis.Kaplansky.Main
import OAI.Analysis.Kaplansky.Ultrapower.Quotient
import OAI.Analysis.Kaplansky.Ultrapower.PartialIsometry

namespace OAI

noncomputable section

namespace KaplanskyConsequences.QuasiValue

attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
variable {A : Type*} [CStarAlgebra A] [Nontrivial A] (V : QuasiValue A)

lemma quotQ_partial_final {w : V.FaithfulQuotient} (hw : IsPartialIsometry w) :
    V.quotQ (w*star w)=V.quotQ w := by
  simpa only [star_star,V.quotQ_star] using V.quotQ_partial_projection hw.star_op.initial

lemma quotQ_partial_add {w z : V.FaithfulQuotient}
    (hw : IsPartialIsometry w) (hz : IsPartialIsometry z)
    (hwz : star w*z=0) (hwz' : w*star z=0) :
    V.quotQ (w+z)=V.quotQ w+V.quotQ z := by
  have hzw : star z*w=0 := by simpa only [star_mul,star_star,star_zero] using congrArg star hwz
  have ho : (star w*w)*(star z*z)=0 := by
    calc _ = star w*(w*star z)*z := by noncomm_ring
         _ = 0 := by rw [hwz',mul_zero,zero_mul]
  rw [← V.quotQ_partial_projection (hw.add_orthogonal hz hwz hwz').initial]
  have he : star (w+z)*(w+z)=star w*w+star z*z := by
    simp only [star_add,add_mul,mul_add,hwz,hzw,add_zero,zero_add]
  rw [he,V.quotQ_projection_add hw.initial hz.initial ho,
    V.quotQ_partial_projection hw.initial,V.quotQ_partial_projection hz.initial]

lemma unitary_of_residual_corner_zero {w : V.FaithfulQuotient}
    (hw : IsPartialIsometry w)
    (hcorner : ∀ a : V.FaithfulQuotient, (1-w*star w)*a*(1-star w*w)=0) :
    star w*w=1 ∧ w*star w=1 := by
  let p := 1-star w*w
  let q := 1-w*star w
  have hp : IsStarProjection p := hw.initial.one_sub
  have hq : IsStarProjection q := hw.final.one_sub
  have hs (n : ℕ) : ∃ s : V.FaithfulQuotient, IsStarProjection s ∧
      V.quotQ s=(n:ℝ)*V.quotQ p ∧ ∀ a, q*a*s=0 := by
    induction n with
    | zero => exact ⟨0,IsStarProjection.zero _,by simp,by simp⟩
    | succ n ih =>
      obtain ⟨s,hs,hsize,hann⟩ := ih
      let y := star w*s
      have hqS : q*s=0 := by simpa only [mul_one] using hann 1
      have hyi : star y*y=s := by
        simp only [y,star_mul,star_star,hs.isSelfAdjoint.star_eq]
        calc _ = s*(w*star w)*s := by noncomm_ring
             _ = s*s-s*(q*s) := by dsimp [q]; noncomm_ring
             _ = s := by rw [hs.isIdempotentElem.eq,hqS,mul_zero,sub_zero]
      have hy : IsPartialIsometry y := IsPartialIsometry.of_initial (hyi ▸ hs)
      have hyf : y*star y=star w*s*w := by
        simp only [y,star_mul,star_star,hs.isSelfAdjoint.star_eq]
        calc _ = star w*(s*s)*w := by noncomm_ring
             _ = _ := by rw [hs.isIdempotentElem.eq]
      have hr : IsStarProjection (star w*s*w) := hyf ▸ hy.final
      have hor : p*(star w*s*w)=0 := by
        calc _ = (p*star w)*s*w := by noncomm_ring
             _ = 0 := by rw [show p*star w=0 from hw.initial_compl_mul_star,zero_mul,zero_mul]
      refine ⟨p+star w*s*w,projection_add hp hr hor,?_,?_⟩
      · rw [V.quotQ_projection_add hp hr hor,← hyf,V.quotQ_partial_final hy,
          ← V.quotQ_partial_projection hy.initial,hyi,hsize]
        push_cast
        ring
      · intro a
        calc _ = q*a*p+(q*(a*star w)*s)*w := by noncomm_ring
             _ = 0 := by rw [hcorner a,hann (a*star w),zero_mul,add_zero]
  have hb (n : ℕ) : (n:ℝ)*V.quotQ p≤1 := by
    obtain ⟨s,hs,he,_⟩ := hs n
    have hh := V.quotQ_bound s
    have hn := hs.norm_le
    rw [he] at hh
    nlinarith [norm_nonneg s]
  have hz : V.quotQ p=0 := by
    by_contra hn
    have ht : 0<V.quotQ p := lt_of_le_of_ne (V.quotQ_nonneg p) (Ne.symm hn)
    obtain ⟨n,hn⟩ := exists_nat_gt (1/V.quotQ p)
    have hh : 1<(n:ℝ)*V.quotQ p := (div_lt_iff₀ ht).mp hn
    exact (not_lt_of_ge (hb n)) hh
  have hp0 : p=0 := (V.quotQ_eq_zero p).mp hz
  have hi : star w*w=1 := (sub_eq_zero.mp hp0).symm
  exact ⟨hi,V.faithfulQuotient_finite w hi⟩


end KaplanskyConsequences.QuasiValue

end

end OAI
