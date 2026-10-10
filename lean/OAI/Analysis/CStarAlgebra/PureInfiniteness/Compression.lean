import OAI.Analysis.CStarAlgebra.PureInfiniteness.Nonvanishing

namespace OAI

noncomputable section
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace

namespace MainGap
variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def cutInverseFn (δ t : ℝ) : ℝ := t/(max δ t)^2

lemma continuous_cutInverseFn {δ : ℝ} (hδ : 0 < δ) : Continuous (cutInverseFn δ) := by
  exact continuous_id.div (((continuous_const.max continuous_id).pow 2))
    (fun t => pow_ne_zero _ (ne_of_gt (hδ.trans_le (le_max_left _ _))))

lemma cutInverseFn_zero (δ : ℝ) : cutInverseFn δ 0=0 := by simp [cutInverseFn]

def cutInverse (a : A) (δ : ℝ) : A := cfcₙ (cutInverseFn δ) a

lemma cutInverseFn_bound {δ t : ℝ} (hδ : 0 < δ) (ht : 0 ≤ t) :
    0 ≤ cutInverseFn δ t ∧ cutInverseFn δ t ≤ 1/δ := by
  refine ⟨div_nonneg ht (sq_nonneg _), ?_⟩
  by_cases htδ : t ≤ δ
  · dsimp [cutInverseFn]
    rw [max_eq_left htδ]
    apply (div_le_iff₀ (sq_pos_of_pos hδ)).mpr
    calc
      t ≤ δ := htδ
      _ = 1/δ*δ^2 := by field_simp
  · have htpos : 0 < t := hδ.trans (lt_of_not_ge htδ)
    have he : cutInverseFn δ t=1/t := by
      dsimp [cutInverseFn]
      rw [max_eq_right (le_of_not_ge htδ)]
      field_simp
    rw [he]
    exact one_div_le_one_div_of_le hδ (le_of_not_ge htδ)

lemma norm_cutInverse_le {a : A} (ha : 0 ≤ a) {δ : ℝ} (hδ : 0 < δ) :
    ‖cutInverse a δ‖ ≤ 1/δ := by
  apply norm_cfcₙ_le
  intro t ht
  have hb := cutInverseFn_bound hδ (quasispectrum_nonneg_of_nonneg a ha t ht)
  rw [Real.norm_eq_abs, abs_of_nonneg hb.1]
  exact hb.2

lemma cut_mul_cutInverse {a : A} (ha : 0 ≤ a) {δ : ℝ} (hδ : 0 < δ) :
    cut a δ * (cutInverse a δ * a) = cut a δ := by
  have hc : Continuous (fun t : ℝ => max (t-δ) 0) := by fun_prop
  have h0 : (fun t : ℝ => max (t-δ) 0) 0=0 := by
    simp [max_eq_right (neg_nonpos.mpr hδ.le)]
  have he : cutInverse a δ*a = cfcₙ (fun t : ℝ => cutInverseFn δ t*t) a := by
    simpa only [id_eq, cfcₙ_id' ℝ a ha.isSelfAdjoint, cutInverse] using
      (cfcₙ_mul (cutInverseFn δ) id a (continuous_cutInverseFn hδ).continuousOn
        (cutInverseFn_zero δ) continuousOn_id rfl).symm
  rw [he, cut, ← cfcₙ_mul (fun t : ℝ => max (t-δ) 0)
    (fun t : ℝ => cutInverseFn δ t*t) a hc.continuousOn h0
    ((continuous_cutInverseFn hδ).mul continuous_id).continuousOn (by simp [cutInverseFn_zero])]
  apply cfcₙ_congr
  intro t _
  dsimp only
  by_cases ht : t ≤ δ
  · rw [max_eq_right (sub_nonpos.mpr ht), zero_mul]
  · have ht0 : t ≠ 0 := ne_of_gt (hδ.trans (lt_of_not_ge ht))
    dsimp [cutInverseFn]
    rw [max_eq_right (le_of_not_ge ht)]
    field_simp

lemma Her_right_fixed_cutInverse {a x : A} (ha : 0 ≤ a) {δ : ℝ} (hδ : 0 < δ)
    (hx : x ∈ Her (cut a δ)) : x*(cutInverse a δ*a)=x :=
  Her_fixed_right (cut_nonneg a δ).isSelfAdjoint (cut_mul_cutInverse ha hδ) hx

end MainGap

namespace MainGap
variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def HerCompression (p q c : A) (κ : ℝ) : Prop :=
  ∀ x : A, x ∈ Her p → ∀ k : A, k ∈ Her q → ‖x*c*k‖ ≤ κ * ‖x‖ * ‖k‖

lemma cut_sqrt_lower {d : A} (hd : 0 ≤ d) {δ : ℝ} (hδ : 0 ≤ δ) :
    δ • cut d δ ≤ CFC.sqrt (cut d δ) * d * CFC.sqrt (cut d δ) := by
  let f : ℝ → ℝ := fun t => max (t-δ) 0
  have hf : Continuous f := (continuous_id.sub continuous_const).max continuous_const
  have hf0 : f 0=0 := by simp [f, max_eq_right (neg_nonpos.mpr hδ)]
  have hl : δ • cut d δ ≤ d * cut d δ := by
    change δ • cfcₙ f d ≤ d * cfcₙ f d
    have hu : cfcₙ (fun t => t*f t) d = d*cfcₙ f d := by
      rw [cfcₙ_mul (fun t : ℝ => t) f d continuousOn_id rfl hf.continuousOn hf0]
      exact congrArg (fun x => x*cfcₙ f d) (cfcₙ_id ℝ d hd.isSelfAdjoint)
    rw [← cfcₙ_const_mul δ f d hf.continuousOn hf0, ← hu]
    apply (cfcₙ_le_iff _ _ d (continuous_const.mul hf).continuousOn
      (continuous_id.mul hf).continuousOn (by simp [hf0]) (by simp [hf0]) hd.isSelfAdjoint).mpr
    intro t _
    by_cases ht : δ ≤ t
    · exact mul_le_mul_of_nonneg_right ht (le_max_right _ _)
    · simp [f, max_eq_right (by linarith : t-δ ≤ 0)]
  have hc : Commute (cut d δ) d := (Commute.refl d).cfcₙ_real f
  have hs : Commute (CFC.sqrt (cut d δ)) d := hc.cfcₙ_nnreal NNReal.sqrt
  calc
    δ • cut d δ ≤ d * cut d δ := hl
    _ = CFC.sqrt (cut d δ) * d * CFC.sqrt (cut d δ) := by
      rw [hs.eq, mul_assoc, CFC.sqrt_mul_sqrt_self (cut d δ) (cut_nonneg d δ)]

lemma norm_mul_factor_of_order {m z : A} {r : ℝ} (hr : 0 ≤ r)
    (h : star (m*z) * (m*z) ≤ r^2 • (star z*z)) (b : A) :
    ‖m*(z*b)‖ ≤ r*‖z*b‖ := by
  have ho := star_left_conjugate_le_conjugate h b
  have ht : star (m*(z*b))*(m*(z*b)) ≤ r^2 • (star (z*b)*(z*b)) := by
    simpa only [star_mul, mul_assoc, mul_smul_comm, smul_mul_assoc] using ho
  have hn := CStarAlgebra.norm_le_norm_of_le_of_nonneg ht (star_mul_self_nonneg _)
  rw [CStarRing.norm_star_mul_self, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (sq_nonneg r), CStarRing.norm_star_mul_self] at hn
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hr (norm_nonneg _))).mp
  calc
    ‖m*(z*b)‖^2 = ‖m*(z*b)‖*‖m*(z*b)‖ := pow_two _
    _ ≤ r^2 * (‖z*b‖*‖z*b‖) := hn
    _ = (r*‖z*b‖)^2 := by ring

lemma norm_mul_Her_of_order {m z : A} {r : ℝ} (hr : 0 ≤ r)
    (h : star (m*z) * (m*z) ≤ r^2 • (star z*z))
    {k : A} (hk : k ∈ Her (z*star z)) : ‖m*k‖ ≤ r*‖k‖ := by
  have hc : IsClosed {k : A | ‖m*k‖ ≤ r*‖k‖} := isClosed_le (by fun_prop) (by fun_prop)
  apply closure_minimal (s := Set.range (fun b : A => (z*star z)*b*star (z*star z))) _ hc hk
  rintro k ⟨b, rfl⟩
  change ‖m*((z*star z)*b*star (z*star z))‖ ≤ r*‖(z*star z)*b*star (z*star z)‖
  simpa only [star_mul, star_star, mul_assoc] using
    norm_mul_factor_of_order hr h (star z*b*(z*star z))

end MainGap

namespace MainGap
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma conditional_defect_bounds {p y c : A} (hp : 0 ≤ p) (hy : 0 ≤ y)
    (hpn : ‖p‖ ≤ 1) (hyn : ‖y‖ ≤ 1) (hcn : ‖c‖ ≤ 1) :
    0 ≤ y*(1-star c*(p*p)*c)*y ∧
    y*(1-star c*(p*p)*c)*y ≤ y*y ∧ y*y ≤ 1 := by
  have hm : ‖p*c‖ ≤ 1 := (norm_mul_le _ _).trans (by nlinarith [norm_nonneg p, norm_nonneg c])
  have hm₁ : star (p*c)*(p*c) ≤ 1 := by
    apply (CStarAlgebra.norm_le_one_iff_of_nonneg _ (star_mul_self_nonneg _)).mp
    rw [CStarRing.norm_star_mul_self]
    nlinarith [norm_nonneg (p*c)]
  have he : star (p*c)*(p*c) = star c*(p*p)*c := by
    simp only [star_mul, hp.isSelfAdjoint.star_eq, mul_assoc]
  have hn : 0 ≤ 1-star c*(p*p)*c := sub_nonneg.mpr (he ▸ hm₁)
  have hl : 1-star c*(p*p)*c ≤ 1 := sub_le_self _ (he ▸ star_mul_self_nonneg (p*c))
  refine ⟨?_, ?_, ?_⟩
  · simpa only [hy.isSelfAdjoint.star_eq] using star_left_conjugate_nonneg hn y
  · simpa only [hy.isSelfAdjoint.star_eq, mul_one] using star_left_conjugate_le_conjugate hl y
  · apply (CStarAlgebra.norm_le_one_iff_of_nonneg _ ?_).mp
    · rw [hy.isSelfAdjoint.norm_mul_self]
      nlinarith [norm_nonneg y]
    · simpa only [hy.isSelfAdjoint.star_eq] using star_mul_self_nonneg y

lemma conditional_order_loss {p y c d : A} (hp : 0 ≤ p) (hy : 0 ≤ y)
    (hd : 0 ≤ d) (_hyd : d ≤ y*y) (hy₂ : y*y ≤ 1)
    (he : d=y*(1-star c*(p*p)*c)*y) {δ : ℝ} (hδ : 0 ≤ δ) :
    let z := y*CFC.sqrt (cut d δ)
    star ((p*c)*z)*((p*c)*z) ≤ (1-δ) • (star z*z) := by
  let s := CFC.sqrt (cut d δ)
  let z := y*s
  have hs : IsSelfAdjoint s := (CFC.sqrt_nonneg _).isSelfAdjoint
  have hZ : star z*z ≤ cut d δ := by
    calc
      star z*z = s*(y*y)*s := by
        dsimp [z]
        simp only [star_mul, hs.star_eq, hy.isSelfAdjoint.star_eq, mul_assoc]
      _ ≤ s*1*s := by
        simpa only [hs.star_eq] using star_left_conjugate_le_conjugate hy₂ s
      _ = cut d δ := by
        rw [mul_one]
        exact CFC.sqrt_mul_sqrt_self (cut d δ) (cut_nonneg d δ)
  have hδZ : δ • (star z*z) ≤ s*d*s :=
    (smul_le_smul_of_nonneg_left hZ hδ).trans (cut_sqrt_lower hd hδ)
  have hid : star ((p*c)*z)*((p*c)*z) = star z*z-s*d*s := by
    dsimp [z]
    rw [he]
    simp only [star_mul, hp.isSelfAdjoint.star_eq, hy.isSelfAdjoint.star_eq, hs.star_eq]
    noncomm_ring
  change star ((p*c)*z)*((p*c)*z) ≤ (1-δ) • (star z*z)
  rw [hid, sub_smul, one_smul]
  exact sub_le_sub_left hδZ _

lemma conditional_Her_loss {p y c : A} (hp : 0 ≤ p) (hy : 0 ≤ y)
    (hpn : ‖p‖ ≤ 1) (hyn : ‖y‖ ≤ 1) (hcn : ‖c‖ ≤ 1)
    {δ : ℝ} (hδ : 0 ≤ δ) (hδ₁ : δ ≤ 1) :
    let d := y*(1-star c*(p*p)*c)*y
    let q := y*cut d δ*y
    ∀ k : A, k ∈ Her q → ‖p*c*k‖ ≤ Real.sqrt (1-δ) * ‖k‖ := by
  let d := y*(1-star c*(p*p)*c)*y
  let z := y*CFC.sqrt (cut d δ)
  have hb := conditional_defect_bounds hp hy hpn hyn hcn
  have hh : star ((p*c)*z)*((p*c)*z) ≤ (Real.sqrt (1-δ))^2 • (star z*z) := by
    rw [Real.sq_sqrt (sub_nonneg.mpr hδ₁)]
    exact conditional_order_loss hp hy hb.1 hb.2.1 hb.2.2 rfl hδ
  have hq : z*star z=y*cut d δ*y := by
    dsimp [z]
    simp only [star_mul, hy.isSelfAdjoint.star_eq, (CFC.sqrt_nonneg (cut d δ)).isSelfAdjoint.star_eq]
    calc
      y*CFC.sqrt (cut d δ)*(CFC.sqrt (cut d δ)*y) =
          y*(CFC.sqrt (cut d δ)*CFC.sqrt (cut d δ))*y := by simp only [mul_assoc]
      _ = _ := by rw [CFC.sqrt_mul_sqrt_self (cut d δ) (cut_nonneg d δ)]
  change ∀ k : A, k ∈ Her (y*cut d δ*y) → ‖p*c*k‖ ≤ Real.sqrt (1-δ)*‖k‖
  intro k hk
  exact norm_mul_Her_of_order (Real.sqrt_nonneg _) hh (hq.symm ▸ hk)

end MainGap

namespace MainGap
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma conditional_q_zero {p y c : A} (hp : 0 ≤ p) (hy : 0 ≤ y)
    (hpn : ‖p‖ ≤ 1) (hyn : ‖y‖ ≤ 1) (hcn : ‖c‖ ≤ 1)
    {δ : ℝ} (hδ : 0 < δ)
    (hq : y*cut (y*(1-star c*(p*p)*c)*y) δ*y=0) :
    ‖y*(1-star c*(p*p)*c)*y‖ ≤ δ := by
  let d := y*(1-star c*(p*p)*c)*y
  let h := cut d δ
  let s := CFC.sqrt h
  have hs : IsSelfAdjoint s := (CFC.sqrt_nonneg h).isSelfAdjoint
  have hd := conditional_defect_bounds hp hy hpn hyn hcn
  have hzz : (y*s)*star (y*s) = y*h*y := by
    simp only [star_mul, hs.star_eq, hy.isSelfAdjoint.star_eq]
    calc
      y*s*(s*y)= y*(s*s)*y := by simp only [mul_assoc]
      _ = y*h*y := by rw [show s*s=h from CFC.sqrt_mul_sqrt_self h (cut_nonneg d δ)]
  have hz : y*s=0 := (CStarRing.mul_star_self_eq_zero_iff _).mp (hzz.trans hq)
  have hl : δ • h ≤ 0 := by
    calc
      δ • h ≤ s*d*s := cut_sqrt_lower hd.1 hδ.le
      _ ≤ s*(y*y)*s := by
        simpa only [hs.star_eq] using star_left_conjugate_le_conjugate hd.2.1 s
      _ = star (y*s)*(y*s) := by
        simp only [star_mul, hs.star_eq, hy.isSelfAdjoint.star_eq, mul_assoc]
      _ = 0 := by rw [hz, star_zero, mul_zero]
  have hsm : δ • h=0 := le_antisymm hl (smul_nonneg hδ.le (cut_nonneg d δ))
  have hh : h=0 := (smul_eq_zero.mp hsm).resolve_left (ne_of_gt hδ)
  have hb := norm_sub_cut_le hd.1 hδ.le
  change ‖d-h‖ ≤ δ at hb
  simpa only [hh, sub_zero] using hb

lemma compression_of_conditional_loss {p q c : A} (hp : 0 ≤ p) {τ r : ℝ}
    (hτ : 0 < τ) (_hr : 0 ≤ r)
    (h : ∀ k : A, k ∈ Her q → ‖p*c*k‖ ≤ r*‖k‖) :
    HerCompression (ramp p τ 1) q c (r/τ) := by
  intro x hx k hk
  have hxH : x ∈ Her (cut p τ) :=
    Her_mono_of_mem (ramp_mem_Her_cut hp hτ.le) hx
  have hfix : x*(cutInverse p τ*p)=x := Her_right_fixed_cutInverse hp hτ hxH
  have he : x*c*k = (x*cutInverse p τ)*(p*c*k) := by
    calc
      x*c*k = (x*(cutInverse p τ*p))*c*k := by rw [hfix]
      _ = _ := by simp only [mul_assoc]
  rw [he]
  calc
    ‖(x*cutInverse p τ)*(p*c*k)‖ ≤ ‖x*cutInverse p τ‖*‖p*c*k‖ := norm_mul_le _ _
    _ ≤ (‖x‖*(1/τ))*(r*‖k‖) := by
      apply mul_le_mul
      · exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left (norm_cutInverse_le hp hτ) (norm_nonneg x))
      · exact h k hk
      · exact norm_nonneg _
      · positivity
    _ = (r/τ)*‖x‖*‖k‖ := by ring

end MainGap

end

end OAI
