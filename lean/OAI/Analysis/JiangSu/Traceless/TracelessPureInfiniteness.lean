import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.Comparison.CuntzBasic
import OAI.Analysis.JiangSu.Nonunital.Hereditary

namespace OAI

section

noncomputable section
open Filter Topology Pureness

namespace CurrentMain.Traceless
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def sandwichSubalgebra (b : A) (hb : IsSelfAdjoint b) : NonUnitalStarSubalgebra ℂ A where
  carrier := Set.range fun a : A => b * a * b
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩; exact ⟨x + y, by simp [mul_add, add_mul]⟩
  mul_mem' := by
    rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
    exact ⟨x * b * b * y, by simp only [mul_assoc]⟩
  smul_mem' := by rintro z _ ⟨x, rfl⟩; exact ⟨z • x, by simp⟩
  star_mem' := by rintro _ ⟨x, rfl⟩; exact ⟨star x, by simp [hb.star_eq, mul_assoc]⟩

noncomputable def hereditaryCorner (b : A) (hb : 0 ≤ b) : NonUnitalStarSubalgebra ℂ A :=
  (sandwichSubalgebra b hb.isSelfAdjoint).topologicalClosure

@[simp] theorem coe_hereditaryCorner (b : A) (hb : 0 ≤ b) :
    (hereditaryCorner b hb : Set A) = closure (Set.range fun a : A => b * a * b) := rfl

theorem self_mem_hereditaryCorner (b : A) (hb : 0 ≤ b) : b ∈ hereditaryCorner b hb :=
  Pureness.self_mem_hereditary b hb

theorem sqrt_mem_hereditaryCorner (b : A) (hb : 0 ≤ b) :
    CFC.sqrt b ∈ hereditaryCorner b hb :=
  Pureness.hereditary_sqrt_mem hb hb (Pureness.self_mem_hereditary b hb)

theorem hereditaryCorner_sandwich (b : A) (hb : 0 ≤ b) {x y : A}
    (hx : x ∈ hereditaryCorner b hb) (hy : y ∈ hereditaryCorner b hb) (a : A) :
    x * a * y ∈ hereditaryCorner b hb := by
  obtain ⟨u, hu, hut⟩ := mem_closure_iff_seq_limit.mp hx
  obtain ⟨v, hv, hvt⟩ := mem_closure_iff_seq_limit.mp hy
  apply mem_closure_of_tendsto ((hut.mul_const a).mul hvt)
  apply Eventually.of_forall
  intro n
  obtain ⟨c, hc⟩ := hu n
  obtain ⟨d, hd⟩ := hv n
  exact ⟨c * b * a * b * d, by rw [← hc, ← hd]; simp only [mul_assoc]⟩

theorem sqrt_sandwich_mem_hereditaryCorner (b : A) (hb : 0 ≤ b) (a : A) :
    CFC.sqrt b * a * CFC.sqrt b ∈ hereditaryCorner b hb :=
  hereditaryCorner_sandwich b hb (sqrt_mem_hereditaryCorner b hb)
    (sqrt_mem_hereditaryCorner b hb) a

theorem hereditaryCorner_le_of_mem {b c : A} (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hcb : c ∈ hereditaryCorner b hb) :
    hereditaryCorner c hc ≤ hereditaryCorner b hb := by
  apply closure_minimal
  · rintro _ ⟨a, rfl⟩
    exact hereditaryCorner_sandwich b hb hcb hcb a
  · exact isClosed_closure

theorem hereditaryCorner_mul_eq_zero {b c x : A} (hb : 0 ≤ b)
    (hbc : b * c = 0) (hx : x ∈ hereditaryCorner b hb) : x * c = 0 := by
  obtain ⟨u, hu, hut⟩ := mem_closure_iff_seq_limit.mp hx
  have hz : ∀ n, u n * c = 0 := by
    intro n
    obtain ⟨a, ha⟩ := hu n
    rw [← ha]
    change b * a * b * c = 0
    rw [mul_assoc, hbc, mul_zero]
  exact tendsto_nhds_unique (hut.mul_const c)
    (by simpa only [hz] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : A)) atTop (𝓝 0)))

lemma cfc_mem_hereditaryCorner {b : A} (hb : 0 ≤ b) (f : ℝ → ℝ)
    (hf : Continuous f) (hf0 : f 0 = 0) :
    cfc f b ∈ hereditaryCorner b hb := by
  let : IsClosed (hereditaryCorner b hb : Set A) := isClosed_closure
  rw [← cfcₙ_eq_cfc hf.continuousOn hf0]
  exact cfcₙ_mem f (self_mem_hereditaryCorner b hb)

theorem orthogonal_pair_of_positive_spectral_values {b : A} (hb : 0 ≤ b)
    {s t : ℝ} (hs : s ∈ spectrum ℝ b) (ht : t ∈ spectrum ℝ b)
    (hs0 : 0 < s) (hst : s < t) :
    ∃ c d : A, 0 ≤ c ∧ 0 ≤ d ∧ c ≠ 0 ∧ d ≠ 0 ∧ c * d = 0 ∧
      c ∈ hereditaryCorner b hb ∧ d ∈ hereditaryCorner b hb := by
  let m := (s + t) / 2
  have hsm : s < m := left_lt_add_div_two.mpr hst
  have hmt : m < t := add_div_two_lt_right.mpr hst
  have hm : 0 < m := hs0.trans hsm
  let f : ℝ → ℝ := fun x => x * max (m - x) 0
  let g : ℝ → ℝ := fun x => max (x - m) 0
  have hf : Continuous f := by dsimp [f]; fun_prop
  have hg : Continuous g := by dsimp [g]; fun_prop
  have hf0 : f 0 = 0 := by simp [f]
  have hg0 : g 0 = 0 := by simp [g, hm.le]
  have hfg : ∀ x : ℝ, f x * g x = 0 := by
    intro x
    by_cases hx : x ≤ m
    · simp [f, g, max_eq_right (sub_nonpos.mpr hx)]
    · simp [f, g, max_eq_right (sub_nonpos.mpr (le_of_not_ge hx))]
  have hsa := hb.isSelfAdjoint
  refine ⟨cfc f b, cfc g b, ?_, ?_, ?_, ?_, ?_,
    cfc_mem_hereditaryCorner hb f hf hf0, cfc_mem_hereditaryCorner hb g hg hg0⟩
  · apply cfc_nonneg
    intro x hx
    exact mul_nonneg (spectrum_nonneg_of_nonneg hb hx) (le_max_right _ _)
  · apply cfc_nonneg
    intro x hx
    exact le_max_right _ _
  · intro hz
    have heq : cfc f b = cfc (fun _ : ℝ => 0) b := by simpa using hz
    have h := eqOn_of_cfc_eq_cfc heq hf.continuousOn continuousOn_const hsa hs
    have hp : 0 < f s := by
      dsimp [f]
      rw [max_eq_left (sub_nonneg.mpr hsm.le)]
      exact mul_pos hs0 (sub_pos.mpr hsm)
    exact (ne_of_gt hp) h
  · intro hz
    have heq : cfc g b = cfc (fun _ : ℝ => 0) b := by simpa using hz
    have h := eqOn_of_cfc_eq_cfc heq hg.continuousOn continuousOn_const hsa ht
    have hp : 0 < g t := by
      dsimp [g]
      rw [max_eq_left (sub_nonneg.mpr hmt.le)]
      exact sub_pos.mpr hmt
    exact (ne_of_gt hp) h
  · rw [← cfc_mul f g b hf.continuousOn hg.continuousOn]
    simp only [hfg, cfc_const_zero]

theorem positive_scalar_projection_or_orthogonal_pair {b : A}
    (hb : 0 ≤ b) (hbn : b ≠ 0) :
    (∃ r : ℝ, 0 < r ∧ ∃ q : A, IsStarProjection q ∧ q ≠ 0 ∧
      q ∈ hereditaryCorner b hb ∧ b = r • q) ∨
    (∃ c d : A, 0 ≤ c ∧ 0 ≤ d ∧ c ≠ 0 ∧ d ≠ 0 ∧ c * d = 0 ∧
      c ∈ hereditaryCorner b hb ∧ d ∈ hereditaryCorner b hb) := by
  classical
  have hsa := hb.isSelfAdjoint
  have hex : ∃ r ∈ spectrum ℝ b, 0 < r := by
    by_contra hn
    push Not at hn
    apply hbn
    apply CFC.eq_zero_of_spectrum_subset_zero (R := ℝ) b
    intro x hx
    exact le_antisymm (hn x hx) (spectrum_nonneg_of_nonneg hb hx)
  obtain ⟨r, hr, hr0⟩ := hex
  by_cases hs : ∀ x ∈ spectrum ℝ b, x = 0 ∨ x = r
  · left
    have hb2 : b * b = r • b := by
      rw [← cfc_id' ℝ b, ← cfc_mul (fun x : ℝ => x) (fun x => x) b,
        ← cfc_smul r (fun x : ℝ => x) b]
      apply cfc_congr
      intro x hx
      rcases hs x hx with h | h <;> simp [h]
    let q : A := r⁻¹ • b
    have hq2 : q * q = q := by
      dsimp [q]
      rw [smul_mul_smul_comm, hb2, smul_smul]
      congr 1
      field_simp
    have hq : IsStarProjection q :=
      ⟨hq2, by change star q = q; simp [q, hb.star_eq]⟩
    have hfactor : b = r • q := by simp [q, smul_smul, hr0.ne']
    refine ⟨r, hr0, q, hq, ?_, ?_, hfactor⟩
    · intro hz
      rw [hz, smul_zero] at hfactor
      exact hbn hfactor
    · exact (hereditaryCorner b hb).smul_mem (r⁻¹ : ℝ) (self_mem_hereditaryCorner b hb)
  · push Not at hs
    obtain ⟨x, hx, hx0, hxr⟩ := hs
    have hxpos := lt_of_le_of_ne (spectrum_nonneg_of_nonneg hb hx) (Ne.symm hx0)
    right
    rcases lt_or_gt_of_ne hxr with h | h
    · exact orthogonal_pair_of_positive_spectral_values hb hx hr hxpos h
    · exact orthogonal_pair_of_positive_spectral_values hb hr hx hr0 h
open scoped ComplexStarModule
open Complex

lemma hereditary_projection_right_identity {q x : A} (hq : IsStarProjection q)
    (hx : x ∈ hereditaryCorner q hq.nonneg) : x * q = x := by
  have hz := hereditaryCorner_mul_eq_zero hq.nonneg
    (c := 1 - q) (by rw [mul_sub, mul_one, hq.isIdempotentElem.eq, sub_self]) hx
  rw [mul_sub, mul_one] at hz
  exact (sub_eq_zero.mp hz).symm

lemma scalar_of_no_orthogonal_pair {q : A} (hq : IsStarProjection q)
    (hno : ∀ c d : A, 0 ≤ c → 0 ≤ d → c ∈ hereditaryCorner q hq.nonneg →
      d ∈ hereditaryCorner q hq.nonneg → c * d = 0 → c = 0 ∨ d = 0)
    {b : A} (hb : 0 ≤ b) (hmem : b ∈ hereditaryCorner q hq.nonneg) :
    ∃ z : ℂ, b = z • q := by
  by_cases hbn : b = 0
  · exact ⟨0, by simp [hbn]⟩
  rcases positive_scalar_projection_or_orthogonal_pair hb hbn with h | h
  · obtain ⟨r, hr, p, hp, hpn, hpm, hfactor⟩ := h
    have hpqmem := hereditaryCorner_le_of_mem hq.nonneg hb hmem hpm
    have hpq := hereditary_projection_right_identity hq hpqmem
    have hdiff := hp.sub_of_mul_eq_left hq hpq
    have hz : p * (q - p) = 0 := by
      rw [mul_sub, hpq, hp.isIdempotentElem.eq, sub_self]
    have heq := hno p (q - p) hp.nonneg hdiff.nonneg hpqmem
      ((hereditaryCorner q hq.nonneg).sub_mem (self_mem_hereditaryCorner q hq.nonneg) hpqmem) hz
    have hpqeq : p = q := by
      rcases heq with h | h
      · exact (hpn h).elim
      · exact (sub_eq_zero.mp h).symm
    refine ⟨(r : ℂ), ?_⟩
    simpa only [hpqeq, Complex.coe_smul] using hfactor
  · obtain ⟨c, d, hc, hd, hcn, hdn, hcd, hcm, hdm⟩ := h
    exact ((hno c d hc hd (hereditaryCorner_le_of_mem hq.nonneg hb hmem hcm)
      (hereditaryCorner_le_of_mem hq.nonneg hb hmem hdm) hcd).elim hcn hdn).elim

lemma scalar_sandwich_of_positive_sandwich {q : A} (_hq : IsStarProjection q)
    (hpos : ∀ b : A, 0 ≤ b → ∃ z : ℂ, q * b * q = z • q) :
    ∀ a : A, ∃ z : ℂ, q * a * q = z • q := by
  have hself : ∀ a : A, IsSelfAdjoint a → ∃ z : ℂ, q * a * q = z • q := by
    intro a ha
    obtain ⟨z, hz⟩ := hpos a⁺ (CFC.posPart_nonneg a)
    obtain ⟨w, hw⟩ := hpos a⁻ (CFC.negPart_nonneg a)
    refine ⟨z - w, ?_⟩
    conv_lhs => rw [← CFC.posPart_sub_negPart a ha]
    rw [mul_sub, sub_mul, hz, hw, sub_smul]
  intro a
  obtain ⟨z, hz⟩ := hself (ℜ a) (ℜ a).property
  obtain ⟨w, hw⟩ := hself (ℑ a) (ℑ a).property
  refine ⟨z + I * w, ?_⟩
  conv_lhs => rw [← realPart_add_I_smul_imaginaryPart a]
  rw [mul_add, add_mul, mul_smul_comm, smul_mul_assoc, hz, hw, smul_smul, add_smul]

theorem exists_orthogonal_positive_pair (hsimple : TopologicallySimple A)
    (hinfinite : ¬ FiniteDimensional ℂ A) {b : A} (hb : 0 ≤ b) (hbn : b ≠ 0) :
    ∃ c d : A, 0 ≤ c ∧ 0 ≤ d ∧ c ≠ 0 ∧ d ≠ 0 ∧ c * d = 0 ∧
      c ∈ hereditaryCorner b hb ∧ d ∈ hereditaryCorner b hb := by
  classical
  by_contra hno
  have hnopair : ∀ c d : A, 0 ≤ c → 0 ≤ d →
      c ∈ hereditaryCorner b hb → d ∈ hereditaryCorner b hb →
      c * d = 0 → c = 0 ∨ d = 0 := by
    intro c d hc hd hcm hdm hcd
    by_contra h
    push Not at h
    exact hno ⟨c, d, hc, hd, h.1, h.2, hcd, hcm, hdm⟩
  rcases positive_scalar_projection_or_orthogonal_pair hb hbn with h | h
  · obtain ⟨r, hr, q, hq, hqn, hqm, hfactor⟩ := h
    have hle := hereditaryCorner_le_of_mem hb hq.nonneg hqm
    apply hinfinite
    apply Pureness.finiteDimensional_of_scalar_sandwich hsimple q hq.nonneg hqn
    apply scalar_sandwich_of_positive_sandwich hq
    intro a ha
    apply scalar_of_no_orthogonal_pair hq
    · intro c d hc hd hcm hdm hcd
      exact hnopair c d hc hd (hle hcm) (hle hdm) hcd
    · simpa only [hq.isSelfAdjoint.star_eq] using star_left_conjugate_nonneg ha q
    · exact subset_closure ⟨a, rfl⟩
  · exact hno h

theorem exists_hereditary_isometry_range {b : A} (hb : 0 ≤ b)
    (hcomp : CuntzSubequiv 1 b) :
    ∃ w : A, star w * w = 1 ∧ IsStarProjection (w * star w) ∧
      w * star w ∈ hereditaryCorner b hb := by
  obtain ⟨x, hx⟩ := (cuntzSubequiv_iff_norm 1 b).mp hcomp 1 zero_lt_one
  let t := star x * b * x
  have ht : 0 ≤ t := star_left_conjugate_nonneg hb x
  have htu : IsUnit t := by
    have hnorm : ‖1-t‖ < 1 := hx
    have h := (Units.oneSub (1-t) hnorm).isUnit
    change IsUnit (1-(1-t)) at h
    simpa only [sub_sub_cancel] using h
  have htp : IsStrictlyPositive t := IsStrictlyPositive.iff_of_unital.mpr ⟨ht,htu⟩
  let z := CFC.rpow t (-(1/2) : ℝ)
  have hz : IsSelfAdjoint z := .of_nonneg CFC.rpow_nonneg
  have hs : IsSelfAdjoint (CFC.sqrt b) := .of_nonneg (CFC.sqrt_nonneg b)
  have hztz : z*t*z = 1 := CFC.conjugate_rpow_neg_one_half t htp
  let w := CFC.sqrt b * x * z
  have hw : star w*w = 1 := by
    change star (CFC.sqrt b*x*z)*(CFC.sqrt b*x*z) = 1
    simp only [star_mul,hz.star_eq,hs.star_eq]
    calc
      _ = z * (star x * (CFC.sqrt b * CFC.sqrt b) * x) * z := by noncomm_ring
      _ = 1 := by rw [CFC.sqrt_mul_sqrt_self b hb]; exact hztz
  have hp : IsStarProjection (w*star w) := by
    refine ⟨?_,?_⟩
    · change w*star w*(w*star w) = w*star w
      calc
        _ = w*(star w*w)*star w := by noncomm_ring
        _ = _ := by rw [hw]; simp
    · simp only [IsSelfAdjoint,star_mul,star_star]
  refine ⟨w,hw,hp,?_⟩
  have he : w*star w = CFC.sqrt b*(x*(z*z)*star x)*CFC.sqrt b := by
    simp only [w,star_mul,hz.star_eq,hs.star_eq,mul_assoc]
  rw [he]
  exact sqrt_sandwich_mem_hereditaryCorner b hb _

def IsInfiniteProjection (p : A) : Prop :=
  IsStarProjection p ∧ ∃ v : A, p*v = v ∧ v*p = v ∧
    star v*v = p ∧ v*star v ≤ p ∧ v*star v ≠ p

theorem isInfiniteProjection_of_isometry {w v : A}
    (hw : star w*w = 1) (hv : star v*v = 1) (hvproper : v*star v ≠ 1) :
    IsInfiniteProjection (w*star w) := by
  let p := w*star w
  let t := w*v*star w
  have hp : IsStarProjection p := by
    refine ⟨?_,?_⟩
    · change w*star w*(w*star w) = w*star w
      calc
        _ = w*(star w*w)*star w := by noncomm_ring
        _ = _ := by rw [hw]; simp
    · simp only [p,IsSelfAdjoint,star_mul,star_star]
  have hpt : p*t = t := by
    calc
      _ = w*(star w*w)*v*star w := by dsimp [p,t]; noncomm_ring
      _ = _ := by rw [hw]; simp [t]
  have htp : t*p = t := by
    calc
      _ = w*v*(star w*w)*star w := by dsimp [p,t]; noncomm_ring
      _ = _ := by rw [hw]; simp [t]
  have htt : star t*t = p := by
    simp only [t,star_mul,star_star]
    calc
      _ = w*star v*(star w*w)*v*star w := by noncomm_ring
      _ = w*(star v*v)*star w := by rw [hw]; noncomm_ring
      _ = p := by rw [hv]; simp [p]
  have htproj : IsStarProjection (t*star t) := by
    refine ⟨?_,?_⟩
    · change t*star t*(t*star t) = t*star t
      calc
        _ = t*(star t*t)*star t := by noncomm_ring
        _ = _ := by rw [htt,htp]
    · simp only [IsSelfAdjoint,star_mul,star_star]
  have hle : t*star t ≤ p := by
    apply (htproj.le_iff_mul_eq_right hp).mpr
    rw [← mul_assoc,hpt]
  refine ⟨hp,t,hpt,htp,htt,hle,?_⟩
  intro he
  apply hvproper
  have he' := congrArg (fun a : A => star w*a*w) he
  have hl : star w*(t*star t)*w = v*star v := by
    simp only [t,star_mul,star_star]
    calc
      _ = (star w*w)*v*(star w*w)*star v*(star w*w) := by noncomm_ring
      _ = _ := by rw [hw]; simp
  have hr : star w*p*w = 1 := by
    calc
      _ = (star w*w)*(star w*w) := by dsimp [p]; noncomm_ring
      _ = _ := by rw [hw]; simp
  exact hl.symm.trans (he'.trans hr)

theorem infinite_projection_in_every_hereditary [Nontrivial A]
    (hsimple : TopologicallySimple A) (hinf : ¬FiniteDimensional ℂ A)
    (hcomparison : ∀ b : A, 0 ≤ b → b ≠ 0 → CuntzSubequiv 1 b)
    (h : A) (hh : 0 ≤ h) (hh0 : h ≠ 0) :
    ∃ p : A, p ∈ hereditaryCorner h hh ∧ IsInfiniteProjection p := by
  obtain ⟨b,c,hb,_hc,hb0,hc0,hbc,_hbm,_hcm⟩ :=
    exists_orthogonal_positive_pair hsimple hinf (show (0:A) ≤ 1 by positivity) one_ne_zero
  obtain ⟨v,hv,_hp,hvm⟩ := exists_hereditary_isometry_range hb (hcomparison b hb hb0)
  have hvproper : v*star v ≠ 1 := by
    intro he
    have hz := hereditaryCorner_mul_eq_zero hb hbc hvm
    rw [he,one_mul] at hz
    exact hc0 hz
  obtain ⟨w,hw,_hp,hwm⟩ := exists_hereditary_isometry_range hh (hcomparison h hh hh0)
  exact ⟨w*star w,hwm,isInfiniteProjection_of_isometry hw hv hvproper⟩

end CurrentMain.Traceless

end
end

end OAI
