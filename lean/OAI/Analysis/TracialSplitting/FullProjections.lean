import OAI.Analysis.TracialSplitting.HereditaryAlgebras

namespace OAI

noncomputable section

universe uA uD

open Filter Topology

namespace Pureness

section

open Filter Topology ComplexStarModule

open scoped ComplexOrder CStarAlgebra

variable {A : Type uA} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

omit [PartialOrder A] [StarOrderedRing A] in
lemma hereditary_complex_smul_mem {h x : A} (z : ℂ) (hx : x ∈ hereditaryCarrier h) :
    z • x ∈ hereditaryCarrier h := by
  obtain ⟨u, hu, ht⟩ := mem_closure_iff_seq_limit.mp hx
  apply isClosed_closure.mem_of_tendsto (ht.const_smul z)
  apply Eventually.of_forall
  intro j
  obtain ⟨w, hw⟩ := hu j
  apply subset_closure
  exact ⟨z • w, by simp only [← hw, mul_smul_comm, smul_mul_assoc]⟩

lemma hereditary_realPart_mem {h x : A} (hh : 0 ≤ h) (hx : x ∈ hereditaryCarrier h) :
    (ℜ x : A) ∈ hereditaryCarrier h := by
  rw [realPart_apply_coe]
  exact (hereditarySubalgebra h hh).smul_mem _
    ((hereditarySubalgebra h hh).add_mem hx (star_mem (s := hereditarySubalgebra h hh) hx))

lemma hereditary_imaginaryPart_mem {h x : A} (hh : 0 ≤ h) (hx : x ∈ hereditaryCarrier h) :
    (ℑ x : A) ∈ hereditaryCarrier h := by
  rw [imaginaryPart_apply_coe]
  apply hereditary_complex_smul_mem
  exact (hereditarySubalgebra h hh).smul_mem _
    ((hereditarySubalgebra h hh).sub_mem hx (star_mem (s := hereditarySubalgebra h hh) hx))

lemma trace_selfAdjoint_im_zero (τ : TracialState A) (x : A) (hx : IsSelfAdjoint x) :
    (τ.functional x).im = 0 := by
  have hp : (τ.functional x⁺).im = 0 :=
    (Complex.nonneg_iff.mp (τ.functional.map_nonneg (CFC.posPart_nonneg x))).2.symm
  have hq : (τ.functional x⁻).im = 0 :=
    (Complex.nonneg_iff.mp (τ.functional.map_nonneg (CFC.negPart_nonneg x))).2.symm
  have he := congrArg (fun a => (τ.functional a).im) (CFC.posPart_sub_negPart x hx)
  simpa only [map_sub, Complex.sub_im, hp, hq, sub_self] using he.symm

lemma trace_zero_selfadjoint_split (τ : TracialState A) (hsimple : TopologicallySimple A)
    (h x : A) (hh : 0 ≤ h) (hx : IsSelfAdjoint x) (hx0 : x ≠ 0)
    (hxm : x ∈ hereditaryCarrier h) (hτ : τ.functional x = 0) :
    ∃ e f : A, 0 ≤ e ∧ e ≠ 0 ∧ e ∈ hereditaryCarrier h ∧
      0 ≤ f ∧ f ≠ 0 ∧ f ∈ hereditaryCarrier h ∧ e * f = 0 := by
  have heq : τ.functional (x⁺) = τ.functional (x⁻) := by
    apply sub_eq_zero.mp
    rw [← map_sub, CFC.posPart_sub_negPart x hx, hτ]
  have hp0 : x⁺ ≠ 0 := by
    intro hp
    have hq := τ.faithful hsimple _ (CFC.negPart_nonneg x) (by rw [← heq, hp, map_zero])
    apply hx0
    rw [← CFC.posPart_sub_negPart x hx, hp, hq, sub_zero]
  have hq0 : x⁻ ≠ 0 := by
    intro hq
    have hp := τ.faithful hsimple _ (CFC.posPart_nonneg x) (by rw [heq, hq, map_zero])
    apply hx0
    rw [← CFC.posPart_sub_negPart x hx, hp, hq, sub_zero]
  refine ⟨x⁺, x⁻, CFC.posPart_nonneg x, hp0, ?_,
    CFC.negPart_nonneg x, hq0, ?_, CFC.posPart_mul_negPart x⟩
  · change x⁺ ∈ hereditarySubalgebra h hh
    rw [CFC.posPart_def]
    exact cfcₙ_mem _ (show x ∈ hereditarySubalgebra h hh from hxm)
  · change x⁻ ∈ hereditarySubalgebra h hh
    rw [CFC.negPart_def]
    exact cfcₙ_mem _ (show x ∈ hereditarySubalgebra h hh from hxm)

theorem exists_orthogonal_pair_hereditary (τ : TracialState A)
    (hsimple : TopologicallySimple A) (hinf : ¬FiniteDimensional ℂ A)
    (h : A) (hh : 0 ≤ h) (hh0 : h ≠ 0) :
    ∃ e f : A, 0 ≤ e ∧ e ≠ 0 ∧ e ∈ hereditaryCarrier h ∧
      0 ≤ f ∧ f ≠ 0 ∧ f ∈ hereditaryCarrier h ∧ e * f = 0 := by
  by_contra hno
  have hτh0 : τ.functional h ≠ 0 := fun hz => hh0 (τ.faithful hsimple h hh hz)
  have hτh : 0 < (τ.functional h).re :=
    (Complex.pos_iff.mp (lt_of_le_of_ne (τ.functional.map_nonneg hh) hτh0.symm)).1
  have hscalar (x : A) (hx : IsSelfAdjoint x) (hxm : x ∈ hereditaryCarrier h) :
      ∃ r : ℝ, x = r • h := by
    let r := (τ.functional x).re / (τ.functional h).re
    have hy : IsSelfAdjoint (x - r • h) := hx.sub ((IsSelfAdjoint.all r).smul hh.isSelfAdjoint)
    have hym : x - r • h ∈ hereditaryCarrier h :=
      (hereditarySubalgebra h hh).sub_mem hxm
        ((hereditarySubalgebra h hh).smul_mem r (self_mem_hereditary h hh))
    have hτy : τ.functional (x - r • h) = 0 := by
      rw [map_sub, τ.functional.map_smul_of_tower]
      apply Complex.ext
      · simp only [Complex.sub_re, Complex.smul_re, Complex.zero_re]
        dsimp [r]
        exact sub_eq_zero.mpr (div_mul_cancel₀ _ (ne_of_gt hτh)).symm
      · simp only [Complex.sub_im, Complex.smul_im, Complex.zero_im,
          trace_selfAdjoint_im_zero τ x hx, trace_selfAdjoint_im_zero τ h hh.isSelfAdjoint,
          smul_zero, sub_zero]
    have hy0 : x - r • h = 0 := by
      by_contra hy0
      exact hno (trace_zero_selfadjoint_split τ hsimple h _ hh hy hy0 hym hτy)
    exact ⟨r, sub_eq_zero.mp hy0⟩
  apply hinf
  apply finiteDimensional_of_scalar_sandwich hsimple h hh hh0
  intro a
  have ham : h * a * h ∈ hereditaryCarrier h := subset_closure ⟨a, rfl⟩
  obtain ⟨r, hr⟩ := hscalar (ℜ (h * a * h)) (ℜ (h * a * h)).2 (hereditary_realPart_mem hh ham)
  obtain ⟨s, hs⟩ := hscalar (ℑ (h * a * h)) (ℑ (h * a * h)).2 (hereditary_imaginaryPart_mem hh ham)
  refine ⟨(r : ℂ) + Complex.I * (s : ℂ), ?_⟩
  rw [← realPart_add_I_smul_imaginaryPart (h * a * h), hr, hs]
  simp only [add_smul, mul_smul, Complex.coe_smul]

end

open scoped ENNReal

variable {A : Type uA} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma exists_orthogonal_family_with_reserve (τ : TracialState A)
    (hsimple : TopologicallySimple A) (hinf : ¬FiniteDimensional ℂ A)
    (h : A) (hh : 0 ≤ h) (hh0 : h ≠ 0) (N : ℕ) :
    ∃ r : A, ∃ a : Fin N → A,
      0 ≤ r ∧ r ≠ 0 ∧ (∀ i, 0 ≤ a i) ∧ (∀ i, a i ≠ 0) ∧
      (∀ i j, i ≠ j → a i * a j = 0) ∧ (∀ i, a i * r = 0) := by
  induction N with
  | zero => exact ⟨h, Fin.elim0, hh, hh0, by simp, by simp, by simp, by simp⟩
  | succ N ih =>
    obtain ⟨r, a, hr, hr0, ha, ha0, horth, har⟩ := ih
    obtain ⟨e, f, he, he0, hem, hf, hf0, hfm, hef⟩ :=
      exists_orthogonal_pair_hereditary τ hsimple hinf r hr hr0
    have hae (i : Fin N) : a i * e = 0 :=
      hereditary_mul_eq_zero (self_mem_hereditary _ (ha i)) hem (har i)
    have hea (i : Fin N) : e * a i = 0 := by
      simpa only [star_mul, he.star_eq, (ha i).star_eq, star_zero] using congrArg star (hae i)
    have haf (i : Fin N) : a i * f = 0 :=
      hereditary_mul_eq_zero (self_mem_hereditary _ (ha i)) hfm (har i)
    refine ⟨f, Fin.cons e a, hf, hf0, ?_, ?_, ?_, ?_⟩
    · intro i
      cases i using Fin.cases with
      | zero => exact he
      | succ i => exact ha i
    · intro i
      cases i using Fin.cases with
      | zero => exact he0
      | succ i => exact ha0 i
    · intro i j hij
      cases i using Fin.cases with
      | zero =>
        cases j using Fin.cases with
        | zero => exact (hij rfl).elim
        | succ j => exact hea j
      | succ i =>
        cases j using Fin.cases with
        | zero => exact hae i
        | succ j => exact horth i j (fun heq => hij (congrArg Fin.succ heq))
    · intro i
      cases i using Fin.cases with
      | zero => exact hef
      | succ i => exact haf i

theorem small_hereditary_rank (hsimple : TopologicallySimple A)
    (hinf : ¬FiniteDimensional ℂ A) (hT : Nonempty (TracialState A))
    (N : ℕ) (hN : 1 ≤ N) :
    ∃ h : A, 0 ≤ h ∧ h ≠ 0 ∧
      ∀ τ : TracialState A, normalizedRootRank τ h ≤ 1 / (N : ℝ≥0∞) := by
  classical
  rcases subsingleton_or_nontrivial A with hsub | hnontriv
  · let := hsub
    exact False.elim (hinf inferInstance)
  · let := hnontriv
    obtain ⟨τ⟩ := hT
    obtain ⟨_, a, _, _, ha, ha0, horth, _⟩ :=
      exists_orthogonal_family_with_reserve τ hsimple hinf 1 zero_le_one one_ne_zero N
    obtain ⟨h, hh, hh0, _, hR⟩ := small_rank_of_orthogonal_family hsimple N hN a ha ha0 horth
    exact ⟨h, hh, hh0, hR⟩

end Pureness

namespace CurrentMain

open Pureness Filter

open scoped Topology NNReal ENNReal ComplexOrder

section SmallFullSupport

variable {A : Type uA} {D : Type uD} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

lemma small_positive (hsimple : TopologicallySimple A) (hinf : ¬FiniteDimensional ℂ A)
    (hT : Nonempty (TracialState A)) (N : ℕ) (hN : 1 ≤ N) :
    ∃ b : A, 0 ≤ b ∧ ‖b‖ = 1 ∧ ∀ τ : TracialState A,
      (τ.functional b).re ≤ 1 / (N : ℝ) := by
  obtain ⟨h,hh,hh0,hr⟩ := small_hereditary_rank hsimple hinf hT N hN
  refine ⟨normalizePositive h,normalizePositive_nonneg h hh,?_,?_⟩
  · simp [normalizePositive,norm_smul,inv_mul_cancel₀ (norm_ne_zero_iff.mpr hh0)]
  · intro τ
    have hb0 : 0 ≤ (τ.functional (normalizePositive h)).re :=
      (τ.functional.map_nonneg (normalizePositive_nonneg h hh)).1
    have hb := (normalized_trace_le_rank τ h hh).trans (hr τ)
    have hN0 : (N : ℝ≥0∞) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
    have ht := ENNReal.toReal_mono (by simp [hN0]) hb
    simpa only [ENNReal.toReal_ofReal hb0,ENNReal.toReal_div,ENNReal.toReal_one,
      ENNReal.toReal_natCast] using ht

omit [PartialOrder A] [StarOrderedRing A] [PartialOrder D] [StarOrderedRing D] in
lemma simple_starAlgHom_injective [Nontrivial D] (hsimple : TopologicallySimple A)
    (ι : A →⋆ₐ[ℂ] D) : Function.Injective ι := by
  have hι : Continuous ι := (ι.toLinearMap.mkContinuous 1 (fun a => by
    change ‖ι a‖ ≤ 1 * ‖a‖
    simpa only [one_mul] using (NonUnitalStarAlgHom.norm_apply_le ι a))).continuous
  have hc : IsClosed (TwoSidedIdeal.ker ι : Set A) := by
    have he : (TwoSidedIdeal.ker ι : Set A) = {a : A | ι a = 0} := by
      ext a; exact TwoSidedIdeal.mem_ker ι
    rw [he]
    exact isClosed_eq hι continuous_const
  rcases hsimple (TwoSidedIdeal.ker ι) hc with hb | ht
  · exact (TwoSidedIdeal.ker_eq_bot ι).mp hb
  · have : (1 : A) ∈ TwoSidedIdeal.ker ι := by rw [ht]; exact Set.mem_univ _
    have hz := (TwoSidedIdeal.mem_ker ι).mp this
    simp at hz

end SmallFullSupport

namespace ClosedSelfAdjointSpan

variable {D : Type uD} [CStarAlgebra D]

lemma span_star_mem {g x : D} (hg : IsSelfAdjoint g)
    (hx : x ∈ TwoSidedIdeal.span {g}) : star x ∈ TwoSidedIdeal.span {g} := by
  induction hx using TwoSidedIdeal.span_induction with
  | mem x hx =>
    rw [Set.mem_singleton_iff.mp hx,hg.star_eq]
    exact TwoSidedIdeal.subset_span (Set.mem_singleton g)
  | zero => simp
  | add x y _ _ hx hy => simpa only [star_add] using (TwoSidedIdeal.span {g}).add_mem hx hy
  | neg x _ hx => simpa only [star_neg] using (TwoSidedIdeal.span {g}).neg_mem hx
  | left_absorb a x _ hx =>
    simpa only [star_mul] using (TwoSidedIdeal.span {g}).mul_mem_right (star x) (star a) hx
  | right_absorb a x _ hx =>
    simpa only [star_mul] using (TwoSidedIdeal.span {g}).mul_mem_left (star a) (star x) hx

def ideal {g : D} (hg : IsSelfAdjoint g) : ClosedStarIdeal D where
  ideal := closedTwoSidedIdeal (TwoSidedIdeal.span {g})
  isClosed := by rw [coe_closedTwoSidedIdeal]; exact isClosed_closure
  star_mem := by
    intro x hx
    rw [← SetLike.mem_coe,coe_closedTwoSidedIdeal] at hx ⊢
    obtain ⟨u,hu,hux⟩ := mem_closure_iff_seq_limit.mp hx
    exact isClosed_closure.mem_of_tendsto hux.star
      (Eventually.of_forall fun n => subset_closure (span_star_mem hg (hu n)))

lemma ideal_coe {g : D} (hg : IsSelfAdjoint g) :
    ((ideal hg).ideal : Set D) = closure (TwoSidedIdeal.span {g} : Set D) :=
  coe_closedTwoSidedIdeal _

lemma quotientMap_g {g : D} (hg : IsSelfAdjoint g) : (ideal hg).quotientMap g = 0 := by
  change (ideal hg).ideal.ringCon.mk' g = (ideal hg).ideal.ringCon.mk' 0
  apply Quotient.sound
  change g ∈ (ideal hg).ideal
  rw [← SetLike.mem_coe,ideal_coe]
  exact subset_closure (TwoSidedIdeal.subset_span (Set.mem_singleton g))

lemma nontrivial_quotient {g : D} (hg : IsSelfAdjoint g) (hfull : ¬IsFull g) :
    Nontrivial (ideal hg).Quotient := by
  apply nontrivial_of_ne (1 : (ideal hg).Quotient) 0
  intro h
  have h1 : (1 : D) ∈ (ideal hg).ideal := by
    have he : (ideal hg).ideal.ringCon.mk' (1 : D) = (ideal hg).ideal.ringCon.mk' 0 := by
      change (ideal hg).quotientMap 1 = (ideal hg).quotientMap 0
      simpa using h
    exact Quotient.exact he
  have htop : (ideal hg).ideal = ⊤ := (TwoSidedIdeal.one_mem_iff _).mp h1
  apply hfull
  unfold IsFull
  rw [← ideal_coe hg,htop,TwoSidedIdeal.coe_top]

end ClosedSelfAdjointSpan

end CurrentMain

end

end OAI
