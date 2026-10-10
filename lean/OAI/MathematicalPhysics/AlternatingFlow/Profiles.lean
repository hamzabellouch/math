import OAI.MathematicalPhysics.AlternatingFlow.Encoding

namespace OAI

open scoped BigOperators ENNReal NNReal Topology ContDiff
open MeasureTheory
namespace AlternatingNS
namespace Profiles

noncomputable def clock (t : ℝ) : ℝ :=
  letI := twoAtLeastTwo
  Real.smoothTransition (2 * t - 1 / 2)

lemma clock_smooth : ContDiff ℝ ∞ clock := by
  unfold clock
  fun_prop

lemma clock_mem (t : ℝ) : clock t ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

lemma clock_zero (t : ℝ) (ht : t ≤ 1 / 4) : clock t = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  linarith

lemma clock_one (t : ℝ) (ht : 3 / 4 ≤ t) : clock t = 1 := by
  apply Real.smoothTransition.one_of_one_le
  linarith

lemma clock_monotone : Monotone clock := by
  intro a b hab
  apply Real.smoothTransition.monotone
  linarith

noncomputable def periodizer (a c x : ℝ) : ℝ :=
  Int.fract x - Real.smoothTransition ((Int.fract x - a) / (c - a))

lemma periodizer_periodic (a c : ℝ) : Function.Periodic (periodizer a c) 1 := by
  intro x
  simp only [periodizer, Int.fract_add_one]

lemma periodizer_int_add (a c : ℝ) (k : ℤ) (x : ℝ) :
    periodizer a c ((k : ℝ) + x) = periodizer a c x := by
  simp only [periodizer, Int.fract_intCast_add]

lemma periodizer_self (a c x : ℝ) (hac : a < c) (ha : a < 1)
    (hx : x ∈ Set.Icc 0 a) : periodizer a c x = x := by
  have hf : Int.fract x = x := Int.fract_eq_self.2 ⟨hx.1, hx.2.trans_lt ha⟩
  rw [periodizer, hf, Real.smoothTransition.zero_of_nonpos]
  · ring
  · exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hx.2) (sub_pos.mpr hac).le

lemma periodizer_near_zero (a c : ℝ) (ha : 0 < a) (hac : a < c) (hc : c < 1)
    (x : ℝ) (hx : x ∈ Set.Ioo (c - 1) a) : periodizer a c x = x := by
  by_cases hx0 : 0 ≤ x
  · exact periodizer_self a c x hac (hac.trans hc) ⟨hx0, hx.2.le⟩
  · have hn : ⌊x⌋ = (-1 : ℤ) := Int.floor_eq_iff.2 (by norm_num; constructor <;> linarith [hx.1])
    have hf : Int.fract x = x + 1 := by rw [Int.fract, hn]; norm_num
    have hh : 1 ≤ (x + 1 - a) / (c - a) :=
      (le_div_iff₀ (sub_pos.mpr hac)).2 (by linarith [hx.1])
    rw [periodizer, hf, Real.smoothTransition.one_of_one_le hh]
    ring

lemma periodizer_smooth (a c : ℝ) (ha : 0 < a) (hac : a < c) (hc : c < 1) :
    ContDiff ℝ ∞ (periodizer a c) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x = (⌊x⌋ : ℝ)
  · have hg : ContDiff ℝ ∞ (fun y : ℝ => y - (⌊x⌋ : ℝ)) := by fun_prop
    apply hg.contDiffAt.congr_of_eventuallyEq
    have hlo : (⌊x⌋ : ℝ) + (c - 1) < x := by linarith
    have hhi : x < (⌊x⌋ : ℝ) + a := by linarith
    filter_upwards [Ioo_mem_nhds hlo hhi] with y hy
    have hy' : y - (⌊x⌋ : ℝ) ∈ Set.Ioo (c - 1) a := by
      constructor <;> linarith [hy.1, hy.2]
    calc
      periodizer a c y = periodizer a c ((⌊x⌋ : ℝ) + (y - (⌊x⌋ : ℝ))) := by congr 1; ring
      _ = periodizer a c (y - (⌊x⌋ : ℝ)) := periodizer_int_add a c _ _
      _ = y - (⌊x⌋ : ℝ) := periodizer_near_zero a c ha hac hc _ hy'
  · have hg : ContDiff ℝ ∞ (fun y : ℝ => (y - (⌊x⌋ : ℝ)) -
        Real.smoothTransition (((y - (⌊x⌋ : ℝ)) - a) / (c - a))) := by fun_prop
    apply hg.contDiffAt.congr_of_eventuallyEq
    have hlo : (⌊x⌋ : ℝ) < x := (Int.floor_le x).lt_of_ne (Ne.symm hx)
    filter_upwards [Ioo_mem_nhds hlo (Int.lt_floor_add_one x)] with y hy
    have hy' : ⌊y⌋ = ⌊x⌋ := Int.floor_eq_iff.2 ⟨hy.1.le, hy.2⟩
    simp only [periodizer, Int.fract, hy']

noncomputable def decoder (b : ℕ) : ℝ → ℝ :=
  letI := twoAtLeastTwo
  letI := threeAtLeastTwo
  periodizer ((2 * Encoding.tailMax b + 1) / 3) ((Encoding.tailMax b + 2) / 3)

lemma decoder_law (b : ℕ) (hb : 2 ≤ b) : Encoding.DecoderLaw b (decoder b) := by
  have hm := Encoding.tailMax_lt_one b hb
  refine ⟨periodizer_periodic _ _, ?_⟩
  intro x hx
  apply periodizer_self
  · linarith
  · linarith
  · exact ⟨hx.1, by linarith [hx.2]⟩

lemma decoder_smooth (b : ℕ) (hb : 2 ≤ b) : ContDiff ℝ ∞ (decoder b) := by
  have hm0 := Encoding.tailMax_nonneg b hb
  have hm1 := Encoding.tailMax_lt_one b hb
  apply periodizer_smooth <;> linarith

lemma iteratedDeriv_periodic (f : ℝ → ℝ) (hf : Function.Periodic f 1) (r : ℕ) :
    Function.Periodic (iteratedDeriv r f) 1 := by
  have heq : (fun x => f (x + 1)) = f := funext hf
  have h := iteratedDeriv_comp_add_const r f 1
  rw [heq] at h
  exact fun x => (congr_fun h x).symm

lemma periodic_derivatives_bounded (f : ℝ → ℝ) (hf : Function.Periodic f 1)
    (hs : ContDiff ℝ ∞ f) (r : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |iteratedDeriv r f x| ≤ C := by
  have hcont : Continuous (fun x => |iteratedDeriv r f x|) :=
    (hs.continuous_iteratedDeriv r (WithTop.coe_le_coe.mpr le_top)).abs
  obtain ⟨C, hC⟩ := isCompact_Icc.bddAbove_image (hcont.continuousOn (s := Set.Icc 0 1))
  refine ⟨max 0 C, le_max_left _ _, ?_⟩
  intro x
  obtain ⟨y, hy, hxy⟩ := (iteratedDeriv_periodic f hf r).exists_mem_Ico (by norm_num) x 0
  rw [hxy]
  apply le_trans _ (le_max_right _ _)
  apply hC
  exact ⟨y, ⟨hy.1, by simpa using hy.2.le⟩, rfl⟩

lemma decoder_derivatives_bounded (b : ℕ) (hb : 2 ≤ b) (r : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |iteratedDeriv r (decoder b) x| ≤ C :=
  periodic_derivatives_bounded (decoder b) (decoder_law b hb).1 (decoder_smooth b hb) r

end Profiles

namespace Encoding

lemma read_donor_configuration (b N n : ℕ) (hb : 2 ≤ b)
    (g : ℕ → ℕ) (L R : ℕ → List ℕ)
    (hL : ∀ j, (L j).length = Scales.K N j)
    (hR : ∀ j, (R j).length = Scales.K N j)
    (hd : ∀ j, ∀ d ∈ g j :: (L j ++ R j), d + 2 ≤ b) :
    let C := fun j => code b (g j :: (L j ++ R j))
    let D := donor b N C n
    Profiles.decoder b ((b : ℝ) ^ Scales.s N n * D) = C n ∧
    Profiles.decoder b ((b : ℝ) ^ (Scales.s N n + 1 + Scales.K N n) * D) =
      code b (R n) ∧
    Profiles.decoder b ((b : ℝ) ^ (Scales.s N n + 1) * D) -
      ((b : ℝ) ^ Scales.K N n)⁻¹ *
        Profiles.decoder b ((b : ℝ) ^ (Scales.s N n + 1 + Scales.K N n) * D) =
      code b (L n) := by
  dsimp only
  have hC : ∀ j, ∃ a : ℤ,
      (b : ℝ) ^ (1 + 2 * Scales.K N j) * code b (g j :: (L j ++ R j)) = a := by
    intro j
    obtain ⟨a, ha⟩ := code_denominator b (by omega) (g j :: (L j ++ R j))
    refine ⟨a, ?_⟩
    simp only [List.length_cons, List.length_append, hL, hR] at ha
    have he : 1 + 2 * Scales.K N j = Scales.K N j + Scales.K N j + 1 := by omega
    simpa only [he, Int.cast_natCast] using ha
  have h := read_configuration b (Scales.s N n) (g n) hb (L n) (R n)
    (donor b N (fun j => code b (g j :: (L j ++ R j))) n)
    (donor_integer_add b N n (by omega) _ hC) (hd n)
    (Profiles.decoder b) (Profiles.decoder_law b hb)
  simpa only [hL] using h

end Encoding
end AlternatingNS

end OAI
