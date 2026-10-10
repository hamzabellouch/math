import Mathlib

namespace OAI

/-! Window Assembly for chordal SLE. -/

section
open Set Filter MeasureTheory ProbabilityTheory Metric Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

lemma window_prod_telescope {ι : Type*} [LinearOrder ι]
    (s : Finset ι) (f : ι → ℝ) :
    ∏ i ∈ s, f i = 1 + ∑ i ∈ s, (f i - 1) * ∏ j ∈ s.filter (· < i), f j := by
  classical
  induction s using Finset.induction_on_max with
  | empty => simp
  | @insert a s ha ih =>
    have hn : a ∉ s := fun h => (lt_irrefl a) (ha a h)
    have hfa : (insert a s).filter (· < a) = s := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_insert]
      constructor
      · rintro ⟨rfl | hj, hja⟩
        · exact (lt_irrefl _ hja).elim
        · exact hj
      · intro hj; exact ⟨Or.inr hj, ha j hj⟩
    have hf (i : ι) (hi : i ∈ s) :
        (insert a s).filter (· < i) = s.filter (· < i) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_insert]
      constructor
      · rintro ⟨rfl | hj, hji⟩
        · exact (not_lt_of_ge (ha i hi).le hji).elim
        · exact ⟨hj, hji⟩
      · exact fun ⟨hj, hji⟩ => ⟨Or.inr hj, hji⟩
    rw [Finset.prod_insert hn, Finset.sum_insert hn, hfa]
    simp_rw [Finset.sum_congr rfl (fun i hi => congrArg (fun t => (f i-1)*∏j∈t,f j) (hf i hi))]
    rw [ih]
    ring

lemma window_integrable_bounded {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] {f : Ω → ℝ} (hf : Measurable f) {C : ℝ}
    (hC : ∀ ω, ‖f ω‖ ≤ C) : Integrable f P :=
  Integrable.mono' (integrable_const C) hf.aestronglyMeasurable (Eventually.of_forall hC)

lemma window_exp_secant {K θ x : ℝ} (hK : 0 < K) (hx : |x| ≤ K) :
    Real.exp (θ*x) ≤ Real.exp ((θ*K)^2/2) + Real.sinh (θ*K)/K*x := by
  let a := (K-x)/(2*K)
  let b := (K+x)/(2*K)
  have ha : 0 ≤ a := div_nonneg (sub_nonneg.mpr (le_abs_self x |>.trans hx)) (by positivity)
  have hb : 0 ≤ b := div_nonneg (by linarith [neg_abs_le x]) (by positivity)
  have hab : a+b=1 := by dsimp [a,b]; field_simp; ring
  have he := convexOn_exp.2 (x := -(θ*K)) (y := θ*K) (by trivial) (by trivial) ha hb hab
  have harg : a * -(θ*K) + b*(θ*K) = θ*x := by dsimp [a,b]; field_simp; ring
  simp only [smul_eq_mul, harg] at he
  have hid : a*Real.exp (-(θ*K)) + b*Real.exp (θ*K) =
      Real.cosh (θ*K) + Real.sinh (θ*K)/K*x := by
    rw [Real.cosh_eq, Real.sinh_eq]
    dsimp [a,b]
    field_simp
    ring
  rw [hid] at he
  exact he.trans (add_le_add (Real.cosh_le_exp_half_sq _) le_rfl)

lemma window_weighted_cond_mean {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsFiniteMeasure P] {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
    {X W : Ω → ℝ} (hX : Integrable X P) (hWX : Integrable (W*X) P)
    (hW : Measurable[m] W) (hW0 : ∀ ω, 0 ≤ W ω)
    (hmean : P[X|m] ≤ᵐ[P] 0) :
    ∫ ω, W ω*X ω ∂P ≤ 0 := by
  have he := condExp_mul_of_stronglyMeasurable_left hW.stronglyMeasurable hWX hX
  calc
    _ = ∫ ω, P[W*X|m] ω ∂P := (integral_condExp hm).symm
    _ = ∫ ω, W ω*P[X|m] ω ∂P := integral_congr_ae he
    _ ≤ 0 := integral_nonpos_of_ae (hmean.mono fun ω h =>
      mul_nonpos_of_nonneg_of_nonpos (hW0 ω) h)

lemma window_weighted_hoeffding {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsFiniteMeasure P] {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
    {X W : Ω → ℝ} {K θ : ℝ} (hK : 0 < K) (hθ : 0 ≤ θ)
    (hX : Measurable[mΩ] X) (hXb : ∀ ω, |X ω| ≤ K)
    (hmean : P[X|m] ≤ᵐ[P] 0) (hW : Measurable[m] W)
    (hW0 : ∀ ω, 0 ≤ W ω) (hWb : ∃ M, ∀ ω, W ω ≤ M) :
    (∫ ω, W ω * Real.exp (θ*X ω) ∂P) ≤
      (∫ ω, W ω ∂P) * Real.exp ((θ*K)^2/2) := by
  let : MeasurableSpace Ω := mΩ
  obtain ⟨M,hM⟩ := hWb
  have hWa : Measurable[mΩ] W := hW.mono hm le_rfl
  have hWi : Integrable W P := window_integrable_bounded hWa
    (fun ω => by simpa only [Real.norm_eq_abs, abs_of_nonneg (hW0 ω)] using hM ω)
  have hXi : Integrable X P := window_integrable_bounded hX (by simpa only [Real.norm_eq_abs] using hXb)
  have hWXi : Integrable (fun ω => W ω*X ω) P := window_integrable_bounded (hWa.mul hX) (fun ω => by
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (hW0 ω)]
    exact mul_le_mul (hM ω) (hXb ω) (norm_nonneg _) (le_trans (hW0 ω) (hM ω)))
  have hc := window_weighted_cond_mean hm hXi hWXi hW hW0 hmean
  have hL : 0 ≤ Real.sinh (θ*K)/K := div_nonneg (by rw [Real.sinh_eq]; exact div_nonneg (sub_nonneg.mpr (Real.exp_le_exp.mpr (by nlinarith [mul_nonneg hθ hK.le]))) (by norm_num)) hK.le
  have hEi : Integrable (fun ω => W ω*Real.exp (θ*X ω)) P :=
    window_integrable_bounded (hWa.mul ((hX.const_mul θ).exp)) (fun ω => by
      rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (hW0 ω), Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul (hM ω) (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left
        (le_abs_self _ |>.trans (hXb ω)) hθ)) (Real.exp_pos _).le (le_trans (hW0 ω) (hM ω)))
  calc
    _ ≤ ∫ ω, W ω * (Real.exp ((θ*K)^2/2) + Real.sinh (θ*K)/K * X ω) ∂P := by
      apply integral_mono hEi
      · have hi := (hWi.mul_const (Real.exp ((θ*K)^2/2))).add
            (hWXi.const_mul (Real.sinh (θ*K)/K))
        convert hi using 1; first | rfl | (ext ω; simp only [Pi.add_apply, mul_add]; ring)
      · intro ω
        exact mul_le_mul_of_nonneg_left (window_exp_secant hK (hXb ω)) (hW0 ω)
    _ = (∫ ω, W ω ∂P)*Real.exp ((θ*K)^2/2) +
        Real.sinh (θ*K)/K*(∫ ω, W ω*X ω ∂P) := by
      simp_rw [mul_add, show ∀ ω, W ω*(Real.sinh (θ*K)/K*X ω) =
        (Real.sinh (θ*K)/K)*(W ω*X ω) from fun _ => by ring]
      rw [integral_add (hWi.mul_const _) (hWXi.const_mul _), integral_mul_const, integral_const_mul]
    _ ≤ _ := by linarith [mul_nonpos_of_nonneg_of_nonpos hL hc]

def windowBefore {Ω ι : Type*} [LinearOrder ι]
    (σ : ι → Ω → WithTop ℝ≥0) (i j : ι) (ω : Ω) : Prop :=
  σ i ω < σ j ω ∨ σ i ω = σ j ω ∧ i < j

lemma window_prod_before {Ω ι : Type*} [Fintype ι] [LinearOrder ι]
    (σ : ι → Ω → WithTop ℝ≥0) (ω : Ω) (f : ι → ℝ) :
    ∏ i, f i = 1 + ∑ i, (f i - 1) * ∏ j, if windowBefore σ j i ω then f j else 1 := by
  classical
  let key (i : ι) : Lex (WithTop ℝ≥0 × ι) := toLex (σ i ω, i)
  have hinj : Function.Injective key := fun i j h => congrArg Prod.snd h
  have hh := @window_prod_telescope ι (LinearOrder.lift' key hinj) Finset.univ f
  simp only [Finset.prod_filter] at hh
  change (∏ i, f i) = 1 + ∑ i, (f i-1)*∏j, if key j < key i then f j else 1 at hh
  rw [hh]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  have he : key j < key i ↔ windowBefore σ j i ω := by
    simp only [key, Prod.Lex.toLex_lt_toLex, windowBefore]
  by_cases hb : windowBefore σ j i ω
  · rw [ite_eq_left hb, ite_eq_left (he.mpr hb)]
  · rw [ite_eq_right hb, ite_eq_right (mt he.mp hb)]

lemma window_before_measurable {Ω ι : Type*} [mΩ : MeasurableSpace Ω] [LinearOrder ι]
    {ℱ : Filtration ℝ≥0 mΩ} {σ : ι → Ω → WithTop ℝ≥0}
    (hs : ∀ i, IsStoppingTime ℱ (σ i)) (i j : ι) :
    MeasurableSet[(hs i).measurableSpace] {ω | windowBefore σ j i ω} := by
  have hlt : MeasurableSet[(hs i).measurableSpace] {ω | σ j ω < σ i ω} := by
    simpa only [compl_ofPred, not_le] using ((hs i).measurableSet_le_stopping_time (hs j)).compl
  have heq : MeasurableSet[(hs i).measurableSpace] {ω | σ j ω = σ i ω} := by
    simpa only [eq_comm] using (hs i).measurableSet_eq_stopping_time (hs j)
  by_cases hij : j < i
  · convert hlt.union heq using 1
    ext ω
    simp only [windowBefore, hij, and_true, mem_ofPred_eq, mem_union]
  · simpa only [windowBefore, hij, and_false, or_false] using hlt

lemma window_measurable_on_event {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {ℱ : Filtration ℝ≥0 mΩ} {σ τ : Ω → WithTop ℝ≥0}
    (hs : IsStoppingTime ℱ σ) (ht : IsStoppingTime ℱ τ)
    {f : Ω → ℝ} (hf : Measurable[ht.measurableSpace] f)
    {E : Set Ω} (hE : MeasurableSet[hs.measurableSpace] E)
    (hle : ∀ ω ∈ E, τ ω ≤ σ ω) (c : ℝ) :
    Measurable[hs.measurableSpace] (fun ω => if ω ∈ E then f ω else c) := by
  classical
  intro B hB
  have hEB : MeasurableSet[hs.measurableSpace] (f ⁻¹' B ∩ E) := by
    have hh := ht.measurableSet_inter_le hs (f ⁻¹' B) (hf hB)
    have hh' : MeasurableSet[hs.measurableSpace] (f ⁻¹' B ∩ {ω | τ ω ≤ σ ω}) :=
      ((ht.min hs).measurableSpace_mono hs (fun _ => min_le_right _ _)) _ hh
    convert hh'.inter hE using 1
    ext ω
    simp only [mem_inter_iff, mem_preimage, mem_ofPred_eq]
    exact ⟨fun ⟨h1,h2⟩ => ⟨⟨h1,hle ω h2⟩,h2⟩, fun ⟨⟨h1,_⟩,h2⟩ => ⟨h1,h2⟩⟩
  by_cases hc : c ∈ B
  · convert hEB.union hE.compl using 1
    ext ω
    by_cases hw : ω ∈ E <;> simp [hw, hc]
  · convert hEB using 1
    ext ω
    by_cases hw : ω ∈ E <;> simp [hw, hc]

lemma window_integrable_nonneg {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] {f : Ω → ℝ} (hf : Measurable f) (h0 : ∀ ω, 0 ≤ f ω)
    {C : ℝ} (hC : ∀ ω, f ω ≤ C) : Integrable f P :=
  window_integrable_bounded hf (fun ω => by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (h0 ω)] using hC ω)

lemma window_weighted_normalized {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsFiniteMeasure P] {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
    {X W : Ω → ℝ} {K θ : ℝ} (hK : 0 < K) (hθ : 0 ≤ θ)
    (hX : Measurable[mΩ] X) (hXb : ∀ ω, |X ω| ≤ K)
    (hmean : P[X|m] ≤ᵐ[P] 0) (hW : Measurable[m] W)
    (hW0 : ∀ ω, 0 ≤ W ω) (hWb : ∃ M, ∀ ω, W ω ≤ M) :
    (∫ ω, W ω * (Real.exp (θ*X ω - (θ*K)^2/2)-1) ∂P) ≤ 0 := by
  let : MeasurableSpace Ω := mΩ
  obtain ⟨M,hM⟩ := hWb
  have hWa : Measurable[mΩ] W := hW.mono hm le_rfl
  have hWi : Integrable W P := window_integrable_nonneg hWa hW0 hM
  have hEi : Integrable (fun ω => W ω*Real.exp (θ*X ω)) P :=
    window_integrable_nonneg (hWa.mul ((hX.const_mul θ).exp))
      (fun ω => mul_nonneg (hW0 ω) (Real.exp_pos _).le) (fun ω =>
      mul_le_mul (hM ω) (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left
        (le_abs_self _ |>.trans (hXb ω)) hθ)) (Real.exp_pos _).le (le_trans (hW0 ω) (hM ω)))
  have h := window_weighted_hoeffding hm hK hθ hX hXb hmean hW hW0 ⟨M,hM⟩
  simp_rw [Real.exp_sub, mul_sub, mul_one, ← mul_div_assoc]
  rw [integral_sub (hEi.div_const _) hWi, integral_div]
  exact sub_nonpos.mpr ((div_le_iff₀ (Real.exp_pos _)).mpr h)

 

lemma window_finite_mgf {Ω ι : Type*} [mΩ : MeasurableSpace Ω]
    [Fintype ι] [LinearOrder ι] {P : Measure Ω} [IsFiniteMeasure P]
    {ℱ : Filtration ℝ≥0 mΩ} {σ τ : ι → Ω → WithTop ℝ≥0}
    (hs : ∀ i, IsStoppingTime ℱ (σ i)) (ht : ∀ i, IsStoppingTime ℱ (τ i))
    (horder : ∀ i j ω, windowBefore σ j i ω → τ j ω ≤ σ i ω)
    {X : ι → Ω → ℝ} {K θ : ℝ} (hK : 0 < K) (hθ : 0 ≤ θ)
    (hX : ∀ i, Measurable[(ht i).measurableSpace] (X i))
    (hXb : ∀ i ω, |X i ω| ≤ K)
    (hmean : ∀ i, P[X i|(hs i).measurableSpace] ≤ᵐ[P] 0)
    {W : Ω → ℝ} (hW : Measurable[ℱ 0] W) (hW0 : ∀ ω, 0 ≤ W ω)
    (hWb : ∃ M, ∀ ω, W ω ≤ M) :
    (∫ ω, W ω * Real.exp (θ*∑ i, X i ω) ∂P) ≤
      (∫ ω, W ω ∂P) * Real.exp (Fintype.card ι * (θ*K)^2/2) := by
  classical
  let q := (θ*K)^2/2
  let g (i : ι) (ω : Ω) := Real.exp (θ*X i ω-q)
  let pre (i : ι) (ω : Ω) := ∏ j, if windowBefore σ j i ω then g j ω else 1
  have hg (i : ι) : Measurable[(ht i).measurableSpace] (g i) :=
    (((hX i).const_mul θ).sub_const q).exp
  have hga (i : ι) : Measurable[mΩ] (g i) := (hg i).mono (ht i).measurableSpace_le le_rfl
  have hg0 (i : ι) (ω : Ω) : 0 ≤ g i ω := (Real.exp_pos _).le
  have hgB (i : ι) (ω : Ω) : g i ω ≤ Real.exp (θ*K) := by
    apply Real.exp_le_exp.mpr
    have := mul_le_mul_of_nonneg_left (le_abs_self _ |>.trans (hXb i ω)) hθ
    dsimp [q]
    nlinarith [sq_nonneg (θ*K)]
  have hp (i : ι) : Measurable[(hs i).measurableSpace] (pre i) := by
    apply Finset.measurable_prod
    intro j hj
    exact window_measurable_on_event (hs i) (ht j) (hg j)
      (window_before_measurable hs i j) (fun ω hω => horder i j ω hω) 1
  have hp0 (i : ι) (ω : Ω) : 0 ≤ pre i ω := by
    apply Finset.prod_nonneg
    intro j hj
    split_ifs <;> positivity
  have hpB (i : ι) (ω : Ω) : pre i ω ≤ Real.exp (θ*K)^Fintype.card ι := by
    calc
      _ ≤ ∏ _j : ι, Real.exp (θ*K) := by
        apply Finset.prod_le_prod₀
        · intro j hj; split_ifs <;> positivity
        · intro j hj; split_ifs
          · exact hgB j ω
          · exact Real.one_le_exp (mul_nonneg hθ hK.le)
      _ = _ := by simp
  have hWstart (i : ι) : Measurable[(hs i).measurableSpace] W := by
    have hle := (isStoppingTime_const ℱ (0 : ℝ≥0)).measurableSpace_mono (hs i)
      (fun ω => bot_le)
    rw [IsStoppingTime.measurableSpace_const] at hle
    exact hW.mono hle le_rfl
  have hWa : Measurable[mΩ] W := hW.mono (ℱ.le 0) le_rfl
  obtain ⟨M,hM⟩ := hWb
  have hWi : Integrable W P := window_integrable_nonneg hWa hW0 hM
  have hHi (i : ι) : Integrable (fun ω => W ω*pre i ω*(g i ω-1)) P := by
    apply window_integrable_bounded (C := (M*Real.exp (θ*K)^Fintype.card ι)*(Real.exp (θ*K)+1)) (((hWa.mul ((hp i).mono (hs i).measurableSpace_le le_rfl))).mul
      ((hga i).sub_const 1))
    intro ω
    change ‖W ω*pre i ω*(g i ω-1)‖ ≤ _
    rw [norm_mul, norm_mul, Real.norm_eq_abs, abs_of_nonneg (hW0 ω),
      Real.norm_eq_abs, abs_of_nonneg (hp0 i ω)]
    apply mul_le_mul
    · exact mul_le_mul (hM ω) (hpB i ω) (hp0 i ω) ((hW0 ω).trans (hM ω))
    · calc
        _ ≤ ‖g i ω‖ + ‖(1 : ℝ)‖ := norm_sub_le _ _
        _ = g i ω + 1 := by rw [Real.norm_eq_abs, abs_of_nonneg (hg0 i ω), norm_one]
        _ ≤ _ := add_le_add (hgB i ω) le_rfl
    · exact norm_nonneg _
    · exact mul_nonneg ((hW0 ω).trans (hM ω)) (by positivity)
  have hHi0 (i : ι) : (∫ ω, W ω*pre i ω*(g i ω-1) ∂P) ≤ 0 := by
    exact window_weighted_normalized (hs i).measurableSpace_le hK hθ
      ((hX i).mono (ht i).measurableSpace_le le_rfl) (hXb i) (hmean i)
      ((hWstart i).mul (hp i)) (fun ω => mul_nonneg (hW0 ω) (hp0 i ω))
      ⟨M*Real.exp (θ*K)^Fintype.card ι, fun ω =>
        mul_le_mul (hM ω) (hpB i ω) (hp0 i ω) ((hW0 ω).trans (hM ω))⟩
  have hnorm : (∫ ω, W ω * ∏ i, g i ω ∂P) ≤ ∫ ω, W ω ∂P := by
    have hid (ω : Ω) := window_prod_before σ ω (fun i => g i ω)
    simp_rw [hid, mul_add, mul_one, Finset.mul_sum]
    change (∫ ω, W ω + ∑ i, W ω*((g i ω-1)*pre i ω) ∂P) ≤ _
    simp_rw [show ∀ i ω, W ω*((g i ω-1)*pre i ω) = W ω*pre i ω*(g i ω-1)
      from fun _ _ => by ring]
    rw [integral_add hWi (integrable_finsetSum _ (fun i hi => hHi i)), integral_finsetSum]
    · exact add_le_of_nonpos_right (Finset.sum_nonpos fun i hi => hHi0 i)
    · exact fun i hi => hHi i
  have hprod (ω : Ω) : (∏ i, g i ω) =
      Real.exp (θ*∑ i, X i ω) / Real.exp (Fintype.card ι * q) := by
    change (∏ i, Real.exp (θ*X i ω-q)) = _
    rw [← Real.exp_sum]
    simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul]
    exact Real.exp_sub _ _
  simp only [hprod, ← mul_div_assoc] at hnorm
  rw [integral_div] at hnorm
  simpa only [q, mul_div_assoc] using (div_le_iff₀ (Real.exp_pos _)).mp hnorm

 

structure SourceDisjointWindows {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (D : Set ℂ) (r R K : ℝ) (γ : ℝ≥0 → Ω → ℂ)
    (σ τ : ℂ → Ω → WithTop ℝ≥0) (Y μ : ℂ → Ω → ℝ) : Prop where
  measurable_D : MeasurableSet D
  bounded_D : D ⊆ ball 0 1
  radius_pos : 0 < r
  radius_le : r ≤ R
  radius_small : 3 * R ≤ 1
  bound_nonneg : 0 ≤ K
  continuous_trace : ∀ ω, Continuous (fun t => γ t ω)
  adapted_trace : ∀ t, Measurable[ℱ t] (γ t)
  start : ∀ z, IsStoppingTime ℱ (σ z)
  finish : ∀ z, IsStoppingTime ℱ (τ z)
  time_le : ∀ z ω, σ z ω ≤ τ z ω
  contact : ∀ z ω, σ z ω ≠ ⊤ → dist (γ ((σ z ω).untopD 0) ω) z = r
  confined : ∀ z ω (t : ℝ≥0), σ z ω ≤ (t : WithTop ℝ≥0) → (t : WithTop ℝ≥0) < τ z ω →
    dist (γ t ω) z < R
  output_measurable : ∀ z, Measurable[(finish z).measurableSpace] (Y z)
  mean_measurable : ∀ z, Measurable[(start z).measurableSpace] (μ z)
  output_bound : ∀ z ω, 0 ≤ Y z ω ∧ Y z ω ≤ K
  mean_nonneg : ∀ z ω, 0 ≤ μ z ω
  mean_bounded : ∃ M : ℝ, ∀ z ω, μ z ω ≤ M
  upper_mean : ∀ z, ∀ᵐ ω ∂P, σ z ω ≠ ⊤ → P[Y z | (start z).measurableSpace] ω ≤ μ z ω
  no_start : ∀ z ω, σ z ω = ⊤ → Y z ω = 0 ∧ μ z ω = 0
  no_end : ∀ z ω, τ z ω = ⊤ → Y z ω = 0
  outside : ∀ z, z ∉ D → ∀ ω, σ z ω = ⊤ ∧ Y z ω = 0 ∧ μ z ω = 0
  joint_output : Measurable (fun p : ℂ × Ω => Y p.1 p.2)
  joint_mean : Measurable (fun p : ℂ × Ω => μ p.1 p.2)

lemma window_cond_mean_at_infinity {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsFiniteMeasure P] {ℱ : Filtration ℝ≥0 mΩ}
    {σ : Ω → WithTop ℝ≥0} (hs : IsStoppingTime ℱ σ)
    {Y μ : Ω → ℝ} (hY : Integrable Y P)
    (hmean : ∀ᵐ ω ∂P, σ ω ≠ ⊤ → P[Y|hs.measurableSpace] ω ≤ μ ω)
    (hno : ∀ ω, σ ω = ⊤ → Y ω = 0 ∧ μ ω = 0) :
    P[Y|hs.measurableSpace] ≤ᵐ[P] μ := by
  have htop : IsStoppingTime ℱ (fun _ => (⊤ : WithTop ℝ≥0)) := by
    intro t
    simp
  have hE : MeasurableSet[hs.measurableSpace] {ω | σ ω = ⊤} :=
    hs.measurableSet_eq_stopping_time htop
  have he := condExp_indicator hY hE
  have hz : ({ω | σ ω = ⊤}.indicator Y) = 0 := by
    ext ω
    by_cases h : σ ω = ⊤
    · simpa [h] using (hno ω h).1
    · simp [h]
  rw [hz, condExp_zero] at he
  filter_upwards [hmean, he] with ω hm he
  by_cases h : σ ω = ⊤
  · have hy : P[Y|hs.measurableSpace] ω = 0 := by simpa [h] using he.symm
    rw [hy, (hno ω h).2]
  · exact hm h

lemma window_capped_cond_mean {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsFiniteMeasure P] {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
    {Y μ : Ω → ℝ} {K : ℝ} (hK : 0 ≤ K) (hY : Measurable[mΩ] Y)
    (hYb : ∀ ω, 0 ≤ Y ω ∧ Y ω ≤ K) (hμ : Measurable[m] μ)
    (hμ0 : ∀ ω, 0 ≤ μ ω) (hmean : P[Y|m] ≤ᵐ[P] μ) :
    P[(fun ω => Y ω-min (μ ω) K)|m] ≤ᵐ[P] 0 := by
  let : MeasurableSpace Ω := mΩ
  have hYi : Integrable Y P := window_integrable_nonneg hY (fun ω => (hYb ω).1) (fun ω => (hYb ω).2)
  have hν : Measurable[m] (fun ω => min (μ ω) K) := hμ.min measurable_const
  have hνi : Integrable (fun ω => min (μ ω) K) P :=
    window_integrable_nonneg (hν.mono hm le_rfl) (fun ω => le_min (hμ0 ω) hK)
      (fun ω => min_le_right _ _)
  have hbound := condExp_mono hYi (integrable_const K) (Eventually.of_forall fun ω => (hYb ω).2) (m := m)
  rw [condExp_const hm] at hbound
  have he := condExp_sub hYi hνi m
  rw [condExp_of_stronglyMeasurable hm hν.stronglyMeasurable hνi] at he
  filter_upwards [he, hbound, hmean] with ω he hb hm
  simp only [Pi.sub_apply] at he
  have he' : P[(fun ω => Y ω-min (μ ω) K)|m] ω = P[Y|m] ω-min (μ ω) K := by
    convert he using 1
  rw [he']
  exact sub_nonpos.mpr (le_min hm hb)

lemma window_geometric_order {Ω ι : Type*} [MeasurableSpace Ω]
    [LinearOrder ι] {P : Measure Ω} {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    {D : Set ℂ} {r R K : ℝ} {γ : ℝ≥0 → Ω → ℂ}
    {σ τ : ℂ → Ω → WithTop ℝ≥0} {Y μ : ℂ → Ω → ℝ}
    (h : SourceDisjointWindows P ℱ D r R K γ σ τ Y μ)
    {z : ι → ℂ} (hz : ∀ i j, i ≠ j → 2*R < dist (z i) (z j)) :
    ∀ i j ω, windowBefore (fun i => σ (z i)) j i ω → τ (z j) ω ≤ σ (z i) ω := by
  intro i j ω hpre
  by_contra hn
  have hne : σ (z i) ω ≠ ⊤ := ne_top_of_lt (lt_of_not_ge hn)
  have hji : j ≠ i := by
    intro he
    subst j
    rcases hpre with hlt | ⟨_,hlt⟩ <;> exact (lt_irrefl _ hlt)
  have hle : σ (z j) ω ≤ σ (z i) ω := hpre.elim le_of_lt (fun h => h.1.le)
  have hcoe : (((σ (z i) ω).untopD 0 : ℝ≥0) : WithTop ℝ≥0) = σ (z i) ω :=
    by
      cases he : σ (z i) ω with
      | top => exact (hne he).elim
      | coe t => rfl
  have hconf := h.confined (z j) ω ((σ (z i) ω).untopD 0) (hcoe.symm ▸ hle)
    (hcoe.symm ▸ lt_of_not_ge hn)
  have hcont := h.contact (z i) ω hne
  have htri := dist_triangle (z j) (γ ((σ (z i) ω).untopD 0) ω) (z i)
  rw [dist_comm (z j) (γ ((σ (z i) ω).untopD 0) ω), hcont] at htri
  have := hz j i hji
  linarith [h.radius_le]

lemma window_source_finite_mgf {Ω ι : Type*} [mΩ : MeasurableSpace Ω]
    [Fintype ι] [LinearOrder ι] {P : Measure Ω} [IsFiniteMeasure P]
    {ℱ : Filtration ℝ≥0 mΩ} {D : Set ℂ} {r R K : ℝ} {γ : ℝ≥0 → Ω → ℂ}
    {σ τ : ℂ → Ω → WithTop ℝ≥0} {Y μ : ℂ → Ω → ℝ}
    (h : SourceDisjointWindows P ℱ D r R K γ σ τ Y μ)
    {z : ι → ℂ} (hz : ∀ i j, i ≠ j → 2*R < dist (z i) (z j))
    {θ : ℝ} (hθ : 0 ≤ θ) {W : Ω → ℝ} (hW : Measurable[ℱ 0] W)
    (hW0 : ∀ ω, 0 ≤ W ω) (hWb : ∃ M, ∀ ω, W ω ≤ M) (hK : 0 < K) :
    (∫ ω, W ω * Real.exp (θ*∑ i, (Y (z i) ω-μ (z i) ω)) ∂P) ≤
      (∫ ω, W ω ∂P) * Real.exp (Fintype.card ι * (θ*K)^2/2) := by
  let X (i : ι) (ω : Ω) := Y (z i) ω-min (μ (z i) ω) K
  have hYa (i : ι) : Measurable[mΩ] (Y (z i)) :=
    (h.output_measurable (z i)).mono (h.finish (z i)).measurableSpace_le le_rfl
  have hμa (i : ι) : Measurable[mΩ] (μ (z i)) :=
    (h.mean_measurable (z i)).mono (h.start (z i)).measurableSpace_le le_rfl
  have hX (i : ι) : Measurable[(h.finish (z i)).measurableSpace] (X i) :=
    (h.output_measurable (z i)).sub (((h.mean_measurable (z i)).mono
      ((h.start (z i)).measurableSpace_mono (h.finish (z i)) (h.time_le (z i))) le_rfl).min measurable_const)
  have hXb (i : ι) (ω : Ω) : |X i ω| ≤ K := by
    rw [abs_le]
    have := h.output_bound (z i) ω
    have := le_min (h.mean_nonneg (z i) ω) hK.le
    have := min_le_right (μ (z i) ω) K
    dsimp [X]
    constructor <;> linarith
  have hm (i : ι) : P[X i|(h.start (z i)).measurableSpace] ≤ᵐ[P] 0 :=
    window_capped_cond_mean (h.start (z i)).measurableSpace_le hK.le (hYa i)
      (h.output_bound (z i)) (h.mean_measurable (z i)) (h.mean_nonneg (z i))
      (window_cond_mean_at_infinity (h.start (z i))
        (window_integrable_nonneg (hYa i) (fun ω => (h.output_bound (z i) ω).1)
          (fun ω => (h.output_bound (z i) ω).2)) (h.upper_mean (z i)) (h.no_start (z i)))
  have ht := window_finite_mgf (fun i => h.start (z i)) (fun i => h.finish (z i))
    (window_geometric_order h hz) hK hθ hX hXb hm hW hW0 hWb
  apply le_trans _ ht
  obtain ⟨M,hM⟩ := hWb
  obtain ⟨L,hL⟩ := h.mean_bounded
  have hWa : Measurable[mΩ] W := hW.mono (ℱ.le 0) le_rfl
  have hib (f : ι → Ω → ℝ) (hf : ∀ i, Measurable[mΩ] (f i))
      (hb : ∀ i ω, f i ω ≤ K) : Integrable (fun ω => W ω*Real.exp (θ*∑ i, f i ω)) P :=
    window_integrable_nonneg (C := M*Real.exp (θ*(Fintype.card ι*K))) (hWa.mul ((Finset.measurable_sum _ (fun i _ => hf i)).const_mul θ).exp)
      (fun ω => mul_nonneg (hW0 ω) (Real.exp_pos _).le)
      (fun ω => mul_le_mul (hM ω) (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left
        ((Finset.sum_le_sum fun i hi => hb i ω).trans_eq (by simp)) hθ))
        (Real.exp_pos _).le ((hW0 ω).trans (hM ω)))
  apply integral_mono
  · exact hib (fun i ω => Y (z i) ω-μ (z i) ω) (fun i => (hYa i).sub (hμa i))
      (fun i ω => sub_le_self _ (h.mean_nonneg (z i) ω) |>.trans (h.output_bound (z i) ω).2)
  · exact hib X (fun i => (hX i).mono (h.finish (z i)).measurableSpace_le le_rfl)
      (fun i ω => le_abs_self _ |>.trans (hXb i ω))
  · intro ω
    apply mul_le_mul_of_nonneg_left _ (hW0 ω)
    apply Real.exp_le_exp.mpr
    apply mul_le_mul_of_nonneg_left _ hθ
    exact Finset.sum_le_sum fun i hi => sub_le_sub_left (min_le_left _ _) _

lemma window_integral_grid_1d {f : ℝ → ℝ} (hf : Measurable f)
    {C a : ℝ} (hC : ∀ x, ‖f x‖ ≤ C) (ha : 0 ≤ a) (n : ℕ) :
    (∫ x in Ioc 0 a, ∑ i : Fin n, f (x + a*i - 2)) =
      ∫ x in Ioc (-2) (a*n-2), f x := by
  have hfi (u v : ℝ) : IntegrableOn f (Ioc u v) :=
    window_integrable_bounded hf hC
  have hi (i : Fin n) : IntegrableOn (fun x => f (x+a*i-2)) (Ioc 0 a) :=
    window_integrable_bounded (hf.comp ((measurable_id.add_const _).sub_const _))
      (fun x => hC _)
  rw [integral_finsetSum _ (fun i _ => hi i)]
  have hpiece (i : Fin n) : (∫ x in Ioc 0 a, f (x+a*i-2)) =
      ∫ x in (a*(i:ℝ)-2)..(a*((i:ℝ)+1)-2), f x := by
    rw [← intervalIntegral.integral_of_le ha]
    have he := intervalIntegral.integral_comp_add_right f (a*i-2) (a := 0) (b := a)
    simp only [zero_add] at he
    have hend : a*((i:ℝ)+1)-2 = a+(a*i-2) := by ring
    simpa only [hend, add_sub_assoc] using he
  simp_rw [hpiece]
  rw [Fin.sum_univ_eq_sum_range (fun k : ℕ =>
    ∫ x in (a*(k:ℝ)-2)..(a*((k:ℝ)+1)-2), f x) n]
  have hsum := intervalIntegral.sum_integral_adjacent_intervals
    (a := fun k => a*k-2) (n := n) (f := f) (μ := volume)
    (fun k hk => (intervalIntegrable_iff_integrableOn_Ioc_of_le
      (by have : (k:ℝ) ≤ k+1 := by linarith
          exact sub_le_sub_right (mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.le_succ k) ha) 2)).mpr (hfi _ _))
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, mul_zero, zero_sub] at hsum
  rw [hsum, intervalIntegral.integral_of_le (by nlinarith [mul_nonneg ha (Nat.cast_nonneg n)])]

noncomputable def windowSquare (a b : ℝ) : Measure (ℝ × ℝ) :=
  (volume.restrict (Ioc a b)).prod (volume.restrict (Ioc a b))

instance windowSquare_finite (a b : ℝ) : IsFiniteMeasure (windowSquare a b) := by
  dsimp [windowSquare]
  infer_instance

lemma window_grid_2d {f : ℝ × ℝ → ℝ} (hf : Measurable f)
    {C a : ℝ} (hC : ∀ x, ‖f x‖ ≤ C) (ha : 0 ≤ a) (n : ℕ) :
    (∫ p, ∑ ij : Fin n × Fin n,
      f (p.1+a*ij.1-2,p.2+a*ij.2-2) ∂windowSquare 0 a) =
      ∫ p, f p ∂windowSquare (-2) (a*n-2) := by
  let G (x : ℝ) := ∫ y in Ioc (-2) (a*n-2), f (x,y)
  have hG : Measurable G := (hf.stronglyMeasurable.integral_prod_right (f := fun x y => f (x,y))).measurable
  have hGb (x : ℝ) : ‖G x‖ ≤ C*(volume.restrict (Ioc (-2) (a*n-2))).real univ :=
    norm_integral_le_of_norm_le_const (Eventually.of_forall fun y => hC (x,y))
  have hrow (x : ℝ) : (∫ y in Ioc 0 a, ∑ ij : Fin n × Fin n,
      f (x+a*ij.1-2,y+a*ij.2-2)) = ∑ i : Fin n, G (x+a*i-2) := by
    simp_rw [Fintype.sum_prod_type]
    rw [integral_finsetSum]
    · congr 1
      ext i
      exact window_integral_grid_1d (hf.comp (measurable_const.prodMk measurable_id))
        (fun y => hC _) ha n
    · intro i hi
      apply window_integrable_bounded (C := n*C)
      · exact Finset.measurable_sum _ (fun j hj => hf.comp (measurable_const.prodMk
          ((measurable_id.add_const _).sub_const _)))
      · intro y
        exact (norm_sum_le _ _).trans ((Finset.sum_le_sum fun j hj => hC _).trans_eq (by simp))
  dsimp only [windowSquare]
  rw [integral_prod]
  · simp_rw [hrow]
    rw [window_integral_grid_1d hG hGb ha n]
    exact (integral_prod f (window_integrable_bounded hf hC)).symm
  · apply window_integrable_bounded (C := (n*n)*C)
    · apply Finset.measurable_sum
      intro ij hij
      exact hf.comp (((measurable_fst.add_const _).sub_const _).prodMk
        ((measurable_snd.add_const _).sub_const _))
    · intro p
      exact (norm_sum_le _ _).trans ((Finset.sum_le_sum fun ij hij => hC _).trans_eq (by simp))

noncomputable def windowShiftLaw (a : ℝ) : Measure (ℝ × ℝ) :=
  (ENNReal.ofReal (a^2))⁻¹ • windowSquare 0 a

lemma windowSquare_mass {a : ℝ} (ha : 0 ≤ a) : windowSquare 0 a univ = ENNReal.ofReal (a^2) := by
  simp [windowSquare, Measure.prod_apply, Real.volume_Ioc, sq, ← ENNReal.ofReal_mul ha]

lemma windowShiftLaw_probability {a : ℝ} (ha : 0 < a) : IsProbabilityMeasure (windowShiftLaw a) := by
  apply isProbabilityMeasure_iff.mpr
  rw [windowShiftLaw, Measure.smul_apply, windowSquare_mass ha.le]
  exact ENNReal.inv_mul_cancel (by positivity) (by finiteness)

lemma window_rectangle_integral {f : ℂ → ℝ} (_hf : Measurable f)
    (hz : ∀ z, z ∉ ball (0:ℂ) 1 → f z = 0) :
    (∫ p, f (Complex.measurableEquivRealProd.symm p) ∂windowSquare (-2) 2) = ∫ z, f z := by
  rw [windowSquare, Measure.prod_restrict]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
  · exact (Complex.volume_preserving_equiv_real_prod.symm).integral_comp' f
  · intro p hp
    apply hz
    intro hb
    apply hp
    have hn : ‖Complex.measurableEquivRealProd.symm p‖ < 1 := by simpa using hb
    have hr := Complex.abs_re_le_norm (Complex.measurableEquivRealProd.symm p)
    have hi := Complex.abs_im_le_norm (Complex.measurableEquivRealProd.symm p)
    change |p.1| ≤ _ at hr
    change |p.2| ≤ _ at hi
    exact ⟨⟨by linarith [neg_abs_le p.1], by linarith [le_abs_self p.1]⟩,
      ⟨by linarith [neg_abs_le p.2], by linarith [le_abs_self p.2]⟩⟩

noncomputable def windowCenter (a : ℝ) (ξ : ℝ × ℝ) {n : ℕ} (i : Fin n × Fin n) : ℂ :=
  Complex.measurableEquivRealProd.symm (ξ.1+a*i.1-2, ξ.2+a*i.2-2)

lemma window_grid_average {f : ℂ → ℝ} (hf : Measurable f)
    {C a : ℝ} (hC : ∀ z, ‖f z‖ ≤ C) (ha : 0 < a) {n : ℕ} (han : a*n=4)
    (hz : ∀ z, z ∉ ball (0:ℂ) 1 → f z = 0) :
    (∫ ξ, a^2 * ∑ i : Fin n × Fin n, f (windowCenter a ξ i) ∂windowShiftLaw a) = ∫ z, f z := by
  rw [windowShiftLaw, integral_smul_measure, integral_const_mul]
  have he := window_grid_2d (hf.comp Complex.measurableEquivRealProd.symm.measurable)
    (fun p => hC _) ha.le n
  rw [han] at he
  norm_num only [Function.comp_apply] at he
  dsimp only [windowCenter]
  rw [he, window_rectangle_integral hf hz]
  simp only [ENNReal.toReal_inv, ENNReal.toReal_ofReal (sq_nonneg a), smul_eq_mul]
  field_simp

lemma window_nat_spacing (a : ℝ) (ha : 0 ≤ a) {i j : ℕ} (hne : i ≠ j) :
    a ≤ |a*i-a*j| := by
  rcases lt_or_gt_of_ne hne with h | h
  · have h' : (i:ℝ)+1 ≤ j := by exact_mod_cast h
    have hle : a*i ≤ a*j := mul_le_mul_of_nonneg_left (by exact_mod_cast h.le) ha
    rw [abs_of_nonpos (sub_nonpos.mpr hle)]
    nlinarith
  · have h' : (j:ℝ)+1 ≤ i := by exact_mod_cast h
    have hle : a*j ≤ a*i := mul_le_mul_of_nonneg_left (by exact_mod_cast h.le) ha
    rw [abs_of_nonneg (sub_nonneg.mpr hle)]
    nlinarith

lemma window_centers_separated {a R : ℝ} (hsep : 2*R < a) (ha : 0 ≤ a)
    {n : ℕ} (ξ : ℝ × ℝ) (i j : Fin n × Fin n) (hne : i ≠ j) :
    2*R < dist (windowCenter a ξ i) (windowCenter a ξ j) := by
  rw [dist_eq_norm]
  rcases not_and_or.mp (mt Prod.ext_iff.mpr hne) with h | h
  · apply hsep.trans_le
    apply le_trans (window_nat_spacing a ha (mt Fin.ext h))
    have he : (windowCenter a ξ i - windowCenter a ξ j).re = a*(i.1:ℝ)-a*(j.1:ℝ) := by
      dsimp [windowCenter]
      ring
    rw [← he]
    exact Complex.abs_re_le_norm _
  · apply hsep.trans_le
    apply le_trans (window_nat_spacing a ha (mt Fin.ext h))
    have he : (windowCenter a ξ i - windowCenter a ξ j).im = a*(i.2:ℝ)-a*(j.2:ℝ) := by
      dsimp [windowCenter]
      ring
    rw [← he]
    exact Complex.abs_im_le_norm _

lemma window_choose_grid {R : ℝ} (hR : 0 < R) (hsmall : 3*R ≤ 1) :
    ∃ (n : ℕ) (a : ℝ), 0 < a ∧ a*n=4 ∧ 2*R<a ∧ a≤4*R := by
  let n := Nat.ceil (1/R)
  have hl := Nat.le_ceil (1/R)
  have hu := Nat.ceil_lt_add_one (a := 1/R) (by positivity)
  have hn : 0 < (n:ℝ) := (by positivity : 0 < 1/R).trans_le hl
  have hnr : 1 ≤ R*n := by
    exact (div_le_iff₀ hR).mp hl |>.trans_eq (mul_comm _ _)
  have hnr' : R*n < 1+R := by
    have H := mul_lt_mul_of_pos_right hu hR
    rw [add_mul, div_mul_cancel₀ _ hR.ne', one_mul] at H
    simpa only [mul_comm] using H
  refine ⟨n,4/n,by positivity,div_mul_cancel₀ 4 hn.ne',?_,?_⟩
  · apply (lt_div_iff₀ hn).mpr
    nlinarith
  · apply (div_le_iff₀ hn).mpr
    nlinarith
lemma window_jensen_mgf {Ξ Ω : Type*} [MeasurableSpace Ξ] [MeasurableSpace Ω]
    {Q : Measure Ξ} [IsProbabilityMeasure Q] {P : Measure Ω} [IsFiniteMeasure P]
    {F : Ξ → Ω → ℝ} (hF : Measurable (Function.uncurry F))
    {B θ A : ℝ} (hFb : ∀ ξ ω, ‖F ξ ω‖ ≤ B) (hθ : 0 ≤ θ)
    {W : Ω → ℝ} (hW : Measurable W) (hW0 : ∀ ω, 0 ≤ W ω)
    (hWb : ∃ M, ∀ ω, W ω ≤ M)
    (hmgf : ∀ ξ, (∫ ω, W ω*Real.exp (θ*F ξ ω) ∂P) ≤ A) :
    (∫ ω, W ω*Real.exp (θ*∫ ξ, F ξ ω ∂Q) ∂P) ≤ A := by
  obtain ⟨M,hM⟩ := hWb
  have hFi (ω : Ω) : Integrable (fun ξ => θ*F ξ ω) Q :=
    window_integrable_bounded ((hF.comp (measurable_id.prodMk measurable_const)).const_mul θ)
      (C := θ*B) (fun ξ => by rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg hθ]
                              exact mul_le_mul_of_nonneg_left (hFb ξ ω) hθ)
  have hEi (ω : Ω) : Integrable (fun ξ => Real.exp (θ*F ξ ω)) Q :=
    window_integrable_nonneg ((hF.comp (measurable_id.prodMk measurable_const)).const_mul θ).exp
      (fun ξ => (Real.exp_pos _).le) (fun ξ => Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_left (le_abs_self _ |>.trans (hFb ξ ω)) hθ))
  have hJ (ω : Ω) : Real.exp (θ*∫ ξ, F ξ ω ∂Q) ≤ ∫ ξ, Real.exp (θ*F ξ ω) ∂Q := by
    rw [← integral_const_mul]
    exact convexOn_exp.map_integral_le Real.continuous_exp.continuousOn isClosed_univ
      (Eventually.of_forall fun _ => mem_univ _) (hFi ω) (hEi ω)
  have hZ : Measurable (fun ω => ∫ ξ, F ξ ω ∂Q) :=
    ((hF.comp measurable_swap).stronglyMeasurable.integral_prod_right (f := fun ω ξ => F ξ ω)).measurable
  have hZb (ω : Ω) : ‖∫ ξ, F ξ ω ∂Q‖ ≤ B := by
    simpa using norm_integral_le_of_norm_le_const (μ := Q) (Eventually.of_forall fun ξ => hFb ξ ω)
  have hleft : Integrable (fun ω => W ω*Real.exp (θ*∫ ξ, F ξ ω ∂Q)) P :=
    window_integrable_nonneg (hW.mul (hZ.const_mul θ).exp)
      (fun ω => mul_nonneg (hW0 ω) (Real.exp_pos _).le)
      (C := M*Real.exp (θ*B)) (fun ω => mul_le_mul (hM ω)
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (le_abs_self _ |>.trans (hZb ω)) hθ))
        (Real.exp_pos _).le ((hW0 ω).trans (hM ω)))
  have hjoint : Integrable (Function.uncurry (fun ξ ω => W ω*Real.exp (θ*F ξ ω))) (Q.prod P) :=
    window_integrable_nonneg ((hW.comp measurable_snd).mul (hF.const_mul θ).exp)
      (fun p => mul_nonneg (hW0 p.2) (Real.exp_pos _).le)
      (C := M*Real.exp (θ*B)) (fun p => mul_le_mul (hM p.2)
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (le_abs_self _ |>.trans (hFb p.1 p.2)) hθ))
        (Real.exp_pos _).le ((hW0 p.2).trans (hM p.2)))
  calc
    _ ≤ ∫ ω, ∫ ξ, W ω*Real.exp (θ*F ξ ω) ∂Q ∂P := by
      apply integral_mono hleft hjoint.integral_prod_right
      intro ω
      change W ω*Real.exp (θ*∫ ξ, F ξ ω ∂Q) ≤ ∫ ξ, W ω*Real.exp (θ*F ξ ω) ∂Q
      rw [integral_const_mul]
      exact mul_le_mul_of_nonneg_left (hJ ω) (hW0 ω)
    _ = ∫ ξ, ∫ ω, W ω*Real.exp (θ*F ξ ω) ∂P ∂Q := (integral_integral_swap hjoint).symm
    _ ≤ ∫ _ξ, A ∂Q := integral_mono hjoint.integral_prod_left (integrable_const A) hmgf
    _ = A := by simp
lemma window_source_mgf_pos {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsFiniteMeasure P] {ℱ : Filtration ℝ≥0 mΩ}
    {D : Set ℂ} {r R K : ℝ} {γ : ℝ≥0 → Ω → ℂ}
    {σ τ : ℂ → Ω → WithTop ℝ≥0} {Y μ : ℂ → Ω → ℝ}
    (h : SourceDisjointWindows P ℱ D r R K γ σ τ Y μ)
    {θ : ℝ} (hθ : 0 ≤ θ) {W : Ω → ℝ} (hW : Measurable[ℱ 0] W)
    (hW0 : ∀ ω, 0 ≤ W ω) (hWb : ∃ M, ∀ ω, W ω ≤ M) (hK : 0 < K) :
    (∫ ω, W ω * Real.exp (θ*∫ z in D, (Y z ω-μ z ω)) ∂P) ≤
      (∫ ω, W ω ∂P) * Real.exp (128*K^2*θ^2*R^2) := by
  obtain ⟨n,a,ha,han,hsep,haR⟩ := window_choose_grid (h.radius_pos.trans_le h.radius_le) h.radius_small
  let : LinearOrder (Fin n × Fin n) := LinearOrder.lift' toLex toLex.injective
  let F (ξ : ℝ × ℝ) (ω : Ω) := a^2 * ∑ i : Fin n × Fin n,
    (Y (windowCenter a ξ i) ω - μ (windowCenter a ξ i) ω)
  have hcenter (i : Fin n × Fin n) : Measurable (fun ξ => windowCenter a ξ i) :=
    Complex.measurableEquivRealProd.symm.measurable.comp
      (((measurable_fst.add_const _).sub_const _).prodMk ((measurable_snd.add_const _).sub_const _))
  have hmeas : Measurable (Function.uncurry F) := by
    apply Measurable.const_mul
    apply Finset.measurable_sum
    intro i hi
    exact (h.joint_output.sub h.joint_mean).comp
      (((hcenter i).comp measurable_fst).prodMk measurable_snd)
  obtain ⟨L,hL⟩ := h.mean_bounded
  have hnorm (z : ℂ) (ω : Ω) : ‖Y z ω-μ z ω‖ ≤ K+L := by
    calc
      _ ≤ ‖Y z ω‖+‖μ z ω‖ := norm_sub_le _ _
      _ = Y z ω+μ z ω := by rw [Real.norm_eq_abs, abs_of_nonneg (h.output_bound z ω).1,
        Real.norm_eq_abs, abs_of_nonneg (h.mean_nonneg z ω)]
      _ ≤ _ := add_le_add (h.output_bound z ω).2 (hL z ω)
  have hFb (ξ : ℝ × ℝ) (ω : Ω) : ‖F ξ ω‖ ≤ a^2*((n:ℝ)^2*(K+L)) := by
    dsimp only [F]
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg a)]
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg a)
    exact (norm_sum_le _ _).trans ((Finset.sum_le_sum fun i hi => hnorm _ ω).trans_eq (by simp [sq]; ring))
  have havg (ω : Ω) : (∫ ξ, F ξ ω ∂windowShiftLaw a) = ∫ z in D, (Y z ω-μ z ω) := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz => by
      obtain ⟨_,hy,hμ⟩ := h.outside z hz ω
      simp only [hy,hμ,sub_self])]
    exact window_grid_average ((h.joint_output.sub h.joint_mean).comp
      (measurable_id.prodMk measurable_const)) (fun z => hnorm z ω) ha han
      (fun z hz => by
        obtain ⟨_,hy,hμ⟩ := h.outside z (fun hzD => hz (h.bounded_D hzD)) ω
        change Y z ω-μ z ω=0
        simp only [hy,hμ,sub_self])
  let : IsProbabilityMeasure (windowShiftLaw a) := windowShiftLaw_probability ha
  have hfinite (ξ : ℝ × ℝ) :
      (∫ ω, W ω*Real.exp (θ*F ξ ω) ∂P) ≤
      (∫ ω, W ω ∂P) * Real.exp (128*K^2*θ^2*R^2) := by
    have ht := window_source_finite_mgf h (window_centers_separated (n := n) hsep ha.le ξ)
      (mul_nonneg hθ (sq_nonneg a)) hW hW0 hWb hK
    have he : (Fintype.card (Fin n × Fin n) : ℝ)*((θ*a^2)*K)^2/2 ≤ 128*K^2*θ^2*R^2 := by
      simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul]
      have hs : a^2 ≤ 16*R^2 := by nlinarith [h.radius_pos.trans_le h.radius_le]
      calc
        _ = (a*n)^2*a^2*θ^2*K^2/2 := by ring
        _ = 8*a^2*θ^2*K^2 := by rw [han]; ring
        _ ≤ 8*(16*R^2)*θ^2*K^2 := by gcongr
        _ = _ := by ring
    have ht' : (∫ ω, W ω*Real.exp (θ*F ξ ω) ∂P) ≤
        (∫ ω, W ω ∂P) * Real.exp ((Fintype.card (Fin n × Fin n) : ℝ)*((θ*a^2)*K)^2/2) := by
      simpa only [F, mul_assoc] using ht
    exact ht'.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) (integral_nonneg hW0))
  have ht := window_jensen_mgf (Q := windowShiftLaw a) hmeas hFb hθ (hW.mono (ℱ.le 0) le_rfl) hW0 hWb hfinite
  simpa only [havg] using ht

lemma window_source_integral_measurable {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {ℱ : Filtration ℝ≥0 mΩ}
    {D : Set ℂ} {r R K : ℝ} {γ : ℝ≥0 → Ω → ℂ}
    {σ τ : ℂ → Ω → WithTop ℝ≥0} {Y μ : ℂ → Ω → ℝ}
    (h : SourceDisjointWindows P ℱ D r R K γ σ τ Y μ) :
    Measurable (fun ω => ∫ z in D, (Y z ω-μ z ω)) :=
  ((h.joint_output.sub h.joint_mean).comp measurable_swap).stronglyMeasurable.integral_prod_right
    (f := fun ω z => Y z ω-μ z ω) |>.measurable

lemma window_source_integral_bounded {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {ℱ : Filtration ℝ≥0 mΩ}
    {D : Set ℂ} {r R K : ℝ} {γ : ℝ≥0 → Ω → ℂ}
    {σ τ : ℂ → Ω → WithTop ℝ≥0} {Y μ : ℂ → Ω → ℝ}
    (h : SourceDisjointWindows P ℱ D r R K γ σ τ Y μ) :
    ∃ B : ℝ, ∀ ω, ‖∫ z in D, (Y z ω-μ z ω)‖ ≤ B := by
  have hfin : volume D ≠ ∞ := (isBounded_ball.subset h.bounded_D).measure_lt_top.ne
  let : IsFiniteMeasure (volume.restrict D) := isFiniteMeasure_restrict.mpr hfin
  obtain ⟨M,hM⟩ := h.mean_bounded
  refine ⟨(K+M)*(volume.restrict D).real univ, fun ω => norm_integral_le_of_norm_le_const
    (Eventually.of_forall fun z => ?_)⟩
  calc
    _ ≤ ‖Y z ω‖+‖μ z ω‖ := norm_sub_le _ _
    _ = Y z ω+μ z ω := by rw [Real.norm_eq_abs, abs_of_nonneg (h.output_bound z ω).1,
      Real.norm_eq_abs, abs_of_nonneg (h.mean_nonneg z ω)]
    _ ≤ _ := add_le_add (h.output_bound z ω).2 (hM z ω)

lemma window_source_mgf {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsFiniteMeasure P] {ℱ : Filtration ℝ≥0 mΩ}
    {D : Set ℂ} {r R K : ℝ} {γ : ℝ≥0 → Ω → ℂ}
    {σ τ : ℂ → Ω → WithTop ℝ≥0} {Y μ : ℂ → Ω → ℝ}
    (h : SourceDisjointWindows P ℱ D r R K γ σ τ Y μ)
    {θ : ℝ} (hθ : 0 ≤ θ) {W : Ω → ℝ} (hW : Measurable[ℱ 0] W)
    (hW0 : ∀ ω, 0 ≤ W ω) (hWb : ∃ M, ∀ ω, W ω ≤ M) :
    (∫ ω, W ω * Real.exp (θ*∫ z in D, (Y z ω-μ z ω)) ∂P) ≤
      (∫ ω, W ω ∂P) * Real.exp (128*K^2*θ^2*R^2) := by
  rcases h.bound_nonneg.eq_or_lt with hK | hK
  · have hz (ω : Ω) : (∫ z in D, (Y z ω-μ z ω)) ≤ 0 := by
      apply integral_nonpos
      intro z
      change Y z ω-μ z ω≤0
      have := (h.output_bound z ω).2
      have := h.mean_nonneg z ω
      linarith
    have he (ω : Ω) : Real.exp (θ*∫ z in D, (Y z ω-μ z ω)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos hθ (hz ω))
    obtain ⟨M,hM⟩ := hWb
    have hWa : Measurable W := hW.mono (ℱ.le 0) le_rfl
    have hWi : Integrable W P := window_integrable_nonneg hWa hW0 hM
    have hli : Integrable (fun ω => W ω*Real.exp (θ*∫ z in D, (Y z ω-μ z ω))) P :=
      window_integrable_nonneg (hWa.mul ((window_source_integral_measurable h).const_mul θ).exp)
        (fun ω => mul_nonneg (hW0 ω) (Real.exp_pos _).le)
        (fun ω => ((mul_le_mul_of_nonneg_left (he ω) (hW0 ω)).trans_eq (mul_one _)).trans (hM ω))
    simp only [← hK, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
      zero_mul, Real.exp_zero, mul_one]
    exact integral_mono hli hWi (fun ω => (mul_le_mul_of_nonneg_left (he ω) (hW0 ω)).trans_eq (mul_one _))
  · exact window_source_mgf_pos h hθ hW hW0 hWb hK
lemma window_source_tail {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {ℱ : Filtration ℝ≥0 mΩ}
    {D : Set ℂ} {r R K : ℝ} {γ : ℝ≥0 → Ω → ℂ}
    {σ τ : ℂ → Ω → WithTop ℝ≥0} {Y μ : ℂ → Ω → ℝ}
    (h : SourceDisjointWindows P ℱ D r R K γ σ τ Y μ) {b : ℝ} (hb : 0 < b) :
    P {ω | b < ∫ z in D, (Y z ω-μ z ω)} ≤
      ENNReal.ofReal (Real.exp (-(1/512:ℝ)*b^2/(K^2*R^2))) := by
  rcases h.bound_nonneg.eq_or_lt with hK | hK
  · simp only [← hK, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul,
      div_zero, Real.exp_zero, ENNReal.ofReal_one]
    exact prob_le_one
  · let X (ω : Ω) := ∫ z in D, (Y z ω-μ z ω)
    let θ := b/(256*K^2*R^2)
    have hR : 0 < R := h.radius_pos.trans_le h.radius_le
    have hθ : 0 ≤ θ := by dsimp [θ]; positivity
    obtain ⟨B,hB⟩ := window_source_integral_bounded h
    have hXi : Integrable (fun ω => Real.exp (θ*X ω)) P :=
      window_integrable_nonneg ((window_source_integral_measurable h).const_mul θ).exp
        (fun ω => (Real.exp_pos _).le) (fun ω => Real.exp_le_exp.mpr
          (mul_le_mul_of_nonneg_left (le_abs_self _ |>.trans (hB ω)) hθ))
    have hmgf : mgf X P θ ≤ Real.exp (128*K^2*θ^2*R^2) := by
      have H := window_source_mgf h hθ (W := fun _ => 1) measurable_const (fun _ => zero_le_one) ⟨1,fun _ => le_rfl⟩
      simpa [mgf, X] using H
    apply (ENNReal.toReal_le_toReal (measure_ne_top _ _) ENNReal.ofReal_ne_top).mp
    rw [ENNReal.toReal_ofReal (Real.exp_pos _).le]
    change P.real {ω | b < X ω} ≤ _
    calc
      _ ≤ P.real {ω | b ≤ X ω} := by
        exact measureReal_mono (fun ω hω => (show b < X ω from hω).le) (measure_ne_top _ _)
      _ ≤ Real.exp (-θ*b)*mgf X P θ := measure_ge_le_exp_mul_mgf b hθ hXi
      _ ≤ Real.exp (-θ*b)*Real.exp (128*K^2*θ^2*R^2) :=
        mul_le_mul_of_nonneg_left hmgf (Real.exp_pos _).le
      _ = _ := by
        rw [← Real.exp_add]
        congr 1
        dsimp [θ]
        field_simp
        ring

end SLEExactGauge
end

end OAI
