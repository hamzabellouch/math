import OAI.Probability.DirectionalWalk.BridgeKernels

namespace OAI

open MeasureTheory ProbabilityTheory Filter Preorder
open scoped ENNReal BigOperators Topology

namespace DirectionalZeroOne

open scoped Classical

noncomputable def renewalPairMass {α : Type*} [MeasurableSpace α]
    (ν : Bool → Measure α) [∀ b, IsProbabilityMeasure (ν b)] (L : Bool → α → ℕ) (H : ℕ) : ℝ≥0∞ :=
  ∏ b : Bool, Measure.infinitePi (fun _ : ℕ => ν b) (renewalCut (L b) H)

lemma renewalPairMass_le_one {α : Type*} [MeasurableSpace α]
    (ν : Bool → Measure α) [∀ b, IsProbabilityMeasure (ν b)] (L : Bool → α → ℕ) (H : ℕ) :
    renewalPairMass ν L H ≤ 1 := Finset.prod_le_one (fun _ _ => prob_le_one)

lemma window_reference_llr {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (ν : Bool → Measure α) [∀ b, IsProbabilityMeasure (ν b)]
    (L : Bool → α → ℕ) (hL : ∀ b, ∀ᵐ a ∂ν b, 0 < L b a)
    (he : ∀ᵐ Z ∂twoTapeLaw ν, ∃ H, 0 < H ∧ Z ∈ commonCut L H)
    (k n : ℕ) [NeZero n]
    (hu : ∀ H b, Measure.infinitePi (fun _ : ℕ => ν b) (renewalCut (L b) H) ≠ 0) :
    let P := windowCommonLaw ν L k n
    let H := chunkHeight L
    let ρ := P.map (fun a => (H a,a))
    let Q := P.map H ⊗ₘ pairBridgeKernel ν L
    (fun a => llr ρ Q (H a,a)) =ᵐ[P] fun a =>
      Real.log (renewalPairMass ν L (H a)).toReal - Real.log (n : ℝ) + informationOf P H a := by
  dsimp only
  let P := windowCommonLaw ν L k n
  let H := chunkHeight L
  let ρ := P.map (fun a => (H a,a))
  let κ := pairBridgeKernel ν L
  let : IsMarkovKernel κ := pairBridgeKernel_markov ν L hu
  let : IsProbabilityMeasure ρ := probabilityMeasure_map (measurable_of_countable _).aemeasurable
  have hmap : MeasurePreserving (fun a => (H a,a)) P ρ := ⟨measurable_of_countable _,rfl⟩
  have hl := hmap.quasiMeasurePreserving.ae (llr_atom ρ (P.map H ⊗ₘ κ)
    (window_reference_ac ν L hL he k n hu))
  filter_upwards [hl,ae_atom_pos P,windowCommonLaw_ae_window ν L hL he k n] with a hl ha hw
  have hw0 : twoListWeight ν a ≠ 0 := by
    intro hz
    apply ha
    change windowCommonLaw ν L k n {a} = 0
    rw [windowCommonLaw_atom ν L hL he,ite_eq_left hw,hz,mul_zero]
  have hwfin : twoListWeight ν a ≠ ∞ := ENNReal.prod_ne_top (fun _ _ =>
    ENNReal.prod_ne_top (fun _ _ => measure_ne_top _ _))
  have hwp : 0 < (twoListWeight ν a).toReal := ENNReal.toReal_pos hw0 hwfin
  have hr0 : renewalPairMass ν L (H a) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun b _ => hu _ b)
  have hrfin : renewalPairMass ν L (H a) ≠ ∞ := ne_of_lt ((renewalPairMass_le_one ν L _).trans_lt (by simp))
  have hrp : 0 < (renewalPairMass ν L (H a)).toReal := ENNReal.toReal_pos hr0 hrfin
  have hpH : 0 < (P.map H).real {H a} := ENNReal.toReal_pos
    (ne_zero_of_lt ((pos_iff_ne_zero.mpr ha).trans_le (atom_le_map P H (measurable_of_countable _) a))) (by finiteness)
  have hρ : ρ.real {(H a,a)} = (1/(n : ℝ))*(twoListWeight ν a).toReal := by
    rw [measureReal_def,map_graph_atom]
    change (windowCommonLaw ν L k n {a}).toReal = _
    rw [windowCommonLaw_atom ν L hL he,ite_eq_left hw,ENNReal.toReal_mul,ENNReal.toReal_inv]
    simp
  have hQ : (P.map H ⊗ₘ κ).real {(H a,a)} =
      (P.map H).real {H a} * ((renewalPairMass ν L (H a)).toReal)⁻¹ * (twoListWeight ν a).toReal := by
    rw [measureReal_def,compProd_atom]
    change (_ * pairBridgeLaw ν L (H a) {a}).toReal = _
    rw [pairBridgeLaw_atom ν L hL (H a) a hw.1]
    simp only [ENNReal.toReal_mul,ENNReal.toReal_inv,measureReal_def,renewalPairMass,mul_assoc]
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne n
  rw [hl,hρ,hQ,Real.log_mul (one_div_ne_zero hn) hwp.ne',
    Real.log_mul (mul_ne_zero hpH.ne' (inv_ne_zero hrp.ne')) hwp.ne',
    Real.log_mul hpH.ne' (inv_ne_zero hrp.ne'),Real.log_inv,Real.log_div one_ne_zero hn,Real.log_one]
  change _ = _ + (-Real.log ((P.map H).real {H a}))
  ring

lemma window_reference_entropy_bound {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (ν : Bool → Measure α) [∀ b, IsProbabilityMeasure (ν b)]
    (L : Bool → α → ℕ) (hL : ∀ b, ∀ᵐ a ∂ν b, 0 < L b a)
    (he : ∀ᵐ Z ∂twoTapeLaw ν, ∃ H, 0 < H ∧ Z ∈ commonCut L H)
    (k n : ℕ) [NeZero n]
    (hu : ∀ H b, Measure.infinitePi (fun _ : ℕ => ν b) (renewalCut (L b) H) ≠ 0)
    (c : ℝ) (hc : 0 < c) (hlo : ∀ H, ENNReal.ofReal c ≤ renewalPairMass ν L H)
    (hH : Integrable (informationOf (windowCommonLaw ν L k n) (chunkHeight L)) (windowCommonLaw ν L k n)) :
    let P := windowCommonLaw ν L k n
    let H := chunkHeight L
    let ρ := P.map (fun a => (H a,a))
    let Q := P.map H ⊗ₘ pairBridgeKernel ν L
    InformationTheory.klDiv ρ Q ≠ ∞ ∧
      (InformationTheory.klDiv ρ Q).toReal ≤ entropyOf P H - Real.log (n : ℝ) := by
  dsimp only
  let P := windowCommonLaw ν L k n
  let H := chunkHeight L
  let ρ := P.map (fun a => (H a,a))
  let κ := pairBridgeKernel ν L
  let : IsMarkovKernel κ := pairBridgeKernel_markov ν L hu
  let : IsProbabilityMeasure ρ := probabilityMeasure_map (measurable_of_countable _).aemeasurable
  let Q := P.map H ⊗ₘ κ
  let : IsProbabilityMeasure (P.map H) := probabilityMeasure_map (measurable_of_countable _).aemeasurable
  let : IsProbabilityMeasure Q := inferInstance
  have hlow (h : ℕ) : c ≤ (renewalPairMass ν L h).toReal := by
    simpa only [ENNReal.toReal_ofReal (le_of_lt hc)] using
      ENNReal.toReal_mono (ne_of_lt ((renewalPairMass_le_one ν L h).trans_lt (by simp))) (hlo h)
  have hupp (h : ℕ) : (renewalPairMass ν L h).toReal ≤ 1 := by
    exact ENNReal.toReal_le_of_le_ofReal (by norm_num) (by simpa using renewalPairMass_le_one ν L h)
  have hlog (h : ℕ) : Real.log c ≤ Real.log (renewalPairMass ν L h).toReal ∧
      Real.log (renewalPairMass ν L h).toReal ≤ 0 :=
    ⟨Real.log_le_log hc (hlow h),Real.log_nonpos ENNReal.toReal_nonneg (hupp h)⟩
  have hi : Integrable (fun a => Real.log (renewalPairMass ν L (H a)).toReal) P := by
    apply (integrable_const |Real.log c|).mono' (measurable_of_countable _).aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun a => by
      rw [Real.norm_eq_abs,abs_of_nonpos (hlog _).2]
      exact (neg_le_neg (hlog _).1).trans (neg_le_abs _))
  have hid : (fun a => llr ρ Q (H a,a)) =ᵐ[P] fun a =>
      Real.log (renewalPairMass ν L (H a)).toReal - Real.log (n : ℝ) + informationOf P H a :=
    window_reference_llr ν L hL he k n hu
  have hii : Integrable (fun a => llr ρ Q (H a,a)) P :=
    ((hi.sub (integrable_const _)).add hH).congr hid.symm
  have hiρ : Integrable (llr ρ Q) ρ :=
    (integrable_map_measure (measurable_of_countable _).aestronglyMeasurable
      (measurable_of_countable _).aemeasurable).mpr hii
  have hac : ρ ≪ Q := window_reference_ac ν L hL he k n hu
  refine ⟨InformationTheory.klDiv_ne_top_iff.mpr ⟨hac,hiρ⟩,?_⟩
  have hkl := InformationTheory.toReal_klDiv hac hiρ
  simp only [probReal_univ,add_sub_cancel_right] at hkl
  rw [hkl,show (∫ x, llr ρ Q x ∂ρ) = ∫ a, llr ρ Q (H a,a) ∂P from
    integral_map_of_stronglyMeasurable (measurable_of_countable _) (measurable_of_countable _).stronglyMeasurable,
    integral_congr_ae hid]
  have hbound := integral_mono_ae ((hi.sub (integrable_const (Real.log (n : ℝ)))).add hH)
    (hH.sub (integrable_const (Real.log (n : ℝ))))
    (Filter.Eventually.of_forall (fun a => by
      dsimp only [Pi.add_apply,Pi.sub_apply]
      linarith [(hlog (H a)).2]))
  change (∫ a, Real.log (renewalPairMass ν L (H a)).toReal - Real.log (n : ℝ) + informationOf P H a ∂P) ≤
    ∫ a, informationOf P H a - Real.log (n : ℝ) ∂P at hbound
  rw [integral_sub hH (integrable_const (Real.log (n : ℝ)))] at hbound
  simpa only [integral_const,probReal_univ,smul_eq_mul,one_mul,entropyOf] using hbound

lemma commonDepth_integrable {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (ν : Bool → Measure α) [∀ b, IsProbabilityMeasure (ν b)]
    (L : Bool → α → ℕ) (hL : ∀ b, ∀ᵐ a ∂ν b, 0 < L b a)
    (he : ∀ᵐ Z ∂twoTapeLaw ν, ∃ H, 0 < H ∧ Z ∈ commonCut L H)
    (hi : Integrable (fun Z => (firstCommonWidth L Z : ℝ)) (twoTapeLaw ν)) (r : ℕ) :
    Integrable (fun Z => (commonDepth L Z r : ℝ)) (twoTapeLaw ν) := by
  simp only [commonDepth,Nat.cast_sum]
  apply integrable_finsetSum
  intro i _
  exact ((commonRestart_measurePreserving ν L hL he).iterate i).integrable_comp_of_integrable hi

lemma commonDepth_integral {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (ν : Bool → Measure α) [∀ b, IsProbabilityMeasure (ν b)]
    (L : Bool → α → ℕ) (hL : ∀ b, ∀ᵐ a ∂ν b, 0 < L b a)
    (he : ∀ᵐ Z ∂twoTapeLaw ν, ∃ H, 0 < H ∧ Z ∈ commonCut L H)
    (hi : Integrable (fun Z => (firstCommonWidth L Z : ℝ)) (twoTapeLaw ν)) (r : ℕ) :
    (∫ Z, (commonDepth L Z r : ℝ) ∂twoTapeLaw ν) =
      (r : ℝ) * ∫ Z, (firstCommonWidth L Z : ℝ) ∂twoTapeLaw ν := by
  simp only [commonDepth,Nat.cast_sum]
  have hii (i : ℕ) : Integrable (fun Z => (firstCommonWidth L ((commonRestart L)^[i] Z) : ℝ)) (twoTapeLaw ν) :=
    ((commonRestart_measurePreserving ν L hL he).iterate i).integrable_comp_of_integrable hi
  rw [integral_finsetSum (Finset.range r) (fun i _ => hii i)]
  have heq (i : ℕ) : (∫ Z, (firstCommonWidth L ((commonRestart L)^[i] Z) : ℝ) ∂twoTapeLaw ν) =
      ∫ Z, (firstCommonWidth L Z : ℝ) ∂twoTapeLaw ν := by
    have hp := (commonRestart_measurePreserving ν L hL he).iterate i
    have hm : Measurable (fun Z : TwoTape α => (firstCommonWidth L Z : ℝ)) :=
      (measurable_of_countable Nat.cast).comp (measurable_firstCommonWidth L)
    conv_rhs => rw [← hp.map_eq]
    exact (integral_map_of_stronglyMeasurable hp.measurable hm.stronglyMeasurable).symm
  simp_rw [heq]
  simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]

lemma nthCommonList_height {α : Type*} (L : Bool → α → ℕ) (Z : TwoTape α)
    (hZ : ∀ b i, 0 < L b (Z (b,i)))
    (he : ∀ r, ∃ H, 0 < H ∧ ((commonRestart L)^[r] Z) ∈ commonCut L H)
    (r : ℕ) : chunkHeight L (nthCommonList L r Z) = commonDepth L Z r := by
  have hc := (commonDepth_spec L Z hZ he r).1
  exact ((commonCutList_atom_iff L _ Z hZ (nthCommonList L r Z)).mp ⟨hc,rfl⟩).1 false

lemma nthCommonList_height_ae {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (ν : Bool → Measure α) [∀ b, IsProbabilityMeasure (ν b)]
    (L : Bool → α → ℕ) (hL : ∀ b, ∀ᵐ a ∂ν b, 0 < L b a)
    (he : ∀ᵐ Z ∂twoTapeLaw ν, ∃ H, 0 < H ∧ Z ∈ commonCut L H) (r : ℕ) :
    (fun Z => chunkHeight L (nthCommonList L r Z)) =ᵐ[twoTapeLaw ν] fun Z => commonDepth L Z r := by
  filter_upwards [ae_twoTape_prop ν (fun b a => 0 < L b a)
    (fun b => measurableSet_lt measurable_const (measurable_of_countable (L b))) hL,
    ae_common_iterates ν L hL he] with Z hZ hiter
  exact nthCommonList_height L Z hZ hiter r

lemma nthCommonLaw_height_integrable {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (ν : Bool → Measure α) [∀ b, IsProbabilityMeasure (ν b)]
    (L : Bool → α → ℕ) (hL : ∀ b, ∀ᵐ a ∂ν b, 0 < L b a)
    (he : ∀ᵐ Z ∂twoTapeLaw ν, ∃ H, 0 < H ∧ Z ∈ commonCut L H)
    (hi : Integrable (fun Z => (firstCommonWidth L Z : ℝ)) (twoTapeLaw ν)) (r : ℕ) :
    Integrable (fun a => (chunkHeight L a : ℝ)) (nthCommonLaw ν L r) := by
  apply (integrable_map_measure (measurable_of_countable _).aestronglyMeasurable
    (measurable_nthCommonList L r).aemeasurable).mpr
  apply (commonDepth_integrable ν L hL he hi r).congr
  filter_upwards [nthCommonList_height_ae ν L hL he r] with Z hZ
  change (commonDepth L Z r : ℝ) = (chunkHeight L (nthCommonList L r Z) : ℝ)
  exact_mod_cast hZ.symm

lemma nthCommonLaw_height_integral {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (ν : Bool → Measure α) [∀ b, IsProbabilityMeasure (ν b)]
    (L : Bool → α → ℕ) (hL : ∀ b, ∀ᵐ a ∂ν b, 0 < L b a)
    (he : ∀ᵐ Z ∂twoTapeLaw ν, ∃ H, 0 < H ∧ Z ∈ commonCut L H)
    (hi : Integrable (fun Z => (firstCommonWidth L Z : ℝ)) (twoTapeLaw ν)) (r : ℕ) :
    (∫ a, (chunkHeight L a : ℝ) ∂nthCommonLaw ν L r) =
      (r : ℝ) * ∫ Z, (firstCommonWidth L Z : ℝ) ∂twoTapeLaw ν := by
  rw [nthCommonLaw,integral_map_of_stronglyMeasurable (measurable_nthCommonList L r)
    (measurable_of_countable _).stronglyMeasurable,← commonDepth_integral ν L hL he hi r]
  apply integral_congr_ae
  filter_upwards [nthCommonList_height_ae ν L hL he r] with Z hZ
  exact_mod_cast hZ

lemma windowCommonLaw_height_integrable {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (ν : Bool → Measure α) [∀ b, IsProbabilityMeasure (ν b)]
    (L : Bool → α → ℕ) (hL : ∀ b, ∀ᵐ a ∂ν b, 0 < L b a)
    (he : ∀ᵐ Z ∂twoTapeLaw ν, ∃ H, 0 < H ∧ Z ∈ commonCut L H)
    (hi : Integrable (fun Z => (firstCommonWidth L Z : ℝ)) (twoTapeLaw ν)) (k n : ℕ) [NeZero n] :
    Integrable (fun a => (chunkHeight L a : ℝ)) (windowCommonLaw ν L k n) := by
  apply Integrable.smul_measure _ (ENNReal.inv_ne_top.mpr (by exact_mod_cast NeZero.ne n))
  apply integrable_finsetSum_measure.mpr
  intro i _
  exact nthCommonLaw_height_integrable ν L hL he hi (k+i)

lemma windowCommonLaw_height_mean {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (ν : Bool → Measure α) [∀ b, IsProbabilityMeasure (ν b)]
    (L : Bool → α → ℕ) (hL : ∀ b, ∀ᵐ a ∂ν b, 0 < L b a)
    (he : ∀ᵐ Z ∂twoTapeLaw ν, ∃ H, 0 < H ∧ Z ∈ commonCut L H)
    (hi : Integrable (fun Z => (firstCommonWidth L Z : ℝ)) (twoTapeLaw ν)) (k n : ℕ) [NeZero n] :
    (∫ a, (chunkHeight L a : ℝ) ∂windowCommonLaw ν L k n) ≤
      ((k+n : ℕ) : ℝ) * ∫ Z, (firstCommonWidth L Z : ℝ) ∂twoTapeLaw ν := by
  rw [windowCommonLaw,integral_smul_measure,integral_finsetSum_measure
    (μ := fun i : Fin n => nthCommonLaw ν L (k+i)) (s := Finset.univ)
    (fun i _ => nthCommonLaw_height_integrable ν L hL he hi (k+i))]
  simp only [ENNReal.toReal_inv,ENNReal.toReal_natCast,smul_eq_mul]
  simp_rw [nthCommonLaw_height_integral ν L hL he hi]
  have hm : 0 ≤ ∫ Z, (firstCommonWidth L Z : ℝ) ∂twoTapeLaw ν := integral_nonneg (fun _ => Nat.cast_nonneg _)
  have hn : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  calc
    _ ≤ (n : ℝ)⁻¹ * ∑ _ : Fin n,
        ((k+n : ℕ) : ℝ) * ∫ Z, (firstCommonWidth L Z : ℝ) ∂twoTapeLaw ν := by
      apply mul_le_mul_of_nonneg_left _ (le_of_lt (inv_pos.mpr hn))
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.add_le_add_left (le_of_lt i.isLt) k) hm
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul];field_simp

lemma window_entropy_uniform {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (ν : Bool → Measure α) [∀ b, IsProbabilityMeasure (ν b)]
    (L : Bool → α → ℕ) (hL : ∀ b, ∀ᵐ a ∂ν b, 0 < L b a)
    (he : ∀ᵐ Z ∂twoTapeLaw ν, ∃ H, 0 < H ∧ Z ∈ commonCut L H)
    (hi : Integrable (fun Z => (firstCommonWidth L Z : ℝ)) (twoTapeLaw ν)) (k n : ℕ) [NeZero n]
    (hk : k ≤ 7*n) :
    Integrable (informationOf (windowCommonLaw ν L k n) (chunkHeight L)) (windowCommonLaw ν L k n) ∧
      entropyOf (windowCommonLaw ν L k n) (chunkHeight L) - Real.log (n : ℝ) ≤
        1 + Real.log (8 * ((∫ Z, (firstCommonWidth L Z : ℝ) ∂twoTapeLaw ν)+1)+1) := by
  let m := ∫ Z, (firstCommonWidth L Z : ℝ) ∂twoTapeLaw ν
  have hm : 0 ≤ m := integral_nonneg (fun _ => Nat.cast_nonneg _)
  have hn : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hn1 : 1 ≤ (n : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne n)
  let A := 8*(m+1)
  have hA : 0 < A := by dsimp [A];positivity
  have hmean : (∫ a, (chunkHeight L a : ℝ) ∂windowCommonLaw ν L k n) ≤ A*n := by
    calc
      _ ≤ ((k+n : ℕ) : ℝ)*m := windowCommonLaw_height_mean ν L hL he hi k n
      _ ≤ (8*(n:ℝ))*m := mul_le_mul_of_nonneg_right (by exact_mod_cast (show k+n ≤ 8*n by omega)) hm
      _ ≤ A*n := by dsimp [A];nlinarith
  have hh := entropyOf_nat_moment (windowCommonLaw ν L k n) (chunkHeight L)
    (windowCommonLaw_height_integrable ν L hL he hi k n) (A*n) (mul_pos hA hn) hmean
  refine ⟨hh.1,?_⟩
  have hlog : Real.log (A*(n:ℝ)+1) ≤ Real.log (A+1) + Real.log (n:ℝ) := by
    rw [← Real.log_mul (by positivity : A+1 ≠ 0) (ne_of_gt hn)]
    exact Real.log_le_log (by positivity) (by nlinarith)
  change _ ≤ 1+Real.log (A+1)
  linarith [hh.2]

lemma window_kl_uniform {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (ν : Bool → Measure α) [∀ b, IsProbabilityMeasure (ν b)]
    (L : Bool → α → ℕ) (hL : ∀ b, ∀ᵐ a ∂ν b, 0 < L b a)
    (he : ∀ᵐ Z ∂twoTapeLaw ν, ∃ H, 0 < H ∧ Z ∈ commonCut L H)
    (hi : Integrable (fun Z => (firstCommonWidth L Z : ℝ)) (twoTapeLaw ν))
    (hu : ∀ H b, Measure.infinitePi (fun _ : ℕ => ν b) (renewalCut (L b) H) ≠ 0)
    (c : ℝ) (hc : 0 < c) (hlo : ∀ H, ENNReal.ofReal c ≤ renewalPairMass ν L H)
    (k n : ℕ) [NeZero n] (hk : k ≤ 7*n) :
    let P := windowCommonLaw ν L k n
    let H := chunkHeight L
    let ρ := P.map (fun a => (H a,a))
    let Q := P.map H ⊗ₘ pairBridgeKernel ν L
    InformationTheory.klDiv ρ Q ≠ ∞ ∧
      (InformationTheory.klDiv ρ Q).toReal ≤
        1 + Real.log (8 * ((∫ Z, (firstCommonWidth L Z : ℝ) ∂twoTapeLaw ν)+1)+1) := by
  have hh := window_entropy_uniform ν L hL he hi k n hk
  have hd := window_reference_entropy_bound ν L hL he k n hu c hc hlo hh.1
  exact ⟨hd.1, hd.2.trans hh.2⟩

lemma klDiv_map_equiv {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν] (e : α ≃ᵐ β) :
    InformationTheory.klDiv (μ.map e) (ν.map e) = InformationTheory.klDiv μ ν := by
  apply le_antisymm (InformationTheory.klDiv_map_le μ ν e.measurable)
  have h := InformationTheory.klDiv_map_le (μ.map e) (ν.map e) e.symm.measurable
  simpa only [Measure.map_map e.symm.measurable e.measurable,
    show e.symm ∘ e = id from funext e.symm_apply_apply,Measure.map_id] using h

lemma klDiv_product {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ ν : Measure α) (ρ η : Measure β) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    [IsProbabilityMeasure ρ] [IsProbabilityMeasure η] :
    InformationTheory.klDiv (μ.prod ρ) (ν.prod η) =
      InformationTheory.klDiv μ ν + InformationTheory.klDiv ρ η := by
  have h := InformationTheory.klDiv_compProd_eq_add μ ν (Kernel.const α ρ) (Kernel.const α η)
  simp only [Measure.compProd_const] at h
  rw [h]
  congr 1
  have hs := klDiv_map_equiv (μ.prod ρ) (μ.prod η) MeasurableEquiv.prodComm
  change InformationTheory.klDiv ((μ.prod ρ).map Prod.swap) ((μ.prod η).map Prod.swap) = _ at hs
  rw [Measure.prod_swap,Measure.prod_swap] at hs
  rw [← hs,← Measure.compProd_const,← Measure.compProd_const]
  exact InformationTheory.klDiv_compProd_left ρ η (Kernel.const β μ)

lemma product_graph {α β γ δ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] [MeasurableSpace δ]
    (μ : Measure α) (ν : Measure β) [SFinite μ] [SFinite ν]
    (f : α → γ) (g : β → δ) (hf : Measurable f) (hg : Measurable g) :
    (μ.prod ν).map (fun a => ((f a.1,g a.2),a)) =
      ((μ.map (fun a => (f a,a))).prod (ν.map (fun b => (g b,b)))).map
        (fun p => ((p.1.1,p.2.1),(p.1.2,p.2.2))) := by
  rw [Measure.map_prod_map μ ν (show Measurable (fun a => (f a,a)) from hf.prodMk measurable_id)
    (show Measurable (fun b => (g b,b)) from hg.prodMk measurable_id),
    Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

end DirectionalZeroOne

end OAI
