import OAI.Analysis.RotationWeights.TrialBounds

namespace OAI

noncomputable section

namespace CircleSampling

universe uι uκ uP uτ

open MeasureTheory
open scoped ENNReal NNReal ComplexInnerProductSpace BigOperators
open MeasureTheory Filter Set Submodule
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ComplexInnerProductSpace
open MeasureTheory Filter Set
open Set
open scoped ComplexInnerProductSpace
open Set
open scoped ComplexInnerProductSpace
open MeasureTheory Set Filter Topology
open scoped BigOperators ComplexConjugate
open MeasureTheory Set Filter
open scoped BigOperators ENNReal
open Filter Set
open scoped Topology
open Filter Set
open scoped Topology
open Set MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter Set
open scoped Topology
open Set MeasureTheory
open scoped ENNReal Classical

section
open scoped Topology
lemma continuousAt_repr {x : CircleX} (hx : x ≠ 0) : ContinuousAt repr x :=
  continuous_subtype_val.continuousAt.comp (AddCircle.continuousAt_equivIco 1 0 (by simpa using hx))
lemma continuous_delta : Continuous delta := by unfold delta; fun_prop
lemma repr_pos {x : CircleX} (hx : x ≠ 0) : 0 < repr x := by
  apply (repr_mem x).1.lt_of_ne'
  intro h
  apply hx
  rw [← coe_repr x,h]
  simp

lemma continuousAt_weight {ℓ α s t : ℝ} (hℓ : 0 < ℓ) (hα : 0 < α)
    (hαs : α ≠ delta s) (ht : 0 < t) (hst : t ≠ ℓ*delta s) :
    ContinuousAt (fun z : ℝ × ℝ => weight ℓ α z.1 z.2) (s,t) := by
  have hd := (continuous_delta.comp continuous_fst).continuousAt (x:=(s,t))
  have ht' := continuous_snd.continuousAt (x:=(s,t))
  by_cases ha : α ≤ delta s
  · have had : α < delta s := lt_of_le_of_ne ha hαs
    have hea : ∀ᶠ z : ℝ × ℝ in 𝓝 (s,t), α ≤ delta z.1 := by
      filter_upwards [hd.eventually (lt_mem_nhds had)] with z hz
      exact hz.le
    have het : ∀ᶠ z : ℝ × ℝ in 𝓝 (s,t), 0 < z.2 := ht'.eventually (lt_mem_nhds ht)
    by_cases hb : t < ℓ*delta s
    · have heb : ∀ᶠ z : ℝ × ℝ in 𝓝 (s,t), z.2 < ℓ*delta z.1 :=
        (ht'.sub (hd.const_mul ℓ)).eventually (gt_mem_nhds (by linarith : t-ℓ*delta s < 0))
          |>.mono fun z h => by change z.2-ℓ*delta z.1 < 0 at h; linarith
      have heq : (fun z : ℝ × ℝ => weight ℓ α z.1 z.2) =ᶠ[𝓝 (s,t)]
          (fun z => 1/(ℓ*delta z.1)) := by
        filter_upwards [hea,het,heb] with z ha ht hb
        simp only [weight,ha,ht,hb,and_self,ite_true]
      exact (continuousAt_const.div (hd.const_mul ℓ)
        (mul_pos hℓ (hα.trans_le ha)).ne').congr_of_eventuallyEq heq
    · have hb' : ℓ*delta s < t := lt_of_le_of_ne (le_of_not_gt hb) (Ne.symm hst)
      have heb : ∀ᶠ z : ℝ × ℝ in 𝓝 (s,t), ℓ*delta z.1 < z.2 := by
        filter_upwards [(ht'.sub (hd.const_mul ℓ)).eventually (lt_mem_nhds (sub_pos.mpr hb'))] with z hz
        exact sub_pos.mp hz
      have heq : (fun z : ℝ × ℝ => weight ℓ α z.1 z.2) =ᶠ[𝓝 (s,t)] (fun _ => (0:ℝ)) := by
        filter_upwards [heb] with z hz
        simp [weight,not_lt_of_ge hz.le]
      exact continuousAt_const.congr_of_eventuallyEq heq
  · have ha' : delta s < α := lt_of_not_ge ha
    have heq : (fun z : ℝ × ℝ => weight ℓ α z.1 z.2) =ᶠ[𝓝 (s,t)] (fun _ => (0:ℝ)) := by
      filter_upwards [hd.eventually (gt_mem_nhds ha')] with z hz
      change delta z.1 < α at hz
      simp [weight,not_le_of_gt hz]
    exact continuousAt_const.congr_of_eventuallyEq heq

lemma ae_repr_ne (r : ℝ) : ∀ᵐ s : CircleX, repr s ≠ r := by
  have he : ∀ᵐ s : CircleX, s ≠ (r:CircleX) := by
    rw [ae_iff]
    simpa only [not_not,Set.ofPred_eq_eq_singleton] using volume_singleton_zero (r:CircleX)
  filter_upwards [he] with s hs heq
  exact hs (by rw [← coe_repr s,heq])
lemma ae_delta_ne (r : ℝ) : ∀ᵐ s : CircleX, delta (repr s) ≠ r := by
  filter_upwards [ae_repr_ne r,ae_repr_ne (1-r)] with s hs ht h
  unfold delta at h
  rcases le_total (repr s) (1-repr s) with hle | hle
  · exact hs (by rwa [min_eq_left hle] at h)
  · exact ht (by rw [min_eq_right hle] at h; linarith)

lemma ae_continuousAt_uPos {ℓ α : ℝ} (hℓ : 0 < ℓ) (hα : 0 < α)
    {t : CircleX} (ht : t ≠ 0) :
    ∀ᵐ s : CircleX, ContinuousAt (Function.uncurry (uPos ℓ α)) (s,t) := by
  have he : ∀ᵐ s : CircleX, s ≠ 0 := by
    rw [ae_iff]
    simpa only [not_not,Set.ofPred_eq_eq_singleton] using volume_singleton_zero (0:CircleX)
  filter_upwards [he,ae_delta_ne α,ae_delta_ne (repr t/ℓ)] with s hs hαs hts
  have hst : repr t ≠ ℓ*delta (repr s) := by
    intro h
    apply hts
    apply (eq_div_iff hℓ.ne').mpr
    linarith only [h]
  have hcmap : ContinuousAt (fun z : CircleX × CircleX => (repr z.1,repr z.2)) (s,t) :=
    ((continuousAt_repr hs).comp (f:=Prod.fst) (x:=(s,t)) continuousAt_fst).prodMk
      ((continuousAt_repr ht).comp (f:=Prod.snd) (x:=(s,t)) continuousAt_snd)
  exact (continuousAt_weight hℓ hα hαs.symm (repr_pos ht) hst).comp (f:=fun z : CircleX × CircleX => (repr z.1,repr z.2)) (x:=(s,t)) hcmap

lemma ae_continuousAt_uNeg {ℓ α : ℝ} (hℓ : 0 < ℓ) (hα : 0 < α)
    {t : CircleX} (ht : t ≠ 0) :
    ∀ᵐ s : CircleX, ContinuousAt (Function.uncurry (uNeg ℓ α)) (s,t) := by
  have h := (measurePreserving_sub_right volume t).quasiMeasurePreserving.ae (ae_continuousAt_uPos hℓ hα ht)
  filter_upwards [h] with s hs
  exact hs.comp (f:=fun z : CircleX × CircleX => (z.1-z.2,z.2)) (x:=(s,t))
    ((continuousAt_fst.sub continuousAt_snd).prodMk continuousAt_snd)
end

section
open ContinuousCircleWeight ContinuousCircleWeight.Sampling Filter
open scoped Topology
variable {ι : Type uι} {κ : Type uκ} [Fintype ι] [Fintype κ] [Nonempty κ]
lemma ae_continuousAt_orientedWeight (positive : Bool) {ℓ α : ℝ} (hℓ : 0 < ℓ) (hα : 0 < α)
    {t : CircleX} (ht : t ≠ 0) :
    ∀ᵐ s : CircleX, ContinuousAt (Function.uncurry (orientedWeight positive ℓ α)) (s,t) := by
  cases positive
  · exact ae_continuousAt_uNeg hℓ hα ht
  · exact ae_continuousAt_uPos hℓ hα ht

omit [Nonempty κ] in
lemma ae_continuousAt_idealAverage (positive : Bool) {ℓ α : ℝ} (hℓ : 0 < ℓ) (hα : 0 < α)
    (c : κ → ℝ) (γ : ι → ℝ) (hγ : ∀ n i, ((c n*γ i:ℝ):CircleX) ≠ 0) :
    ∀ᵐ s : ι → CircleX ∂Measure.pi (fun _ => volume),
      ContinuousAt (fun z : (ι → CircleX) × (ι → ℝ) => idealAverage positive ℓ α c z.1 z.2) (s,γ) := by
  have hh : ∀ᵐ s : ι → CircleX ∂Measure.pi (fun _ => volume), ∀ n i,
      ContinuousAt (Function.uncurry (orientedWeight positive ℓ α)) (s i,((c n*γ i:ℝ):CircleX)) := by
    apply ae_all_iff.mpr
    intro n
    apply ae_all_iff.mpr
    intro i
    exact (measurePreserving_eval (fun _ : ι => (volume : Measure CircleX)) i).quasiMeasurePreserving.ae
      (ae_continuousAt_orientedWeight positive hℓ hα (hγ n i))
  filter_upwards [hh] with s hs
  unfold idealAverage
  apply ContinuousAt.const_mul
  apply tendsto_finsetSum
  intro n _
  apply tendsto_finsetProd
  intro i _
  have hm : Continuous (fun z : (ι → CircleX) × (ι → ℝ) => (z.1 i,((c n*z.2 i:ℝ):CircleX))) := by fun_prop
  exact (hs n i).comp (f:=fun z : (ι → CircleX) × (ι → ℝ) => (z.1 i,((c n*z.2 i:ℝ):CircleX))) (x:=(s,γ)) hm.continuousAt

lemma squared_ideal_test_bound (positive : Bool) {ℓ α : ℝ} (hℓ : 0 < ℓ) (hα : 0 < α)
    (c : κ → ℝ) (s : ι → CircleX) (γ : ι → ℝ) :
    ‖Complex.ofReal ((idealAverage positive ℓ α c s γ-1)^2)‖ ≤ ((1/(ℓ*α))^(Fintype.card ι)+1)^2 := by
  rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _),← sq_abs (idealAverage positive ℓ α c s γ-1)]
  apply (sq_le_sq₀ (abs_nonneg _) (by positivity)).mpr
  rw [abs_le]
  have h := idealAverage_bounds positive hℓ hα c s γ
  constructor <;> linarith [pow_nonneg (by positivity : 0 ≤ 1/(ℓ*α)) (Fintype.card ι)]

lemma ideal_sampling_tendsto {P : Type uP} [MetricSpace P] [CompactSpace P]
    [MeasurableSpace P] [BorelSpace P] {r : ℕ}
    (q : ℕ → ℕ → ℤ) (hq : ∀ n i, i < r → 0 < q n i)
    (hsep : ∀ i, i+1 < r → Tendsto (fun n => (q n (i+1):ℝ)/q n i) atTop atTop)
    {bs : ℕ → P} {b : P} (hb : Tendsto bs atTop (𝓝 b))
    (β : P → Fin r → ℝ) (hβ : Continuous β)
    (positive : Bool) {ℓ α : ℝ} (hℓ : 0 < ℓ) (hα : 0 < α)
    (c : κ → ℝ) (hphase : ∀ n i, ((c n*β b i:ℝ):CircleX) ≠ 0) :
    Tendsto (fun n => ∫ x : CircleX,
      (idealAverage positive ℓ α c (characterCurve (fun i : Fin r => q n i) x) (β (bs n))-1)^2)
      atTop (𝓝 (idealEnergy positive ℓ α c (β b))) := by
  have hvol : (AddCircle.haarAddCircle : Measure CircleX) = volume := by
    simpa using (AddCircle.volume_eq_smul_haarAddCircle (T:=(1:ℝ))).symm
  have htorus : (torusHaar (ι:=Fin r) : Measure (Fin r → CircleX)) = Measure.pi (fun _ => volume) := by
    change Measure.pi (fun _ => AddCircle.haarAddCircle) = _
    simp_rw [hvol]
  let Φ := fun z : (Fin r → CircleX) × P => Complex.ofReal ((idealAverage positive ℓ α c z.1 (β z.2)-1)^2)
  have hΦ : Measurable Φ := by
    exact Complex.measurable_ofReal.comp
      (((measurable_idealAverage positive ℓ α c).comp
        (measurable_fst.prodMk (hβ.measurable.comp measurable_snd))).sub measurable_const |>.pow_const 2)
  have hc : ∀ᵐ z ∂(withParameter (torusHaar (ι:=Fin r)) b : Measure _), ContinuousAt Φ z := by
    rw [withParameter,ProbabilityMeasure.toMeasure_map]
    apply ae_map_iff (measurable_id.prodMk measurable_const).aemeasurable (measurableSet_of_continuousAt Φ) |>.mpr
    rw [htorus]
    change ∀ᵐ s ∂Measure.pi (fun _ : Fin r => (volume : Measure CircleX)), ContinuousAt Φ (s,b)
    filter_upwards [ae_continuousAt_idealAverage positive hℓ hα c (β b) hphase] with s hs
    have hm := hs.comp (f:=fun z : (Fin r → CircleX) × P => (z.1,β z.2)) (x:=(s,b))
      (continuous_fst.prodMk (hβ.comp continuous_snd)).continuousAt
    exact Complex.continuous_ofReal.continuousAt.comp ((hm.sub continuousAt_const).pow 2)
  have ht := circle_approximation_with_parameters q hq hsep hb Φ hΦ hc
    (((1/(ℓ*α))^r+1)^2) (fun z => by simpa only [Φ,Fintype.card_fin] using squared_ideal_test_bound positive hℓ hα c z.1 (β z.2))
  have ht' := Complex.continuous_re.continuousAt.tendsto.comp ht
  simpa only [Function.comp_def,Φ,integral_complex_ofReal,Complex.ofReal_re,idealEnergy,htorus,hvol] using ht'
end

open Filter
open scoped Topology
section
lemma finite_accuracy_of_sequential {P : Type uP} [MetricSpace P]
    {r : ℕ} (b : P) (T : (ℕ → ℤ) → P → ℝ) {L η : ℝ} (hL : L < η)
    (hseq : ∀ (q : ℕ → ℕ → ℤ), (∀ n i, i < r → 0 < q n i) →
      (∀ i, i+1 < r → Tendsto (fun n => (q n (i+1):ℝ)/q n i) atTop atTop) →
      ∀ (bs : ℕ → P), Tendsto bs atTop (𝓝 b) →
        Tendsto (fun n => T (q n) (bs n)) atTop (𝓝 L)) :
    ∃ M : ℕ, ∃ δ : ℝ, 0 < δ ∧ ∀ (q : ℕ → ℤ) (β : P),
      (∀ i, i < r → 0 < q i) →
      (∀ i, i+1 < r → (M:ℝ) ≤ (q (i+1):ℝ)/q i) →
      dist β b < δ → T q β < η := by
  classical
  by_contra! h
  have hex (n : ℕ) : ∃ (q : ℕ → ℤ) (β : P),
      (∀ i, i < r → 0 < q i) ∧
      (∀ i, i+1 < r → (n:ℝ) ≤ (q (i+1):ℝ)/q i) ∧
      dist β b < 1/((n:ℝ)+1) ∧ η ≤ T q β := by
    exact h n (1/((n:ℝ)+1)) (by positivity)
  choose q bs hq hsep hdist hbad using hex
  have hq' : ∀ i, i+1 < r → Tendsto (fun n => (q n (i+1):ℝ)/q n i) atTop atTop := by
    intro i hi
    exact tendsto_atTop_mono (fun n => hsep n i hi) tendsto_natCast_atTop_atTop
  have hb : Tendsto bs atTop (𝓝 b) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    apply squeeze_zero (fun _ => dist_nonneg) (fun n => (hdist n).le)
    simpa only [one_div,Function.comp_def] using tendsto_inv_atTop_zero.comp
      (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
  have hh := (hseq q hq hq' bs hb).eventually (gt_mem_nhds hL)
  obtain ⟨n,hn⟩ := hh.exists
  exact (not_lt_of_ge (hbad n)) hn

open ContinuousCircleWeight.Sampling
open scoped Topology
abbrev PhaseCube (r : ℕ) := Fin r → Set.Icc (0:ℝ) 1
lemma sampling_finite_accuracy {r : ℕ} {κ : Type uκ} [Fintype κ] [Nonempty κ]
    (positive : Bool) {ℓ α : ℝ} (hℓ : 0 < ℓ) (hα : 0 < α)
    (c : κ → ℝ) (γ : PhaseCube r)
    (hphase : ∀ n i, ((c n*(γ i:ℝ):ℝ):CircleX) ≠ 0)
    {η : ℝ} (hη : idealEnergy positive ℓ α c (fun i => (γ i:ℝ)) < η) :
    ∃ M : ℕ, ∃ δ : ℝ, 0 < δ ∧ ∀ (q : ℕ → ℤ) (β : PhaseCube r),
      (∀ i, i < r → 0 < q i) →
      (∀ i, i+1 < r → (M:ℝ) ≤ (q (i+1):ℝ)/q i) →
      dist β γ < δ →
      (∫ x : CircleX, (idealAverage positive ℓ α c (characterCurve (fun i : Fin r => q i) x)
        (fun i => (β i:ℝ))-1)^2) < η := by
  apply finite_accuracy_of_sequential γ _ hη
  intro q hq hsep bs hb
  exact ideal_sampling_tendsto q hq hsep hb (fun β : PhaseCube r => fun i => (β i:ℝ))
    (by fun_prop) positive hℓ hα c hphase
end

open Set Filter
open scoped Topology
section
lemma closed_interval_in_open {O : Set ℝ} (hO : IsOpen O) (hne : O.Nonempty) :
    ∃ a b : ℝ, a < b ∧ Icc a b ⊆ O := by
  obtain ⟨x,hx⟩ := hne
  obtain ⟨a,b,⟨ha,hb⟩,hab⟩ := mem_nhds_iff_exists_Ioo_subset.mp (hO.mem_nhds hx)
  refine ⟨(a+x)/2,(x+b)/2,by linarith,?_⟩
  intro y hy
  apply hab
  exact ⟨by linarith [hy.1],by linarith [hy.2]⟩

lemma fractional_interval {a b u v q : ℝ} (_hab : a < b) (hq : 0 < q)
    (hlong : 2 < q*(b-a)) (hu : 0 ≤ u) (hv : v ≤ 1) (huv : u < v) :
    ∃ c d : ℝ, c < d ∧ Icc c d ⊆ Ioo a b ∧
      ∀ x∈Icc c d, Int.fract (q*x) ∈ Ioo u v := by
  let t := (u+v)/2
  have ht : t∈Ioo u v := ⟨by dsimp [t]; linarith,by dsimp [t]; linarith⟩
  have ht0 : 0 < t := lt_of_le_of_lt hu ht.1
  have ht1 : t < 1 := lt_of_lt_of_le ht.2 hv
  let x := ((⌊q*a⌋:ℝ)+1+t)/q
  have hqx : q*x = (⌊q*a⌋:ℝ)+1+t := by dsimp [x]; field_simp
  have hxa : a < x := by
    apply (lt_div_iff₀ hq).mpr
    have h := Int.lt_floor_add_one (q*a)
    nlinarith
  have hxb : x < b := by
    apply (div_lt_iff₀ hq).mpr
    have h := Int.floor_le (q*a)
    nlinarith
  have hfract : Int.fract (q*x)=t := by
    rw [hqx,add_comm _ t,← Int.cast_one,← Int.cast_add,Int.fract_add_intCast]
    exact Int.fract_eq_self.mpr ⟨ht0.le,ht1⟩
  have hne : q*x ≠ (⌊q*x⌋:ℝ) := by
    intro he
    have hz : Int.fract (q*x)=0 := by rw [he,Int.fract_intCast]
    linarith
  have hc : ContinuousAt (fun z : ℝ => Int.fract (q*z)) x :=
    (continuousAt_fract hne).comp (by fun_prop)
  have hU : Ioo a b ∩ (fun z : ℝ => Int.fract (q*z)) ⁻¹' Ioo u v ∈ 𝓝 x :=
    inter_mem (Ioo_mem_nhds hxa hxb) (hc.preimage_mem_nhds (by rw [hfract]; exact Ioo_mem_nhds ht.1 ht.2))
  obtain ⟨c,d,⟨hc,hd⟩,hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp hU
  refine ⟨(c+x)/2,(x+d)/2,by linarith,?_,?_⟩
  · intro z hz
    exact (hsub ⟨by linarith [hz.1],by linarith [hz.2]⟩).1
  · intro z hz
    exact (hsub ⟨by linarith [hz.1],by linarith [hz.2]⟩).2

lemma divisible_frequency_interval {a b u v : ℝ} (hab : a < b)
    (hu : 0 ≤ u) (hv : v ≤ 1) (huv : u < v) {p : ℕ} (hp : 0 < p) (M : ℝ) :
    ∃ q : ℕ, 0 < q ∧ p ∣ q ∧ M < (q:ℝ)/p ∧
      ∃ c d : ℝ, c < d ∧ Icc c d ⊆ Ioo a b ∧
        ∀ x∈Icc c d, Int.fract ((q:ℝ)*x)∈Ioo u v := by
  obtain ⟨L,hL⟩ := exists_nat_gt (max (max M 1) (2/((p:ℝ)*(b-a))))
  have hpR : 0 < (p:ℝ) := Nat.cast_pos.mpr hp
  have hL1 : 1 < (L:ℝ) := lt_of_le_of_lt (le_trans (le_max_right M 1) (le_max_left _ _)) hL
  have hL0 : 0 < L := by exact_mod_cast (lt_trans (by norm_num : (0:ℝ)<1) hL1)
  have hM : M < (L:ℝ) := lt_of_le_of_lt (le_trans (le_max_left M 1) (le_max_left _ _)) hL
  have hlong : 2 < (p*L:ℕ)* (b-a) := by
    have h := lt_of_le_of_lt (le_max_right (max M 1) (2/((p:ℝ)*(b-a)))) hL
    have hh := (div_lt_iff₀ (mul_pos hpR (sub_pos.mpr hab))).mp h
    push_cast
    nlinarith
  obtain ⟨c,d,hcd,hsub,hfr⟩ := fractional_interval hab
    (show 0 < ((p*L:ℕ):ℝ) by positivity) hlong hu hv huv
  refine ⟨p*L,Nat.mul_pos hp hL0, dvd_mul_right p L,?_,c,d,hcd,hsub,hfr⟩
  simpa only [Nat.cast_mul,mul_div_cancel_left₀ _ hpR.ne'] using hM

lemma finite_frequency_realization (m : ℕ) (u v : ℕ → ℝ)
    (hu : ∀ i < m, 0 ≤ u i) (hv : ∀ i < m, v i ≤ 1) (huv : ∀ i < m, u i < v i)
    {a b : ℝ} (hab : a < b) {p : ℕ} (hp : 0 < p) (M : ℝ) :
    ∃ q : ℕ → ℕ, q 0=p ∧ (∀ i ≤ m, 0 < q i) ∧
      (∀ i < m, q i ∣ q (i+1) ∧ M < (q (i+1):ℝ)/q i) ∧
      ∃ c d : ℝ, c < d ∧ Icc c d ⊆ Ioo a b ∧
        ∀ i < m, ∀ x∈Icc c d, Int.fract ((q (i+1):ℝ)*x)∈Ioo (u i) (v i) := by
  induction m with
  | zero =>
    refine ⟨fun _ => p,rfl,fun _ _ => hp,by simp, (2*a+b)/3,(a+2*b)/3,by linarith,?_,by simp⟩
    intro x hx
    exact ⟨by linarith [hx.1],by linarith [hx.2]⟩
  | succ m ih =>
    obtain ⟨q,hq0,hqp,hqM,c,d,hcd,hsub,hfr⟩ :=
      ih (fun i hi => hu i (by omega)) (fun i hi => hv i (by omega)) (fun i hi => huv i (by omega))
    obtain ⟨r,hr,hrdiv,hrM,e,f,hef,hefs,hphase⟩ :=
      divisible_frequency_interval hcd (hu m (by omega)) (hv m (by omega)) (huv m (by omega)) (hqp m le_rfl) M
    refine ⟨Function.update q (m+1) r,?_,?_,?_,e,f,hef,?_,?_⟩
    · simpa using hq0
    · intro i hi
      by_cases he : i=m+1
      · subst i; simpa
      · rw [Function.update_of_ne he]
        exact hqp i (by omega)
    · intro i hi
      by_cases he : i=m
      · subst i
        simpa [Function.update_of_ne (show m ≠ m+1 by omega)] using And.intro hrdiv hrM
      · rw [Function.update_of_ne (show i≠m+1 by omega),Function.update_of_ne (show i+1≠m+1 by omega)]
        exact hqM i (by omega)
    · exact fun x hx => hsub ⟨(hefs hx).1.le,(hefs hx).2.le⟩
    · intro i hi x hx
      by_cases he : i=m
      · subst i
        simpa using hphase x hx
      · rw [Function.update_of_ne (show i+1≠m+1 by omega)]
        exact hfr i (by omega) x ⟨(hefs hx).1.le,(hefs hx).2.le⟩

def fractionalCube (m : ℕ) (q : ℕ → ℕ) (θ : ℝ) : Fin m → Set.Icc (0:ℝ) 1 :=
  fun i => ⟨Int.fract ((q (i+1):ℝ)*θ),Int.fract_nonneg _,(Int.fract_lt_one _).le⟩

lemma realize_phase_neighborhood {m : ℕ} (γ : Fin m → Set.Icc (0:ℝ) 1)
    (hγ : ∀ i, (γ i:ℝ)∈Ioo 0 1) {U : Set (Fin m → Set.Icc (0:ℝ) 1)} (hU : U∈𝓝 γ)
    {a b : ℝ} (hab : a < b) {p : ℕ} (hp : 0 < p) (M : ℝ) :
    ∃ q : ℕ → ℕ, q 0=p ∧ (∀ i ≤ m, 0 < q i) ∧
      (∀ i < m, q i ∣ q (i+1) ∧ M < (q (i+1):ℝ)/q i) ∧
      ∃ c d : ℝ, c < d ∧ Icc c d ⊆ Ioo a b ∧
        ∀ θ∈Icc c d, fractionalCube m q θ ∈ U := by
  obtain ⟨δ,hδ,hdU⟩ := Metric.mem_nhds_iff.mp hU
  let g : ℕ → ℝ := fun i => if hi : i < m then (γ ⟨i,hi⟩:ℝ) else 1/2
  let u : ℕ → ℝ := fun i => max 0 (g i-δ/2)
  let v : ℕ → ℝ := fun i => min 1 (g i+δ/2)
  have hg (i : ℕ) (hi : i < m) : g i∈Ioo 0 1 := by simpa [g,hi] using hγ ⟨i,hi⟩
  have huv (i : ℕ) (hi : i < m) : u i < v i := by
    dsimp [u,v]
    rw [max_lt_iff,lt_min_iff,lt_min_iff]
    constructor <;> constructor <;> linarith [(hg i hi).1,(hg i hi).2]
  obtain ⟨q,hq0,hqp,hqM,c,d,hcd,hsub,hfr⟩ := finite_frequency_realization m u v
    (fun i _ => le_max_left _ _) (fun i _ => min_le_left _ _) huv hab hp M
  refine ⟨q,hq0,hqp,hqM,c,d,hcd,hsub,?_⟩
  intro θ hθ
  apply hdU
  rw [Metric.mem_ball,dist_pi_lt_iff hδ]
  intro i
  rw [Subtype.dist_eq,Real.dist_eq,abs_lt]
  have h := hfr i i.isLt θ hθ
  have hl := lt_of_le_of_lt (le_max_right 0 (g i-δ/2)) h.1
  have hh := lt_of_lt_of_le h.2 (min_le_right 1 (g i+δ/2))
  simp only [g,i.isLt,↓reduceDIte,Fin.eta] at hl hh
  change -δ < Int.fract ((q (i+1):ℝ)*θ)-(γ i:ℝ) ∧ Int.fract ((q (i+1):ℝ)*θ)-(γ i:ℝ) < δ
  constructor <;> linarith
end

open ContinuousCircleWeight.Sampling
open scoped Topology
lemma realize_finite_sampling {m : ℕ} {τ : Type uτ} [Fintype τ]
    {κ : τ → Type uκ} [∀ t, Fintype (κ t)] [∀ t, Nonempty (κ t)]
    (positive : τ → Bool) {ℓ α : ℝ} (hℓ : 0 < ℓ) (hα : 0 < α)
    (c : ∀ t, κ t → ℝ) (γ : PhaseCube m)
    (hγ : ∀ i, (γ i:ℝ)∈Set.Ioo 0 1)
    (hphase : ∀ t n i, ((c t n*(γ i:ℝ):ℝ):CircleX) ≠ 0)
    {η : ℝ} (hE : ∀ t, idealEnergy (positive t) ℓ α (c t) (fun i => (γ i:ℝ)) < η)
    {U : Set (PhaseCube m)} (hU : U∈𝓝 γ)
    {a b : ℝ} (hab : a < b) {p : ℕ} (hp : 0 < p) (M : ℝ) :
    ∃ q : ℕ → ℕ, q 0=p ∧ (∀ i ≤ m, 0 < q i) ∧
      (∀ i < m, q i ∣ q (i+1) ∧ M < (q (i+1):ℝ)/q i) ∧
      ∃ d e : ℝ, d < e ∧ Set.Icc d e ⊆ Set.Ioo a b ∧
        ∀ θ∈Set.Icc d e, fractionalCube m q θ∈U ∧
          ∀ t, (∫ x : CircleX, (idealAverage (positive t) ℓ α (c t)
            (characterCurve (fun i : Fin m => (q (i+1):ℤ)) x)
            (fun i => Int.fract ((q (i+1):ℝ)*θ))-1)^2) < η := by
  classical
  choose Mt δ hδ hacc using fun t => sampling_finite_accuracy (positive t) hℓ hα (c t) γ (hphase t) (hE t)
  let K := Finset.univ.sup Mt
  have hK (t : τ) : Mt t ≤ K := Finset.le_sup (f:=Mt) (Finset.mem_univ t)
  have hboth : (U∩{β : PhaseCube m | ∀ t, dist β γ < δ t})∈𝓝 γ := by
    apply Filter.inter_mem hU
    exact Filter.eventually_all.mpr (fun t => Metric.ball_mem_nhds γ (hδ t))
  obtain ⟨q,hq0,hqp,hqM,d,e,hde,hsub,hβ⟩ := realize_phase_neighborhood γ hγ hboth hab hp (max M (K:ℝ))
  refine ⟨q,hq0,hqp,?_,d,e,hde,hsub,?_⟩
  · intro i hi
    exact ⟨(hqM i hi).1,lt_of_le_of_lt (le_max_left _ _) (hqM i hi).2⟩
  · intro θ hθ
    refine ⟨(hβ θ hθ).1,?_⟩
    intro t
    apply hacc t (fun i => (q (i+1):ℤ)) (fractionalCube m q θ)
    · intro i hi
      exact_mod_cast hqp (i+1) (by omega)
    · intro i hi
      push_cast
      calc
        (Mt t:ℝ) ≤ K := Nat.cast_le.mpr (hK t)
        _ ≤ max M (K:ℝ) := le_max_right _ _
        _ ≤ (q (i+1+1):ℝ)/q (i+1) := (hqM (i+1) (by omega)).2.le
    · exact (hβ θ hθ).2 t


end CircleSampling

end

end OAI
