import OAI.Dynamics.StandardMap.EntropyEndpoint
import OAI.Dynamics.StandardMap.Towers.FiniteCouplingRealization

namespace OAI

section
section
namespace HyperbolicCoding
open MeasureTheory Set
open scoped ENNReal BigOperators
variable {X A B I : Type*} [MeasurableSpace X] [StandardBorelSpace X]
    [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A]
    [MeasurableSpace B] [Fintype B] [MeasurableSingletonClass B] [Nonempty B] [Fintype I]

omit [StandardBorelSpace X] [Fintype A] [MeasurableSingletonClass A] in
lemma map_restrict_image_equiv (μ : Measure X) (f : X ≃ᵐ X) (hf : MeasurePreserving f μ μ)
    (U : Set X) (p : X → A) (hp : Measurable p) :
    (μ.restrict (f '' U)).map p=(μ.restrict U).map (p ∘ f) := by
  have hh := hf.restrict_image_emb f.measurableEmbedding U
  rw [←hh.map_eq,Measure.map_map hp f.measurable]

omit [StandardBorelSpace X] [Fintype A] [MeasurableSingletonClass A] in
lemma map_restrict_finite_iUnion (μ : Measure X) (S : I → Set X)
    (hS : ∀ i,MeasurableSet (S i)) (hd : Pairwise (fun i j => Disjoint (S i) (S j)))
    (p : X → A) (hp : Measurable p) :
    (μ.restrict (⋃ i,S i)).map p=∑ i,(μ.restrict (S i)).map p := by
  rw [Measure.restrict_iUnion hd hS,Measure.map_sum hp.aemeasurable,Measure.sum_fintype]

theorem exists_phase_averaging (μ : Measure X) [IsFiniteMeasure μ] [NullSingletonClass μ]
    (f : I → X ≃ᵐ X) (hf : ∀ i,MeasurePreserving (f i) μ μ)
    {U : Set X} (hU : MeasurableSet U)
    (hd : Pairwise (fun i j => Disjoint (f i '' U) (f j '' U)))
    (p : X → A) (hp : Measurable p) :
    ∃ q : X → B,Measurable q ∧ ∀ c : I → B,
      (μ.restrict (⋃ i,f i '' (U∩q ⁻¹' {c i}))).map p=
        (Fintype.card B : ℝ≥0∞)⁻¹ • (μ.restrict (⋃ i,f i '' U)).map p := by
  classical
  let P : X → (I → A) := fun x i => p (f i x)
  have hP : Measurable P := Measurable.of_eval (fun i => hp.comp (f i).measurable)
  obtain ⟨q,hq,hphase⟩ := exists_independent_finite_phase (B:=B) (μ.restrict U) P hP
  refine ⟨q,hq,fun c => ?_⟩
  have hS (i : I) : MeasurableSet (f i '' (U∩q ⁻¹' {c i})) :=
    (f i).measurableSet_image.mpr (hU.inter (hq (measurableSet_singleton _)))
  have hS0 (i : I) : MeasurableSet (f i '' U) := (f i).measurableSet_image.mpr hU
  have hd' : Pairwise (fun i j => Disjoint (f i '' (U∩q ⁻¹' {c i})) (f j '' (U∩q ⁻¹' {c j}))) :=
    fun i j hij => (hd hij).mono (image_mono inter_subset_left) (image_mono inter_subset_left)
  rw [map_restrict_finite_iUnion μ _ hS hd' p hp,map_restrict_finite_iUnion μ _ hS0 hd p hp,
    Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_restrict_image_equiv μ (f i) (hf i) _ p hp,map_restrict_image_equiv μ (f i) (hf i) U p hp]
  have hh := finite_phase_factor (μ.restrict U) P hP q (c i) (hphase (c i))
    (fun w : I → A => w i) (measurable_pi_apply i)
  rw [Measure.restrict_restrict (hq (measurableSet_singleton _)),inter_comm] at hh
  exact hh

end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Set
open scoped ENNReal BigOperators
variable {X : Type*} [MeasurableSpace X]

def phaseBlockStart (n : ℕ) {K : ℕ} (kr : Fin K × Fin n) : ℕ := n+kr.1.val*n+kr.2.val

lemma phaseBlockStart_add_lt (n K : ℕ) (kr : Fin K × Fin n) (i : Fin n) :
    i.val+phaseBlockStart n kr<(K+2)*n := by
  have hk := Nat.mul_le_mul_right n (Nat.succ_le_iff.mpr kr.1.isLt)
  have hr := kr.2.isLt
  have hi := i.isLt
  simp only [phaseBlockStart,Nat.add_mul,Nat.one_mul,Nat.succ_eq_add_one] at hk ⊢
  omega

lemma phaseBlockStart_lt (n K : ℕ) (kr : Fin K × Fin n) : phaseBlockStart n kr<(K+2)*n := by
  have hn : 0<n := Nat.zero_lt_of_lt kr.2.isLt
  exact (Nat.le_add_left _ 0).trans_lt (phaseBlockStart_add_lt n K kr ⟨0,hn⟩)

lemma phaseBlockStart_injective {n K : ℕ} (hn : 0<n) :
    Function.Injective (phaseBlockStart n (K:=K)) := by
  rintro ⟨k,r⟩ ⟨k',r'⟩ he
  have hh : k.val*n+r.val=k'.val*n+r'.val := by simpa only [phaseBlockStart,Nat.add_assoc,Nat.add_right_inj] using he
  have hr : r.val=r'.val := by
    have hm := congrArg (fun t => t%n) hh
    simpa only [Nat.mul_add_mod_self_right,
      Nat.mod_eq_of_lt r.isLt,Nat.mod_eq_of_lt r'.isLt] using hm
  have hk : k.val=k'.val := Nat.eq_of_mul_eq_mul_right hn (by omega)
  exact Prod.ext (Fin.ext hk) (Fin.ext hr)

noncomputable def phaseBlockBase (e : X ≃ᵐ X) (U : Set X) (n K : ℕ) (q : X → Fin n) : Set X :=
  ⋃ kr : Fin K × Fin n,(e^[phaseBlockStart n kr]) '' (U∩q ⁻¹' {kr.2})

lemma measurableSet_phaseBlockBase (e : X ≃ᵐ X) {U : Set X} (hU : MeasurableSet U)
    (n K : ℕ) {q : X → Fin n} (hq : Measurable q) : MeasurableSet (phaseBlockBase e U n K q) :=
  MeasurableSet.iUnion (fun kr => measurableSet_iterate_image e
    (hU.inter (hq (measurableSet_singleton _))) (phaseBlockStart n kr))

lemma phaseBlockBase_level (e : X ≃ᵐ X) (U : Set X) (n K : ℕ) (q : X → Fin n) (i : ℕ) :
    (e^[i]) '' phaseBlockBase e U n K q=
      ⋃ kr : Fin K × Fin n,(e^[i+phaseBlockStart n kr]) '' (U∩q ⁻¹' {kr.2}) := by
  rw [phaseBlockBase,image_iUnion]
  apply iUnion_congr
  intro kr
  rw [image_image]
  congr 1
  exact (Function.iterate_add e i (phaseBlockStart n kr)).symm

lemma phaseBlockBase_disjoint (e : X ≃ᵐ X) (U : Set X) {n K : ℕ} (_ : 0<n)
    (hd : Pairwise (fun i j : Fin ((K+2)*n) => Disjoint ((e^[i.val]) '' U) ((e^[j.val]) '' U)))
    (q : X → Fin n) : Pairwise (fun i j : Fin n =>
      Disjoint ((e^[i.val]) '' phaseBlockBase e U n K q) ((e^[j.val]) '' phaseBlockBase e U n K q)) := by
  intro i j hij
  rw [phaseBlockBase_level,phaseBlockBase_level]
  apply Set.disjoint_left.mpr
  intro x hxi hxj
  obtain ⟨kr,y,hy,hyi⟩ := mem_iUnion.mp hxi
  obtain ⟨lr,z,hz,hzj⟩ := mem_iUnion.mp hxj
  let a : Fin ((K+2)*n) := ⟨i.val+phaseBlockStart n kr,phaseBlockStart_add_lt n K kr i⟩
  let b : Fin ((K+2)*n) := ⟨j.val+phaseBlockStart n lr,phaseBlockStart_add_lt n K lr j⟩
  have hab : a=b := by
    by_contra hne
    exact Set.disjoint_left.mp (hd hne) (show x∈(e^[a.val]) '' U from ⟨y,hy.1,hyi⟩)
      (show x∈(e^[b.val]) '' U from ⟨z,hz.1,hzj⟩)
  have he : i.val+phaseBlockStart n kr=j.val+phaseBlockStart n lr := congrArg Fin.val hab
  have hyz : y=z := (e.injective.iterate (i.val+phaseBlockStart n kr))
    (hyi.trans (by simpa only [he] using hzj.symm))
  have hr : kr.2=lr.2 := hy.2.symm.trans (hyz ▸ hz.2)
  have hnum : kr.1.val*n+i.val=lr.1.val*n+j.val := by
    simp only [phaseBlockStart,hr] at he
    omega
  have hi : i.val=j.val := by
    have hm := congrArg (fun t => t%n) hnum
    simpa only [Nat.mul_add_mod_self_right,
      Nat.mod_eq_of_lt i.isLt,Nat.mod_eq_of_lt j.isLt] using hm
  exact hij (Fin.ext hi)

end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Set
open scoped ENNReal BigOperators
variable {X A : Type*} [MeasurableSpace X] [StandardBorelSpace X]
    [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A]

def middleTower (e : X ≃ᵐ X) (U : Set X) (n K : ℕ) : Set X :=
  ⋃ kr : Fin K × Fin n,(e^[phaseBlockStart n kr]) '' U

omit [StandardBorelSpace X] in
lemma measurableSet_middleTower (e : X ≃ᵐ X) {U : Set X} (hU : MeasurableSet U) (n K : ℕ) :
    MeasurableSet (middleTower e U n K) :=
  MeasurableSet.iUnion (fun _ => measurableSet_iterate_image e hU _)

omit [StandardBorelSpace X] in
lemma middleTower_disjoint (e : X ≃ᵐ X) (U : Set X) {n K : ℕ} (hn : 0<n)
    (hd : Pairwise (fun i j : Fin ((K+2)*n) => Disjoint ((e^[i.val]) '' U) ((e^[j.val]) '' U))) :
    Pairwise (fun kr lr : Fin K × Fin n =>
      Disjoint ((e^[phaseBlockStart n kr]) '' U) ((e^[phaseBlockStart n lr]) '' U)) := by
  intro kr lr hne
  exact hd (i:=⟨phaseBlockStart n kr,phaseBlockStart_lt n K kr⟩)
    (j:=⟨phaseBlockStart n lr,phaseBlockStart_lt n K lr⟩) (fun hh =>
      hne (phaseBlockStart_injective hn (congrArg Fin.val hh)))

omit [StandardBorelSpace X] in
lemma middleTower_measure (μ : Measure X) (e : X ≃ᵐ X) (he : MeasurePreserving e μ μ)
    {U : Set X} (hU : MeasurableSet U) {n K : ℕ} (hn : 0<n)
    (hd : Pairwise (fun i j : Fin ((K+2)*n) => Disjoint ((e^[i.val]) '' U) ((e^[j.val]) '' U))) :
    μ (middleTower e U n K)=(K*n : ℕ)*μ U := by
  rw [middleTower,measure_iUnion (middleTower_disjoint e U hn hd)
    (fun _ => measurableSet_iterate_image e hU _),tsum_fintype]
  simp only [measure_iterate_image μ e he,Finset.sum_const,Finset.card_univ,Fintype.card_prod,
    Fintype.card_fin,nsmul_eq_mul]

theorem exists_unbiased_block_base (μ : Measure X) [IsFiniteMeasure μ] [NullSingletonClass μ]
    (e : X ≃ᵐ X) (he : MeasurePreserving e μ μ)
    {U : Set X} (hU : MeasurableSet U) {n K : ℕ} (hn : 0<n)
    (hd : Pairwise (fun i j : Fin ((K+2)*n) => Disjoint ((e^[i.val]) '' U) ((e^[j.val]) '' U)))
    (p : X → A) (hp : Measurable p) :
    ∃ V : Set X,MeasurableSet V ∧
      Pairwise (fun i j : Fin n => Disjoint ((e^[i.val]) '' V) ((e^[j.val]) '' V)) ∧
      (μ.restrict V).map p=(n : ℝ≥0∞)⁻¹ • (μ.restrict (middleTower e U n K)).map p ∧
      μ V=(K : ℝ≥0∞)*μ U := by
  let : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  let f (kr : Fin K × Fin n) : X ≃ᵐ X := iterateEquiv e (phaseBlockStart n kr)
  have hf (kr : Fin K × Fin n) : MeasurePreserving (f kr) μ μ :=
    iterateEquiv_measurePreserving e he _
  have hdf : Pairwise (fun kr lr => Disjoint (f kr '' U) (f lr '' U)) := by
    intro kr lr hne
    simpa only [f,funext (iterateEquiv_apply e (phaseBlockStart n kr)),
      funext (iterateEquiv_apply e (phaseBlockStart n lr))] using middleTower_disjoint e U hn hd hne
  obtain ⟨q,hq,hphase⟩ := exists_phase_averaging (B:=Fin n) μ f hf hU hdf p hp
  let V := phaseBlockBase e U n K q
  have hmap : (μ.restrict V).map p=(n : ℝ≥0∞)⁻¹ • (μ.restrict (middleTower e U n K)).map p := by
    have hh := hphase (fun kr => kr.2)
    have hfcoe (kr : Fin K×Fin n) : (f kr : X → X)=e^[phaseBlockStart n kr] :=
      funext (iterateEquiv_apply e _)
    simpa only [hfcoe,Fintype.card_fin,V,phaseBlockBase,middleTower] using hh
  refine ⟨V,measurableSet_phaseBlockBase e hU n K hq,phaseBlockBase_disjoint e U hn hd q,hmap,?_⟩
  have hm := congrArg (fun M : Measure A => M univ) hmap
  simp only [Measure.map_apply hp MeasurableSet.univ,preimage_univ,Measure.restrict_apply_univ,
    Measure.smul_apply,smul_eq_mul] at hm
  rw [middleTower_measure μ e he hU hn hd] at hm
  have hn0 : (n : ℝ≥0∞)≠0 := by exact_mod_cast hn.ne'
  have hnf : (n : ℝ≥0∞)≠⊤ := by simp
  rw [hm,Nat.cast_mul]
  calc
    (n : ℝ≥0∞)⁻¹*((K : ℝ≥0∞)*n*μ U)=(K : ℝ≥0∞)*((n : ℝ≥0∞)⁻¹*n)*μ U := by ring
    _=(K : ℝ≥0∞)*μ U := by rw [ENNReal.inv_mul_cancel hn0 hnf,mul_one]

end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Set
open scoped ENNReal
variable {X A : Type*} [MeasurableSpace X] [MeasurableSpace A]

theorem normalized_restriction_lawClose (μ : Measure X) [IsProbabilityMeasure μ]
    {U : Set X} (hU : MeasurableSet U) (hUp : 0<μ U) :
    LawClose ((μ U)⁻¹ • μ.restrict U) μ (1-μ.real U) := by
  have hb0 : 0<μ.real U := ENNReal.toReal_pos hUp.ne' (measure_ne_top _ _)
  have hb1 : μ.real U≤1 := by
    have hh := measureReal_mono (μ:=μ) (subset_univ U)
    simpa only [Measure.real,measure_univ,ENNReal.toReal_one] using hh
  intro S hS
  have hnorm : (((μ U)⁻¹ • μ.restrict U).real S)=μ.real (S∩U)/μ.real U := by
    rw [Measure.real,Measure.smul_apply,smul_eq_mul,ENNReal.toReal_mul,ENNReal.toReal_inv,
      Measure.restrict_apply hS]
    exact (div_eq_inv_mul _ _).symm
  rw [hnorm,abs_le]
  have hc0 : 0≤μ.real (S∩U) := ENNReal.toReal_nonneg
  have hcS : μ.real (S∩U)≤μ.real S := measureReal_mono inter_subset_left
  have hcU : μ.real (S∩U)≤μ.real U := measureReal_mono inter_subset_right
  have hcomp : μ.real U+μ.real Uᶜ=1 := by
    simpa only [Measure.real,measure_univ,ENNReal.toReal_one] using
      measureReal_add_measureReal_compl (μ:=μ) hU
  have hSc : μ.real S≤μ.real (S∩U)+(1-μ.real U) := by
    have hsub : S⊆(S∩U)∪Uᶜ := by
      intro x hx
      by_cases hxU : x∈U
      · exact Or.inl ⟨hx,hxU⟩
      · exact Or.inr hxU
    have hh := (measureReal_mono (μ:=μ) hsub).trans (measureReal_union_le (μ:=μ) (S∩U) Uᶜ)
    linarith
  constructor
  · have hh : (-(1-μ.real U)+μ.real S)*μ.real U≤μ.real (S∩U) := by
      nlinarith [mul_nonneg hc0 (sub_nonneg.mpr hb1)]
    have hh' := (le_div_iff₀ hb0).mpr hh
    linarith
  · have hh : μ.real (S∩U)≤(1-μ.real U+μ.real S)*μ.real U := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hcU) (sub_nonneg.mpr hb1)]
    have hh' := (div_le_iff₀ hb0).mpr hh
    linarith

lemma normalized_restriction_observation_close (μ : Measure X) [IsProbabilityMeasure μ]
    {U : Set X} (hU : MeasurableSet U) (hUp : 0<μ U)
    (p : X → A) (hp : Measurable p) :
    LawClose (((μ U)⁻¹ • μ.restrict U).map p) (μ.map p) (1-μ.real U) :=
  (normalized_restriction_lawClose μ hU hUp).map hp

lemma normalize_scaled_observation (ν ρ : Measure X) (p : X → A) (hp : Measurable p)
    {c : ℝ≥0∞} (hc0 : c≠0) (hcf : c≠⊤) (h : ν.map p=c • ρ.map p) :
    (((ν univ)⁻¹ • ν).map p)=(((ρ univ)⁻¹ • ρ).map p) := by
  have hm := congrArg (fun M : Measure A => M univ) h
  simp only [Measure.map_apply hp MeasurableSet.univ,preimage_univ,
    Measure.smul_apply,smul_eq_mul] at hm
  rw [Measure.map_smul _ hp.aemeasurable,Measure.map_smul _ hp.aemeasurable,h,smul_smul,hm]
  have hs : (c*ρ univ)⁻¹*c=(ρ univ)⁻¹ := by
    rw [ENNReal.mul_inv (Or.inl hc0) (Or.inl hcf)]
    calc
      c⁻¹*(ρ univ)⁻¹*c=(ρ univ)⁻¹*(c⁻¹*c) := by ring
      _=(ρ univ)⁻¹ := by rw [ENNReal.inv_mul_cancel hc0 hcf,mul_one]
  rw [hs]

end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Set
open scoped ENNReal BigOperators
variable {X A : Type*} [MeasurableSpace X] [StandardBorelSpace X]
    [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A]

omit [StandardBorelSpace X] in
lemma tower_measure (μ : Measure X) (e : X ≃ᵐ X) (he : MeasurePreserving e μ μ)
    {U : Set X} (hU : MeasurableSet U) (N : ℕ)
    (hd : Pairwise (fun i j : Fin N => Disjoint ((e^[i.val]) '' U) ((e^[j.val]) '' U))) :
    μ (⋃ i : Fin N,(e^[i.val]) '' U)=(N : ℝ≥0∞)*μ U := by
  rw [measure_iUnion hd (fun i => measurableSet_iterate_image e hU i.val),tsum_fintype]
  simp only [measure_iterate_image μ e he,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]

theorem exists_unbiased_rohlin_tower [TopologicalSpace X] [SecondCountableTopology X]
    [OpensMeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    [NullSingletonClass μ] [μ.OuterRegular] (e : X ≃ᵐ X) (he : Ergodic e μ)
    {n : ℕ} (hn : 0<n) (p : X → A) (hp : Measurable p) {ε : ℝ} (hε : 0<ε) :
    ∃ V : Set X,MeasurableSet V ∧ 0<μ V ∧
      Pairwise (fun i j : Fin n => Disjoint ((e^[i.val]) '' V) ((e^[j.val]) '' V)) ∧
      μ.real (⋃ i : Fin n,(e^[i.val]) '' V)ᶜ<ε ∧
      LawClose (((μ V)⁻¹ • μ.restrict V).map p) (μ.map p) ε := by
  let δ : ℝ := min (ε/2) (1/4)
  have hδ : 0<δ := lt_min (by positivity) (by norm_num)
  have hδε : 2*δ≤ε := by have hh := min_le_left (ε/2) (1/4); dsimp [δ]; linarith
  have hδ1 : 2*δ≤1/2 := by have hh := min_le_right (ε/2) (1/4); dsimp [δ]; linarith
  obtain ⟨K,hK⟩ := exists_nat_gt (2/δ)
  have hKr : 0<(K : ℝ) := (div_pos (by norm_num) hδ).trans hK
  have hKp : 0<K := by exact_mod_cast hKr
  have hKδ : 2<δ*((K : ℝ)+2) := by
    have hh := (div_lt_iff₀ hδ).mp hK
    nlinarith
  obtain ⟨U,hU,hd,hcover⟩ := exists_rohlin_tower μ e he (N:=((K+2)*n)) (Nat.mul_pos (by omega) hn) hδ
  have hmp := he.toMeasurePreserving
  let T : Set X := ⋃ i : Fin ((K+2)*n),(e^[i.val]) '' U
  let M : Set X := middleTower e U n K
  have hT : MeasurableSet T := MeasurableSet.iUnion (fun i => measurableSet_iterate_image e hU i.val)
  have hM : MeasurableSet M := measurableSet_middleTower e hU n K
  have hTm : μ.real T=(((K : ℝ)+2)*(n : ℝ))*μ.real U := by
    have hh := congrArg ENNReal.toReal (tower_measure μ e hmp hU ((K+2)*n) hd)
    rw [ENNReal.toReal_mul,ENNReal.toReal_natCast] at hh
    simpa only [Nat.cast_mul,Nat.cast_add,Nat.cast_ofNat,Measure.real,T] using hh
  have hMm : μ.real M=((K : ℝ)*(n : ℝ))*μ.real U := by
    have hh := congrArg ENNReal.toReal (middleTower_measure μ e hmp hU hn hd)
    simpa only [ENNReal.toReal_mul,ENNReal.toReal_natCast,Nat.cast_mul,Measure.real,M] using hh
  have hTc : μ.real T+μ.real Tᶜ=1 := by
    simpa only [Measure.real,measure_univ,ENNReal.toReal_one] using
      measureReal_add_measureReal_compl (μ:=μ) hT
  have hTcδ : μ.real Tᶜ<δ := by
    have hh := (ENNReal.toReal_lt_toReal (measure_ne_top _ _) ENNReal.ofReal_ne_top).mpr hcover
    simpa only [ENNReal.toReal_ofReal hδ.le,T,Measure.real] using hh
  have hTm1 : μ.real T≤1 := by
    have hh : 0≤μ.real Tᶜ := ENNReal.toReal_nonneg
    linarith
  have hcap : 2*((n : ℝ)*μ.real U)<δ := by
    have hK2 : 0<(K : ℝ)+2 := by positivity
    have hh : ((K : ℝ)+2)*(2*((n : ℝ)*μ.real U))<((K : ℝ)+2)*δ := by
      rw [hTm] at hTm1
      nlinarith
    nlinarith
  have herror : 1-μ.real M<2*δ := by rw [hTm] at hTc; rw [hMm]; nlinarith
  have hMpR : 0<μ.real M := by linarith
  have hMp : 0<μ M := (ENNReal.toReal_pos_iff.mp hMpR).1
  have hUpR : 0<μ.real U := by
    have hu0 : 0≤μ.real U := ENNReal.toReal_nonneg
    by_contra hbad
    have hz := le_antisymm (le_of_not_gt hbad) hu0
    rw [hMm,hz,mul_zero] at hMpR
    linarith
  have hUp : 0<μ U := (ENNReal.toReal_pos_iff.mp hUpR).1
  obtain ⟨V,hV,hdV,hmap,hVm⟩ := exists_unbiased_block_base μ e hmp hU hn hd p hp
  have hVp : 0<μ V := by
    rw [hVm]
    exact ENNReal.mul_pos (by exact_mod_cast hKp.ne') hUp.ne'
  have hVcover : μ (⋃ i : Fin n,(e^[i.val]) '' V)=μ M := by
    rw [tower_measure μ e hmp hV n hdV,hVm,middleTower_measure μ e hmp hU hn hd]
    push_cast
    ring
  have hVmeas : MeasurableSet (⋃ i : Fin n,(e^[i.val]) '' V) :=
    MeasurableSet.iUnion (fun i => measurableSet_iterate_image e hV i.val)
  have hVcomp : μ.real (⋃ i : Fin n,(e^[i.val]) '' V)ᶜ=1-μ.real M := by
    have hh := measureReal_add_measureReal_compl (μ:=μ) hVmeas
    simp only [Measure.real,hVcover,measure_univ,ENNReal.toReal_one] at hh
    change (μ _).toReal=1-(μ M).toReal
    linarith
  have hn0 : (n : ℝ≥0∞)≠0 := by exact_mod_cast hn.ne'
  have hnf : (n : ℝ≥0∞)≠⊤ := by simp
  have hnorm := normalize_scaled_observation (μ.restrict V) (μ.restrict M) p hp
    (ENNReal.inv_ne_zero.mpr hnf) (ENNReal.inv_ne_top.mpr hn0) hmap
  simp only [Measure.restrict_apply_univ] at hnorm
  refine ⟨V,hV,hVp,hdV,?_,?_⟩
  · rw [hVcomp]
    exact herror.trans_le hδε
  · rw [hnorm]
    intro D hD
    exact (normalized_restriction_observation_close μ hM hMp p hp D hD).trans (herror.le.trans hδε)

end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Set StandardMapEntropy.Entropy
open scoped ENNReal BigOperators
variable {X A : Type*} [MeasurableSpace X] [StandardBorelSpace X]
    [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A] [Nonempty A]

omit [StandardBorelSpace X] [Nonempty A] in
lemma paintTower_repaint_integral (μ : Measure X) [IsFiniteMeasure μ]
    (e : X ≃ᵐ X) (he : MeasurePreserving e μ μ)
    {U : Set X} (hU : MeasurableSet U) (N : ℕ)
    (hd : Pairwise (fun i j : Fin N => Disjoint ((e^[i.val]) '' U) ((e^[j.val]) '' U)))
    {B : X → (Fin N → A)} (hB : Measurable B) {p : X → A} (hp : Measurable p) :
    μ.real {x | p x≠paintTower e U N B p x}=
      ∫ x,nameCost (word e p N x) (B x) ∂μ.restrict U := by
  rw [Measure.real,paintTower_repaint μ e he hU N hd hB hp,
    ENNReal.toReal_sum (fun _ _ => measure_ne_top μ _)]
  simp only [nameCost,word]
  rw [integral_finsetSum _ (fun (i : Fin N) _ => integrable_finite_observation (μ.restrict U)
    (fun x => (p (e^[i.val] x),B x i))
    ((hp.comp (e.measurable.iterate i.val)).prodMk ((measurable_pi_apply i).comp hB))
    (fun ab => symbolCost ab.1 ab.2))]
  apply Finset.sum_congr rfl
  intro i _
  rw [finite_symbolCost_integral (μ.restrict U) (fun x => p (e^[i.val] x)) (fun x => B x i)
    (hp.comp (e.measurable.iterate i.val)) ((measurable_pi_apply i).comp hB)]
  have hm : MeasurableSet {x | p (e^[i.val] x)≠B x i} :=
    (measurableSet_eq_fun (hp.comp (e.measurable.iterate i.val)) ((measurable_pi_apply i).comp hB)).compl
  rw [Measure.real,Measure.restrict_apply hm,inter_comm]

theorem realize_tower_coupling (μ : Measure X) [IsFiniteMeasure μ] [NullSingletonClass μ]
    (e : X ≃ᵐ X) (he : MeasurePreserving e μ μ)
    {U : Set X} (hU : MeasurableSet U) (N : ℕ)
    (hd : Pairwise (fun i j : Fin N => Disjoint ((e^[i.val]) '' U) ((e^[j.val]) '' U)))
    (p : X → A) (hp : Measurable p) (t : (Fin N → A) → ℝ)
    (R : MatrixCoupling (mass (μ.restrict U) (word e p N)) t) :
    ∃ q : X → A,Measurable q ∧
      (∀ a b,mass (μ.restrict U) (fun x => (word e p N x,word e q N x)) (a,b)=R.weight a b) ∧
      (∀ b,mass (μ.restrict U) (word e q N) b=t b) ∧
      μ.real {x | p x≠q x}=R.cost nameCost ∧
      ∀ x,x∉⋃ i : Fin N,(e^[i.val]) '' U → q x=p x := by
  obtain ⟨B,hB,hR⟩ := realize_finite_coupling_finite (μ.restrict U) (word e p N)
    (word_measurable e e.measurable p hp N) t R
  let q := paintTower e U N B p
  have hq : Measurable q := measurable_paintTower e hU N hd hB hp
  have hj (a b : Fin N → A) :
      mass (μ.restrict U) (fun x => (word e p N x,word e q N x)) (a,b)=R.weight a b := by
    rw [←hR a b]
    unfold mass
    apply congrArg ENNReal.toReal
    apply measure_congr
    filter_upwards [ae_restrict_mem hU] with x hx
    change ((word e p N x,word e q N x)=(a,b)) = ((word e p N x,B x)=(a,b))
    rw [show word e q N x=B x from paintTower_word e U N hd B p hx]
  refine ⟨q,hq,hj,?_,?_,fun x hx => paintTower_off e U N B p hx⟩
  · intro b
    rw [mass_joint_col (μ.restrict U) (word e p N) (word e q N)
      (word_measurable e e.measurable p hp N) (word_measurable e e.measurable q hq N)]
    simp_rw [hj]
    exact R.col b
  · exact (paintTower_repaint_integral μ e he hU N hd hB hp).trans
      (integral_cost_of_realization (μ.restrict U) (word e p N)
        (word_measurable e e.measurable p hp N) B hB R hR nameCost)

omit [StandardBorelSpace X] [Nonempty A] in
lemma tower_decoder_error (μ : Measure X) [IsFiniteMeasure μ]
    (e : X ≃ᵐ X) {U : Set X} (_ : MeasurableSet U) (N : ℕ)
    (p q : X → A) (hp : Measurable p) (hq : Measurable q)
    {t : (Fin N → A) → ℝ} (R : MatrixCoupling (mass (μ.restrict U) (word e p N)) t)
    (hR : ∀ a b,mass (μ.restrict U) (fun x => (word e p N x,word e q N x)) (a,b)=R.weight a b)
    (D : (Fin N → A) → (Fin N → A)) :
    μ.real (U∩{x | word e p N x≠D (word e q N x)})=
      R.cost (fun a b => symbolCost a (D b)) := by
  have hpw := word_measurable e e.measurable p hp N
  have hqw := word_measurable e e.measurable q hq N
  have hD : Measurable D := measurable_of_countable D
  have hh := finite_symbolCost_integral (μ.restrict U) (word e p N) (D ∘ word e q N) hpw (hD.comp hqw)
  have he : (μ.restrict U).real {x | word e p N x≠(D ∘ word e q N) x}=
      μ.real (U∩{x | word e p N x≠D (word e q N x)}) := by
    have hm : MeasurableSet {x | word e p N x≠(D ∘ word e q N) x} :=
      (measurableSet_eq_fun hpw (hD.comp hqw)).compl
    rw [Measure.real,Measure.real,Measure.restrict_apply hm,inter_comm]
    rfl
  rw [he] at hh
  exact hh.symm.trans (integral_cost_of_realization (μ.restrict U) (word e p N) hpw
    (word e q N) hqw R hR (fun a b => symbolCost a (D b)))

end HyperbolicCoding

end
end

end OAI
