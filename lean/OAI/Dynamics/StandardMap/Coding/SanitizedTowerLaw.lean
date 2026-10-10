import OAI.Dynamics.StandardMap.EntropyEndpoint
import OAI.Dynamics.StandardMap.Coding.DecodedTowerCopy

namespace OAI

section
namespace HyperbolicCoding
open MeasureTheory Set StandardMapEntropy.Entropy
open scoped BigOperators ENNReal
variable {X Y A : Type*} [MeasurableSpace X] [StandardBorelSpace X]
    [MeasurableSpace Y] [MeasurableSpace A] [Fintype A] [DecidableEq A]
    [MeasurableSingletonClass A] [Nonempty A]

theorem sanitized_tower_short_word_lawClose
    (μ : Measure X) [IsProbabilityMeasure μ] [NullSingletonClass μ]
    (ν : Measure Y) [IsProbabilityMeasure ν]
    (e : X ≃ᵐ X) (he : MeasurePreserving e μ μ)
    (f : Y → Y) (hf : MeasurePreserving f ν ν)
    {U : Set X} (hU : MeasurableSet U) (hUp : 0<μ U)
    (p : X → A) (q : Y → A) (hp : Measurable p) (hq : Measurable q)
    {n m : ℕ} (hm : m<n)
    (hd : Pairwise (fun i j : Fin n => Disjoint ((e^[i.val]) '' U) ((e^[j.val]) '' U)))
    (g : (Fin n → A) → (Fin n → A)) {K : ℝ} (hK0 : 0≤K) (hK : ∀ w,nameCost (g w) w≤K)
    (hbase : ∀ w,mass (μ.restrict U) (word e p n) w=
      μ.real U*pushWeight (mass ν (word f q n)) g w)
    {ε : ℝ} (hcover : μ.real (⋃ i : Fin n,(e^[i.val]) '' U)ᶜ<ε) :
    LawClose (μ.map (word e p m)) (ν.map (word f q m))
      (ε+(m : ℝ)/(n : ℝ)+(m : ℝ)*K/(n : ℝ)) := by
  have hqw := word_measurable f hf.measurable q hq n
  have hv : ∀ w,0 ≤ mass ν (word f q n) w := fun w => mass_nonneg _ _ _
  have hs : (∑ w,mass ν (word f q n) w)=1 := by rw [mass_sum ν _ hqw]; simp
  obtain ⟨r,hr,hrbase,hpaint⟩ := unsanitize_tower μ e he hU n hd p hp _ hv hs g K hK hbase
  have hbaseMap := base_mass_to_law μ ν (word_measurable e e.measurable r hr n) hqw hrbase
  have hraw := tower_short_word_lawClose μ ν e he f hf hU hUp r q hr hq hm hd hbaseMap hcover
  have hclose := (word_lawClose_of_repaint μ e he p r hp hr m).triangle hraw
  apply hclose.mono
  have hn : (0 : ℝ)<n := Nat.cast_pos.mpr (lt_of_le_of_lt (Nat.zero_le m) hm)
  have hmass : (n : ℝ)*μ.real U≤1 := by
    have hh := congrArg ENNReal.toReal (tower_measure μ e he hU n hd)
    rw [ENNReal.toReal_mul,ENNReal.toReal_natCast] at hh
    have hi := measureReal_mono (μ:=μ) (subset_univ (⋃ i : Fin n,(e^[i.val]) '' U))
    simpa only [Measure.real,measure_univ,ENNReal.toReal_one,hh] using hi
  have hb : K*μ.real U≤K/(n : ℝ) := by
    apply (le_div_iff₀ hn).mpr
    have hh := mul_le_mul_of_nonneg_left hmass hK0
    nlinarith
  have hh := mul_le_mul_of_nonneg_left (hpaint.trans hb) (Nat.cast_nonneg m)
  rw [←mul_div_assoc] at hh
  linarith

lemma marked_tower_short_word_lawClose
    (μ : Measure X) [IsProbabilityMeasure μ] [NullSingletonClass μ]
    (ν : Measure Y) [IsProbabilityMeasure ν]
    (e : X ≃ᵐ X) (he : MeasurePreserving e μ μ)
    (f : Y → Y) (hf : MeasurePreserving f ν ν)
    {U : Set X} (hU : MeasurableSet U) (hUp : 0<μ U)
    (p : X → A) (q : Y → A) (hp : Measurable p) (hq : Measurable q)
    {n m r : ℕ} (hm : m<n)
    (hd : Pairwise (fun i j : Fin n => Disjoint ((e^[i.val]) '' U) ((e^[j.val]) '' U)))
    (zero one : A)
    (hbase : ∀ w,mass (μ.restrict U) (word e p n) w=
      μ.real U*pushWeight (mass ν (word f q n)) (Marker.markWord r zero one) w)
    {ε : ℝ} (hcover : μ.real (⋃ i : Fin n,(e^[i.val]) '' U)ᶜ<ε) :
    LawClose (μ.map (word e p m)) (ν.map (word f q m))
      (ε+(m : ℝ)/(n : ℝ)+(m : ℝ)*(Marker.reserved n r).card/(n : ℝ)) := by
  apply sanitized_tower_short_word_lawClose μ ν e he f hf hU hUp p q hp hq hm hd
    (Marker.markWord r zero one) (Nat.cast_nonneg _) _ hbase hcover
  intro w
  rw [nameCost_comm]
  exact Marker.markWord_cost zero one w

end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Set StandardMapEntropy.Entropy Filter
open scoped BigOperators ENNReal Topology
variable {X A C : Type*} [MeasurableSpace X] [StandardBorelSpace X]
  [TopologicalSpace X] [SecondCountableTopology X] [OpensMeasurableSpace X]
  [MeasurableSpace A] [Fintype A] [DecidableEq A] [MeasurableSingletonClass A] [Nonempty A]
  [MeasurableSpace C] [Fintype C] [DecidableEq C] [MeasurableSingletonClass C] [Nonempty C]

omit [MeasurableSpace A] [MeasurableSingletonClass A] [Nonempty A] in
lemma marked_pushWeight_support {n r : ℕ} (v : (Fin n → A) → ℝ) (hr0 : 0 < r) (hr : r < n)
    (zero one : A) (w : Fin n → A) (hw : ¬Marker.MarkedBlock hr zero one w) :
    pushWeight v (Marker.markWord r zero one) w=0 := by
  unfold pushWeight
  apply Finset.sum_eq_zero
  intro b _
  have hne : Marker.markWord r zero one b≠w := by
    intro h
    exact hw (h ▸ Marker.markWord_isMarked hr0 hr zero one b)
  simp only [ite_eq_right hne]

theorem actual_synchronized_copy (μ : Measure X) [IsProbabilityMeasure μ]
    [NullSingletonClass μ] [μ.OuterRegular] (e : X ≃ᵐ X) (he : Ergodic e μ)
    (htotal : ∀ m : ℕ, 0  <  m → Ergodic (e^[m]) μ)
    (p : X → C) (hp : Measurable p) (F : C → A)
    (β : A → ℝ) (hβ : ∀ a,0≤β a) (hβsum : ∑ a,β a=1)
    (hβentropy : 0 < weightEntropy β) (hrate : rate μ e p≤weightEntropy β)
    (zero one : A) (h01 : zero≠one) (l : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ K r m : ℕ,0 < K ∧ 0 < r ∧ 0 < m ∧ ∀ᶠ n : ℕ in atTop,
      0 < n ∧ ∀ R : MatrixCoupling (mass μ (word e p (n*K*m)))
        (productWordWeight β (n*K*m+n*m)),
      ∃ (q : X → A) (s : ℤ) (M : ℕ) (G : (Fin M → A) → C),Measurable q ∧
        μ.real {x | F (p x)≠q x} < R.cost (normalizedPrefixCost F)+ε ∧
        LawClose (μ.map (word e q l)) (Measure.pi (fun _ : Fin l => finiteWeightLaw β)) ε ∧
        μ.real {x | G (word e q M (integerIterate e s x))≠p x} < ε := by
  let θ : ℝ := min (ε/8) (ε/(4*((l : ℝ)+1)))
  have hθ : 0 < θ := lt_min (by positivity) (by positivity)
  have hθε : θ≤ε/8 := min_le_left _ _
  have hθl : θ≤ε/(4*((l : ℝ)+1)) := min_le_right _ _
  have hprod : ((l : ℝ)+1)*θ≤ε/4 := by
    have hh := (le_div_iff₀ (by positivity : 0 < 4*((l : ℝ)+1))).mp hθl
    nlinarith
  obtain ⟨K,r,m,hK,hr,hm,hn⟩ := synchronized_codebook_producer μ e he.toMeasurePreserving
    htotal p hp F β hβ hβsum hβentropy hrate zero one hθ
  obtain ⟨B,hB⟩ := exists_nat_gt (max (l : ℝ) (4*(l : ℝ)/ε))
  refine ⟨K,r,m,hK,hr,hm,?_⟩
  filter_upwards [hn,eventually_ge_atTop B] with n hn hnB
  obtain ⟨hnpos,hrN,htail,hres,hcouple⟩ := hn
  have hnN : n≤n*K*m+n*m := by
    exact (Nat.le_mul_of_pos_right n hK).trans ((Nat.le_mul_of_pos_right (n*K) hm).trans (Nat.le_add_right _ _))
  have hBN : (B : ℝ)≤(n*K*m+n*m : ℕ) := by exact_mod_cast hnB.trans hnN
  have hlN : l < n*K*m+n*m := by
    have hh := (le_max_left _ _).trans_lt hB
    exact_mod_cast hh.trans_le hBN
  have hN : (0 : ℝ) < (n*K*m+n*m : ℕ) := Nat.cast_pos.mpr (lt_trans hr hrN)
  have hfrac : (l : ℝ)/(n*K*m+n*m : ℕ) < ε/4 := by
    apply (div_lt_iff₀ hN).mpr
    have hh := ((le_max_right _ _).trans_lt hB).trans_le hBN
    have hh' := (div_lt_iff₀ hε).mp hh
    nlinarith
  refine ⟨hnpos,?_⟩
  intro R
  obtain ⟨D,H,hD,hH⟩ := hcouple R
  obtain ⟨U,q,hU,hUp,hq,hd,hcover,hbase,hpaint,hdecode⟩ := lift_decoded_prefix_transport
    μ e he (lt_trans hr hrN) hrN p hp F _ H zero one h01
    (marked_pushWeight_support _ hr hrN zero one) D (Classical.arbitrary C) hθ
  let G := Marker.decodeWindow (lt_trans hr hrN) hrN zero one
    (extendPrefixDecoder D (Classical.arbitrary C))
  let : IsProbabilityMeasure (finiteWeightLaw β) := finiteWeightLaw_probability β hβ hβsum
  let ν := Measure.infinitePi (fun _ : ℤ => finiteWeightLaw β)
  have hmap : ∀ w,mass (μ.restrict U) (word e q (n*K*m+n*m)) w=
      μ.real U*pushWeight (mass ν (word iidShift (fun z : ℤ → A => z 0) (n*K*m+n*m)))
        (Marker.markWord r zero one) w := by
    intro w
    simpa only [ν,funext (iid_word_mass β hβ hβsum (n*K*m+n*m))] using hbase w
  have hLaw := marked_tower_short_word_lawClose μ ν e he.toMeasurePreserving iidShift
    (iidShift_preserving (finiteWeightLaw β)) hU hUp q (fun z : ℤ → A => z 0) hq
    (measurable_pi_apply 0) hlN hd zero one hmap hcover
  have hLaw' : LawClose (μ.map (word e q l))
      (Measure.pi (fun _ : Fin l => finiteWeightLaw β))
      (θ+(l : ℝ)/(n*K*m+n*m : ℕ)+(l : ℝ)*(Marker.reserved (n*K*m+n*m) r).card/(n*K*m+n*m : ℕ)) := by
    simpa only [ν,iid_word_law] using hLaw
  refine ⟨q,-((n*K*m+n*m : ℕ) : ℤ),2*(n*K*m+n*m),G,hq,?_,?_,?_⟩
  · linarith
  · apply hLaw'.mono
    have hres' := mul_le_mul_of_nonneg_left hres.le (Nat.cast_nonneg l)
    rw [←mul_div_assoc] at hres'
    linarith
  · change μ.real {x | Marker.decodeWindow _ _ zero one _
        (word e q (2*(n*K*m+n*m)) (integerIterate e (-((n*K*m+n*m : ℕ) : ℤ)) x))≠p x} < ε
    linarith

theorem actual_rate_controlled_copy (μ : Measure X) [IsProbabilityMeasure μ]
    [NullSingletonClass μ] [μ.OuterRegular] (e : X ≃ᵐ X) (he : Ergodic e μ)
    (htotal : ∀ m : ℕ, 0 < m → Ergodic (e^[m]) μ)
    (p : X → C) (hp : Measurable p) (F : C → A)
    (β : A → ℝ) (hβ : ∀ a,0≤β a) (hβsum : ∑ a,β a=1)
    (hβentropy : 0 < weightEntropy β) (hrate : rate μ e p≤weightEntropy β)
    (zero one : A) (h01 : zero≠one) (l : ℕ) {ε ρ : ℝ} (hε : 0 < ε) (hρ : 0 < ρ) :
    ∃ K r m : ℕ,0 < K ∧ 0 < r ∧ 0 < m ∧ ∀ᶠ n : ℕ in atTop,
      0 < n ∧ ∀ R : MatrixCoupling (mass μ (word e p (n*K*m)))
        (productWordWeight β (n*K*m+n*m)),
      ∃ (q : X → A) (s : ℤ) (M : ℕ) (G : (Fin M → A) → C),Measurable q ∧
        μ.real {x | F (p x)≠q x} < R.cost (normalizedPrefixCost F)+ε ∧
        LawClose (μ.map (word e q l)) (Measure.pi (fun _ : Fin l => finiteWeightLaw β)) ε ∧
        μ.real {x | G (word e q M (integerIterate e s x))≠p x} < ε ∧
        rate μ e p-ρ < rate μ e q := by
  obtain ⟨η,hη,hsmall⟩ := rate_lower_of_small_window_error (B:=A) μ e he.toMeasurePreserving p hp hρ
  obtain ⟨K,r,m,hK,hr,hm,hn⟩ := actual_synchronized_copy μ e he htotal p hp F β hβ hβsum
    hβentropy hrate zero one h01 l (lt_min hε hη)
  refine ⟨K,r,m,hK,hr,hm,?_⟩
  filter_upwards [hn] with n hn
  refine ⟨hn.1,?_⟩
  intro R
  obtain ⟨q,s,M,G,hq,hpaint,hlaw,hdecode⟩ := hn.2 R
  have heq : mass μ (errorObs p (G ∘ word e q M ∘ integerIterate e s)) true=
      μ.real {x | G (word e q M (integerIterate e s x))≠p x} := by
    simp only [mass,Measure.real]
    congr 2
    ext x
    simp only [mem_preimage,mem_singleton_iff,errorObs,decide_eq_true_eq,
      mem_ofPred_eq,Function.comp_apply]
    exact ne_comm
  refine ⟨q,s,M,G,hq,lt_of_lt_of_le hpaint (add_le_add_right (min_le_left _ _) _),
    hlaw.mono (min_le_left _ _),hdecode.trans_le (min_le_left _ _),?_⟩
  apply hsmall q hq s M G
  rw [heq]
  exact hdecode.trans_le (min_le_right _ _)

end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Set StandardMapEntropy.Entropy
open scoped BigOperators
variable {X A C : Type*} {k t : ℕ} [MeasurableSpace X]
  [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
  [Fintype C] [MeasurableSpace C] [MeasurableSingletonClass C]

omit [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
  [Fintype C] [MeasurableSpace C] [MeasurableSingletonClass C] in
lemma normalizedPrefixCost_modify (F : C → A) (a : Fin k → C) (b d : Fin (k+t) → A) :
    normalizedPrefixCost F a d ≤ normalizedPrefixCost F a b+nameCost b d/(k+t : ℕ) := by
  rw [normalizedPrefixCost,normalizedPrefixCost,←add_div]
  exact div_le_div_of_nonneg_right (prefixNameCost_modify F a b d) (Nat.cast_nonneg _)

omit [MeasurableSpace X] [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
  [Fintype C] [MeasurableSpace C] [MeasurableSingletonClass C] in
lemma prefixNameCost_word_factor (f : X → X) (p : X → C) (F : C → A) (x : X) :
    prefixNameCost (k:=k) (t:=t) F (word f p k x) (word f (F ∘ p) (k+t) x)=0 := by
  simp [prefixNameCost,word,symbolCost]

theorem lift_prefix_transport (μ : Measure X) [IsProbabilityMeasure μ]
    (f : X → X) (hf : Measurable f) (p : X → C) (hp : Measurable p) (F : C → A)
    {v : (Fin (k+t) → A) → ℝ}
    (S : MatrixCoupling (mass μ (word f (F ∘ p) (k+t))) v) :
    ∃ R : MatrixCoupling (mass μ (word f p k)) v,
      R.cost (normalizedPrefixCost F)≤S.cost nameCost/(k+t : ℕ) := by
  have hF : Measurable F := measurable_of_finite F
  let P := MatrixCoupling.observations μ (word f p k) (word f (F ∘ p) (k+t))
    (word_measurable f hf p hp k) (word_measurable f hf _ (hF.comp hp) (k+t))
  have hP : P.cost (normalizedPrefixCost F)=0 := by
    rw [MatrixCoupling.observations_cost]
    simp only [normalizedPrefixCost,prefixNameCost_word_factor,zero_div,integral_zero]
  refine ⟨P.comp S,?_⟩
  have hc := P.comp_cost_le S (normalizedPrefixCost F)
    (fun a b => nameCost a b/(k+t : ℕ)) (normalizedPrefixCost F)
    (normalizedPrefixCost_modify F)
  rw [hP,zero_add] at hc
  have he : S.cost (fun a b => nameCost a b/(k+t : ℕ))=S.cost nameCost/(k+t : ℕ) := by
    simp only [MatrixCoupling.cost,mul_div_assoc,Finset.sum_div]
  exact hc.trans_eq he

end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Set Filter StandardMapEntropy.Entropy
open scoped BigOperators ENNReal Topology
variable {X A C : Type*} [MeasurableSpace X] [StandardBorelSpace X]
  [TopologicalSpace X] [SecondCountableTopology X] [OpensMeasurableSpace X]
  [MeasurableSpace A] [Fintype A] [DecidableEq A] [MeasurableSingletonClass A] [Nonempty A]
  [MeasurableSpace C] [Fintype C] [DecidableEq C] [MeasurableSingletonClass C] [Nonempty C]

theorem entropy_controlled_copy_tests
    (β : A → ℝ) (hβ : ∀ a,0≤β a) (hβsum : ∑ a,β a=1)
    (hβentropy : 0 < weightEntropy β) (zero one : A) (h01 : zero≠one)
    {η : ℝ} (hη : 0 < η) :
    ∃ m₀ : ℕ,∃ δ : ℝ,0 < δ ∧
      ∀ (μ : Measure X) (_ : IsProbabilityMeasure μ) (_ : NullSingletonClass μ)
        (_ : μ.OuterRegular) (e : X ≃ᵐ X) (_he : Ergodic e μ),
        (∀ m : ℕ,0 < m → Ergodic (e^[m]) μ) →
      ∀ (p : X → C), Measurable p → ∀ (F : C → A),
        LawClose (μ.map (word e (F ∘ p) m₀))
          (Measure.pi (fun _ : Fin m₀ => finiteWeightLaw β)) δ →
        weightEntropy β-δ≤rate μ e (F ∘ p) →
        rate μ e p≤weightEntropy β →
      ∀ (l : ℕ) (ε ρ : ℝ),0 < ε → 0 < ρ →
        ∃ (q : X → A) (s : ℤ) (M : ℕ) (G : (Fin M → A) → C),Measurable q ∧
          μ.real {x | F (p x)≠q x} < η ∧
          LawClose (μ.map (word e q l))
            (Measure.pi (fun _ : Fin l => finiteWeightLaw β)) ε ∧
          μ.real {x | G (word e q M (integerIterate e s x))≠p x} < ε ∧
          rate μ e p-ρ < rate μ e q := by
  obtain ⟨m₀,t,ht,δ,hδ,hfd⟩ := iid_finite_determination (X:=X) β hβ hβsum
    hβentropy (half_pos hη)
  refine ⟨m₀,δ,hδ,?_⟩
  intro μ hμ hnonatomic hr e he htotal p hp F hlaw hrate hupper l ε ρ hε hρ
  let : IsProbabilityMeasure μ := hμ
  let : NullSingletonClass μ := hnonatomic
  let : μ.OuterRegular := hr
  obtain ⟨K,r,m,hK,_hr,hm,hcopy⟩ := actual_rate_controlled_copy μ e he htotal p hp F
    β hβ hβsum hβentropy hupper zero one h01 l (lt_min hε (half_pos hη)) hρ
  have hF : Measurable (F ∘ p) := (measurable_of_finite F).comp hp
  have htend : Tendsto (fun n : ℕ => n*t) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [eventually_ge_atTop b] with n hn
    exact hn.trans (Nat.le_mul_of_pos_right n ht)
  obtain ⟨n,hn⟩ := (htend.eventually hcopy).exists
  have hpos := hn.1
  have hN : 0 < n*t*K*m+n*t*m :=
    add_pos (Nat.mul_pos (Nat.mul_pos hpos hK) hm) (Nat.mul_pos hpos hm)
  have hlen : (n*K*m+n*m)*t=n*t*K*m+n*t*m := by ring
  have hST := hfd μ hμ hnonatomic e he.toMeasurePreserving (F ∘ p) hF hlaw hrate (n*K*m+n*m)
  rw [hlen] at hST
  obtain ⟨S,hS⟩ := hST
  obtain ⟨R,hR⟩ := lift_prefix_transport (k:=n*t*K*m) (t:=n*t*m) μ e
    he.toMeasurePreserving.measurable p hp F S
  have hcost : R.cost (normalizedPrefixCost F)≤η/2 := by
    apply hR.trans
    apply (div_le_iff₀ (Nat.cast_pos.mpr hN)).mpr
    exact hS
  obtain ⟨q,s,M,G,hq,hpaint,hqlaw,hdec,hqrate⟩ := hn.2 R
  refine ⟨q,s,M,G,hq,?_,hqlaw.mono (min_le_left _ _),hdec.trans_le (min_le_left _ _),hqrate⟩
  have hmin : min ε (η/2)≤η/2 := min_le_right _ _
  linarith

end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Set Filter StandardMapEntropy.Entropy
open scoped BigOperators ENNReal Topology
variable {X A : Type*} [MeasurableSpace X] [StandardBorelSpace X]
  [MeasurableSpace A] [Fintype A] [DecidableEq A] [MeasurableSingletonClass A] [Nonempty A]

structure IIDCopyTest (μ : Measure X) (e : X ≃ᵐ X) (β : A → ℝ) (η : ℝ) where
  length : ℕ
  step : ℕ
  step_pos : 0 < step
  tolerance : ℝ
  tolerance_pos : 0 < tolerance
  transport : ∀ q : X → A,Measurable q →
    LawClose (μ.map (word e q length))
      (Measure.pi (fun _ : Fin length => finiteWeightLaw β)) tolerance →
    weightEntropy β-tolerance≤rate μ e q →
    ∀ n : ℕ,∃ R : MatrixCoupling (mass μ (word e q (n*step)))
      (productWordWeight β (n*step)), R.cost nameCost≤η*(n*step : ℕ)

lemma exists_iidCopyTest (μ : Measure X) [IsProbabilityMeasure μ] [NullSingletonClass μ]
    (e : X ≃ᵐ X) (he : MeasurePreserving e μ μ)
    (β : A → ℝ) (hβ : ∀ a,0≤β a) (hβsum : ∑ a,β a=1)
    (hβentropy : 0 < weightEntropy β) {η : ℝ} (hη : 0 < η) :
    Nonempty (IIDCopyTest μ e β η) := by
  obtain ⟨m,t,ht,δ,hδ,hfd⟩ := iid_finite_determination (X:=X) β hβ hβsum hβentropy hη
  exact ⟨⟨m,t,ht,δ,hδ,fun q hq hl hr => hfd μ inferInstance inferInstance e he q hq hl hr⟩⟩

variable [TopologicalSpace X] [SecondCountableTopology X] [OpensMeasurableSpace X]
variable {C : Type*} [MeasurableSpace C] [Fintype C] [DecidableEq C]
  [MeasurableSingletonClass C] [Nonempty C]

theorem IIDCopyTest.copy (μ : Measure X) [IsProbabilityMeasure μ]
    [NullSingletonClass μ] [μ.OuterRegular] (e : X ≃ᵐ X) (he : Ergodic e μ)
    (htotal : ∀ m : ℕ,0 < m → Ergodic (e^[m]) μ)
    (β : A → ℝ) (hβ : ∀ a,0≤β a) (hβsum : ∑ a,β a=1)
    (hβentropy : 0 < weightEntropy β) (zero one : A) (h01 : zero≠one)
    {η : ℝ} (hη : 0 < η) (T : IIDCopyTest μ e β (η/2))
    (p : X → C) (hp : Measurable p) (F : C → A)
    (hlaw : LawClose (μ.map (word e (F ∘ p) T.length))
      (Measure.pi (fun _ : Fin T.length => finiteWeightLaw β)) T.tolerance)
    (hrate : weightEntropy β-T.tolerance≤rate μ e (F ∘ p))
    (hupper : rate μ e p≤weightEntropy β)
    (l : ℕ) {ε ρ : ℝ} (hε : 0 < ε) (hρ : 0 < ρ) :
    ∃ (q : X → A) (s : ℤ) (M : ℕ) (G : (Fin M → A) → C),Measurable q ∧
      μ.real {x | F (p x)≠q x} < η ∧
      LawClose (μ.map (word e q l)) (Measure.pi (fun _ : Fin l => finiteWeightLaw β)) ε ∧
      μ.real {x | G (word e q M (integerIterate e s x))≠p x} < ε ∧
      rate μ e p-ρ < rate μ e q := by
  obtain ⟨K,r,m,hK,_hr,hm,hcopy⟩ := actual_rate_controlled_copy μ e he htotal p hp F
    β hβ hβsum hβentropy hupper zero one h01 l (lt_min hε (half_pos hη)) hρ
  have hF : Measurable (F ∘ p) := (measurable_of_finite F).comp hp
  have htend : Tendsto (fun n : ℕ => n*T.step) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [eventually_ge_atTop b] with n hn
    exact hn.trans (Nat.le_mul_of_pos_right n T.step_pos)
  obtain ⟨n,hn⟩ := (htend.eventually hcopy).exists
  have hN : 0 < n*T.step*K*m+n*T.step*m :=
    add_pos (Nat.mul_pos (Nat.mul_pos hn.1 hK) hm) (Nat.mul_pos hn.1 hm)
  have hlen : (n*K*m+n*m)*T.step=n*T.step*K*m+n*T.step*m := by ring
  have hST := T.transport (F ∘ p) hF hlaw hrate (n*K*m+n*m)
  rw [hlen] at hST
  obtain ⟨S,hS⟩ := hST
  obtain ⟨R,hR⟩ := lift_prefix_transport (k:=n*T.step*K*m) (t:=n*T.step*m) μ e
    he.toMeasurePreserving.measurable p hp F S
  have hcost : R.cost (normalizedPrefixCost F)≤η/2 := by
    apply hR.trans
    exact (div_le_iff₀ (Nat.cast_pos.mpr hN)).mpr hS
  obtain ⟨q,s,M,G,hq,hpaint,hqlaw,hdec,hqrate⟩ := hn.2 R
  refine ⟨q,s,M,G,hq,?_,hqlaw.mono (min_le_left _ _),hdec.trans_le (min_le_left _ _),hqrate⟩
  have hmin : min ε (η/2)≤η/2 := min_le_right _ _
  linarith

noncomputable def MatrixCoupling.independent {B D : Type*} [Fintype B] [Fintype D]
    (u : B → ℝ) (v : D → ℝ) (hu : ∀ b,0≤u b) (hv : ∀ d,0≤v d)
    (hsu : ∑ b,u b=1) (hsv : ∑ d,v d=1) : MatrixCoupling u v where
  weight b d := u b*v d
  nonneg b d := mul_nonneg (hu b) (hv d)
  row b := by rw [←Finset.mul_sum,hsv,mul_one]
  col d := by rw [←Finset.sum_mul,hsu,one_mul]

theorem initial_rate_controlled_copy (μ : Measure X) [IsProbabilityMeasure μ]
    [NullSingletonClass μ] [μ.OuterRegular] (e : X ≃ᵐ X) (he : Ergodic e μ)
    (htotal : ∀ m : ℕ,0 < m → Ergodic (e^[m]) μ)
    (p : X → C) (hp : Measurable p)
    (β : A → ℝ) (hβ : ∀ a,0≤β a) (hβsum : ∑ a,β a=1)
    (hβentropy : 0 < weightEntropy β) (hupper : rate μ e p≤weightEntropy β)
    (zero one : A) (h01 : zero≠one) (l : ℕ) {ε ρ : ℝ} (hε : 0 < ε) (hρ : 0 < ρ) :
    ∃ q : X → A,Measurable q ∧
      LawClose (μ.map (word e q l)) (Measure.pi (fun _ : Fin l => finiteWeightLaw β)) ε ∧
      rate μ e p-ρ < rate μ e q := by
  obtain ⟨K,r,m,hK,hr,hm,hcopy⟩ := actual_rate_controlled_copy μ e he htotal p hp (fun _ => zero)
    β hβ hβsum hβentropy hupper zero one h01 l hε hρ
  obtain ⟨n,hn⟩ := hcopy.exists
  let R := MatrixCoupling.independent (mass μ (word e p (n*K*m)))
    (productWordWeight β (n*K*m+n*m)) (mass_nonneg μ _) (productWordWeight_nonneg β hβ _)
    (by simpa using mass_sum μ _ (word_measurable e he.toMeasurePreserving.measurable p hp _))
    (productWordWeight_sum β hβsum _)
  obtain ⟨q,s,M,G,hq,_hc,hl,_hd,hrr⟩ := hn.2 R
  exact ⟨q,hq,hl,hrr⟩

end HyperbolicCoding

end

end OAI
