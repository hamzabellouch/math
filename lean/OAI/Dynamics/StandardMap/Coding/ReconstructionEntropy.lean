import OAI.Dynamics.StandardMap.EntropyEndpoint
import OAI.Dynamics.StandardMap.Towers.FiniteCouplingRealization
import OAI.Dynamics.StandardMap.Coding.EntropyRateCodebook

namespace OAI

section
namespace StandardMapEntropy.Entropy
open MeasureTheory Set Filter HyperbolicCoding
open scoped BigOperators ENNReal Topology
variable {X A B : Type*} [MeasurableSpace X]
    [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
    [Fintype B] [MeasurableSpace B] [MeasurableSingletonClass B]
    (μ : Measure X) [IsProbabilityMeasure μ]

lemma rate_factor (f : X → X) (hf : MeasurePreserving f μ μ)
    (p : X → A) (hp : Measurable p) (g : A → B) :
    rate μ f (g ∘ p) ≤ rate μ f p := by
  have hg : Measurable g := measurable_of_finite g
  apply le_of_tendsto_of_tendsto
    (rate_tendsto μ f hf (g ∘ p) (hg.comp hp)) (rate_tendsto μ f hf p hp)
  apply Eventually.of_forall
  intro n
  have heq : word f (g ∘ p) n = (fun v : Fin n → A => fun i => g (v i)) ∘ word f p n := rfl
  dsimp only
  rw [heq]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
  exact obs_factor μ _ _ (word_measurable f hf.measurable p hp n)
    (word_measurable f hf.measurable (g ∘ p) (hg.comp hp) n)

lemma rate_word_le (f : X → X) (hf : MeasurePreserving f μ μ)
    (p : X → A) (hp : Measurable p) (m : ℕ) :
    rate μ f (word f p m) ≤ rate μ f p := by
  have hb (n : ℕ) : obs μ (word f (word f p m) n) ≤
      obs μ (word f p n) + obs μ (word f p m) := by
    let G : (Fin (n+m) → A) → (Fin n → Fin m → A) :=
      fun v i j => v ⟨i.val+j.val, Nat.add_lt_add i.isLt j.isLt⟩
    have heq : word f (word f p m) n = G ∘ word f p (n+m) := by
      funext x i j
      simp only [word,Function.comp_apply,G,←Function.iterate_add_apply,Nat.add_comm]
    have hh : obs μ (word f (word f p m) n) ≤ obs μ (word f p (n+m)) := by
      rw [heq]
      exact obs_factor μ _ G (word_measurable f hf.measurable p hp (n+m))
        ((measurable_of_finite G).comp (word_measurable f hf.measurable p hp (n+m)))
    exact hh.trans (obs_word_subadd μ f hf p hp n m)
  have hlim : Tendsto (fun n : ℕ => obs μ (word f p n)/(n : ℝ) +
      obs μ (word f p m)/(n : ℝ)) atTop (𝓝 (rate μ f p)) := by
    simpa only [add_zero] using (rate_tendsto μ f hf p hp).add
      (tendsto_const_div_atTop_nhds_zero_nat (obs μ (word f p m)))
  apply le_of_tendsto_of_tendsto
    (rate_tendsto μ f hf (word f p m) (word_measurable f hf.measurable p hp m)) hlim
  apply Eventually.of_forall
  intro n
  simpa only [add_div] using div_le_div_of_nonneg_right (hb n) (Nat.cast_nonneg n)

lemma rate_word_eq (f : X → X) (hf : MeasurePreserving f μ μ)
    (p : X → A) (hp : Measurable p) {m : ℕ} (hm : 0 < m) :
    rate μ f (word f p m) = rate μ f p := by
  apply le_antisymm (rate_word_le μ f hf p hp m)
  have h := rate_factor μ f hf (word f p m) (word_measurable f hf.measurable p hp m)
    (fun v : Fin m → A => v ⟨0,hm⟩)
  simpa only [Function.comp_def,word,Function.iterate_zero,Function.id_def] using h

omit [IsProbabilityMeasure μ] in
lemma rate_integer_shift (e : X ≃ᵐ X) (he : MeasurePreserving e μ μ)
    (p : X → A) (hp : Measurable p) (s : ℤ) :
    rate μ e (p ∘ integerIterate e s) = rate μ e p := by
  have hw (n : ℕ) : word e (p ∘ integerIterate e s) n =
      word e p n ∘ integerIterate e s := by
    funext x i
    simp only [word,Function.comp_apply,←integerIterate_nat,
      ←integerIterate_add,add_comm]
  have ho (n : ℕ) : obs μ (word e (p ∘ integerIterate e s) n) = obs μ (word e p n) := by
    rw [hw]
    exact obs_comp_preserving μ _ (integerIterate_measurePreserving e he s)
      _ (word_measurable e e.measurable p hp n)
  unfold rate
  simp only [ho]

lemma rate_le_window_decoder (e : X ≃ᵐ X) (he : MeasurePreserving e μ μ)
    (p : X → A) (hp : Measurable p) (q : X → B) (hq : Measurable q)
    (s : ℤ) (m : ℕ) (D : (Fin m → B) → A) :
    rate μ e p ≤ rate μ e q +
      cond μ p (D ∘ word e q m ∘ integerIterate e s) := by
  let r : X → A := D ∘ word e q m ∘ integerIterate e s
  have hr : Measurable r := (measurable_of_finite D).comp
    ((word_measurable e e.measurable q hq m).comp (integerIterate_measurable e s))
  have hR : rate μ e r ≤ rate μ e q := by
    have hshift := rate_integer_shift μ e he (D ∘ word e q m)
      ((measurable_of_finite D).comp (word_measurable e e.measurable q hq m)) s
    change rate μ e ((D ∘ word e q m) ∘ integerIterate e s) ≤ _
    rw [hshift]
    exact (rate_factor μ e he (word e q m) (word_measurable e e.measurable q hq m) D).trans
      (rate_word_le μ e he q hq m)
  exact (rate_comparison μ e he p r hp hr).trans (add_le_add_left hR _)

theorem rate_lower_of_window_decoder (e : X ≃ᵐ X) (he : MeasurePreserving e μ μ)
    (p : X → A) (hp : Measurable p) (q : X → B) (hq : Measurable q)
    (s : ℤ) (m : ℕ) (D : (Fin m → B) → A) :
    let r := D ∘ word e q m ∘ integerIterate e s
    let d := mass μ (errorObs p r) true
    rate μ e p - (Real.negMulLog d + Real.negMulLog (1-d) +
      d*Real.log (Fintype.card A)) ≤ rate μ e q := by
  intro r d
  have hr : Measurable r := (measurable_of_finite D).comp
    ((word_measurable e e.measurable q hq m).comp (integerIterate_measurable e s))
  have h1 := rate_le_window_decoder μ e he p hp q hq s m D
  have h2 := cond_fano_bound μ p r hp hr
  dsimp only [r,d] at *
  linarith

theorem rate_lower_of_small_window_error (e : X ≃ᵐ X) (he : MeasurePreserving e μ μ)
    (p : X → A) (hp : Measurable p) {ε : ℝ} (hε : 0 < ε) :
    ∃ η : ℝ,0 < η ∧ ∀ (q : X → B),Measurable q →
      ∀ (s : ℤ) (m : ℕ) (D : (Fin m → B) → A),
      mass μ (errorObs p (D ∘ word e q m ∘ integerIterate e s)) true < η →
      rate μ e p-ε < rate μ e q := by
  obtain ⟨η,hη,hsmall⟩ := cond_small_of_error (α:=A) μ ε hε
  refine ⟨η,hη,?_⟩
  intro q hq s m D hd
  have hr : Measurable (D ∘ word e q m ∘ integerIterate e s) :=
    (measurable_of_finite D).comp
      ((word_measurable e e.measurable q hq m).comp (integerIterate_measurable e s))
  have h1 := rate_le_window_decoder μ e he p hp q hq s m D
  have h2 := hsmall p _ hp hr hd
  linarith

end StandardMapEntropy.Entropy

end
section
namespace HyperbolicCoding
open MeasureTheory Set StandardMapEntropy.Entropy
open scoped ENNReal BigOperators
variable {X A C : Type*} [MeasurableSpace X]

lemma word_centered_iterate (e : X ≃ᵐ X) (q : X → A) (n : ℕ)
    (b : X) (i : Fin n) :
    word e q (2*n) (integerIterate e (-(n : ℤ)) (e^[i.val] b)) =
      Marker.centeredWindow n (orbitName e q b) i := by
  funext j
  simp only [word,Marker.centeredWindow,orbitName,←integerIterate_nat,
    ←integerIterate_add]
  congr 2
  omega

theorem marked_tower_decode_level (e : X ≃ᵐ X) (p : X → C) (q : X → A)
    {n r : ℕ} (hn : 0 < n) (hr : r < n) (zero one : A) (h01 : zero≠one)
    (D : (Fin n → A) → (Fin n → C)) (b : X)
    (hb : Marker.MarkedBlock hr zero one (word e q n b))
    (hD : D (word e q n b)=word e p n b) (i : Fin n) :
    Marker.decodeWindow hn hr zero one D
      (word e q (2*n) (integerIterate e (-(n : ℤ)) (e^[i.val] b))) = p (e^[i.val] b) := by
  rw [word_centered_iterate]
  have hw : (fun j : Fin n => orbitName e q b (j.val : ℤ))=word e q n b := by
    funext j
    simp only [orbitName,integerIterate_nat,word]
  rw [Marker.decode_centeredWindow hn hr zero one h01 D _ (by rw [hw]; exact hb),hw,hD]
  rfl

theorem marked_tower_decode_symbol (e : X ≃ᵐ X) (p : X → C) (q : X → A)
    {n r : ℕ} (hn : 0 < n) (hr : r < n) (zero one : A) (h01 : zero≠one)
    (D : (Fin n → A) → (Fin n → C)) (b : X) (i : Fin n)
    (hb : Marker.MarkedBlock hr zero one (word e q n b))
    (hD : D (word e q n b) i=p (e^[i.val] b)) :
    Marker.decodeWindow hn hr zero one D
      (word e q (2*n) (integerIterate e (-(n : ℤ)) (e^[i.val] b))) = p (e^[i.val] b) := by
  rw [word_centered_iterate]
  have hw : (fun j : Fin n => orbitName e q b (j.val : ℤ))=word e q n b := by
    funext j
    simp only [orbitName,integerIterate_nat,word]
  rw [Marker.decode_centeredWindow hn hr zero one h01 D _ (by rw [hw]; exact hb),hw]
  exact hD

theorem marked_tower_decode_error_sum (μ : Measure X) (e : X ≃ᵐ X)
    (he : MeasurePreserving e μ μ) (p : X → C) (q : X → A)
    {n r : ℕ} (hn : 0 < n) (hr : r < n) (zero one : A) (h01 : zero≠one)
    (D : (Fin n → A) → (Fin n → C)) (U : Set X) :
    let Bad := fun i : Fin n => U ∩ {b | ¬Marker.MarkedBlock hr zero one (word e q n b) ∨
      D (word e q n b) i≠p (e^[i.val] b)}
    μ {x | Marker.decodeWindow hn hr zero one D
      (word e q (2*n) (integerIterate e (-(n : ℤ)) x))≠p x} ≤
      μ (⋃ i : Fin n,(e^[i.val]) '' U)ᶜ + ∑ i : Fin n,μ (Bad i) := by
  intro Bad
  have hsub : {x | Marker.decodeWindow hn hr zero one D
      (word e q (2*n) (integerIterate e (-(n : ℤ)) x))≠p x} ⊆
      (⋃ i : Fin n,(e^[i.val]) '' U)ᶜ ∪ ⋃ i : Fin n,(e^[i.val]) '' Bad i := by
    intro x hx
    by_cases ht : x∈⋃ i : Fin n,(e^[i.val]) '' U
    · obtain ⟨i,b,hb,rfl⟩ := mem_iUnion.mp ht
      right
      refine mem_iUnion.mpr ⟨i,b,⟨hb,?_⟩,rfl⟩
      by_contra h
      change ¬(¬Marker.MarkedBlock hr zero one (word e q n b) ∨
        D (word e q n b) i≠p (e^[i.val] b)) at h
      push Not at h
      exact hx (marked_tower_decode_symbol e p q hn hr zero one h01 D b i h.1 h.2)
    · exact Or.inl ht
  calc
    _ ≤ μ ((⋃ i : Fin n,(e^[i.val]) '' U)ᶜ ∪ ⋃ i : Fin n,(e^[i.val]) '' Bad i) := measure_mono hsub
    _ ≤ μ (⋃ i : Fin n,(e^[i.val]) '' U)ᶜ + μ (⋃ i : Fin n,(e^[i.val]) '' Bad i) := measure_union_le _ _
    _ ≤ μ (⋃ i : Fin n,(e^[i.val]) '' U)ᶜ + ∑' i : Fin n,μ ((e^[i.val]) '' Bad i) :=
      add_le_add_right (measure_iUnion_le _) _
    _ = _ := by simp only [measure_iterate_image μ e he,tsum_fintype]

theorem marked_tower_decode_error (μ : Measure X) (e : X ≃ᵐ X)
    (he : MeasurePreserving e μ μ) (p : X → C) (q : X → A)
    {n r : ℕ} (hn : 0 < n) (hr : r < n) (zero one : A) (h01 : zero≠one)
    (D : (Fin n → A) → (Fin n → C)) (U : Set X) :
    let Bad := U ∩ {b | ¬Marker.MarkedBlock hr zero one (word e q n b) ∨
      D (word e q n b)≠word e p n b}
    μ {x | Marker.decodeWindow hn hr zero one D
      (word e q (2*n) (integerIterate e (-(n : ℤ)) x))≠p x} ≤
      μ (⋃ i : Fin n,(e^[i.val]) '' U)ᶜ + (n : ℝ≥0∞)*μ Bad := by
  intro Bad
  have hsub : {x | Marker.decodeWindow hn hr zero one D
      (word e q (2*n) (integerIterate e (-(n : ℤ)) x))≠p x} ⊆
      (⋃ i : Fin n,(e^[i.val]) '' U)ᶜ ∪ ⋃ i : Fin n,(e^[i.val]) '' Bad := by
    intro x hx
    by_cases ht : x∈⋃ i : Fin n,(e^[i.val]) '' U
    · obtain ⟨i,b,hb,rfl⟩ := mem_iUnion.mp ht
      right
      refine mem_iUnion.mpr ⟨i,b,⟨hb,?_⟩,rfl⟩
      by_contra h
      change ¬(¬Marker.MarkedBlock hr zero one (word e q n b) ∨
        D (word e q n b)≠word e p n b) at h
      push Not at h
      exact hx (marked_tower_decode_level e p q hn hr zero one h01 D b h.1 h.2 i)
    · exact Or.inl ht
  calc
    _ ≤ μ ((⋃ i : Fin n,(e^[i.val]) '' U)ᶜ ∪ ⋃ i : Fin n,(e^[i.val]) '' Bad) := measure_mono hsub
    _ ≤ μ (⋃ i : Fin n,(e^[i.val]) '' U)ᶜ + μ (⋃ i : Fin n,(e^[i.val]) '' Bad) := measure_union_le _ _
    _ ≤ μ (⋃ i : Fin n,(e^[i.val]) '' U)ᶜ + ∑' i : Fin n,μ ((e^[i.val]) '' Bad) :=
      add_le_add_right (measure_iUnion_le _) _
    _ = _ := by simp only [measure_iterate_image μ e he,tsum_fintype,Finset.sum_const,
      Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]

end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Set StandardMapEntropy.Entropy
open scoped ENNReal BigOperators
variable {X A C : Type*} [MeasurableSpace X]

noncomputable def extendPrefixDecoder {k t : ℕ} (D : (Fin (k+t) → A) → (Fin k → C))
    (c₀ : C) (w : Fin (k+t) → A) : Fin (k+t) → C :=
  Fin.addCases (D w) (fun _ => c₀)

theorem marked_tower_prefix_decoder_error (μ : Measure X) [IsFiniteMeasure μ]
    (e : X ≃ᵐ X) (he : MeasurePreserving e μ μ)
    (p : X → C) (q : X → A) {k t r : ℕ} (hn : 0 < k+t) (hr : r < k+t)
    (zero one : A) (h01 : zero≠one)
    (D : (Fin (k+t) → A) → (Fin k → C)) (c₀ : C)
    {U : Set X} (hU : MeasurableSet U)
    (hmarked : ∀ᵐ b ∂μ.restrict U,Marker.MarkedBlock hr zero one (word e q (k+t) b)) :
    μ.real {x | Marker.decodeWindow hn hr zero one (extendPrefixDecoder D c₀)
      (word e q (2*(k+t)) (integerIterate e (-((k+t : ℕ) : ℤ)) x))≠p x} ≤
      μ.real (⋃ i : Fin (k+t),(e^[i.val]) '' U)ᶜ +
      (k+t : ℕ)*μ.real (U∩{b | D (word e q (k+t) b)≠word e p k b})+
      (t : ℝ)*μ.real U := by
  let E := U∩{b | D (word e q (k+t) b)≠word e p k b}
  let Bad := fun i : Fin (k+t) => U∩{b |
    ¬Marker.MarkedBlock hr zero one (word e q (k+t) b) ∨
      extendPrefixDecoder D c₀ (word e q (k+t) b) i≠p (e^[i.val] b)}
  have hmain := marked_tower_decode_error_sum μ e he p q hn hr zero one h01
    (extendPrefixDecoder D c₀) U
  dsimp only at hmain
  have hhead (i : Fin k) : μ (Bad (Fin.castAdd t i)) ≤ μ E := by
    apply measure_mono_ae
    filter_upwards [(ae_restrict_iff' hU).mp hmarked] with b hb
    intro hbad
    refine ⟨hbad.1,?_⟩
    intro hEq
    have hm := hb hbad.1
    have hd := hbad.2.resolve_left (not_not.mpr hm)
    apply hd
    simp only [extendPrefixDecoder,Fin.addCases_left,hEq,word]
    rfl
  have htail (i : Fin t) : μ (Bad (Fin.natAdd k i)) ≤ μ U :=
    measure_mono (inter_subset_left)
  have hsum : (∑ i : Fin (k+t),μ (Bad i))≤(k : ℝ≥0∞)*μ E+(t : ℝ≥0∞)*μ U := by
    rw [Fin.sum_univ_add]
    apply add_le_add
    · simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] using
        Finset.sum_le_sum (s := Finset.univ) (fun i _ => hhead i)
    · simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] using
        Finset.sum_le_sum (s := Finset.univ) (fun i _ => htail i)
  have hEfin : μ E≠⊤ := measure_ne_top _ _
  have hweak : (k : ℝ≥0∞)*μ E≤((k+t : ℕ) : ℝ≥0∞)*μ E :=
    by gcongr; exact_mod_cast Nat.le_add_right k t
  have hbound := hmain.trans (add_le_add_right (hsum.trans (add_le_add_left hweak _)) _)
  have hfin : μ (⋃ i : Fin (k+t),(e^[i.val]) '' U)ᶜ+
      (((k+t : ℕ) : ℝ≥0∞)*μ E+(t : ℝ≥0∞)*μ U)≠⊤ := by finiteness
  have hreal := ENNReal.toReal_mono hfin hbound
  rw [ENNReal.toReal_add (measure_ne_top _ _) (by finiteness),
    ENNReal.toReal_add (by finiteness) (by finiteness)] at hreal
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_natCast, Measure.real, add_assoc, E] using hreal

end HyperbolicCoding

end
section
namespace HyperbolicCoding.MatrixCoupling
open scoped BigOperators
variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] [Nonempty A]
    {p : A → ℝ} {q : B → ℝ}

theorem exists_decodable_coupling_scaled (r : MatrixCoupling p q) (hq : ∑ b,q b=1)
    (c : A → B → ℝ) (hc0 : ∀ a b,0≤c a b) (hc1 : ∀ a b,c a b≤1)
    {τ M : ℝ} (hτ : 0 < τ) (hM : ∀ b,q b≤M) :
    ∃ (D : B → A) (R : MatrixCoupling p q),
      R.cost (fun a b => symbolCost a (D b))≤Real.sqrt ((Fintype.card A : ℝ)*M+τ*r.cost c) ∧
      R.cost c≤r.cost c+(Fintype.card A : ℝ)*M/τ+
        Real.sqrt ((Fintype.card A : ℝ)*M+τ*r.cost c) := by
  obtain ⟨D,hD⟩ := r.exists_rounded_decoder hq (fun a b => τ*c a b) hM
  let E : ℝ := ∑ a,|assignedMass q D a-p a|
  let C : ℝ := ∑ b,q b*c (D b) b
  have hE : 0≤E := Finset.sum_nonneg (fun a _ => abs_nonneg _)
  have hC : 0≤C := Finset.sum_nonneg (fun b _ => mul_nonneg (r.right_nonneg b) (hc0 _ _))
  have hsum : (∑ b,q b*(τ*c (D b) b))=τ*C := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    ring
  have hscaledCost : r.cost (fun left right => τ*c left right)=τ*r.cost c := by
    simp only [cost,Finset.mul_sum,mul_left_comm]
  rw [hscaledCost,hsum] at hD
  change E^2+τ*C≤(Fintype.card A : ℝ)*M+τ*r.cost c at hD
  have hnonneg : 0≤(Fintype.card A : ℝ)*M+τ*r.cost c := by
    nlinarith [sq_nonneg E,mul_nonneg hτ.le hC]
  have herror : E≤Real.sqrt ((Fintype.card A : ℝ)*M+τ*r.cost c) := by
    nlinarith [Real.sq_sqrt hnonneg,Real.sqrt_nonneg ((Fintype.card A : ℝ)*M+τ*r.cost c),
      mul_nonneg hτ.le hC]
  have hcost : C≤r.cost c+(Fintype.card A : ℝ)*M/τ := by
    have h := (le_div_iff₀ hτ).mpr (show C*τ≤(Fintype.card A : ℝ)*M+τ*r.cost c by
      nlinarith [sq_nonneg E])
    apply h.trans_eq
    field_simp
    ring
  obtain ⟨R,hdecode,hpaint⟩ := r.repair_assignment hq D c hc0 hc1
  refine ⟨D,R,hdecode.trans herror,?_⟩
  change R.cost c≤C+E at hpaint
  linarith

noncomputable def decodingThreshold (ε : ℝ) : ℝ :=
  min (ε^2/16) ((ε^2/16)*ε/4)

lemma decodingThreshold_pos {ε : ℝ} (hε : 0<ε) : 0<decodingThreshold ε :=
  lt_min (by positivity) (by positivity)

theorem decodable_coupling_tolerance {ε : ℝ} (hε : 0<ε)
    (r : MatrixCoupling p q) (hq : (∑ b,q b)=1)
    (c : A → B → ℝ) (hc0 : ∀ a b,0≤c a b) (hc1 : ∀ a b,c a b≤1)
    (M : ℝ) (hM : ∀ b,q b≤M) (hsmall : (Fintype.card A : ℝ)*M≤decodingThreshold ε) :
    ∃ (D : B → A) (R : MatrixCoupling p q),
      R.cost (fun a b => symbolCost a (D b))<ε ∧ R.cost c<r.cost c+ε := by
  let τ : ℝ := ε^2/16
  have hτ : 0<τ := by dsimp [τ]; positivity
  have hr1 : r.cost c≤1 := by
    calc
      r.cost c≤r.cost (fun _ _ => 1) := r.cost_mono _ _ hc1
      _=1 := by
        unfold cost
        simp only [mul_one]
        rw [Finset.sum_comm]
        simp only [r.col,hq]
  obtain ⟨D,R,hD,hR⟩ := r.exists_decodable_coupling_scaled hq c hc0 hc1 hτ hM
  have hs : Real.sqrt ((Fintype.card A : ℝ)*M+τ*r.cost c)<ε/2 := by
    apply (Real.sqrt_lt' (by positivity : 0<ε/2)).mpr
    have h1 : (Fintype.card A : ℝ)*M≤ε^2/16 := hsmall.trans (min_le_left _ _)
    have h2 := mul_le_mul_of_nonneg_left hr1 hτ.le
    dsimp [τ] at h2 ⊢
    nlinarith [sq_pos_of_pos hε]
  have hd : (Fintype.card A : ℝ)*M/τ≤ε/4 := by
    apply (div_le_iff₀ hτ).mpr
    have hb := hsmall.trans (min_le_right _ _)
    change _≤τ*ε/4 at hb
    nlinarith
  exact ⟨D,R,hD.trans_lt (hs.trans (by linarith)),by linarith⟩

theorem exists_decodable_coupling_tolerance {ε : ℝ} (hε : 0<ε) :
    ∃ θ : ℝ,0<θ ∧ ∀ (p : A → ℝ) (q : B → ℝ) (r : MatrixCoupling p q), (∑ b,q b)=1 →
      ∀ (c : A → B → ℝ), (∀ a b,0≤c a b) → (∀ a b,c a b≤1) →
      ∀ M : ℝ,(∀ b,q b≤M) → (Fintype.card A : ℝ)*M≤θ →
      ∃ (D : B → A) (R : MatrixCoupling p q),
        R.cost (fun a b => symbolCost a (D b))<ε ∧ R.cost c<r.cost c+ε :=
  ⟨decodingThreshold ε,decodingThreshold_pos hε,fun _ _ r hq c hc0 hc1 M hM hsmall =>
    decodable_coupling_tolerance hε r hq c hc0 hc1 M hM hsmall⟩

end HyperbolicCoding.MatrixCoupling

end

end OAI
