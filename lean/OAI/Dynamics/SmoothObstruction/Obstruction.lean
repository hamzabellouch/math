import OAI.Dynamics.SmoothObstruction.PairBounds
import OAI.Dynamics.SmoothObstruction.Models
import OAI.Dynamics.SmoothObstruction.SymbolCores

namespace OAI

section

namespace SmoothObstruction.PairUpper
open MeasureTheory Set Finset FiniteLaw
open scoped ENNReal
variable {X C J V : Type*} [MeasurableSpace X]
  [Fintype C] [MeasurableSpace C] [MeasurableSingletonClass C]
  [Fintype J] [DecidableEq J] [Nonempty J]
  [AddCommGroup V] [Module (ZMod 2) V] [Fintype V] [DecidableEq V] [Nontrivial V]
  [MeasurableSpace V] [MeasurableSingletonClass V]

omit [DecidableEq J] [Fintype V] [DecidableEq V] [Nonempty J] [Nontrivial V] [MeasurableSpace V] [MeasurableSingletonClass V] in
lemma statistic_nonneg (B : LinearMap.BilinForm (ZMod 2) V)
    (u v : J → {v : V // v≠0}) : 0 ≤ statistic B u v := by
  unfold statistic
  positivity

omit [DecidableEq J] [Fintype V] [DecidableEq V] [Nontrivial V] [MeasurableSpace V] [MeasurableSingletonClass V] in
lemma statistic_le_one (B : LinearMap.BilinForm (ZMod 2) V)
    (u v : J → {v : V // v≠0}) : statistic B u v ≤ 1 := by
  have hc : (0:ℝ) < Fintype.card J := by exact_mod_cast Fintype.card_pos
  rw [statistic,div_le_iff₀ hc,one_mul]
  calc
    _ ≤ ∑ _j : J,(1:ℝ) := sum_le_sum (fun j _ => by split_ifs <;> norm_num)
    _ = _ := by simp

/-- The upper bound is genuinely an integral in the original same-cell
law. Entropies are the original input-observable entropies. -/
theorem integral_upper (μ : Measure X) [IsProbabilityMeasure μ]
    (P : X → C) (hP : Measurable P)
    (U W : X → J → {v : V // v≠0}) (hU : Measurable U) (hW : Measurable W)
    (B : LinearMap.BilinForm (ZMod 2) V) (hB : B.Nondegenerate)
    (hentU : (249/250:ℝ)*Fintype.card J*Real.log (Fintype.card {v : V // v≠0})≤
      entropy (observed μ U hU))
    (hentW : (249/250:ℝ)*Fintype.card J*Real.log (Fintype.card {v : V // v≠0})≤
      entropy (observed μ W hW))
    (hC : Real.log (Fintype.card C)≤
      (3/500:ℝ)*Fintype.card J*Real.log (Fintype.card {v : V // v≠0}))
    (hlog : 1000*Real.log 2≤ Real.log (Fintype.card {v : V // v≠0})) :
    (∫ z,statistic B (U z.1) (W z.2) ∂(PairLaw.law μ P))≤ 31/50 := by
  let := PairLaw.law_probability μ P hP
  have hh := expectation_upper μ P hP U W hU hW B hB hentU hentW hC hlog
  rwa [observed_integral] at hh

omit [Nonempty J] [Nontrivial V] in
omit [DecidableEq J] [DecidableEq V] in
/-- The success set is measured in the unconditioned law. -/
theorem integral_success_lower (μ : Measure X) [IsProbabilityMeasure μ]
    (P : X → C) (hP : Measurable P)
    (U W : X → J → {v : V // v≠0}) (hU : Measurable U) (hW : Measurable W)
    (B : LinearMap.BilinForm (ZMod 2) V)
    (G : Set (X × X)) (hG : MeasurableSet G)
    (hGm : (19/20:ℝ) ≤ (PairLaw.law μ P).real G)
    (hZG : ∀ z∈G,(24/25:ℝ) ≤ statistic B (U z.1) (W z.2)) :
    (114/125:ℝ) ≤ ∫ z,statistic B (U z.1) (W z.2) ∂(PairLaw.law μ P) := by
  let := PairLaw.law_probability μ P hP
  have hobs : Measurable (fun z : X × X => (U z.1,W z.2)) :=
    (hU.comp measurable_fst).prodMk (hW.comp measurable_snd)
  have hZi : Integrable (fun z : X × X => statistic B (U z.1) (W z.2)) (PairLaw.law μ P) := by
    let f := fun z : X × X => (U z.1,W z.2)
    let g := fun uv : (J → {v : V // v≠0}) × (J → {v : V // v≠0}) => statistic B uv.1 uv.2
    exact (Integrable.of_finite (f:=g) (μ:=(PairLaw.law μ P).map f)).comp_aemeasurable hobs.aemeasurable
  have hl := integral_lower_of_event (PairLaw.law μ P) _ hZi
    (fun z => statistic_nonneg B (U z.1) (W z.2)) G hG (24/25) (19/20)
    (by norm_num) hGm hZG
  have hnum : (24/25:ℝ)*(19/20)=114/125 := by norm_num
  rwa [hnum] at hl

/-- Section7's two conflicting bounds are checked on the SAME original
probability. In particular an event of mass .95 with value≥ .96 is impossible;
no assertion of independence is made on that event or its complement. -/
theorem no_success_event (μ : Measure X) [IsProbabilityMeasure μ]
    (P : X → C) (hP : Measurable P)
    (U W : X → J → {v : V // v≠0}) (hU : Measurable U) (hW : Measurable W)
    (B : LinearMap.BilinForm (ZMod 2) V) (hB : B.Nondegenerate)
    (hentU : (249/250:ℝ)*Fintype.card J*Real.log (Fintype.card {v : V // v≠0})≤
      entropy (observed μ U hU))
    (hentW : (249/250:ℝ)*Fintype.card J*Real.log (Fintype.card {v : V // v≠0})≤
      entropy (observed μ W hW))
    (hC : Real.log (Fintype.card C)≤
      (3/500:ℝ)*Fintype.card J*Real.log (Fintype.card {v : V // v≠0}))
    (hlog : 1000*Real.log 2≤ Real.log (Fintype.card {v : V // v≠0}))
    (G : Set (X × X)) (hG : MeasurableSet G)
    (hGm : (19/20:ℝ)≤ (PairLaw.law μ P).real G)
    (hZG : ∀ z∈G,(24/25:ℝ)≤ statistic B (U z.1) (W z.2)) : False := by
  have hl := integral_success_lower μ P hP U W hU hW B G hG hGm hZG
  have hu := integral_upper μ P hP U W hU hW B hB hentU hentW hC hlog
  linarith
end SmoothObstruction.PairUpper

namespace SmoothObstruction.FiniteLaw
open MeasureTheory Set
variable {X Y A : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
lemma observed_preserving (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (f : X → Y) (hf : MeasurePreserving f μ ν)
    (g : Y → A) (hg : Measurable g) :
    observed μ (g ∘ f) (hg.comp hf.measurable)=observed ν g hg := by
  apply observed_ext
  funext a
  change μ.real (f ⁻¹' {y | g y=a})=ν.real {y | g y=a}
  rw [Measure.real,←Measure.map_apply hf.measurable (measurableSet_eq_fun hg measurable_const),hf.map_eq]
  rfl
end SmoothObstruction.FiniteLaw

namespace SmoothObstruction.WordHierarchy
open MeasureTheory Set Finset WordParameters WordAlphabet WordStep WordConcatenation FiniteLaw
open scoped ENNReal
lemma firstList_entropy (μ : Measure Extension) [IsProbabilityMeasure μ]
    (hT : MeasurePreserving T μ μ) {i D : ℕ} (hi : 1 ≤ i) (hD : 2≤D)
    (hDmax : D-1≤WordStep.D (S i)) :
    (249/250:ℝ)*(D-1:ℕ)*Real.log (Fintype.card (A i))≤
      entropy (observed μ (firstList i D) (measurable_firstList i D)) := by
  let : IsProbabilityMeasure (boundary μ i) := boundary_isProbability μ hT i
  have ha : MeasurePreserving (advance i) μ (boundary μ i) :=
    ⟨measurable_advance i,advance_map μ hT i⟩
  have he := observed_preserving μ (boundary μ i) (advance i) ha (labelList i (D-1))
    (measurable_labelList i (D-1))
  change observed μ (firstList i D) (measurable_firstList i D)=_ at he
  rw [he]
  simpa only [show (249/250:ℝ)=996/1000 by norm_num] using
    stationary_window_entropy_996 μ hT hi (by omega : 1≤D-1) hDmax

lemma advance_block (i D : ℕ) (x : Extension) :
    advance i (T^[D*length 40000 i] x)=T^[D*length 40000 i] (advance i x) := by
  have hp : phase i (T^[D*length 40000 i] x)=phase i x := by
    rw [phase_iterate,Nat.cast_mul,ZMod.natCast_self,mul_zero,add_zero]
  change T^[(-phase i (T^[D*length 40000 i] x)).val] (T^[D*length 40000 i] x)=_
  rw [hp]
  change T^[(-phase i x).val] (T^[D*length 40000 i] x)=T^[D*length 40000 i] (T^[(-phase i x).val] x)
  rw [←Function.iterate_add_apply,←Function.iterate_add_apply,Nat.add_comm]

lemma graph_firstLists (i k : ℕ) (x : Extension)
    (hg : graphWindows i k (advance i x)) :
    ∀ j : Fin (2^k-1),form (S i) (firstList i (2^k) x j).val
      (firstList i (2^k) (T^[2^k*length 40000 i] x) j).val=0 := by
  intro j
  have hh := hg j
  dsimp only [firstList,labelList]
  rw [advance_block,←Function.iterate_add_apply]
  have he : j.val*length 40000 i+2^k*length 40000 i=(j.val+2^k)*length 40000 i := by ring
  rw [he]
  exact hh

lemma actual_passing_lower (i k : ℕ) (hk : 2≤2^k) (x y z : Extension)
    (hy : (mismatches (firstList i (2^k) y) (firstList i (2^k) z):ℝ)<(2^k:ℕ)/100)
    (hx : (mismatches (firstList i (2^k) x)
      (firstList i (2^k) (T^[2^k*length 40000 i] z)):ℝ)<(2^k:ℕ)/100)
    (hg : graphWindows i k (advance i z)) :
    (24/25:ℝ)≤PairUpper.statistic (form (S i)) (firstList i (2^k) y) (firstList i (2^k) x) := by
  simpa only [PairUpper.statistic,Fintype.card_fin,Nat.cast_sub (by omega : 1≤2^k),Nat.cast_one] using RecognitionWindow.paired_graph_bound hk (fun a b : A i => form (S i) a.val b.val=0)
    (firstList i (2^k) y) (firstList i (2^k) x) (firstList i (2^k) z)
    (firstList i (2^k) (T^[2^k*length 40000 i] z)) (graph_firstLists i k z hg) hy hx

lemma graph_bad_small (i k : ℕ) (hk : k≤K (S i)/8) :
    ((2*2^k-2:ℕ):ℝ)/H (S i)≤1/1000 := by
  have hK := (step_conditions initial_threshold i).1
  change 256≤K (S i) at hK
  have hp : 2048*(2^k:ℕ)≤H (S i) := by
    calc
      _ = 2^(k+11) := by rw [pow_add]; norm_num; ring
      _ ≤ _ := Nat.pow_le_pow_right (by decide) (by omega)
  have hH : (0:ℝ)<H (S i) := by dsimp only [H]; positivity
  apply (div_le_iff₀ hH).mpr
  have hr : (1000:ℝ)*((2*2^k-2:ℕ):ℝ)≤H (S i) := by
    exact_mod_cast (show 1000*(2*2^k-2)≤H (S i) by omega)
  linarith

lemma alphabet_log_large (i : ℕ) : 1000*Real.log 2≤Real.log (Fintype.card (A i)) := by
  rw [log_card]
  apply mul_le_mul_of_nonneg_right _ (Real.log_pos (by norm_num : (1:ℝ)<2)).le
  have hK := (step_conditions initial_threshold i).1
  change 256≤K (S i) at hK
  have he := (K_bounds (S i)).1
  have hKr : (256:ℝ)≤K (S i) := by exact_mod_cast hK
  nlinarith
end SmoothObstruction.WordHierarchy

namespace SmoothObstruction.SwitchData
open MeasureTheory Set
open scoped ENNReal
variable {M : Type} [MeasurableSpace M] (μ : Measure M) [IsProbabilityMeasure μ]

lemma real_preimage_le {X : Type*} [MeasurableSpace X] (σ : Measure X) [IsFiniteMeasure σ]
    (f : X → M) (hf : Measurable f) (C : ℝ≥0∞) (hC : C≠∞)
    (hd : σ.map f≤C • μ) (E : Set M) (hE : MeasurableSet E) :
    σ.real (f ⁻¹' E)≤C.toReal*μ.real E := by
  have hh := hd E
  rw [Measure.map_apply hf hE,Measure.smul_apply,smul_eq_mul] at hh
  exact (ENNReal.toReal_mono (ENNReal.mul_ne_top hC (measure_ne_top _ _)) hh).trans_eq
    (ENNReal.toReal_mul)

/-- Null transport guards and the rare graph exception are removed from
an already successful set using the ORIGINAL, unnormalized retained law. -/
theorem retain_statistic (D : SwitchData μ)
    (hdom : D.retained.map D.point≤(2:ℝ≥0∞) • μ)
    (H : Set (M×M)) (hH : MeasurableSet H) (hHG : H⊆D.carrier)
    (hHm : (98/100:ℝ)≤D.law.real H)
    (B E : Set M) (hB : MeasurableSet B) (hE : MeasurableSet E)
    (hBc : μ Bᶜ=0) (hEc : μ.real Eᶜ≤1/1000) :
    ∃ K : Set (M×M),MeasurableSet K ∧ K⊆H ∧ (19/20:ℝ)≤D.law.real K ∧
      ∀ p∈K,p.1∈B ∧ p.2∈B ∧ D.point p∈B ∧ D.point p∈E := by
  let : IsProbabilityMeasure D.law := PairLaw.law_probability μ D.label D.label_measurable
  let σ := D.retained
  let : IsFiniteMeasure σ := inferInstanceAs (IsFiniteMeasure (D.law.restrict D.carrier))
  have hf : σ.map Prod.fst≤(1:ℝ≥0∞) • μ := by
    rw [one_smul,←PairLaw.first_marginal μ D.label D.label_measurable]
    exact Measure.map_mono Measure.restrict_le_self measurable_fst
  have hs : σ.map Prod.snd≤(1:ℝ≥0∞) • μ := by
    rw [one_smul,←PairLaw.second_marginal μ D.label D.label_measurable]
    exact Measure.map_mono Measure.restrict_le_self measurable_snd
  have hBr : μ.real Bᶜ=0 := by simp only [Measure.real,hBc,ENNReal.toReal_zero]
  have hm₁ := real_preimage_le μ σ Prod.fst measurable_fst 1 (by norm_num) hf Bᶜ hB.compl
  have hm₂ := real_preimage_le μ σ Prod.snd measurable_snd 1 (by norm_num) hs Bᶜ hB.compl
  have hm₃ := real_preimage_le μ σ D.point D.point_measurable 2 (by norm_num) hdom Bᶜ hB.compl
  have hm₄ := real_preimage_le μ σ D.point D.point_measurable 2 (by norm_num) hdom Eᶜ hE.compl
  simp only [hBr,mul_zero,ENNReal.toReal_ofNat,ENNReal.toReal_one] at hm₁ hm₂ hm₃ hm₄
  let W : Set (M×M) := Prod.fst ⁻¹' Bᶜ ∪ Prod.snd ⁻¹' Bᶜ ∪ D.point ⁻¹' Bᶜ ∪ D.point ⁻¹' Eᶜ
  have hW : MeasurableSet W := (((hB.compl.preimage measurable_fst).union
    (hB.compl.preimage measurable_snd)).union (hB.compl.preimage D.point_measurable)).union
    (hE.compl.preimage D.point_measurable)
  have hWm : σ.real W≤2/1000 := by
    have h₁ := measureReal_union_le (μ:=σ) (s₁:=Prod.fst ⁻¹' Bᶜ) (s₂:=Prod.snd ⁻¹' Bᶜ)
    have h₂ := measureReal_union_le (μ:=σ) (s₁:=Prod.fst ⁻¹' Bᶜ ∪ Prod.snd ⁻¹' Bᶜ) (s₂:=D.point ⁻¹' Bᶜ)
    have h₃ := measureReal_union_le (μ:=σ) (s₁:=Prod.fst ⁻¹' Bᶜ ∪ Prod.snd ⁻¹' Bᶜ ∪ D.point ⁻¹' Bᶜ) (s₂:=D.point ⁻¹' Eᶜ)
    dsimp only [W]
    linarith
  let K := H\(W∩D.carrier)
  have hKm : (19/20:ℝ)≤D.law.real K := by
    have he : D.law.real (W∩D.carrier)=σ.real W := by
      simp only [σ,SwitchData.retained,Measure.real,Measure.restrict_apply hW]
    have hh := le_measureReal_sdiff (μ:=D.law) (s₁:=H) (s₂:=W∩D.carrier)
    rw [he] at hh
    change _≤D.law.real K at hh
    linarith
  refine ⟨K,hH.diff (hW.inter D.carrier_measurable),sdiff_subset,hKm,?_⟩
  intro p hp
  have hpW : p∉W := fun hh => hp.2 ⟨hh,hHG hp.1⟩
  change ¬(((p.1∉B ∨ p.2∉B) ∨ D.point p∉B) ∨ D.point p∉E) at hpW
  tauto
end SmoothObstruction.SwitchData

namespace SmoothObstruction.WordHierarchy
open MeasureTheory Filter Topology WordParameters WordAlphabet WordStep WordConcatenation

lemma cell_cost {J : Type*} [Fintype J] [Nonempty J]
    (i Q n : ℕ) (hQ : 2 ≤ Q) (hn : length 40000 i*Q=n)
    {B C : ℝ} (hB : 0≤B)
    (hc : |C| *(B/rate 40000 i)≤(3/1000:ℝ)*Real.log 2)
    (hcard : (Fintype.card J:ℝ)≤Real.exp (C*B*n)) :
    Real.log (Fintype.card J)≤(3/500:ℝ)*(Q-1:ℕ)*Real.log (Fintype.card (A i)) := by
  have hm : (0:ℝ)<length 40000 i := by exact_mod_cast length_pos 40000 i
  have hL : 0≤ell (S i) := ell_nonneg _
  have hR : 0<rate 40000 i := rate_pos initial_threshold i
  have hrate : rate 40000 i*(length 40000 i:ℝ)=ell (S i) := by
    dsimp only [rate,S]
    exact div_mul_cancel₀ _ hm.ne'
  have hc' : C*B≤(3/1000:ℝ)*Real.log 2*rate 40000 i := by
    have hh : |C| *B≤(3/1000:ℝ)*Real.log 2*rate 40000 i := by
      apply (div_le_iff₀ hR).mp
      simpa only [mul_div_assoc] using hc
    exact (mul_le_mul_of_nonneg_right (le_abs_self C) hB).trans hh
  have hnR : (n:ℝ)=(length 40000 i:ℝ)*Q := by exact_mod_cast hn.symm
  have hc'' : C*B*n≤(3/1000:ℝ)*Q*Real.log (Fintype.card (A i)) := by
    have hh := mul_le_mul_of_nonneg_right hc' (show (0:ℝ)≤length 40000 i*Q by positivity)
    rw [←hnR] at hh
    apply hh.trans_eq
    rw [WordHierarchy.log_card,hnR]
    calc
      _ = (3/1000:ℝ)*Q*(rate 40000 i*length 40000 i)*Real.log 2 := by ring
      _ = _ := by rw [hrate]; ring
  have hlog : 0≤Real.log (Fintype.card (A i)) := by
    rw [WordHierarchy.log_card]
    exact mul_nonneg hL (Real.log_nonneg (by norm_num))
  have hQr : (Q:ℝ)≤2*(Q-1:ℕ) := by exact_mod_cast (show Q≤2*(Q-1) by omega)
  calc
    Real.log (Fintype.card J) ≤ C*B*n := (Real.log_le_iff_le_exp (by exact_mod_cast Fintype.card_pos)).mpr hcard
    _ ≤ _ := hc''
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_right hQr hlog]

lemma cheap_index_tendsto (i j : ℕ → ℕ) (hi : Tendsto i atTop atTop)
    (hj : ∀ a,j a∈testScales 40000 (i a)) : Tendsto j atTop atTop := by
  apply tendsto_atTop_mono (fun a => ?_) hi
  have hh := (Finset.mem_Icc.mp (hj a)).1
  have hl : i a ≤ logLevel 40000 (i a) := (logLevel_strictMono initial_threshold).id_le (i a)
  omega
end SmoothObstruction.WordHierarchy

namespace SmoothObstruction.WordHierarchy
open Set MeasureTheory WordParameters WordAlphabet WordStep WordConcatenation FiniteLaw
open scoped ENNReal

noncomputable def initialSymbol (x : Extension) : A 0 := x.val.1 0
lemma measurable_initialSymbol : Measurable initialSymbol := by
  unfold initialSymbol
  fun_prop

lemma iterate_forward_inverse {X : Type*} (e : X ≃ X) (n t : ℕ) (ht : t ≤ n) (x : X) :
    (e^[t]) ((e.symm^[n]) x)=(e.symm^[n-t]) x := by
  calc
    _ = (e^[t]) ((e.symm^[t]) ((e.symm^[n-t]) x)) := by
      rw [←Function.iterate_add_apply,Nat.add_sub_of_le ht]
    _ = _ := (Function.LeftInverse.iterate (fun x => e.apply_symm_apply x) t) _

lemma statistic_symm (i Q : ℕ) (u v : Fin (Q-1) → A i) :
    PairUpper.statistic (form (S i)) u v=PairUpper.statistic (form (S i)) v u := by
  unfold PairUpper.statistic
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [form_symm]

variable {M : Type} [MeasurableSpace M]
  (μ : Measure Extension) [IsProbabilityMeasure μ]
  (ν : Measure M) [IsProbabilityMeasure ν]
  (R : M ≃ M) (hR : MeasurePreserving R ν ν) (hRi : MeasurePreserving R.symm ν ν)
  (r : M → Extension) (hr : MeasurePreserving r ν μ)
  (B : Set M) (hBinv : R.symm ⁻¹' B=B)
  (hforward : ∀ t,∀ x∈B,r ((R^[t]) x)=(T^[t]) (r x))

include hforward in
omit [MeasurableSpace M] in
lemma pull_symbol (t : ℕ) (x : M) (hx : x∈B) :
    initialSymbol (r ((R^[t]) x))=(r x).val.1 t := by
  rw [hforward t x hx]
  exact (actual_iterate_symbol (r x) t 0).trans (by rw [zero_add])

include hBinv hforward in
omit [MeasurableSpace M] in
lemma pull_past_symbol (n t : ℕ) (ht : t ≤ n) (x : M) (hx : x∈B) :
    initialSymbol (r ((R.symm^[n-t]) x))=(r ((R.symm^[n]) x)).val.1 t := by
  have hb := ConullTransport.invariant_iterates R.symm B hBinv n x hx
  have hh := pull_symbol R r B hforward t ((R.symm^[n]) x) hb
  rwa [iterate_forward_inverse R n t ht] at hh

include hBinv hforward in
omit [MeasurableSpace M] in
lemma pull_past_advance (n : ℕ) (x : M) (hx : x∈B) :
    (T^[n]) (r ((R.symm^[n]) x))=r x := by
  have hb := ConullTransport.invariant_iterates R.symm B hBinv n x hx
  rw [←hforward n _ hb,iterate_forward_inverse R n n le_rfl,Nat.sub_self,Function.iterate_zero_apply]

include hr hRi in
lemma transported_graph_bad (hT : MeasurePreserving T μ μ) (i k n : ℕ)
    (hk : k ≤ K (S i)/8) :
    ν.real {x | graphWindows i k (advance i (r ((R.symm^[n]) x)))}ᶜ ≤ 1/1000 := by
  have hp := hr.comp (hRi.iterate n)
  have hG : MeasurableSet {x | graphWindows i k (advance i x)} :=
    (measurable_graphWindows i k).preimage (measurable_advance i)
  have he : ν.real {x | graphWindows i k (advance i (r ((R.symm^[n]) x)))}=
      μ.real {x | graphWindows i k (advance i x)} := by
    simp only [Measure.real]
    rw [←hp.map_eq,Measure.map_apply hp.measurable hG]
    rfl
  have hE : MeasurableSet {x | graphWindows i k (advance i (r ((R.symm^[n]) x)))} :=
    hG.preimage hp.measurable
  rw [measureReal_compl hE,probReal_univ,he]
  have hh := stationary_graph_probability μ hT i k hk
  have hb := graph_bad_small i k hk
  linarith

include hr hRi hBinv hforward in
/-- Conull guards, both full-half original names, and the graph test are joined
in the ORIGINAL cell-weighted law. The two entries keep their original order. -/
theorem transported_success (hT : MeasurePreserving T μ μ)
    (hB : MeasurableSet B) (hBc : ν Bᶜ=0)
    (i k : ℕ) (hk : k ≤ K (S i)/8) (hQ : 2 ≤ 2^k)
    (D : SwitchData ν) (hdom : D.retained.map D.point≤(2:ℝ≥0∞) • ν)
    (H : Set (M×M)) (hH : MeasurableSet H) (hHG : H⊆D.carrier)
    (hHm : (98/100:ℝ)≤D.law.real H)
    (hgood : ∀ p∈H,
      (mismatches (fun t : Fin (2^k*length 40000 i) => initialSymbol (r ((R^[t.val]) p.1)))
        (fun t : Fin (2^k*length 40000 i) => initialSymbol (r ((R^[t.val]) (D.point p)))):ℝ)<
          (3/400:ℝ)*(2^k*length 40000 i) ∧
      (mismatches (fun t : Fin (2^k*length 40000 i) => initialSymbol (r ((R.symm^[2^k*length 40000 i-t.val]) p.2)))
        (fun t : Fin (2^k*length 40000 i) => initialSymbol (r ((R.symm^[2^k*length 40000 i-t.val]) (D.point p)))):ℝ)<
          (3/400:ℝ)*(2^k*length 40000 i)) :
    ∃ F : Set (M×M),MeasurableSet F ∧ (19/20:ℝ)≤D.law.real F ∧
      ∀ p∈F,(24/25:ℝ)≤PairUpper.statistic (form (S i))
        (firstList i (2^k) (r p.1))
        (firstList i (2^k) (r ((R.symm^[2^k*length 40000 i]) p.2))) := by
  let n := 2^k*length 40000 i
  let E := {x | graphWindows i k (advance i (r ((R.symm^[n]) x)))}
  have hE : MeasurableSet E := (measurable_graphWindows i k).preimage
    ((measurable_advance i).comp (hr.measurable.comp (hRi.measurable.iterate n)))
  have hEc : ν.real Eᶜ≤1/1000 := transported_graph_bad μ ν R hRi r hr hT i k n hk
  obtain ⟨F,hF,hFH,hFm,hguard⟩ := D.retain_statistic ν hdom H hH hHG hHm B E hB hE hBc hEc
  refine ⟨F,hF,hFm,?_⟩
  intro p hp
  obtain ⟨hx,hy,hz,hgraph⟩ := hguard p hp
  obtain ⟨hf,hp'⟩ := hgood p (hFH hp)
  have hfc : (mismatches (fun t : Fin n => (r p.1).val.1 t.val)
      (fun t : Fin n => (r (D.point p)).val.1 t.val):ℝ)<(3/4:ℝ)*(2^k*length 40000 i)/100 := by
    have he₁ : (fun t : Fin n => initialSymbol (r ((R^[t.val]) p.1)))=
        (fun t : Fin n => (r p.1).val.1 t.val) := by
      funext t; exact pull_symbol R r B hforward t.val p.1 hx
    have he₂ : (fun t : Fin n => initialSymbol (r ((R^[t.val]) (D.point p))))=
        (fun t : Fin n => (r (D.point p)).val.1 t.val) := by
      funext t; exact pull_symbol R r B hforward t.val (D.point p) hz
    rw [he₁,he₂] at hf
    convert hf using 1; ring
  have hpc : (mismatches (fun t : Fin n => (r ((R.symm^[n]) p.2)).val.1 t.val)
      (fun t : Fin n => (r ((R.symm^[n]) (D.point p))).val.1 t.val):ℝ)<(3/4:ℝ)*(2^k*length 40000 i)/100 := by
    have he₁ : (fun t : Fin n => initialSymbol (r ((R.symm^[n-t.val]) p.2)))=
        (fun t : Fin n => (r ((R.symm^[n]) p.2)).val.1 t.val) := by
      funext t; exact pull_past_symbol R r B hBinv hforward n t.val (Nat.le_of_lt t.isLt) p.2 hy
    have he₂ : (fun t : Fin n => initialSymbol (r ((R.symm^[n-t.val]) (D.point p))))=
        (fun t : Fin n => (r ((R.symm^[n]) (D.point p))).val.1 t.val) := by
      funext t; exact pull_past_symbol R r B hBinv hforward n t.val (Nat.le_of_lt t.isLt) (D.point p) hz
    rw [he₁,he₂] at hp'
    convert hp' using 1; ring
  have hfr := (actual_recovery i (2^k) hQ (r p.1) (r (D.point p)) (by simpa only [Nat.cast_pow,Nat.cast_ofNat] using hfc)).2
  have hpr := (actual_recovery i (2^k) hQ (r ((R.symm^[n]) p.2))
    (r ((R.symm^[n]) (D.point p))) (by simpa only [Nat.cast_pow,Nat.cast_ofNat] using hpc)).2
  have had := pull_past_advance R r B hBinv hforward n (D.point p) hz
  have hfr' : (mismatches (firstList i (2^k) (r p.1))
      (firstList i (2^k) ((T^[n]) (r ((R.symm^[n]) (D.point p))))):ℝ)<(2^k:ℕ)/100 := by
    rw [had]
    exact hfr
  have hh := actual_passing_lower i k hQ (r p.1) (r ((R.symm^[n]) p.2))
    (r ((R.symm^[n]) (D.point p))) hpr hfr' hgraph
  rwa [statistic_symm] at hh
end SmoothObstruction.WordHierarchy

namespace SmoothObstruction.WordHierarchy
open MeasureTheory Set Filter Topology WordParameters WordAlphabet WordStep WordConcatenation FiniteLaw
open scoped ENNReal

/-- The obstruction for the genuine word extension, using the entire smooth
switching property and exact invariant-conull transport, not a factor-only
or globally defined conjugacy substitute. -/
theorem no_switching {M : Type} [MetricSpace M] [CompactSpace M]
    [MeasurableSpace M] [BorelSpace M] [Nonempty M]
    (μ : Measure Extension) [IsProbabilityMeasure μ] (hT : MeasurePreserving T μ μ)
    (ν : Measure M) [IsProbabilityMeasure ν]
    (R : M ≃ M) (hR : MeasurePreserving R ν ν) (hRi : MeasurePreserving R.symm ν ν)
    (r : M → Extension) (hr : MeasurePreserving r ν μ)
    (B : Set M) (hB : MeasurableSet B) (hBc : ν Bᶜ=0) (hBinv : R.symm ⁻¹' B=B)
    (hforward : ∀ t,∀ x∈B,r ((R^[t]) x)=(T^[t]) (r x))
    (hswitch : SmoothSwitching ν R R.symm) : False := by
  classical
  obtain ⟨δ,hδ,hδworks⟩ := SymbolMass.symbol_success ν R R.symm hR hRi
    (initialSymbol ∘ r) (measurable_initialSymbol.comp hr.measurable)
  obtain ⟨b,C,Ds,hb,hbs,hDs,hshadow⟩ := hswitch (1/100) (by norm_num)
  obtain ⟨ii,jj,hij,hjt,hit,hcheap,hwindow⟩ := actual_cheap_scales initial_threshold hb hbs
  have hjtend := cheap_index_tendsto ii jj hit hjt
  have heC : ∀ᶠ a in atTop,|C| *(b (jj a)/rate 40000 (ii a))≤(3/1000:ℝ)*Real.log 2 := by
    have h : Tendsto (fun a => |C| *(b (jj a)/rate 40000 (ii a))) atTop (𝓝 0) := by
      simpa only [mul_zero] using hcheap.const_mul |C|
    have hp : (0:ℝ)<(3/1000:ℝ)*Real.log 2 := mul_pos (by norm_num) (Real.log_pos (by norm_num))
    exact h.eventually_le_const hp
  have hei : ∀ᶠ a in atTop,1 ≤ ii a := hit.eventually (eventually_ge_atTop 1)
  obtain ⟨a,hai,haC,haD,hash⟩ := (hei.and (heC.and ((hjtend.eventually hDs).and
    (hjtend.eventually (hshadow δ hδ))))).exists
  obtain ⟨k,hkmin,hk,hwin,hQ⟩ := hwindow a
  let i := ii a
  let j := jj a
  let D := Ds j
  have hin : 1 ≤ i := hai
  have hkn : k≤K (S i)/8 := hk
  have hwin' : 2^k*length 40000 i=2^j := by simpa only [Nat.mul_comm] using hwin
  have hm : (99/100:ℝ)≤D.law.real D.carrier := by
    have hh := haD.2.1
    norm_num at hh
    exact hh
  have hn : 0<2^j := by positivity
  obtain ⟨H,hH,hHG,hHm,hgood⟩ := hδworks D (2^j) hn hm haD.2.2 hash
  rw [←hwin'] at hgood
  obtain ⟨F,hF,hFm,hpass⟩ := transported_success μ ν R hRi r hr B hBinv hforward
    hT hB hBc i k hkn hQ D haD.2.2 H hH hHG hHm
      (by simpa only [Function.comp_apply,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat] using hgood)
  let U : M → Fin (2^k-1) → A i := firstList i (2^k) ∘ r
  let W : M → Fin (2^k-1) → A i := firstList i (2^k) ∘ r ∘ (R.symm^[2^k*length 40000 i])
  have hU : Measurable U := (measurable_firstList i (2^k)).comp hr.measurable
  have hpast := hr.comp (hRi.iterate (2^k*length 40000 i))
  have hW : Measurable W := (measurable_firstList i (2^k)).comp hpast.measurable
  have hDmax : 2^k-1≤WordStep.D (S i) := by
    exact (Nat.sub_le _ _).trans (Nat.pow_le_pow_right (by decide) hkn)
  have hent := firstList_entropy μ hT hin hQ hDmax
  have hentU : (249/250:ℝ)*(2^k-1:ℕ)*Real.log (Fintype.card (A i))≤
      entropy (observed ν U hU) := by
    have hh := observed_preserving ν μ r hr (firstList i (2^k)) (measurable_firstList i (2^k))
    change observed ν U hU=_ at hh
    rw [hh]
    exact hent
  have hentW : (249/250:ℝ)*(2^k-1:ℕ)*Real.log (Fintype.card (A i))≤
      entropy (observed ν W hW) := by
    have hh := observed_preserving ν μ (r ∘ (R.symm^[2^k*length 40000 i])) hpast
      (firstList i (2^k)) (measurable_firstList i (2^k))
    change observed ν W hW=_ at hh
    rw [hh]
    exact hent
  let : Nonempty D.J := ⟨D.label (Classical.choice ‹Nonempty M›)⟩
  have hC : Real.log (Fintype.card D.J)≤(3/500:ℝ)*(2^k-1:ℕ)*Real.log (Fintype.card (A i)) :=
    cell_cost i (2^k) (2^j) hQ hwin (hb _).le haC haD.1
  let : NeZero (2^k-1) := ⟨by omega⟩
  let v : A i := Classical.choice (levelNonempty i)
  let : Nontrivial (Space (S i)) := ⟨⟨v.val,0,v.property⟩⟩
  apply PairUpper.no_success_event ν D.label D.label_measurable U W hU hW (form (S i))
    (form_nondegenerate _) (by simpa only [Fintype.card_fin] using hentU)
    (by simpa only [Fintype.card_fin] using hentW)
    (by simpa only [Fintype.card_fin] using hC) (alphabet_log_large i) F hF hFm
  exact hpass
end SmoothObstruction.WordHierarchy

end

end OAI
