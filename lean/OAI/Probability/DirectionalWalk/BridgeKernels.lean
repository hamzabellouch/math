import OAI.Probability.DirectionalWalk.RenewalFactorization

namespace OAI

open MeasureTheory ProbabilityTheory Filter Preorder
open scoped ENNReal BigOperators Topology

namespace DirectionalZeroOne

open scoped Classical

def InCountWindow {α : Type*} (L : Bool → α → ℕ) (k n : ℕ) (a : TwoTapeList α) : Prop :=
  BalancedList L a ∧ k ≤ listCommonCount L a ∧ listCommonCount L a < k+n

lemma windowCommonLaw_atom {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (ν : Bool → Measure α) [∀ b, IsProbabilityMeasure (ν b)]
    (L : Bool → α → ℕ) (hL : ∀ b, ∀ᵐ a ∂ν b, 0 < L b a)
    (he : ∀ᵐ Z ∂twoTapeLaw ν, ∃ H, 0 < H ∧ Z ∈ commonCut L H)
    (k n : ℕ) (a : TwoTapeList α) :
    windowCommonLaw ν L k n {a} =
      (by classical exact if InCountWindow L k n a then (n : ℝ≥0∞)⁻¹ * twoListWeight ν a else 0) := by
  classical
  rw [windowCommonLaw,Measure.smul_apply,smul_eq_mul,Measure.finsetSum_apply]
  simp_rw [nthCommonLaw_atom ν L hL he]
  by_cases ha : InCountWindow L k n a
  · rw [ite_eq_left ha]
    congr 1
    let i : Fin n := ⟨listCommonCount L a-k,by obtain ⟨_,_,_⟩ := ha;omega⟩
    rw [Finset.sum_eq_single i]
    · exact ite_eq_left ⟨ha.1,by dsimp [i];obtain ⟨_,_,_⟩ := ha;omega⟩
    · intro j _ hji
      apply ite_eq_right
      rintro ⟨_,hj⟩
      apply hji
      apply Fin.ext
      dsimp [i]
      omega
    · simp
  · rw [ite_eq_right ha]
    have hh : ∑ i : Fin n, (if BalancedList L a ∧ listCommonCount L a = k+↑i then
        (∏ b : Bool, ∏ j : Fin (a b).1, ν b {(a b).2 j}) else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      apply ite_eq_right
      rintro ⟨hb,hc⟩
      exact ha ⟨hb,by omega,by omega⟩
    rw [hh,mul_zero]

lemma windowCommonLaw_ae_window {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (ν : Bool → Measure α) [∀ b, IsProbabilityMeasure (ν b)]
    (L : Bool → α → ℕ) (hL : ∀ b, ∀ᵐ a ∂ν b, 0 < L b a)
    (he : ∀ᵐ Z ∂twoTapeLaw ν, ∃ H, 0 < H ∧ Z ∈ commonCut L H)
    (k n : ℕ) : ∀ᵐ a ∂windowCommonLaw ν L k n, InCountWindow L k n a := by
  classical
  filter_upwards [ae_atom_pos (windowCommonLaw ν L k n)] with a ha
  by_contra hn
  rw [windowCommonLaw_atom ν L hL he,ite_eq_right hn] at ha
  exact ha rfl

noncomputable def pairBridgeLaw {α : Type*} [MeasurableSpace α]
    (ν : Bool → Measure α) [∀ b, IsProbabilityMeasure (ν b)]
    (L : Bool → α → ℕ) (H : ℕ) : Measure (TwoTapeList α) :=
  Measure.pi (fun b => bridgeListLaw (ν b) (L b) H)

lemma pairBridgeLaw_probability {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (ν : Bool → Measure α) [∀ b, IsProbabilityMeasure (ν b)]
    (L : Bool → α → ℕ) (H : ℕ)
    (hH : ∀ b, Measure.infinitePi (fun _ : ℕ => ν b) (renewalCut (L b) H) ≠ 0) :
    IsProbabilityMeasure (pairBridgeLaw ν L H) := by
  let : ∀ b, IsProbabilityMeasure (bridgeListLaw (ν b) (L b) H) :=
    fun b => bridgeListLaw_probability (ν b) (L b) H (hH b)
  unfold pairBridgeLaw
  infer_instance

instance bridgeListLaw_finite {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (ν : Measure α) [IsProbabilityMeasure ν]
    (L : α → ℕ) (H : ℕ) : IsFiniteMeasure (bridgeListLaw ν L H) := by
  constructor
  rw [bridgeListLaw,Measure.smul_apply,smul_eq_mul,bridgeListMeasure_mass]
  exact (ENNReal.inv_mul_le_one _).trans_lt (by simp)

lemma pairBridgeLaw_atom {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (ν : Bool → Measure α) [∀ b, IsProbabilityMeasure (ν b)]
    (L : Bool → α → ℕ) (hL : ∀ b, ∀ᵐ a ∂ν b, 0 < L b a) (H : ℕ) (a : TwoTapeList α)
    (ha : ∀ b, listHeight (L b) (a b) = H) :
    pairBridgeLaw ν L H {a} =
      (∏ b : Bool, Measure.infinitePi (fun _ : ℕ => ν b) (renewalCut (L b) H))⁻¹ * twoListWeight ν a := by
  classical
  have hs : ({a} : Set (TwoTapeList α)) = Set.univ.pi (fun b => {a b}) := by
    ext x
    simp only [Set.mem_singleton_iff,Set.mem_pi,Set.mem_univ,true_implies]
    exact funext_iff
  rw [pairBridgeLaw,hs,Measure.pi_pi]
  simp_rw [bridgeListLaw_atom (ν _) (L _) (hL _) H _ (ha _)]
  rw [Finset.prod_mul_distrib]
  change _ * twoListWeight ν a = _ * twoListWeight ν a
  congr 1
  simp only [Fintype.prod_bool]
  exact (ENNReal.mul_inv (Or.inr (measure_ne_top _ _)) (Or.inl (measure_ne_top _ _))).symm

noncomputable def chunkHeight {α : Type*} (L : Bool → α → ℕ) (a : TwoTapeList α) : ℕ :=
  listHeight (L false) (a false)

noncomputable def pairBridgeKernel {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (ν : Bool → Measure α) [∀ b, IsProbabilityMeasure (ν b)]
    (L : Bool → α → ℕ) : Kernel ℕ (TwoTapeList α) where
  toFun := pairBridgeLaw ν L
  measurable' := measurable_of_countable _

lemma pairBridgeKernel_markov {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (ν : Bool → Measure α) [∀ b, IsProbabilityMeasure (ν b)]
    (L : Bool → α → ℕ)
    (hu : ∀ H b, Measure.infinitePi (fun _ : ℕ => ν b) (renewalCut (L b) H) ≠ 0) :
    IsMarkovKernel (pairBridgeKernel ν L) :=
  ⟨fun H => pairBridgeLaw_probability ν L H (hu H)⟩

lemma map_graph_atom {α β : Type*} [Countable α] [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    (μ : Measure α) (f : α → β) (x : α) : μ.map (fun a => (f a,a)) {(f x,x)} = μ {x} := by
  rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _)]
  congr 1
  ext a
  simp only [Set.mem_preimage,Set.mem_singleton_iff,Prod.mk.injEq,and_iff_right_iff_imp]
  rintro rfl
  rfl

lemma map_graph_fst {α β : Type*} [Countable α] [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    (μ : Measure α) (f : α → β) : (μ.map (fun a => (f a,a))).fst = μ.map f := by
  rw [Measure.fst,Measure.map_map measurable_fst (measurable_of_countable _)]
  rfl

lemma window_reference_ac {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (ν : Bool → Measure α) [∀ b, IsProbabilityMeasure (ν b)]
    (L : Bool → α → ℕ) (hL : ∀ b, ∀ᵐ a ∂ν b, 0 < L b a)
    (he : ∀ᵐ Z ∂twoTapeLaw ν, ∃ H, 0 < H ∧ Z ∈ commonCut L H)
    (k n : ℕ) [NeZero n]
    (hu : ∀ H b, Measure.infinitePi (fun _ : ℕ => ν b) (renewalCut (L b) H) ≠ 0) :
    (windowCommonLaw ν L k n).map (fun a => (chunkHeight L a,a)) ≪
      (windowCommonLaw ν L k n).map (chunkHeight L) ⊗ₘ pairBridgeKernel ν L := by
  classical
  let P := windowCommonLaw ν L k n
  let H := chunkHeight L
  let κ := pairBridgeKernel ν L
  let : IsMarkovKernel κ := pairBridgeKernel_markov ν L hu
  have hP : IsProbabilityMeasure P := inferInstance
  apply absolutelyContinuous_of_atoms
  rintro ⟨h,a⟩ hz
  by_contra hap
  have hg : h = H a := by
    by_contra hne
    apply hap
    rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _)]
    have hh : (fun a => (H a,a)) ⁻¹' {(h,a)} = ∅ := by
      ext b
      simp only [Set.mem_preimage,Set.mem_singleton_iff,Prod.mk.injEq,Set.mem_empty_iff_false,iff_false,not_and]
      intro hh hb
      exact hne (hb ▸ hh.symm)
    rw [hh,measure_empty]
  subst h
  rw [map_graph_atom] at hap
  have hw : InCountWindow L k n a := by
    by_contra hn
    exact hap (by rw [windowCommonLaw_atom ν L hL he,ite_eq_right hn])
  have hwa : twoListWeight ν a ≠ 0 := by
    intro hz
    apply hap
    rw [windowCommonLaw_atom ν L hL he,ite_eq_left hw,hz,mul_zero]
  have hx : (P.map H) {H a} ≠ 0 := fun hh => hap (le_antisymm ((atom_le_map P H (measurable_of_countable _) a).trans hh.le) bot_le)
  have hκ : κ (H a) {a} ≠ 0 := by
    change pairBridgeLaw ν L (H a) {a} ≠ 0
    rw [pairBridgeLaw_atom ν L hL (H a) a hw.1]
    exact mul_ne_zero (ENNReal.inv_ne_zero.mpr (ENNReal.prod_ne_top (fun _ _ => measure_ne_top _ _))) hwa
  exact (mul_ne_zero hx hκ) (by simpa only [compProd_atom] using hz)

end DirectionalZeroOne

end OAI
