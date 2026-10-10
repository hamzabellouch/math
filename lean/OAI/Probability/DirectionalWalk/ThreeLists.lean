import OAI.Probability.DirectionalWalk.BufferedComparison

namespace OAI

open MeasureTheory ProbabilityTheory Filter Preorder
open scoped ENNReal BigOperators Topology

namespace DirectionalZeroOne

open scoped Classical

abbrev ThreeLists (α : Type*) := TapeList α × (TapeList α × TapeList α)

def splitThree {α : Type*} (a : ThreeChunk α) : ThreeLists α × ThreeLists α :=
  ((a.1 false,a.2.1 false,a.2.2 false),(a.1 true,a.2.1 true,a.2.2 true))

def joinThree {α : Type*} (p : ThreeLists α × ThreeLists α) : ThreeChunk α :=
  ((fun b => if b then p.2.1 else p.1.1),
    (fun b => if b then p.2.2.1 else p.1.2.1),
    (fun b => if b then p.2.2.2 else p.1.2.2))

lemma split_joinThree {α : Type*} (p : ThreeLists α × ThreeLists α) :
    splitThree (joinThree p) = p := by
  rcases p with ⟨⟨a,b,c⟩,⟨d,e,f⟩⟩
  rfl

lemma join_splitThree {α : Type*} (a : ThreeChunk α) : joinThree (splitThree a) = a := by
  apply Prod.ext
  · funext b;cases b <;> rfl
  · apply Prod.ext <;> (funext b;cases b <;> rfl)

def splitThreeEquiv {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] : ThreeChunk α ≃ᵐ ThreeLists α × ThreeLists α where
  toFun := splitThree
  invFun := joinThree
  left_inv := join_splitThree
  right_inv := split_joinThree
  measurable_toFun := measurable_of_countable _
  measurable_invFun := measurable_of_countable _

noncomputable def oneBridgeKernel {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (ν : Measure α) [IsProbabilityMeasure ν] (L : α → ℕ) :
    Kernel ℕ (TapeList α) where
  toFun := bridgeListLaw ν L
  measurable' := measurable_of_countable _

noncomputable def signedThreeKernel {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (ν : Measure α) [IsProbabilityMeasure ν] (L : α → ℕ) :
    Kernel (ℕ × (ℕ × ℕ)) (ThreeLists α) :=
  oneBridgeKernel ν L ∥ₖ (oneBridgeKernel ν L ∥ₖ oneBridgeKernel ν L)

lemma signedThreeKernel_markov {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (ν : Measure α) [IsProbabilityMeasure ν] (L : α → ℕ)
    (hu : ∀ H, Measure.infinitePi (fun _ : ℕ => ν) (renewalCut L H) ≠ 0) :
    IsMarkovKernel (signedThreeKernel ν L) := by
  let : IsMarkovKernel (oneBridgeKernel ν L) := ⟨fun H => bridgeListLaw_probability ν L H (hu H)⟩
  unfold signedThreeKernel
  infer_instance

lemma pairBridgeLaw_atom_general {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (ν : Bool → Measure α) [∀ b, IsProbabilityMeasure (ν b)]
    (L : Bool → α → ℕ) (H : ℕ) (a : TwoTapeList α) :
    pairBridgeLaw ν L H {a} =
      bridgeListLaw (ν false) (L false) H {a false} * bridgeListLaw (ν true) (L true) H {a true} := by
  have hs : ({a} : Set (TwoTapeList α)) = Set.univ.pi (fun b => {a b}) := by
    ext x
    simp only [Set.mem_singleton_iff,Set.mem_pi,Set.mem_univ,true_implies]
    exact funext_iff
  rw [pairBridgeLaw,hs,Measure.pi_pi,Fintype.prod_bool]
  exact mul_comm _ _

lemma threeBridgeKernel_split {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (ν : Bool → Measure α) [∀ b, IsProbabilityMeasure (ν b)]
    (L : Bool → α → ℕ)
    (hu : ∀ H b, Measure.infinitePi (fun _ : ℕ => ν b) (renewalCut (L b) H) ≠ 0) :
    (threeBridgeKernel ν L).map splitThree =
      signedThreeKernel (ν false) (L false) ×ₖ signedThreeKernel (ν true) (L true) := by
  let : IsMarkovKernel (pairBridgeKernel ν L) := pairBridgeKernel_markov ν L hu
  let : ∀ b, IsMarkovKernel (oneBridgeKernel (ν b) (L b)) :=
    fun b => ⟨fun H => bridgeListLaw_probability (ν b) (L b) H (hu H b)⟩
  apply Kernel.ext
  intro h
  apply Measure.ext_of_singleton
  intro p
  rw [Kernel.map_apply _ (measurable_of_countable _),Measure.map_apply
    (measurable_of_countable _) (measurableSet_singleton _)]
  have hs : splitThree ⁻¹' {p} = {joinThree p} := by
    ext a
    change splitThree a = p ↔ a = joinThree p
    exact ⟨fun h => by rw [← h,join_splitThree],fun h => by rw [h,split_joinThree]⟩
  rw [hs]
  rcases p with ⟨⟨a,b,c⟩,⟨d,e,f⟩⟩
  simp only [joinThree]
  simp only [threeBridgeKernel,signedThreeKernel,Kernel.parallelComp_apply,Kernel.prod_apply,
    ← Set.singleton_prod_singleton,Measure.prod_prod]
  change (pairBridgeLaw ν L h.1 {fun b => if b then d else a}) *
    ((pairBridgeLaw ν L h.2.1 {fun u => if u then e else b}) *
    (pairBridgeLaw ν L h.2.2 {fun b => if b then f else c})) = _
  simp only [pairBridgeLaw_atom_general,Bool.false_eq_true,↓reduceIte]
  simp only [oneBridgeKernel,Kernel.coe_mk]
  ring

end DirectionalZeroOne

end OAI
