import OAI.Probability.DirectionalWalk.RenewalMass

namespace OAI

open MeasureTheory ProbabilityTheory Filter Preorder
open scoped ENNReal BigOperators Topology

namespace DirectionalZeroOne

open scoped Classical

def interlace {α β γ δ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] [MeasurableSpace δ] : (α × β) × (γ × δ) ≃ᵐ (α × γ) × (β × δ) where
  toEquiv := Equiv.prodProdProdComm α β γ δ
  measurable_toFun := by dsimp [Equiv.prodProdProdComm];fun_prop
  measurable_invFun := by dsimp [Equiv.prodProdProdComm];fun_prop

lemma compProd_product {α β γ δ : Type*} [Countable α] [Countable β] [Countable γ] [Countable δ]
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] [MeasurableSpace δ]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    [MeasurableSingletonClass γ] [MeasurableSingletonClass δ]
    (μ : Measure α) (ν : Measure γ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (κ : Kernel α β) (η : Kernel γ δ) [IsMarkovKernel κ] [IsMarkovKernel η] :
    (μ.prod ν) ⊗ₘ (κ ∥ₖ η) = ((μ ⊗ₘ κ).prod (ν ⊗ₘ η)).map interlace := by
  apply Measure.ext_of_singleton
  rintro ⟨⟨a,c⟩,⟨b,d⟩⟩
  rw [compProd_atom,Kernel.parallelComp_apply,Measure.map_apply interlace.measurable (measurableSet_singleton _)]
  have hh : interlace ⁻¹' {((a,c),(b,d))} = {((a,b),(c,d))} := by
    ext p
    simp only [Set.mem_preimage,Set.mem_singleton_iff,interlace,MeasurableEquiv.coe_mk,
      Equiv.prodProdProdComm_apply,Prod.ext_iff]
    tauto
  rw [hh]
  simp only [← Set.singleton_prod_singleton,Measure.prod_prod]
  rw [Set.singleton_prod_singleton,Set.singleton_prod_singleton,compProd_atom,compProd_atom]
  ring

lemma graph_product_kl {α β γ δ : Type*} [Countable α] [Countable β] [Countable γ] [Countable δ]
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] [MeasurableSpace δ]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    [MeasurableSingletonClass γ] [MeasurableSingletonClass δ]
    (μ : Measure α) (ν : Measure γ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (f : α → β) (g : γ → δ)
    (κ : Kernel β α) (η : Kernel δ γ) [IsMarkovKernel κ] [IsMarkovKernel η] :
    InformationTheory.klDiv ((μ.prod ν).map (fun a => ((f a.1,g a.2),a)))
      (((μ.prod ν).map (fun a => (f a.1,g a.2))) ⊗ₘ (κ ∥ₖ η)) =
    InformationTheory.klDiv (μ.map (fun a => (f a,a))) ((μ.map f) ⊗ₘ κ) +
      InformationTheory.klDiv (ν.map (fun a => (g a,a))) ((ν.map g) ⊗ₘ η) := by
  have : IsProbabilityMeasure (μ.map f) := probabilityMeasure_map (measurable_of_countable _).aemeasurable
  have : IsProbabilityMeasure (ν.map g) := probabilityMeasure_map (measurable_of_countable _).aemeasurable
  have : IsProbabilityMeasure (μ.map (fun a => (f a,a))) := probabilityMeasure_map (measurable_of_countable _).aemeasurable
  have : IsProbabilityMeasure (ν.map (fun a => (g a,a))) := probabilityMeasure_map (measurable_of_countable _).aemeasurable
  have hm : (μ.prod ν).map (fun a => (f a.1,g a.2)) = (μ.map f).prod (ν.map g) :=
    (Measure.map_prod_map μ ν (measurable_of_countable _) (measurable_of_countable _)).symm
  rw [hm,compProd_product,product_graph μ ν f g (measurable_of_countable _) (measurable_of_countable _)]
  change InformationTheory.klDiv (Measure.map interlace _) (Measure.map interlace _) = _
  rw [klDiv_map_equiv,klDiv_product]

abbrev ThreeChunk (α : Type*) := TwoTapeList α × (TwoTapeList α × TwoTapeList α)

noncomputable def threeChunkLaw {α : Type*} [MeasurableSpace α]
    (ν : Bool → Measure α) [∀ b, IsProbabilityMeasure (ν b)] (L : Bool → α → ℕ) (n : ℕ) :
    Measure (ThreeChunk α) :=
  (windowCommonLaw ν L n n).prod ((windowCommonLaw ν L (7*n) n).prod (windowCommonLaw ν L n n))

instance threeChunkLaw_probability {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (ν : Bool → Measure α) [∀ b, IsProbabilityMeasure (ν b)]
    (L : Bool → α → ℕ) (n : ℕ) [NeZero n] : IsProbabilityMeasure (threeChunkLaw ν L n) :=
  inferInstanceAs (IsProbabilityMeasure ((windowCommonLaw ν L n n).prod
    ((windowCommonLaw ν L (7*n) n).prod (windowCommonLaw ν L n n))))

noncomputable def threeHeight {α : Type*} (L : Bool → α → ℕ) (a : ThreeChunk α) : ℕ × (ℕ × ℕ) :=
  (chunkHeight L a.1,chunkHeight L a.2.1,chunkHeight L a.2.2)

noncomputable def threeBridgeKernel {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (ν : Bool → Measure α) [∀ b, IsProbabilityMeasure (ν b)]
    (L : Bool → α → ℕ) : Kernel (ℕ × (ℕ × ℕ)) (ThreeChunk α) :=
  pairBridgeKernel ν L ∥ₖ (pairBridgeKernel ν L ∥ₖ pairBridgeKernel ν L)

lemma threeBridgeKernel_markov {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (ν : Bool → Measure α) [∀ b, IsProbabilityMeasure (ν b)]
    (L : Bool → α → ℕ)
    (hu : ∀ H b, Measure.infinitePi (fun _ : ℕ => ν b) (renewalCut (L b) H) ≠ 0) :
    IsMarkovKernel (threeBridgeKernel ν L) := by
  let : IsMarkovKernel (pairBridgeKernel ν L) := pairBridgeKernel_markov ν L hu
  unfold threeBridgeKernel
  infer_instance

lemma threeChunk_kl_uniform {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (ν : Bool → Measure α) [∀ b, IsProbabilityMeasure (ν b)]
    (L : Bool → α → ℕ) (hL : ∀ b, ∀ᵐ a ∂ν b, 0 < L b a)
    (he : ∀ᵐ Z ∂twoTapeLaw ν, ∃ H, 0 < H ∧ Z ∈ commonCut L H)
    (hi : Integrable (fun Z => (firstCommonWidth L Z : ℝ)) (twoTapeLaw ν))
    (hu : ∀ H b, Measure.infinitePi (fun _ : ℕ => ν b) (renewalCut (L b) H) ≠ 0)
    (c : ℝ) (hc : 0 < c) (hlo : ∀ H, ENNReal.ofReal c ≤ renewalPairMass ν L H)
    (n : ℕ) [NeZero n] :
    let P := threeChunkLaw ν L n
    let H := threeHeight L
    let ρ := P.map (fun a => (H a,a))
    let Q := P.map H ⊗ₘ threeBridgeKernel ν L
    InformationTheory.klDiv ρ Q ≠ ∞ ∧
      (InformationTheory.klDiv ρ Q).toReal ≤
        3 * (1+Real.log (8*((∫ Z, (firstCommonWidth L Z : ℝ) ∂twoTapeLaw ν)+1)+1)) := by
  dsimp only
  let : IsMarkovKernel (pairBridgeKernel ν L) := pairBridgeKernel_markov ν L hu
  have hl := window_kl_uniform ν L hL he hi hu c hc hlo n n (by omega)
  have hm := window_kl_uniform ν L hL he hi hu c hc hlo (7*n) n le_rfl
  have hid : InformationTheory.klDiv
      ((threeChunkLaw ν L n).map (fun a => (threeHeight L a,a)))
      ((threeChunkLaw ν L n).map (threeHeight L) ⊗ₘ threeBridgeKernel ν L) =
      InformationTheory.klDiv
        ((windowCommonLaw ν L n n).map (fun a => (chunkHeight L a,a)))
        ((windowCommonLaw ν L n n).map (chunkHeight L) ⊗ₘ pairBridgeKernel ν L) +
      (InformationTheory.klDiv
        ((windowCommonLaw ν L (7*n) n).map (fun a => (chunkHeight L a,a)))
        ((windowCommonLaw ν L (7*n) n).map (chunkHeight L) ⊗ₘ pairBridgeKernel ν L) +
      InformationTheory.klDiv
        ((windowCommonLaw ν L n n).map (fun a => (chunkHeight L a,a)))
        ((windowCommonLaw ν L n n).map (chunkHeight L) ⊗ₘ pairBridgeKernel ν L)) := by
    unfold threeChunkLaw threeHeight threeBridgeKernel
    rw [graph_product_kl (windowCommonLaw ν L n n)
      ((windowCommonLaw ν L (7*n) n).prod (windowCommonLaw ν L n n))
      (chunkHeight L) (fun p : TwoTapeList α × TwoTapeList α =>
        (chunkHeight L p.1,chunkHeight L p.2))
      (pairBridgeKernel ν L) (pairBridgeKernel ν L ∥ₖ pairBridgeKernel ν L),
      graph_product_kl (windowCommonLaw ν L (7*n) n) (windowCommonLaw ν L n n)
      (chunkHeight L) (chunkHeight L) (pairBridgeKernel ν L) (pairBridgeKernel ν L)]
  rw [hid]
  exact ⟨ENNReal.add_ne_top.mpr ⟨hl.1,ENNReal.add_ne_top.mpr ⟨hm.1,hl.1⟩⟩,by
    rw [ENNReal.toReal_add hl.1 (ENNReal.add_ne_top.mpr ⟨hm.1,hl.1⟩),
      ENNReal.toReal_add hm.1 hl.1]
    linarith [hl.2,hm.2]⟩

end DirectionalZeroOne

end OAI
