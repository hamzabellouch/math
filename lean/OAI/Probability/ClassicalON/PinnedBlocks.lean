import OAI.Probability.ClassicalON.WeightedProduct

namespace OAI

universe uE uK uV

noncomputable section
open MeasureTheory Set
open scoped BigOperators InnerProductSpace Classical
namespace ClassicalON
variable {V : Type uV} {E : Type uE} {K : Type uK} [Fintype V] [Fintype E] [Fintype K]

omit [Fintype E] in
theorem sum_fibers (label : V → K) (f : V → ℝ) :
    (∑ k,∑ v : {v // label v=k},f v.val)=∑ v,f v := by
  rw [← Fintype.sum_sigma (fun v : Σ k : K,{v // label v=k} => f v.2.val)]
  exact (Equiv.sigmaFiberEquiv label).sum_comp f

omit [Fintype E] in
theorem prod_fibers (label : V → K) (f : V → ℝ) :
    (∏ k,∏ v : {v // label v=k},f v.val)=∏ v,f v := by
  rw [← Fintype.prod_sigma (fun v : Σ k : K,{v // label v=k} => f v.2.val)]
  exact (Equiv.sigmaFiberEquiv label).prod_comp f

abbrev BlockVertex (B : Set V) (label : V → K) (k : K) := {v : ↥(Bᶜ) // label v.val=k}

def blockSpin (B : Set V) (label : V → K) (k : K) (s : BlockVertex B label k → Spin 3) : V → Spin 3 :=
  fun v => if hv : v∈B then poleSpin true else
    if hk : label v=k then s ⟨⟨v,hv⟩,hk⟩ else poleSpin true

omit [Fintype V] [Fintype E] [Fintype K] in
theorem continuous_blockSpin (B : Set V) (label : V → K) (k : K) :
    Continuous (blockSpin B label k) := by
  apply continuous_pi
  intro v
  by_cases hv : v∈B
  · simp only [blockSpin,hv,↓reduceDIte]
    exact continuous_const
  · by_cases hk : label v=k
    · simp only [blockSpin,hv,hk,↓reduceDIte]
      exact continuous_apply _
    · simp only [blockSpin,hv,hk,↓reduceDIte]
      exact continuous_const

omit [Fintype V] [Fintype E] [Fintype K] in
theorem blockSpin_eq_glue (B : Set V) (label : V → K) (k : K) (s : ↥(Bᶜ) → Spin 3)
    (v : V) (h : v∉B → label v=k) :
    blockSpin B label k (fun w => s w.val) v=glueFamily B (fun _ => poleSpin true) s v := by
  by_cases hv : v∈B
  · rw [show glueFamily B (fun _ => poleSpin true) s v=poleSpin true from
      glueFamily_in B _ _ ⟨v,hv⟩]
    simp only [blockSpin,hv,↓reduceDIte]
  · rw [show glueFamily B (fun _ => poleSpin true) s v=s ⟨v,hv⟩ from
      glueFamily_out B _ _ ⟨v,hv⟩]
    simp only [blockSpin,hv,h hv,↓reduceDIte]

def blockEnergy (left right : E → V) (b : E → ℝ) (B : Set V) (label : V → K)
    (elabel : E → K) (k : K) (s : BlockVertex B label k → Spin 3) : ℝ :=
  freeSpinEnergy 3 (fun e : {e // elabel e=k} => left e.val) (fun e => right e.val)
    (fun e => b e.val) (blockSpin B label k s)

def blockBondWeight (left right : E → V) (b : E → ℝ) (B : Set V) (label : V → K)
    (elabel : E → K) (k : K) (s : BlockVertex B label k → Spin 3)
    (η : {e // elabel e=k} → Bool) : ℝ :=
  spinBondWeight (fun e : {e // elabel e=k} => left e.val) (fun e => right e.val)
    (fun e => b e.val) (blockSpin B label k s) η

def blockBondMean (left right : E → V) (b : E → ℝ) (B : Set V) (label : V → K)
    (elabel : E → K) (k : K) (f : ({e // elabel e=k} → Bool) → ℝ) : ℝ :=
  weightedMean (Measure.pi (fun _ : BlockVertex B label k => sphereProbability 3))
    (fun s => Real.exp (blockEnergy left right b B label elabel k s))
    (fun s => ∑ η,blockBondWeight left right b B label elabel k s η*f η)

omit [Fintype V] in
theorem block_energy_sum (left right : E → V) (b : E → ℝ) (B : Set V) (label : V → K)
    (elabel : E → K) (hl : ∀ e,left e∉B → label (left e)=elabel e)
    (hr : ∀ e,right e∉B → label (right e)=elabel e) (s : ↥(Bᶜ) → Spin 3) :
    (∑ k,blockEnergy left right b B label elabel k (fun v => s v.val))=
      freeSpinEnergy 3 left right b (glueFamily B (fun _ => poleSpin true) s) := by
  unfold blockEnergy freeSpinEnergy
  have he (k : K) (e : {e // elabel e=k}) :
      b e.val*⟪(blockSpin B label k (fun v => s v.val) (left e.val)).val,
        (blockSpin B label k (fun v => s v.val) (right e.val)).val⟫_ℝ=
      b e.val*⟪(glueFamily B (fun _ => poleSpin true) s (left e.val)).val,
        (glueFamily B (fun _ => poleSpin true) s (right e.val)).val⟫_ℝ := by
    rw [blockSpin_eq_glue _ _ _ _ _ (fun h => (hl _ h).trans e.property),
      blockSpin_eq_glue _ _ _ _ _ (fun h => (hr _ h).trans e.property)]
  simp_rw [he]
  convert sum_fibers elabel (fun e => b e*⟪(glueFamily B (fun _ => poleSpin true) s (left e)).val,
    (glueFamily B (fun _ => poleSpin true) s (right e)).val⟫_ℝ) using 1

omit [Fintype V] in
theorem block_bond_product (left right : E → V) (b : E → ℝ) (B : Set V) (label : V → K)
    (elabel : E → K) (hl : ∀ e,left e∉B → label (left e)=elabel e)
    (hr : ∀ e,right e∉B → label (right e)=elabel e) (s : ↥(Bᶜ) → Spin 3) (η : E → Bool) :
    (∏ k,blockBondWeight left right b B label elabel k (fun v => s v.val) (fun e => η e.val))=
      spinBondWeight left right b (glueFamily B (fun _ => poleSpin true) s) η := by
  unfold blockBondWeight spinBondWeight spinBondParameter
  have he (k : K) (e : {e // elabel e=k}) :
      blockSpin B label k (fun v => s v.val) (left e.val)=glueFamily B (fun _ => poleSpin true) s (left e.val) :=
    blockSpin_eq_glue _ _ _ _ _ (fun h => (hl _ h).trans e.property)
  have he' (k : K) (e : {e // elabel e=k}) :
      blockSpin B label k (fun v => s v.val) (right e.val)=glueFamily B (fun _ => poleSpin true) s (right e.val) :=
    blockSpin_eq_glue _ _ _ _ _ (fun h => (hr _ h).trans e.property)
  simp_rw [he,he']
  convert prod_fibers elabel (fun e => if η e then spinBondParameter left right b
    (glueFamily B (fun _ => poleSpin true) s) e else 1-spinBondParameter left right b
    (glueFamily B (fun _ => poleSpin true) s) e) using 1 <;> congr!

theorem poleBondMean_collapse (left right : E → V) (b : E → ℝ) (B : Set V) (f : (E → Bool) → ℝ) :
    poleBondMean left right b B (fun _ => true) f=
      weightedMean (Measure.pi (fun _ : ↥(Bᶜ) => sphereProbability 3))
        (fun s => Real.exp (freeSpinEnergy 3 left right b (glueFamily B (fun _ => poleSpin true) s)))
        (fun s => ∑ η,spinBondWeight left right b (glueFamily B (fun _ => poleSpin true) s) η*f η) := by
  unfold poleBondMean weightedMean
  rw [poleSystem_reference]
  have hc : Continuous (fun s : V → Spin 3 => Real.exp (freeSpinEnergy 3 left right b s)*
      ∑ η,spinBondWeight left right b s η*f η) :=
    (continuous_freeSpinEnergy _ _ _ _).rexp.mul
      (continuous_finsetSum _ (fun _ _ => (continuous_spinBondWeight _ _ _ _).mul continuous_const))
  rw [integral_pinProductMeasure _ _ _ _ hc,
    integral_pinProductMeasure _ _ _ _ (continuous_freeSpinEnergy 3 left right b).rexp]

omit [Fintype V] in
theorem block_event_product (left right : E → V) (b : E → ℝ) (B : Set V) (label : V → K)
    (elabel : E → K) (hl : ∀ e,left e∉B → label (left e)=elabel e)
    (hr : ∀ e,right e∉B → label (right e)=elabel e)
    (f : (k : K) → ({e // elabel e=k} → Bool) → ℝ) (s : ↥(Bᶜ) → Spin 3) :
    (∑ η,spinBondWeight left right b (glueFamily B (fun _ => poleSpin true) s) η*
        ∏ k,f k (fun e => η e.val))=
      ∏ k,∑ η,blockBondWeight left right b B label elabel k (fun v => s v.val) η*f k η := by
  have hp (η : E → Bool) := (block_bond_product left right b B label elabel hl hr s η).symm
  simp_rw [hp,← Finset.prod_mul_distrib]
  convert sum_grouped_product (C := fun _ => Bool) elabel (fun k η =>
    blockBondWeight left right b B label elabel k (fun v => s v.val) η*f k η) using 1

theorem poleBondMean_blocks (left right : E → V) (b : E → ℝ) (B : Set V) (label : V → K)
    (elabel : E → K) (hl : ∀ e,left e∉B → label (left e)=elabel e)
    (hr : ∀ e,right e∉B → label (right e)=elabel e)
    (f : (k : K) → ({e // elabel e=k} → Bool) → ℝ) :
    poleBondMean left right b B (fun _ => true) (fun η => ∏ k,f k (fun e => η e.val))=
      ∏ k,blockBondMean left right b B label elabel k (f k) := by
  rw [poleBondMean_collapse]
  have hw (s : ↥(Bᶜ) → Spin 3) :
      Real.exp (freeSpinEnergy 3 left right b (glueFamily B (fun _ => poleSpin true) s))=
      ∏ k,Real.exp (blockEnergy left right b B label elabel k (fun v => s v.val)) := by
    rw [← block_energy_sum _ _ _ _ _ _ hl hr,Real.exp_sum]
  have hf := block_event_product left right b B label elabel hl hr f
  simp_rw [hw,hf]
  unfold blockBondMean
  convert weightedMean_grouped_product (fun _ : ↥(Bᶜ) => Spin 3) (fun v => label v.val)
    (fun _ => sphereProbability 3)
    (fun k s => Real.exp (blockEnergy left right b B label elabel k s))
    (fun k s => ∑ η,blockBondWeight left right b B label elabel k s η*f k η) using 1

end ClassicalON

end

end OAI
