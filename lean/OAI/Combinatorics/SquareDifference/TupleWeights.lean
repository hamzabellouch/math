import OAI.Combinatorics.SquareDifference.CrossProducts

namespace OAI

section
open Finset
open scoped BigOperators
namespace SquareDifference
open scoped Classical

lemma expect_two_evals {I X : Type*} [Fintype I] [DecidableEq I] [Fintype X] [Nonempty X]
    (i j : I) (hij : i≠j) (f : X → X → ℝ) :
    (𝔼 Y : I → X, f (Y i) (Y j))=𝔼 x, 𝔼 y, f x y := by
  let j' : {k : I // k≠i} := ⟨j, hij.symm⟩
  have h := Fintype.expect_equiv (Equiv.funSplitAt i X) (fun Y => f (Y i) (Y j))
    (fun z => f z.1 (z.2 j')) (fun _ => rfl)
  rw [h, ← univ_product_univ, expect_product]
  apply expect_congr rfl; intro x _
  exact expect_eval j' (f x)

lemma tupleProjection_cycle_ne (S : Finset (Fin tupleBlocks))
    (hS : S.card≤tupleT+1) (k : ℕ) :
    tupleProjection S (cycleVertex k)≠tupleProjection S (cycleVertex (k+1)) := by
  have hc : 0<Fintype.card {b : Fin tupleBlocks // b∉S} := by
    rw [card_cleanBlocks]
    change 0<161-S.card
    change S.card≤81 at hS
    omega
  obtain ⟨b⟩ := Fintype.card_pos_iff.mp hc
  intro he
  have h : tupleCycle^k=tupleCycle^(k+1) := congrFun he b
  rw [pow_succ] at h
  apply tupleCycle_ne_one
  exact mul_left_cancel (show tupleCycle^k*tupleCycle=tupleCycle^k*1 by simpa using h.symm)

lemma tupleValidity_terminal {p : ℕ} [Fact p.Prime]
    (S : Finset (Fin tupleBlocks)) (hS : S.card=tupleT+1)
    (Y : TupleListEntry S → ZMod p) : tupleValidity S Y=1 := by
  have hn : ¬S.card≤tupleT := by omega
  simp only [tupleValidity, tupleListEdges, ite_eq_right hn, prod_empty]

lemma tupleComponent_pair_uniform {p : ℕ} [Fact p.Prime]
    (S : Finset (Fin tupleBlocks)) (hS : S.card=tupleT+1) (k : ℕ)
    (F : ZMod p → ZMod p → ℝ) :
    tupleComponent S (fun z => F (z (cycleVertex k)) (z (cycleVertex (k+1))))=
      tupleComponent (p := p) S (fun _ => 1)*(𝔼 x, 𝔼 y, F x y) := by
  have he (j : TupleVertex → TupleListIndex S) :
      (𝔼 Y : TupleListEntry S → ZMod p,
        F (tupleOutput S Y j (cycleVertex k)) (tupleOutput S Y j (cycleVertex (k+1))))=
          𝔼 x, 𝔼 y, F x y := by
    apply expect_two_evals
    intro hh
    exact tupleProjection_cycle_ne S hS.le k (congrArg Prod.fst hh)
  unfold tupleComponent
  simp only [tupleValidity_terminal S hS, one_mul, mul_one, Fintype.expect_const]
  rw [expect_comm]
  simp only [← mul_expect, he, ← expect_mul]

lemma filtered_powerset_sum {B M : Type*} [Fintype B] [DecidableEq B] [AddCommMonoid M]
    (n : ℕ) (f : Finset B → M) :
    (∑S∈(univ : Finset (Finset B)).filter (fun S => S.card≤n), f S)=
      ∑S∈(univ : Finset B).powerset, if S.card≤n then f S else 0 := by
  rw [sum_filter, powerset_univ]

lemma filtered_card_split {B M : Type*} [Fintype B] [DecidableEq B] [AddCommMonoid M]
    (n : ℕ) (f : Finset B → M) :
    (∑S∈(univ : Finset (Finset B)).filter (fun S => S.card≤n+1), f S)=
      (∑S∈(univ : Finset (Finset B)).filter (fun S => S.card≤n), f S)+
      (∑S∈(univ : Finset (Finset B)).filter (fun S => S.card=n+1), f S) := by
  simp only [sum_filter, ← sum_add_distrib]
  apply sum_congr rfl
  intro S _
  by_cases h : S.card≤n
  · simp only [ite_eq_left h, ite_eq_left (h.trans (Nat.le_succ _)), ite_eq_right (by omega : S.card≠n+1), add_zero]
  · by_cases he : S.card=n+1
    · simp only [ite_eq_left he, ite_eq_left he.le, ite_eq_right h, zero_add]
    · simp only [ite_eq_right h, ite_eq_right he, ite_eq_right (by omega : ¬S.card≤n+1), add_zero]

noncomputable def tupleFamily (n : ℕ) : Finset (Finset (Fin tupleBlocks)) :=
  univ.filter (fun S => S.card≤n)

lemma mem_tupleFamily {n : ℕ} {S : Finset (Fin tupleBlocks)} : S∈tupleFamily n ↔ S.card≤n := by
  simp only [tupleFamily, mem_filter, mem_univ, true_and]

lemma empty_mem_tupleFamily (n : ℕ) : ∅∈tupleFamily n :=
  mem_tupleFamily.mpr (by simp only [card_empty, Nat.zero_le])

lemma tupleSubmixture_full {p : ℕ} [Fact p.Prime] :
    tupleSubmixture (p := p) (tupleFamily (tupleT+1))=tupleMixtureMap := by
  apply LinearMap.ext
  intro F
  rw [tupleSubmixture_apply, tupleMixtureMap_apply]
  exact filtered_powerset_sum (tupleT+1) (fun S => tupleMixtureWeight p S*tupleComponent S F)

lemma tupleSubLaw_full {p : ℕ} [Fact p.Prime] :
    tupleSubLaw (p := p) (tupleFamily (tupleT+1))=tupleLaw := by
  rw [tupleSubLaw, tupleSubmixture_full]
  simp only [tupleLaw, tupleMixtureMap_apply]

noncomputable def tupleGoodLaw {p : ℕ} [Fact p.Prime] :
    ((TupleVertex → ZMod p) → ℝ) →ₗ[ℝ] ℝ := tupleSubLaw (tupleFamily tupleT)

noncomputable def tupleTerminalFamily : Finset (Finset (Fin tupleBlocks)) :=
  univ.filter (fun S => S.card=tupleT+1)

lemma mem_tupleTerminalFamily {S : Finset (Fin tupleBlocks)} :
    S∈tupleTerminalFamily ↔ S.card=tupleT+1 := by
  simp only [tupleTerminalFamily, mem_filter, mem_univ, true_and]

lemma tupleSubmixture_split {p : ℕ} [Fact p.Prime] :
    tupleMixtureMap (p := p)=tupleSubmixture (tupleFamily tupleT)+tupleSubmixture tupleTerminalFamily := by
  rw [← tupleSubmixture_full]
  apply LinearMap.ext
  intro F
  simp only [LinearMap.add_apply, tupleSubmixture_apply]
  exact filtered_card_split tupleT (fun S => tupleMixtureWeight p S*tupleComponent S F)

noncomputable def tupleExceptionalLaw {p : ℕ} [Fact p.Prime] :
    ((TupleVertex → ZMod p) → ℝ) →ₗ[ℝ] ℝ :=
  (tupleMixture (p := p) (fun _ => 1))⁻¹ • tupleSubmixture tupleTerminalFamily

noncomputable def tupleEta (p : ℕ) [Fact p.Prime] : ℝ := tupleExceptionalLaw (p := p) (fun _ => 1)

lemma tupleExceptionalLaw_nonneg {p : ℕ} [Fact p.Prime]
    (F : (TupleVertex → ZMod p) → ℝ) (hF : ∀z, 0≤F z) :
    0≤tupleExceptionalLaw F :=
  mul_nonneg (inv_nonneg.mpr (tupleMixture_nonneg _ (fun _ => by norm_num)))
    (tupleSubmixture_nonneg _ F hF)

lemma tupleEta_nonneg (p : ℕ) [Fact p.Prime] : 0≤tupleEta p :=
  tupleExceptionalLaw_nonneg _ (fun _ => by norm_num)

lemma tupleLaw_decomposition {p : ℕ} [Fact p.Prime]
    (hp : tupleMassThreshold≤(p : ℝ)) :
    tupleLaw (p := p)=(1-tupleEta p) • tupleGoodLaw+tupleExceptionalLaw := by
  have hm := lt_of_lt_of_le tupleLeadingMassLower_pos (tupleMixture_mass_lower hp)
  have hg := lt_of_lt_of_le tupleLeadingMassLower_pos
    (tupleSubmixture_mass_lower hp (tupleFamily tupleT) (empty_mem_tupleFamily _))
  have hs : tupleMixture (p := p) (fun _ => 1)=
      tupleSubmixture (p := p) (tupleFamily tupleT) (fun _ => 1)+tupleSubmixture (p := p) tupleTerminalFamily (fun _ => 1) := by
    rw [← tupleMixtureMap_apply, tupleSubmixture_split, LinearMap.add_apply]
  have hc : 1-tupleEta p=(tupleMixture (p := p) (fun _ => 1))⁻¹*
      tupleSubmixture (p := p) (tupleFamily tupleT) (fun _ => 1) := by
    unfold tupleEta tupleExceptionalLaw
    simp only [LinearMap.smul_apply, smul_eq_mul]
    calc
      _ = (tupleMixture (p := p) (fun _ => 1))⁻¹*tupleMixture (p := p) (fun _ => 1)-
          (tupleMixture (p := p) (fun _ => 1))⁻¹*tupleSubmixture (p := p) tupleTerminalFamily (fun _ => 1) := by
        rw [inv_mul_cancel₀ hm.ne']
      _ = _ := by rw [hs]; ring
  rw [tupleLaw, tupleSubmixture_split, smul_add, hc]
  simp only [tupleGoodLaw, tupleSubLaw, smul_smul, mul_assoc, mul_inv_cancel₀ hg.ne', mul_one,
    tupleExceptionalLaw]

lemma tupleGoodLaw_pair {p : ℕ} [Fact p.Prime]
    (hp : tupleMassThreshold≤(p : ℝ)) (k : ℕ) (F : ZMod p → ZMod p → ℝ) :
    tupleGoodLaw (fun z => F (z (cycleVertex k)) (z (cycleVertex (k+1))))=squarePairAverage F := by
  have hs : tupleSubmixture (tupleFamily tupleT)
      (fun z => F (z (cycleVertex k)) (z (cycleVertex (k+1))))=
      tupleSubmixture (p := p) (tupleFamily tupleT) (fun _ => 1)*squarePairAverage F := by
    simp only [tupleSubmixture_apply, sum_mul]
    apply sum_congr rfl
    intro S hS
    rw [tupleComponent_pair_square S (mem_tupleFamily.mp hS), mul_assoc]
  have hm := lt_of_lt_of_le tupleLeadingMassLower_pos
    (tupleSubmixture_mass_lower hp (tupleFamily tupleT) (empty_mem_tupleFamily _))
  simp only [tupleGoodLaw, tupleSubLaw, LinearMap.smul_apply, smul_eq_mul, hs, ← mul_assoc,
    inv_mul_cancel₀ hm.ne', one_mul]

lemma tupleExceptionalLaw_pair {p : ℕ} [Fact p.Prime]
    (k : ℕ) (F : ZMod p → ZMod p → ℝ) :
    tupleExceptionalLaw (fun z => F (z (cycleVertex k)) (z (cycleVertex (k+1))))=
      tupleEta p*(𝔼 x, 𝔼 y, F x y) := by
  have hs : tupleSubmixture tupleTerminalFamily
      (fun z => F (z (cycleVertex k)) (z (cycleVertex (k+1))))=
      tupleSubmixture (p := p) tupleTerminalFamily (fun _ => 1)*(𝔼 x, 𝔼 y, F x y) := by
    simp only [tupleSubmixture_apply, sum_mul]
    apply sum_congr rfl
    intro S hS
    rw [tupleComponent_pair_uniform S (mem_tupleTerminalFamily.mp hS), mul_assoc]
  simp only [tupleEta, tupleExceptionalLaw, LinearMap.smul_apply, smul_eq_mul, hs, mul_assoc]

lemma tupleLaw_pair {p : ℕ} [Fact p.Prime]
    (hp : tupleMassThreshold≤(p : ℝ)) (k : ℕ) (F : ZMod p → ZMod p → ℝ) :
    tupleLaw (fun z => F (z (cycleVertex k)) (z (cycleVertex (k+1))))=
      (1-tupleEta p)*squarePairAverage F+tupleEta p*(𝔼 x, 𝔼 y, F x y) := by
  rw [tupleLaw_decomposition hp, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
    tupleGoodLaw_pair hp, tupleExceptionalLaw_pair]

lemma tupleGoodLaw_probability {p : ℕ} [Fact p.Prime]
    (hp : tupleMassThreshold≤(p : ℝ)) : tupleGoodLaw (p := p) (fun _ => 1)=1 :=
  tupleSubLaw_probability hp _ (empty_mem_tupleFamily _)

lemma tupleGoodLaw_nonneg {p : ℕ} [Fact p.Prime]
    (F : (TupleVertex → ZMod p) → ℝ) (hF : ∀z, 0≤F z) : 0≤tupleGoodLaw F :=
  tupleSubLaw_nonneg _ F hF

lemma tupleGoodLaw_marginal {p : ℕ} [Fact p.Prime]
    (hp : tupleMassThreshold≤(p : ℝ)) (v : TupleVertex) (f : ZMod p → ℝ) :
    tupleGoodLaw (fun z => f (z v))=𝔼 x, f x :=
  tupleSubLaw_marginal hp _ (empty_mem_tupleFamily _) v f

lemma tupleLaw_conditional {p : ℕ} [Fact p.Prime]
    (hp : tupleConditionalThreshold≤(p : ℝ)) (v : TupleVertex) (f : ZMod p → ℝ) (hf : (𝔼 x, f x)=0) :
    conditionalEnergy (jointDensity tupleLaw (Equiv.funSplitAt v (ZMod p))) f ≤
      (p : ℝ)^(-(1:ℝ)/32)*(𝔼 x, f x^2) := by
  rw [← tupleSubLaw_full]
  exact tupleSubLaw_conditional hp _ (empty_mem_tupleFamily _)
    (fun S hS => mem_tupleFamily.mp hS) v f hf

lemma tupleGoodLaw_conditional {p : ℕ} [Fact p.Prime]
    (hp : tupleConditionalThreshold≤(p : ℝ)) (v : TupleVertex) (f : ZMod p → ℝ) (hf : (𝔼 x, f x)=0) :
    conditionalEnergy (jointDensity tupleGoodLaw (Equiv.funSplitAt v (ZMod p))) f ≤
      (p : ℝ)^(-(1:ℝ)/32)*(𝔼 x, f x^2) :=
  tupleSubLaw_conditional hp _ (empty_mem_tupleFamily _)
    (fun _S hS => (mem_tupleFamily.mp hS).trans (Nat.le_succ _)) v f hf

noncomputable def tupleExceptionalConstant : ℝ :=
  ((univ : Finset (Finset (Fin tupleBlocks))).card : ℝ)*tupleWeightBound/tupleLeadingMassLower

lemma tupleEta_le {p : ℕ} [Fact p.Prime] (hp : tupleMassThreshold≤(p : ℝ)) :
    tupleEta p≤tupleExceptionalConstant*(p : ℝ)^(-(81:ℝ)/16) := by
  have hs : tupleSubmixture (p := p) tupleTerminalFamily (fun _ => 1)≤
      (p : ℝ)^(-(81:ℝ)/16)*(((univ : Finset (Finset (Fin tupleBlocks))).card : ℝ)*tupleWeightBound) := by
    rw [tupleSubmixture_apply]
    calc
      _ ≤ ∑_S∈tupleTerminalFamily, (p : ℝ)^(-(81:ℝ)/16)*tupleWeightBound := by
        apply sum_le_sum
        intro S hS
        have hc : S.card=81 := mem_tupleTerminalFamily.mp hS
        simp only [tupleMixtureWeight, hc, Nat.cast_ofNat]
        exact mul_le_mul_of_nonneg_left (tupleComponent_mass_le S (by change S.card≤81; omega))
          (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      _ = (p : ℝ)^(-(81:ℝ)/16)*((tupleTerminalFamily.card : ℝ)*tupleWeightBound) := by
        rw [sum_const, nsmul_eq_mul]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
        (by exact_mod_cast card_le_card (subset_univ tupleTerminalFamily)) tupleWeightBound_pos.le)
        (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hm := lt_of_lt_of_le tupleLeadingMassLower_pos (tupleMixture_mass_lower hp)
  unfold tupleEta tupleExceptionalLaw
  simp only [LinearMap.smul_apply, smul_eq_mul]
  calc
    _ ≤ (tupleMixture (p := p) (fun _ => 1))⁻¹*
        ((p : ℝ)^(-(81:ℝ)/16)*(((univ : Finset (Finset (Fin tupleBlocks))).card : ℝ)*tupleWeightBound)) :=
      mul_le_mul_of_nonneg_left hs (inv_nonneg.mpr hm.le)
    _ ≤ tupleLeadingMassLower⁻¹*
        ((p : ℝ)^(-(81:ℝ)/16)*(((univ : Finset (Finset (Fin tupleBlocks))).card : ℝ)*tupleWeightBound)) :=
      mul_le_mul_of_nonneg_right (inv_anti₀ tupleLeadingMassLower_pos (tupleMixture_mass_lower hp))
        (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)
          (mul_nonneg (Nat.cast_nonneg _) tupleWeightBound_pos.le))
    _ = _ := by unfold tupleExceptionalConstant; ring

end SquareDifference

namespace SquareDifference

open Finset

noncomputable def kernelForm {X : Type*} [Fintype X]
    (K : Matrix X X ℝ) (f g : X → ℝ) : ℝ :=
  𝔼 x, 𝔼 y, f x*K x y*g y

noncomputable def conditionalGram {X Y : Type*} [Fintype X] [Fintype Y]
    (W : X → Y → ℝ) : Matrix X X ℝ :=
  fun x x' => 𝔼 y, W x y*W x' y/(𝔼 z, W z y)

lemma kernelForm_conditionalGram {X Y : Type*} [Fintype X] [Fintype Y]
    (W : X → Y → ℝ) (f : X → ℝ) :
    kernelForm (conditionalGram W) f f = conditionalEnergy W f := by
  unfold kernelForm conditionalGram conditionalEnergy
  simp only [mul_expect, expect_mul]
  have hc : (𝔼 x, 𝔼 x', 𝔼 y, f x*(W x y*W x' y/(𝔼 z, W z y))*f x') =
      (𝔼 x, 𝔼 y, 𝔼 x', f x*(W x y*W x' y/(𝔼 z, W z y))*f x') := by
    apply expect_congr rfl
    intro x _
    rw [expect_comm]
  rw [hc, expect_comm]
  apply expect_congr rfl
  intro y _
  calc
    _ = (𝔼 x, f x*W x y)*(𝔼 x', f x'*W x' y)/(𝔼 z, W z y) := by
      simp only [mul_expect, expect_mul, expect_div]
      apply expect_congr rfl
      intro x _
      apply expect_congr rfl
      intro x' _
      ring
    _ = _ := by ring

lemma conditionalGram_symm {X Y : Type*} [Fintype X] [Fintype Y]
    (W : X → Y → ℝ) (x x' : X) : conditionalGram W x x'=conditionalGram W x' x := by
  unfold conditionalGram
  simp only [mul_comm (W x _) (W x' _)]

lemma conditionalGram_row {X Y : Type*} [Fintype X] [Nonempty X] [Fintype Y]
    (W : X → Y → ℝ) (hW : ∀ x y, 0 ≤ W x y)
    (hrow : ∀ x, (𝔼 y, W x y)=1) (x : X) :
    (𝔼 x', conditionalGram W x x')=1 := by
  unfold conditionalGram
  rw [expect_comm]
  have he (y : Y) : (𝔼 x', W x y*W x' y/(𝔼 z, W z y))=W x y := by
    by_cases ha : (𝔼 z, W z y)=0
    · have hz := (Finset.expect_eq_zero_iff_of_nonneg (fun z _ => hW z y)).mp ha x (mem_univ _)
      simp [hz]
    · simp only [← expect_div, ← mul_expect]
      field_simp
  simp only [he, hrow]

lemma kernelForm_nonneg_iff {X : Type*} [Fintype X] [Nonempty X]
    (K : Matrix X X ℝ) (hs : ∀ x y, K x y=K y x) :
    Matrix.PosSemidef K ↔ ∀ f, 0 ≤ kernelForm K f f := by
  have hn : (0 : ℝ) < Fintype.card X := Nat.cast_pos.mpr Fintype.card_pos
  have he (f : X → ℝ) : kernelForm K f f =
      (dotProduct (star f) (Matrix.mulVec K f))/(Fintype.card X : ℝ)^2 := by
    unfold kernelForm
    simp only [expect_eq_sum_div_card, card_univ, dotProduct, Matrix.mulVec,
      Pi.star_apply, star_trivial, mul_sum, mul_assoc]
    rw [← sum_div]
    ring
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  constructor
  · intro h f
    rw [he]
    exact div_nonneg (h.2 f) (sq_nonneg _)
  · intro h
    constructor
    · ext x y
      exact hs y x
    · intro f
      have hp := h f
      rw [he] at hp
      have hh := mul_nonneg hp (le_of_lt (sq_pos_of_pos hn))
      simpa only [div_mul_cancel₀ _ (ne_of_gt (sq_pos_of_pos hn))] using hh

lemma conditionalGram_posSemidef {X Y : Type*} [Fintype X] [Nonempty X] [Fintype Y]
    (W : X → Y → ℝ) (hW : ∀ x y, 0 ≤ W x y) :
    Matrix.PosSemidef (conditionalGram W) := by
  apply (kernelForm_nonneg_iff _ (conditionalGram_symm W)).mpr
  intro f
  rw [kernelForm_conditionalGram]
  exact conditionalEnergy_nonneg W f hW

lemma kernelForm_symmetric {X : Type*} [Fintype X] (K : Matrix X X ℝ)
    (hs : ∀ x y, K x y=K y x) (f g : X → ℝ) :
    kernelForm K f g=kernelForm K g f := by
  unfold kernelForm
  rw [expect_comm]
  apply expect_congr rfl
  intro x _
  apply expect_congr rfl
  intro y _
  rw [hs y x]
  ring

lemma kernelForm_const_right {X : Type*} [Fintype X]
    (K : Matrix X X ℝ) (hrow : ∀ x, (𝔼 y, K x y)=1)
    (f : X → ℝ) (c : ℝ) : kernelForm K f (fun _ => c)=c*(𝔼 x, f x) := by
  unfold kernelForm
  simp only [← expect_mul, ← mul_expect, hrow, mul_one]
  ring

lemma kernelForm_center {X : Type*} [Fintype X] [Nonempty X]
    (K : Matrix X X ℝ) (hs : ∀ x y, K x y=K y x)
    (hrow : ∀ x, (𝔼 y, K x y)=1) (f : X → ℝ) :
    kernelForm K (fun x => f x-(𝔼 z, f z)) (fun x => f x-(𝔼 z, f z)) =
      kernelForm K f f-(𝔼 z, f z)^2 := by
  let c := 𝔼 z, f z
  have he : kernelForm K (fun x => f x-c) (fun x => f x-c) =
      kernelForm K f f-kernelForm K f (fun _ => c)-
      kernelForm K (fun _ => c) f+kernelForm K (fun _ => c) (fun _ => c) := by
    unfold kernelForm
    simp only [sub_mul, mul_sub, expect_sub_distrib]
    ring
  rw [he, kernelForm_symmetric K hs (fun _ => c) f,
    kernelForm_const_right K hrow, kernelForm_const_right K hrow,
    Fintype.expect_const]
  dsimp only [c]
  ring

noncomputable def noiseKernel {X : Type*} [Fintype X] [DecidableEq X]
    (δ : ℝ) : Matrix X X ℝ :=
  fun x y => 1-δ^2+δ^2*(Fintype.card X : ℝ)*(if x=y then 1 else 0)

lemma kernelForm_noise {X : Type*} [Fintype X] [Nonempty X] [DecidableEq X]
    (δ : ℝ) (f : X → ℝ) :
    kernelForm (noiseKernel δ) f f = (𝔼 x, f x)^2+
      δ^2*((𝔼 x, f x^2)-(𝔼 x, f x)^2) := by
  have hn : (Fintype.card X : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have he (x : X) : (𝔼 y, (if x=y then (1 : ℝ) else 0)*f y)=
      f x/(Fintype.card X : ℝ) := by
    simp [expect_eq_sum_div_card]
  have he' (x : X) : (𝔼 y, f x*noiseKernel δ x y*f y) =
      (1-δ^2)*f x*(𝔼 y, f y)+δ^2*f x^2 := by
    unfold noiseKernel
    simp only [mul_add, add_mul, expect_add_distrib, mul_assoc, ← mul_expect, he]
    field_simp
  unfold kernelForm
  simp only [he', expect_add_distrib, ← expect_mul, ← mul_expect]
  ring

lemma centered_square_mean {X : Type*} [Fintype X] [Nonempty X] (f : X → ℝ) :
    (𝔼 x, (f x-(𝔼 y, f y))^2) = (𝔼 x, f x^2)-(𝔼 x, f x)^2 := by
  simp only [sub_sq, expect_add_distrib, expect_sub_distrib, ← mul_expect,
    ← expect_mul, Fintype.expect_const]
  ring

lemma conditionalGram_noise_domination {X Y : Type*}
    [Fintype X] [Nonempty X] [DecidableEq X] [Fintype Y]
    (W : X → Y → ℝ) (hW : ∀ x y, 0 ≤ W x y)
    (hrow : ∀ x, (𝔼 y, W x y)=1) (δ : ℝ)
    (hmix : ∀ f : X → ℝ, (𝔼 x, f x)=0 →
      conditionalEnergy W f ≤ δ^2*(𝔼 x, f x^2)) :
    Matrix.PosSemidef (fun x y => noiseKernel δ x y-conditionalGram W x y) := by
  apply (kernelForm_nonneg_iff _ (by
    intro x y
    simp only [noiseKernel, conditionalGram_symm W x y, eq_comm])).mpr
  intro f
  have hm := hmix (fun x => f x-(𝔼 z, f z)) (by
    simp only [expect_sub_distrib, Fintype.expect_const, sub_self])
  rw [← kernelForm_conditionalGram, kernelForm_center _ (conditionalGram_symm W)
    (conditionalGram_row W hW hrow), centered_square_mean] at hm
  have he : kernelForm (fun x y => noiseKernel δ x y-conditionalGram W x y) f f =
      kernelForm (noiseKernel δ) f f-kernelForm (conditionalGram W) f f := by
    unfold kernelForm
    simp only [mul_sub, sub_mul, expect_sub_distrib]
  rw [he, kernelForm_noise, kernelForm_conditionalGram]
  rw [kernelForm_conditionalGram] at hm
  linarith

lemma matrix_prod_monotone {J I : Type*} [Fintype J] [Fintype I]
    (A B : J → Matrix I I ℝ) (hA : ∀ j, (A j).PosSemidef)
    (hD : ∀ j, (B j-A j).PosSemidef) :
    Matrix.PosSemidef (fun x y => (∏ j, B j x y)-(∏ j, A j x y)) := by
  classical
  have hB j : (B j).PosSemidef := by
    have hh := (hD j).add (hA j)
    simpa only [sub_add_cancel] using hh
  have hprod (s : Finset J) : Matrix.PosSemidef (fun x y => ∏ j ∈ s, A j x y) := by
    have hh := matrix_prod_posSemidef (fun j : s => A j) (fun j => hA j)
    have he : (fun x y => ∏ j : s, A j x y) = (fun x y => ∏ j∈s, A j x y) := by
      funext x y
      exact prod_coe_sort s (fun j => A j x y)
    rw [he] at hh
    exact hh
  have hd (s : Finset J) :
      Matrix.PosSemidef (fun x y => (∏ j ∈ s, B j x y)-(∏ j ∈ s, A j x y)) := by
    induction s using Finset.induction_on with
    | empty =>
      simp only [prod_empty, sub_self]
      change (0 : Matrix I I ℝ).PosSemidef
      exact Matrix.PosSemidef.zero
    | @insert j s hj ih =>
      have hh := ((hD j).hadamard (hprod s)).add ((hB j).hadamard ih)
      have he : ((fun x y => (∏ k∈insert j s, B k x y)-(∏ k∈insert j s, A k x y)) : Matrix I I ℝ) =
          (B j-A j).hadamard (fun x y => ∏ k∈s, A k x y) +
          (B j).hadamard (fun x y => (∏ k∈s, B k x y)-(∏ k∈s, A k x y)) := by
        ext x y
        simp only [prod_insert hj, Matrix.add_apply]
        change B j x y*(∏ k∈s, B k x y)-A j x y*(∏ k∈s, A k x y) =
          (B j x y-A j x y)*(∏ k∈s, A k x y)+
          B j x y*((∏ k∈s, B k x y)-(∏ k∈s, A k x y))
        ring
      rw [he]
      exact hh
  exact hd univ

lemma product_kernel_monotone {J : Type*} [Fintype J]
    {X : J → Type*} [∀ j, Fintype (X j)]
    (A B : ∀ j, Matrix (X j) (X j) ℝ) (hA : ∀ j, (A j).PosSemidef)
    (hD : ∀ j, (B j-A j).PosSemidef) :
    Matrix.PosSemidef (fun x y : ∀ j, X j =>
      (∏ j, B j (x j) (y j))-(∏ j, A j (x j) (y j))) := by
  classical
  apply matrix_prod_monotone (fun j => (A j).submatrix (fun x : ∀ j, X j => x j) (fun x : ∀ j, X j => x j))
    (fun j => (B j).submatrix (fun x : ∀ j, X j => x j) (fun x : ∀ j, X j => x j))
  · intro j; exact (hA j).submatrix _
  · intro j
    exact (hD j).submatrix _

lemma expect_update_dep {J : Type*} [Fintype J] [DecidableEq J]
    {X : J → Type*} [∀ j, Fintype (X j)] [∀ j, Nonempty (X j)]
    (j : J) (f : (∀ j, X j) → ℝ) :
    (𝔼 x : ∀ j, X j, 𝔼 t : X j, f (Function.update x j t))=𝔼 x, f x := by
  let e : ((∀ j, X j) × X j) ≃ ((∀ j, X j) × X j) :=
    { toFun := fun a => (Function.update a.1 j a.2, a.1 j)
      invFun := fun a => (Function.update a.1 j a.2, a.1 j)
      left_inv := by rintro ⟨x,t⟩; simp
      right_inv := by rintro ⟨x,t⟩; simp }
  have he := Fintype.expect_equiv e
    (fun a : (∀ j, X j) × X j => f (Function.update a.1 j a.2))
    (fun a : (∀ j, X j) × X j => f a.1) (fun _ => rfl)
  rw [← univ_product_univ, expect_product, expect_product] at he
  simpa only [Fintype.expect_const] using he

noncomputable def coordOp {J : Type*} [DecidableEq J]
    {X : J → Type*} [∀ j, Fintype (X j)]
    (K : ∀ j, Matrix (X j) (X j) ℝ) (j : J)
    (f : (∀ j, X j) → ℝ) (x : ∀ j, X j) : ℝ :=
  𝔼 t : X j, K j (x j) t*f (Function.update x j t)

def patch {J : Type*} [DecidableEq J] {X : J → Type*}
    (s : Finset J) (x y : ∀ j, X j) (j : J) : X j := if j∈s then y j else x j

lemma patch_empty {J : Type*} [DecidableEq J] {X : J → Type*} (x y : ∀ j, X j) :
    patch ∅ x y=x := by ext j; simp [patch]

lemma patch_univ {J : Type*} [Fintype J] [DecidableEq J]
    {X : J → Type*} (x y : ∀ j, X j) : patch univ x y=y := by ext j; simp [patch]

end SquareDifference
end

end OAI
