import OAI.Geometry.LatticeCovering.Residuals

namespace OAI

section
section
noncomputable section
open scoped BigOperators
open Real
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Set
noncomputable section
open scoped BigOperators
open MeasureTheory Set
noncomputable section
open Module Submodule MeasureTheory
open scoped BigOperators
noncomputable section
open Real Filter Topology
noncomputable section
open scoped BigOperators
noncomputable section
open Filter Topology Asymptotics
noncomputable section
open scoped BigOperators
open Classical
noncomputable section
open scoped BigOperators
open Classical
noncomputable section
open scoped BigOperators
open Classical
noncomputable section
open scoped BigOperators
noncomputable section
open Module MeasureTheory

namespace SingleLatticeCovering.Vertical
open Folded ConstructionA Blocks LatticeGeometry
open scoped BigOperators

lemma rationalAlphabet_log_card (Q p : ℕ) (hQ : 1 ≤ Q) (hp : 1 ≤ p) :
    Real.log ((rationalAlphabet Q p).card+1 : ℝ) ≤
      Real.log 4+Real.log (Q : ℝ)+Real.log (p : ℝ) := by
  have hQr : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hpr : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hcard : ((rationalAlphabet Q p).card : ℝ) ≤ 2*(Q : ℝ)*p+1 := by
    exact_mod_cast rationalAlphabet_card Q p
  have hprod : (1 : ℝ) ≤ (Q : ℝ)*p := by nlinarith [mul_nonneg (sub_nonneg.mpr hQr) (sub_nonneg.mpr hpr)]
  have hle : ((rationalAlphabet Q p).card+1 : ℝ) ≤ 4*(Q : ℝ)*p := by nlinarith
  have hlog := Real.log_le_log (by positivity : (0 : ℝ) < (rationalAlphabet Q p).card+1) hle
  calc
    _ ≤ Real.log (4*(Q : ℝ)*p) := hlog
    _ = _ := by rw [Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by norm_num) (by positivity)]

namespace Chain
variable {B : Block}
lemma every_and {P Q : Block → Prop} (c : Chain B) (hP : c.Every P) (hQ : c.Every Q) :
    c.Every (fun B => P B ∧ Q B) := by
  induction c with
  | base B => exact ⟨hP,hQ⟩
  | append c B w ih => exact ⟨ih hP.1 hQ.1, hP.2,hQ.2⟩

lemma denominator_log_le (c : Chain B) {R : ℝ}
    (hc : c.Every (fun B => Real.log (B.p : ℝ) ≤ R)) :
    ∀ j, Real.log (c.denominators j : ℝ) ≤ R := by
  induction c with
  | base B => exact fun _ => hc
  | append c B w ih =>
    intro j
    refine Fin.addCases ?_ ?_ j <;> intro k
    · simpa only [denominators,Fin.append_left] using ih hc.1 k
    · simpa only [denominators,Fin.append_right] using hc.2

lemma full_denominator_log_le (c : Chain B) {R : ℝ} (hR : 0 ≤ R)
    (hc : c.Every (fun B => Real.log (B.p : ℝ) ≤ R)) :
    ∀ j, Real.log (c.fullDenominators j : ℝ) ≤ R := by
  intro j
  refine Fin.addCases ?_ ?_ j <;> intro k
  · simpa only [fullDenominators,Fin.append_left] using c.denominator_log_le hc k
  · simpa only [fullDenominators,Fin.append_right,Nat.cast_one,Real.log_one] using hR

lemma alphabet_log_card (c : Chain B) {R : ℝ} (hR : 0 ≤ R)
    (hc : c.Every (fun B => Real.log (B.p : ℝ) ≤ R)) (j : Fin c.fullDim) :
    Real.log ((c.alphabets j).card+1 : ℝ) ≤
      Real.log 8+(c.fullDim : ℝ)*Real.log ((c.fullDim : ℝ)+2)+R := by
  have hp : 1 ≤ c.fullDenominators j := by
    refine Fin.addCases ?_ ?_ j <;> intro k
    · simpa only [fullDenominators,Fin.append_left] using Nat.succ_le_iff.mpr (c.denominators_pos k)
    · simp [fullDenominators]
  have hQ : 1 ≤ c.alphabetRadius := by dsimp [alphabetRadius]; omega
  have hlog := rationalAlphabet_log_card c.alphabetRadius (c.fullDenominators j) hQ hp
  have hx : (1 : ℝ) ≤ ((c.fullDim+2 : ℕ) : ℝ)^c.fullDim := one_le_pow₀ (by norm_cast; omega)
  have hQr : (c.alphabetRadius : ℝ) ≤ 2*((c.fullDim+2 : ℕ) : ℝ)^c.fullDim := by
    have heq : (c.alphabetRadius : ℝ) = 1+((c.fullDim+2 : ℕ) : ℝ)^c.fullDim := by
      simp only [alphabetRadius,Nat.cast_add,Nat.cast_one,Nat.cast_pow]
    rw [heq]
    linarith
  have hlogQ : Real.log (c.alphabetRadius : ℝ) ≤
      Real.log 2+(c.fullDim : ℝ)*Real.log ((c.fullDim : ℝ)+2) := by
    have h : (0 : ℝ) < c.alphabetRadius := by exact_mod_cast (show 0 < c.alphabetRadius by omega)
    have ht := Real.log_le_log h hQr
    rw [Real.log_mul (by norm_num) (by positivity),Real.log_pow] at ht
    convert ht using 1 ; push_cast ; rfl
  have hlogp := c.full_denominator_log_le hR hc j
  have h48 : Real.log (4 : ℝ)+Real.log 2=Real.log 8 := by
    rw [←Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) (by norm_num : (2 : ℝ) ≠ 0)]; norm_num
  change Real.log ((rationalAlphabet c.alphabetRadius (c.fullDenominators j)).card+1 : ℝ) ≤ _
  linarith

lemma regular_primes_log_bound (c : Chain B) (A : ℝ) (hc : c.Halving)
    (hr : c.Every (fun W => Regular A W ∧ logMean (height W.b) ≤ (W.b : ℝ))) :
    c.Every (fun W => Real.log (W.p : ℝ) ≤ (c.first.b : ℝ)^2) := by
  apply c.every_mono (c.every_and hr (c.every_le_first hc))
  intro W hW
  have hs : 0 ≤ (W.b : ℝ)^(56/100 : ℝ) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hm := mul_le_mul_of_nonneg_left hW.1.2 (Nat.cast_nonneg W.b)
  have hb2 := pow_le_pow_left₀ (Nat.cast_nonneg W.b)
    (show (W.b : ℝ) ≤ c.first.b by exact_mod_cast hW.2) 2
  nlinarith [hW.1.1.2.2.1]


end Chain
end SingleLatticeCovering.Vertical

namespace SingleLatticeCovering.Vertical
open Folded ConstructionA Blocks LatticeGeometry Filter Topology
open scoped BigOperators




theorem vertical_patterns_alphabets :
    ∃ cutoff : ℕ, 2 ≤ cutoff ∧ ∃ C k κ : ℝ, 0 < C ∧ 0 < k ∧ 0 < κ ∧
      ∀ b₁ ≥ cutoff, ∃ B : Block, ∃ c : Chain B,
        c.first.b=b₁ ∧ c.CeilingSizes ∧
        (c.dim+B.terminalDim : ℝ) ≤ C*((b₁ : ℝ)+1) ∧
        c.radiusSq+(B.terminalDim : ℝ) ≤ C*((b₁ : ℝ)*Real.log ((b₁ : ℝ)+1)+1) ∧
        (∀ j, Real.log ((c.alphabets j).card+1 : ℝ) ≤
          Real.log 8+(c.fullDim : ℝ)*Real.log ((c.fullDim : ℝ)+2)+(b₁ : ℝ)^2) ∧
        ∀ y : c.FullVec, ∃ P : Finset c.FullVec,
          P.Nonempty ∧ SuffixBinary P ∧
          (∀ l ∈ P, l ∈ c.fullRaw ∧ c.FullResidual y l ∧
            c.det*gamma (y-c.fullLinear l) ≤ Real.exp (-k*(b₁ : ℝ)^(70/100 : ℝ))) ∧
          (∃ t : Fin B.terminalDim → ℝ, ∀ l ∈ P, ∀ j, l (Fin.natAdd c.dim j)=t j) ∧
          κ ≤ ∑ l ∈ P, c.det*gamma (y-c.fullLinear l) := by
  classical
  obtain ⟨A,hA,N,hN,hsmall,hbuild⟩ := hierarchy_preparation
  obtain ⟨k,hk,hatom⟩ := eventually_eligible_atom
  have hround : ∀ᶠ b : ℕ in atTop, ∀ p : ℕ, 0 < p →
      (b : ℝ)*logMean (height b)-4*(b : ℝ)^(56/100 : ℝ) ≤ Real.log p →
      (b : ℝ)*height b^2/p ≤ (b : ℝ)^(-(1/100 : ℝ)) := by
    filter_upwards [tendsto_natCast_atTop_atTop.eventually eventually_rounding_slack,
      eventually_ge_atTop (1 : ℕ)] with b hb hb1 p hp hpl
    exact (hb p (by exact_mod_cast hp) hpl).1.trans
      (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hb1) (by norm_num))
  have hden : 0 < 1-(2 : ℝ)^(-(1/100 : ℝ)) := sub_pos.mpr
    (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num))
  have hsumSmall : ∀ᶠ b : ℕ in atTop,
      (1+2*A)*(b : ℝ)^(-(1/100 : ℝ))/(1-(2 : ℝ)^(-(1/100 : ℝ))) ≤ 1/2 := by
    have ht := ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1/100)).const_mul (1+2*A)).div_const
      (1-(2 : ℝ)^(-(1/100 : ℝ)))
    have hn : Tendsto (fun b : ℕ => (1+2*A)*(b : ℝ)^(-(1/100 : ℝ))/
        (1-(2 : ℝ)^(-(1/100 : ℝ)))) atTop (𝓝 0) := by
      have hcast : Tendsto (fun b : ℕ => (b : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
      simpa only [Function.comp_def,mul_zero,zero_div] using ht.comp hcast
    exact hn.eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1/2))
  obtain ⟨N',hN'⟩ := eventually_atTop.mp (hatom.and (hround.and hsumSmall))
  let cutoff := max N N'
  have hcutN : N ≤ cutoff := le_max_left _ _
  have hcutN' : N' ≤ cutoff := le_max_right _ _
  have hcut2 : 2 ≤ cutoff := hN.trans hcutN
  let M : ℕ := ⌈(cutoff : ℝ)^((1 : ℝ)/(9/10))⌉₊
  let Q : ℕ := ⌈Real.exp ((M : ℝ)^2)⌉₊
  let T : ℕ := M*Nat.clog 2 Q
  let C : ℝ := (T : ℝ)+5
  let κ : ℝ := (1/4 : ℝ)*gamma1 1^T
  have hκ : 0 < κ := mul_pos (by norm_num) (pow_pos (gamma1_pos 1) _)
  refine ⟨cutoff,hcut2,C,k,κ,by dsimp [C]; positivity,hk,hκ,?_⟩
  intro b₁ hb₁
  obtain ⟨B,c,hfirst,hreg,hgood,hhalf,hsizes,hstop⟩ := hbuild cutoff hcutN b₁ hb₁
  have hbN (W : Block) (hW : cutoff ≤ W.b) := hsmall W.b (hcutN.trans hW)
  have hbN' (W : Block) (hW : cutoff ≤ W.b) := hN' W.b (hcutN'.trans hW)
  have hr := c.every_mono hreg (fun W hW => hW.2)
  have hpos := c.every_mono hreg (fun W hW => show 1 ≤ W.b by omega)
  have hB := c.every_last hreg
  have hBound := c.terminal_bound A hB.2 hstop (Nat.le_ceil _) (Nat.le_ceil _) (hbN B hB.1).2
  have hT : B.terminalDim ≤ T := hBound.2.2
  have hloss : c.Every (fun W => cutoff ≤ W.b ∧
      W.roundingLoss ≤ (W.b : ℝ)^(-(1/100 : ℝ)) ∧ blockLoss A W ≤ 1/2) := by
    apply c.every_mono hreg
    intro W hW
    refine ⟨hW.1,?_,(hbN W hW.1).1⟩
    dsimp [Block.roundingLoss]
    rw [hW.2.1]
    exact (hbN' W hW.1).2.1 W.p W.prime.pos hW.2.2.1
  have hcoeff : 1/2 ≤ c.coefficient (blockLoss A) :=
    c.coefficient_half A hA.le cutoff (by omega) hhalf hloss (hN' cutoff hcutN').2.2
  have hcAtoms : c.Every (Chain.AtomBound (fun W => Real.exp (-k*(W.b : ℝ)^(70/100 : ℝ)))) := by
    apply c.every_mono hreg
    intro W hW z hz t ht e
    rw [hW.2.1]
    exact ((hbN' W hW.1).1 W.p hW.2.2.1 z (hW.2.2.2.2.1 hz) t ht e).2
  refine ⟨B,c,hfirst,hsizes,?_,?_,?_,?_⟩
  · have hd : (c.dim : ℝ) ≤ 2*(b₁ : ℝ) := by
      exact_mod_cast (show c.dim ≤ 2*b₁ by have := c.dim_last_le hhalf; omega)
    have ht : (B.terminalDim : ℝ) ≤ T := by exact_mod_cast hT
    dsimp [C]
    nlinarith [(Nat.cast_nonneg T : (0 : ℝ) ≤ T),(Nat.cast_nonneg b₁ : (0 : ℝ) ≤ b₁),
      mul_nonneg (show (0 : ℝ) ≤ T by positivity) (show (0 : ℝ) ≤ b₁ by positivity)]
  · have hradius := c.radius_bound A hhalf hr hpos
    rw [hfirst] at hradius
    have ht : (B.terminalDim : ℝ) ≤ T := by exact_mod_cast hT
    have hlog : 0 ≤ Real.log ((b₁ : ℝ)+1) := Real.log_nonneg (by linarith [(Nat.cast_nonneg b₁ : (0 : ℝ) ≤ b₁)])
    dsimp [C]
    nlinarith [mul_nonneg (Nat.cast_nonneg b₁) hlog,
      mul_nonneg (Nat.cast_nonneg T) (mul_nonneg (Nat.cast_nonneg b₁) hlog)]
  · have hrlog : c.Every (fun W => Regular A W ∧ logMean (height W.b) ≤ (W.b : ℝ)) := by
      apply c.every_mono hreg
      intro W hW
      exact ⟨hW.2,(hbN W hW.1).2⟩
    have hlog := c.regular_primes_log_bound A hhalf hrlog
    rw [hfirst] at hlog
    exact c.alphabet_log_card (sq_nonneg _) hlog
  · intro y
    obtain ⟨P,hPb,hPl,hPt,hPw⟩ := c.full_patterns (blockLoss A) hgood
      (regular_mean hB.2 (hbN B hB.1).1).1 y
    have hgT : gamma1 1^T ≤ gamma1 1^B.terminalDim :=
      pow_le_pow_of_le_one (gamma1_pos 1).le (gamma1_le_one 1) hT
    have hweight : κ ≤ ∑ l ∈ P, c.det*gamma (y-c.fullLinear l) := by
      apply le_trans _ hPw
      dsimp [κ]
      have h0 : 0 ≤ gamma1 1^B.terminalDim := (pow_pos (gamma1_pos 1) _).le
      nlinarith [mul_nonneg (sub_nonneg.mpr hcoeff) h0]
    have hPn : P.Nonempty := by
      by_contra he
      rw [Finset.not_nonempty_iff_eq_empty.mp he,Finset.sum_empty] at hweight
      exact (not_le_of_gt hκ) hweight
    refine ⟨P,hPn,hPb,?_,hPt,hweight⟩
    intro l hl
    have hle := hPl l hl
    refine ⟨hle.1,hle.2.1,?_⟩
    have hcap := c.full_selected_cap k hk.le hcAtoms y l hle.2.2
    simpa only [hfirst] using hcap


end SingleLatticeCovering.Vertical

end
end
end
end
end
end
end
end
end
end
end
end
end

section





noncomputable section
open MeasureTheory MeasureTheory.Measure Set
open scoped ENNReal Pointwise
namespace SingleLatticeCovering.Shear

section Haar
variable {T : Type*} [AddCommGroup T] [MeasurableSpace T]
  [MeasurableAdd₂ T] [MeasurableNeg T]
  (μ : Measure T) [IsProbabilityMeasure μ] [IsAddLeftInvariant μ] [IsNegInvariant μ]



def translate (A : Set T) (t : T) : Set T := (fun x => x-t) ⁻¹' A

lemma measurableSet_translate {A : Set T} (hA : MeasurableSet A) (t : T) :
    MeasurableSet (translate A t) := hA.preimage (by fun_prop)

lemma measure_translate {T : Type*} [AddCommGroup T] [MeasurableSpace T] [MeasurableAdd₂ T] [MeasurableNeg T] (μ : Measure T) [IsProbabilityMeasure μ] [IsAddLeftInvariant μ] [IsNegInvariant μ] (A : Set T) (t : T) : μ (translate A t) = μ A := by
  simp only [translate, sub_eq_add_neg, measure_preimage_add_right]

lemma translate_add {T : Type*} [AddCommGroup T] [MeasurableSpace T] [MeasurableAdd₂ T] [MeasurableNeg T] (A : Set T) (a b : T) :
    translate A (a+b) = translate (translate A a) b := by
  ext x
  simp only [translate, mem_preimage]
  abel_nf

lemma translate_inter {T : Type*} [AddCommGroup T] [MeasurableSpace T] [MeasurableAdd₂ T] [MeasurableNeg T] (A B : Set T) (t : T) :
    translate (A ∩ B) t = translate A t ∩ translate B t := rfl

lemma overlap_common_translate (A B : Set T) (a b : T) :
    μ (translate A a ∩ translate B (a+b)) = μ (A ∩ translate B b) := by
  rw [add_comm a b, translate_add, ← translate_inter, measure_translate]

lemma measurable_overlap {T : Type*} [AddCommGroup T] [MeasurableSpace T] [MeasurableAdd₂ T] [MeasurableNeg T] (μ : Measure T) [IsProbabilityMeasure μ] [IsAddLeftInvariant μ] [IsNegInvariant μ] {A B : Set T} (hA : MeasurableSet A) (hB : MeasurableSet B) :
    Measurable (fun t => μ (A ∩ translate B t)) := by
  exact measurable_measure_prodMk_left
    ((hA.preimage measurable_snd).inter (hB.preimage (by fun_prop :
      Measurable (fun z : T × T => z.2-z.1))))


lemma lintegral_overlap {A B : Set T} (hA : MeasurableSet A) (hB : MeasurableSet B) :
    ∫⁻ t, μ (A ∩ translate B t) ∂μ = μ A * μ B := by
  let f : T × T → T × T := fun z => (z.2, z.2-z.1)
  have hf : MeasurePreserving f (μ.prod μ) (μ.prod μ) := by
    have h := (measurePreserving_prod_add_swap μ μ).comp
      ((measurePreserving_neg μ).prod (MeasurePreserving.id μ))
    simpa [f, Function.comp_def, sub_eq_add_neg] using h
  have hm : MeasurableSet (f ⁻¹' (A ×ˢ B)) := (hA.prod hB).preimage hf.measurable
  calc
    _ = (μ.prod μ) (f ⁻¹' (A ×ˢ B)) := (Measure.prod_apply hm).symm
    _ = (μ.prod μ) (A ×ˢ B) := hf.measure_preimage (hA.prod hB).nullMeasurableSet
    _ = _ := Measure.prod_prod A B

end Haar

section FiniteChoice
variable {X I : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]



lemma simultaneous_choice (s : Finset I) (f : I → X → ℝ≥0∞) (w : I → ℝ≥0∞)
    (hf : ∀ i ∈ s, Measurable (f i))
    (hw0 : ∀ i ∈ s, w i ≠ 0) (hwt : ∀ i ∈ s, w i ≠ ∞)
    (hfint : ∀ i ∈ s, ∫⁻ x, f i x ∂μ ≤ w i)
    (L : ℝ≥0∞) (hL : (s.card : ℝ≥0∞) < L) :
    ∃ x, ∀ i ∈ s, f i x ≤ L * w i := by
  classical
  let F : X → ℝ≥0∞ := fun x => ∑ i ∈ s, (w i)⁻¹ * f i x
  have hF : ∫⁻ x, F x ∂μ ≤ (s.card : ℝ≥0∞) := by
    dsimp [F]
    rw [lintegral_finsetSum s (fun i hi => (hf i hi).const_mul _)]
    calc
      _ = ∑ i ∈ s, (w i)⁻¹ * ∫⁻ x, f i x ∂μ := by
        apply Finset.sum_congr rfl
        intro i hi
        exact lintegral_const_mul _ (hf i hi)
      _ ≤ ∑ i ∈ s, (w i)⁻¹ * w i := Finset.sum_le_sum (fun i hi =>
        mul_le_mul' le_rfl (hfint i hi))
      _ = ∑ _i ∈ s, (1 : ℝ≥0∞) := Finset.sum_congr rfl (fun i hi =>
        ENNReal.inv_mul_cancel (hw0 i hi) (hwt i hi))
      _ = _ := by simp
  have hex : ∃ x, F x < L := by
    by_contra h
    push Not at h
    have hle := lintegral_mono (μ := μ) h
    simp only [lintegral_const, measure_univ, mul_one] at hle
    exact (not_le_of_gt hL) (hle.trans hF)
  obtain ⟨x, hx⟩ := hex
  refine ⟨x, fun i hi => ?_⟩
  have hiF : (w i)⁻¹ * f i x ≤ F x := by
    dsimp [F]
    exact Finset.single_le_sum (f := fun j => (w j)⁻¹ * f j x) (fun _ _ => zero_le) hi
  have hdiv : f i x / w i ≤ L := by
    simpa only [div_eq_mul_inv, mul_comm] using hiF.trans hx.le
  exact (ENNReal.div_le_iff (hw0 i hi) (hwt i hi)).mp hdiv

end FiniteChoice

end SingleLatticeCovering.Shear

namespace SingleLatticeCovering.Shear

universe u



inductive Pattern (α : Type u) : ℕ → Type u where
  | leaf (a : α) : Pattern α 0
  | mono {q : ℕ} (v : ℝ) (p : Pattern α q) : Pattern α (q+1)
  | split {q : ℕ} (v : ℝ) (p r : Pattern α q) : Pattern α (q+1)

namespace Pattern
variable {α : Type*}

def size : {q : ℕ} → Pattern α q → ℕ
  | _, .leaf _ => 1
  | _, .mono _ p => p.size
  | _, .split _ p r => p.size+r.size

lemma size_pos {q : ℕ} (p : Pattern α q) : 0 < p.size := by
  induction p with
  | leaf => exact Nat.zero_lt_one
  | mono v p ih => exact ih
  | split v p r ih ihr => exact Nat.add_pos_left ih _

lemma size_le_two_pow {q : ℕ} (p : Pattern α q) : p.size ≤ 2^q := by
  induction p with
  | leaf => simp [size]
  | @mono q v p ih =>
    simpa only [size, pow_succ] using ih.trans (Nat.le_mul_of_pos_right (2^q) (by decide))
  | @split q v p r ih ihr =>
    simp only [size, pow_succ]
    omega

def weight (L : ℝ≥0∞) (η : α → ℝ≥0∞) : {q : ℕ} → Pattern α q → ℝ≥0∞
  | _, .leaf a => η a
  | _, .mono _ p => p.weight L η
  | _, .split _ p r => L * p.weight L η * r.weight L η

def labelProduct (η : α → ℝ≥0∞) : {q : ℕ} → Pattern α q → ℝ≥0∞
  | _, .leaf a => η a
  | _, .mono _ p => p.labelProduct η
  | _, .split _ p r => p.labelProduct η * r.labelProduct η

lemma weight_eq {q : ℕ} (p : Pattern α q) (L : ℝ≥0∞) (η : α → ℝ≥0∞) :
    p.weight L η = L^(p.size-1) * p.labelProduct η := by
  induction p with
  | leaf => simp [weight, size, labelProduct]
  | mono v p ih => exact ih
  | split v p r ih ihr =>
    have he : p.size+r.size-1 = 1+(p.size-1)+(r.size-1) := by
      have := p.size_pos
      have := r.size_pos
      omega
    simp only [weight, size, labelProduct, ih, ihr, he, pow_add, pow_one]
    ac_rfl

lemma weight_ne_zero {q : ℕ} (p : Pattern α q) {L : ℝ≥0∞} (hL : L ≠ 0)
    {η : α → ℝ≥0∞} (hη : ∀ a, η a ≠ 0) : p.weight L η ≠ 0 := by
  induction p with
  | leaf a => exact hη a
  | mono v p ih => exact ih
  | split v p r ih ihr => exact mul_ne_zero (mul_ne_zero hL ih) ihr

lemma weight_ne_top {q : ℕ} (p : Pattern α q) {L : ℝ≥0∞} (hL : L ≠ ∞)
    {η : α → ℝ≥0∞} (hη : ∀ a, η a ≠ ∞) : p.weight L η ≠ ∞ := by
  induction p with
  | leaf a => exact hη a
  | mono v p ih => exact ih
  | split v p r ih ihr => exact ENNReal.mul_ne_top (ENNReal.mul_ne_top hL ih) ihr

def first {q : ℕ} : Pattern α (q+1) → Pattern α q
  | .mono _ p => p
  | .split _ p _ => p

def second {q : ℕ} : Pattern α (q+1) → Pattern α q
  | .mono _ p => p
  | .split _ _ r => r

def branches {q : ℕ} : Pattern α (q+1) → Prop
  | .mono _ _ => False
  | .split _ _ _ => True

section Evaluation
variable {E T : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup T]

def failure (π : E →+ T) (U : α → Set T) : {q : ℕ} → Pattern α q → (Fin q → E) → Set T
  | _, .leaf a, _ => U a
  | _, .mono v p, Z => translate (p.failure π U (Fin.init Z)) (π (v • Z (Fin.last _)))
  | _, .split v p r, Z =>
    translate (p.failure π U (Fin.init Z)) (π (v • Z (Fin.last _))) ∩
    translate (r.failure π U (Fin.init Z)) (π ((v+1) • Z (Fin.last _)))

lemma measurableSet_failure [MeasurableSpace T] [MeasurableAdd₂ T] [MeasurableNeg T]
    (π : E →+ T) {U : α → Set T} (hU : ∀ a, MeasurableSet (U a))
    {q : ℕ} (p : Pattern α q) (Z : Fin q → E) : MeasurableSet (p.failure π U Z) := by
  induction p with
  | leaf a => exact hU a
  | mono v p ih => exact measurableSet_translate (ih _) _
  | split v p r ih ihr =>
    exact (measurableSet_translate (ih _) _).inter (measurableSet_translate (ihr _) _)

end Evaluation
end Pattern



def restrictColumns {E : Type*} {q d : ℕ} (h : q ≤ d) (Z : Fin d → E) : Fin q → E :=
  fun i => Z (Fin.castLE h i)

lemma restrictColumns_snoc {E : Type*} {q d : ℕ} (h : q ≤ d) (Z : Fin d → E) (z : E) :
    restrictColumns (h.trans (Nat.le_succ d)) (Fin.snoc Z z) = restrictColumns h Z := by
  funext i
  exact Fin.snoc_castSucc (α := fun _ => E) z Z (Fin.castLE h i)

@[simp] lemma restrictColumns_self {E : Type*} {d : ℕ} (Z : Fin d → E) :
    restrictColumns (le_refl d) Z = Z := rfl

def SliceClosed {α : Type*} (P : (q : ℕ) → Finset (Pattern α q)) (D : ℕ) : Prop :=
  ∀ q < D, ∀ p ∈ P (q+1), p.first ∈ P q ∧ p.second ∈ P q

section Simultaneous
variable {α E T : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup T]
  [MeasurableSpace T] [MeasurableAdd₂ T] [MeasurableNeg T]
  (μ : Measure T) [IsProbabilityMeasure μ] [IsAddLeftInvariant μ] [IsNegInvariant μ]
  (π : E →+ T) (hπ : Function.Surjective π)
  (U : α → Set T) (hU : ∀ a, MeasurableSet (U a))
  (η : α → ℝ≥0∞) (hη0 : ∀ a, η a ≠ 0) (hηt : ∀ a, η a ≠ ∞)
  (hUη : ∀ a, μ (U a) ≤ η a)
  (L : ℝ≥0∞) (hL0 : L ≠ 0) (hLt : L ≠ ∞)

include hπ hU hη0 hηt hUη hL0 hLt




theorem simultaneous_shear_aux (D : ℕ) (P : (q : ℕ) → Finset (Pattern α q))
    (hP : SliceClosed P D) (hcard : ∀ q ≤ D, ((P q).card : ℝ≥0∞) < L) :
    ∃ Z : Fin D → E, ∀ q (hq : q ≤ D) (p : Pattern α q), p ∈ P q →
      μ (p.failure π U (restrictColumns hq Z)) ≤ p.weight L η := by
  classical
  induction D with
  | zero =>
    refine ⟨fun i => Fin.elim0 i, ?_⟩
    intro q hq p hp
    have hq0 : q = 0 := by omega
    subst q
    cases p with
    | leaf a => exact hUη a
  | succ D ih =>
    have hP' : SliceClosed P D := fun q hq p hp => hP q (by omega) p hp
    obtain ⟨Z, hZ⟩ := ih hP' (fun q hq => hcard q (by omega))
    let s := (P (D+1)).filter Pattern.branches
    let f := fun p : Pattern α (D+1) => fun t : T =>
      μ (p.first.failure π U Z ∩ translate (p.second.failure π U Z) t)
    let w := fun p : Pattern α (D+1) => p.first.weight L η * p.second.weight L η
    have hf : ∀ p ∈ s, Measurable (f p) := fun p _ =>
      measurable_overlap μ (p.first.measurableSet_failure π hU Z)
        (p.second.measurableSet_failure π hU Z)
    have hw0 : ∀ p ∈ s, w p ≠ 0 := fun p _ => mul_ne_zero
      (p.first.weight_ne_zero hL0 hη0) (p.second.weight_ne_zero hL0 hη0)
    have hwt : ∀ p ∈ s, w p ≠ ∞ := fun p _ => ENNReal.mul_ne_top
      (p.first.weight_ne_top hLt hηt) (p.second.weight_ne_top hLt hηt)
    have hfint : ∀ p ∈ s, ∫⁻ t, f p t ∂μ ≤ w p := by
      intro p hp
      have hpP : p ∈ P (D+1) := (Finset.mem_filter.mp hp).1
      obtain ⟨hp1,hp2⟩ := hP D (by omega) p hpP
      dsimp [f, w]
      rw [lintegral_overlap μ (p.first.measurableSet_failure π hU Z)
        (p.second.measurableSet_failure π hU Z)]
      exact mul_le_mul' (hZ D le_rfl p.first hp1) (hZ D le_rfl p.second hp2)
    have hsL : (s.card : ℝ≥0∞) < L := lt_of_le_of_lt
      (Nat.cast_le.mpr (Finset.card_filter_le _ _)) (hcard (D+1) le_rfl)
    obtain ⟨t,ht⟩ := simultaneous_choice μ s f w hf hw0 hwt hfint L hsL
    obtain ⟨z,hz⟩ := hπ t
    refine ⟨Fin.snoc Z z, ?_⟩
    intro q hq p hp
    by_cases hqD : q ≤ D
    · rw [show restrictColumns hq (Fin.snoc Z z) = restrictColumns hqD Z from
        restrictColumns_snoc hqD Z z]
      exact hZ q hqD p hp
    · have hqeq : q = D+1 := by omega
      subst q
      simp only [restrictColumns_self]
      cases p with
      | mono v p =>
        have hp' := (hP D (by omega) (.mono v p) hp).1
        simpa only [Pattern.failure, Pattern.weight, Fin.init_snoc, Fin.snoc_last,
          measure_translate, Pattern.first, restrictColumns_self] using hZ D le_rfl p hp'
      | split v p r =>
        have hp' : Pattern.split v p r ∈ s := Finset.mem_filter.mpr ⟨hp, trivial⟩
        have hφ : π ((v+1) • z) = π (v • z)+t := by
          rw [add_smul, one_smul, map_add, hz]
        simp only [Pattern.failure, Fin.init_snoc, Fin.snoc_last, hφ,
          overlap_common_translate, Pattern.weight]
        simpa only [f, w, Pattern.first, Pattern.second, mul_assoc] using ht (.split v p r) hp'


theorem simultaneous_shear (D : ℕ) (P : (q : ℕ) → Finset (Pattern α q))
    (hP : SliceClosed P D)
    (hQ : (∑ q ∈ Finset.range (D+1), ((P q).card : ℝ≥0∞)) < L) :
    ∃ Z : Fin D → E, ∀ q (hq : q ≤ D) (p : Pattern α q), p ∈ P q →
      μ (p.failure π U (restrictColumns hq Z)) ≤
        L^(p.size-1) * p.labelProduct η := by
  obtain ⟨Z,hZ⟩ := simultaneous_shear_aux μ π hπ U hU η hη0 hηt hUη L hL0 hLt D P hP
    (fun q hq => (Finset.single_le_sum (f := fun q => ((P q).card : ℝ≥0∞)) (fun _ _ => zero_le)
      (Finset.mem_range.mpr (by omega : q < D+1))).trans_lt hQ)
  exact ⟨Z, fun q hq p hp => (hZ q hq p hp).trans_eq (p.weight_eq L η)⟩

end Simultaneous

end SingleLatticeCovering.Shear

namespace SingleLatticeCovering.Shear.Pattern
variable {α : Type*}
local instance {q : ℕ} : DecidableEq ((Fin q → ℝ) × α) := Classical.decEq _



def appendPoint {q : ℕ} (v : ℝ) (l : (Fin q → ℝ) × α) : (Fin (q+1) → ℝ) × α :=
  (Fin.snoc l.1 v, l.2)

lemma appendPoint_injective {q : ℕ} (v : ℝ) :
    Function.Injective (appendPoint (α := α) (q := q) v) := by
  intro x y h
  have h1 := congrArg (fun l : (Fin (q+1) → ℝ) × α => Fin.init l.1) h
  have h2 := congrArg Prod.snd h
  exact Prod.ext (by simpa only [appendPoint, Fin.init_snoc] using h1) h2

lemma appendPoint_disjoint {q : ℕ} (v : ℝ) (s t : Finset ((Fin q → ℝ) × α)) :
    Disjoint (s.image (appendPoint v)) (t.image (appendPoint (v+1))) := by
  classical
  apply Finset.disjoint_left.mpr
  intro x hx hy
  obtain ⟨a,ha,hax⟩ := Finset.mem_image.mp hx
  obtain ⟨b,hb,hbx⟩ := Finset.mem_image.mp hy
  have h := congrArg (fun l : (Fin (q+1) → ℝ) × α => l.1 (Fin.last q)) (hax.trans hbx.symm)
  simp only [appendPoint, Fin.snoc_last] at h
  linarith


def points : {q : ℕ} → Pattern α q → Finset ((Fin q → ℝ) × α)
  | _, .leaf a => {(0,a)}
  | _, .mono v p => by classical exact p.points.image (appendPoint v)
  | _, .split v p r => by
    classical
    exact p.points.image (appendPoint v) ∪ r.points.image (appendPoint (v+1))

lemma points_card {q : ℕ} (p : Pattern α q) : p.points.card = p.size := by
  classical
  induction p with
  | leaf a => simp [points, size]
  | mono v p ih =>
    simp only [points, Finset.card_image_of_injective _ (appendPoint_injective _), size, ih]
  | split v p r ih ihr =>
    rw [points, Finset.card_union_of_disjoint (appendPoint_disjoint _ _ _)]
    simp only [Finset.card_image_of_injective _ (appendPoint_injective _), size, ih, ihr]

lemma points_nonempty {q : ℕ} (p : Pattern α q) : p.points.Nonempty := by
  rw [← Finset.card_pos, points_card]
  exact p.size_pos

lemma labelProduct_eq_prod {q : ℕ} (p : Pattern α q) (η : α → ℝ≥0∞) :
    p.labelProduct η = ∏ l ∈ p.points, η l.2 := by
  classical
  induction p with
  | leaf a => simp [points, labelProduct]
  | mono v p ih =>
    rw [points, Finset.prod_image (fun _ _ _ _ h => appendPoint_injective v h)]
    exact ih
  | split v p r ih ihr =>
    rw [points, Finset.prod_union (appendPoint_disjoint _ _ _)]
    rw [Finset.prod_image (fun _ _ _ _ h => appendPoint_injective v h),
      Finset.prod_image (fun _ _ _ _ h => appendPoint_injective (v+1) h)]
    exact congrArg₂ (· * ·) ih ihr

section Semantics
variable {E T : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup T]

def linearShift {q : ℕ} (Z : Fin q → E) (x : Fin q → ℝ) : E := ∑ i, x i • Z i

lemma linearShift_snoc {q : ℕ} (Z : Fin (q+1) → E) (x : Fin q → ℝ) (v : ℝ) :
    linearShift Z (Fin.snoc x v) = linearShift (Fin.init Z) x + v • Z (Fin.last q) := by
  rw [linearShift, Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last, linearShift, Fin.init_def]


lemma mem_failure_iff (π : E →+ T) (U : α → Set T) {q : ℕ} (p : Pattern α q)
    (Z : Fin q → E) (x : T) :
    x ∈ p.failure π U Z ↔
      ∀ l ∈ p.points, x ∈ translate (U l.2) (π (linearShift Z l.1)) := by
  classical
  induction p generalizing x with
  | leaf a => simp [failure, points, linearShift, translate]
  | @mono q v p ih =>
    simp only [failure, translate, mem_preimage]
    rw [ih]
    simp only [points, Finset.forall_mem_image, appendPoint, linearShift_snoc, map_add,
      translate, mem_preimage]
    have hs (a b : T) : x-a-b = x-(b+a) := by abel
    simp only [hs]
  | @split q v p r ih ihr =>
    simp only [failure, mem_inter_iff, translate, mem_preimage]
    rw [ih, ihr]
    simp only [points, Finset.forall_mem_union, Finset.forall_mem_image, appendPoint,
      linearShift_snoc, map_add, translate, mem_preimage]
    have hs (a b : T) : x-a-b = x-(b+a) := by abel
    simp only [hs]

lemma failure_eq_intersection (π : E →+ T) (U : α → Set T) {q : ℕ} (p : Pattern α q)
    (Z : Fin q → E) :
    p.failure π U Z = ⋂ l ∈ p.points, translate (U l.2) (π (linearShift Z l.1)) := by
  ext x
  simpa only [mem_iInter] using p.mem_failure_iff π U Z x

end Semantics
end SingleLatticeCovering.Shear.Pattern


end
end
end

end OAI
