import OAI.Dynamics.MultipleMixing.Foundations

namespace OAI

noncomputable section

namespace Rokhlin

section
open MeasureTheory Filter
open scoped BigOperators Topology
variable {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]

lemma shannonEntropy_eq_negMulLog (p : A → ℝ) :
    shannonEntropy p = ∑ a, Real.negMulLog (p a) := rfl

def rowEntropy (p : A → ℝ) : ℝ :=
  shannonEntropy p - Real.negMulLog (∑ a, p a)

lemma rowEntropy_zero : rowEntropy (fun _ : A => 0) = 0 := by
  simp [rowEntropy,shannonEntropy,Real.negMulLog]

lemma zero_row {p : A → ℝ} (hp : ∀ a, 0 ≤ p a) (h : ∑ a, p a = 0) (a : A) : p a = 0 := by
  exact le_antisymm (h ▸ Finset.single_le_sum (fun a _ => hp a) (Finset.mem_univ a)) (hp a)

lemma rowEntropy_normalize (p : A → ℝ) (hp : ∀ a, 0 ≤ p a) :
    rowEntropy p = (∑ a, p a) * shannonEntropy (fun a => p a / ∑ a, p a) := by
  classical
  let w := ∑ a, p a
  have hw : 0 ≤ w := Finset.sum_nonneg (fun a _ => hp a)
  by_cases hz : w = 0
  · have h0 : p = fun _ => 0 := funext (zero_row hp hz)
    subst p
    simp [rowEntropy_zero]
  · have hs : ∑ a, p a / w = 1 := by rw [←Finset.sum_div,div_self hz]
    have he (a : A) : Real.negMulLog (p a) =
        p a / w * Real.negMulLog w + w * Real.negMulLog (p a / w) := by
      conv_lhs => rw [show p a = w * (p a / w) by field_simp]
      exact Real.negMulLog_mul _ _
    simp only [rowEntropy,shannonEntropy_eq_negMulLog]
    change (∑ a, Real.negMulLog (p a)) - Real.negMulLog w = _
    simp_rw [he]
    rw [Finset.sum_add_distrib,←Finset.sum_mul,hs,one_mul,←Finset.mul_sum]
    ring

lemma rowEntropy_sum_le (p : B → A → ℝ) (hp : ∀ b a, 0 ≤ p b a) :
    (∑ b, rowEntropy (p b)) ≤ rowEntropy (fun a => ∑ b, p b a) := by
  classical
  let w (b : B) := ∑ a, p b a
  let s := ∑ b, w b
  have hw (b : B) : 0 ≤ w b := Finset.sum_nonneg (fun a _ => hp b a)
  have hs : 0 ≤ s := Finset.sum_nonneg (fun b _ => hw b)
  by_cases hz : s = 0
  · have hw0 b : w b = 0 := zero_row hw hz b
    have hp0 b a : p b a = 0 := zero_row (hp b) (hw0 b) a
    have hpz : p = fun _ _ => 0 := funext fun b => funext (hp0 b)
    rw [hpz]
    simp only [Finset.sum_const_zero,rowEntropy_zero,le_refl]
  · have hspos : 0 < s := lt_of_le_of_ne hs (Ne.symm hz)
    have hweights : ∑ b, w b / s = 1 := by rw [←Finset.sum_div,div_self hz]
    have he (a : A) : ∑ b, (w b / s) * (p b a / w b) = (∑ b, p b a) / s := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro b _
      by_cases hwb : w b = 0
      · rw [zero_row (hp b) hwb a,hwb]; simp
      · field_simp
    have hj (a : A) : ∑ b, (w b / s) * Real.negMulLog (p b a / w b) ≤
        Real.negMulLog ((∑ b, p b a) / s) := by
      have h := Real.concaveOn_negMulLog.le_map_sum
        (t := Finset.univ) (w := fun b => w b / s) (p := fun b => p b a / w b)
        (fun b _ => div_nonneg (hw b) hs) hweights
        (fun b _ => div_nonneg (hp b a) (hw b))
      simpa only [smul_eq_mul,he] using h
    rw [rowEntropy_normalize _ (fun a => Finset.sum_nonneg (fun b _ => hp b a))]
    have hsum : (∑ a, ∑ b, p b a) = s := Finset.sum_comm
    rw [hsum]
    calc
      ∑ b, rowEntropy (p b) = s * ∑ a, ∑ b, (w b / s) * Real.negMulLog (p b a / w b) := by
        simp_rw [rowEntropy_normalize _ (hp _),shannonEntropy_eq_negMulLog]
        rw [Finset.sum_comm,Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro b _
        rw [←Finset.mul_sum,←mul_assoc,mul_div_cancel₀ _ hz]
      _ ≤ s * ∑ a, Real.negMulLog ((∑ b, p b a) / s) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun a _ => hj a)) hs
      _ = _ := rfl

def conditionalShannon (p : B → A → ℝ) : ℝ := ∑ b, rowEntropy (p b)

lemma shannon_chain_rule (p : B → A → ℝ) :
    shannonEntropy (fun z : B × A => p z.1 z.2) =
      shannonEntropy (fun b => ∑ a, p b a) + conditionalShannon p := by
  simp only [conditionalShannon,rowEntropy,shannonEntropy_eq_negMulLog,Fintype.sum_prod_type,
    Finset.sum_sub_distrib]
  ring

lemma conditionalShannon_refine (p : C → B → A → ℝ) (hp : ∀ c b a, 0 ≤ p c b a) :
    conditionalShannon (fun z : C × B => p z.1 z.2) ≤
      conditionalShannon (fun b a => ∑ c, p c b a) := by
  simp only [conditionalShannon,Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  exact Finset.sum_le_sum fun b _ => rowEntropy_sum_le (fun c a => p c b a) (fun c a => hp c b a)
end

section
open MeasureTheory Filter
open scoped BigOperators Topology
variable {Ω A B C : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    [Fintype A] [Fintype B] [Fintype C]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    [MeasurableSpace B] [MeasurableSingletonClass B]
    [MeasurableSpace C] [MeasurableSingletonClass C]

def randomEntropy (F : Ω → A) : ℝ := shannonEntropy (fun a => μ.real (F ⁻¹' {a}))

def randomConditionalEntropy (F : Ω → A) (G : Ω → B) : ℝ :=
  conditionalShannon (fun b a => μ.real {x | G x = b ∧ F x = a})

omit [Fintype B] in
lemma sum_joint_mass (F : Ω → A) (G : Ω → B) (hF : Measurable F) (hG : Measurable G) (b : B) :
    (∑ a, μ.real {x | G x = b ∧ F x = a}) = μ.real (G ⁻¹' {b}) := by
  rw [←measureReal_iUnion_fintype]
  · congr 1
    ext x
    simp
  · intro a a' haa
    apply Set.disjoint_left.mpr
    intro x hx hx'
    exact haa (hx.2.symm.trans hx'.2)
  · intro a
    exact (hG (measurableSet_singleton b)).inter (hF (measurableSet_singleton a))

lemma randomEntropy_pair (F : Ω → A) (G : Ω → B) (hF : Measurable F) (hG : Measurable G) :
    randomEntropy μ (fun x => (G x,F x)) = randomEntropy μ G + randomConditionalEntropy μ F G := by
  have h := shannon_chain_rule (fun b a => μ.real {x | G x = b ∧ F x = a})
  simp_rw [sum_joint_mass μ F G hF hG] at h
  simpa only [randomEntropy,randomConditionalEntropy,Set.preimage,Set.mem_singleton_iff,Prod.ext_iff] using h

lemma randomEntropy_nonneg (F : Ω → A) (hF : Measurable F) : 0 ≤ randomEntropy μ F := by
  apply shannonEntropy_nonneg _ (fun _ => measureReal_nonneg)
  simpa using (sum_measureReal_preimage_singleton (μ := μ) Finset.univ
    (fun a _ => hF (measurableSet_singleton a)))

lemma randomConditionalEntropy_nonneg (F : Ω → A) (G : Ω → B)
    (hF : Measurable F) (hG : Measurable G) : 0 ≤ randomConditionalEntropy μ F G := by
  have h := randomEntropy_comp_le (η := μ) (fun x => (G x,F x)) (hG.prodMk hF) Prod.fst
  change randomEntropy μ G ≤ randomEntropy μ (fun x => (G x,F x)) at h
  rw [randomEntropy_pair μ F G hF hG] at h
  linarith

lemma randomConditionalEntropy_le (F : Ω → A) (G : Ω → B)
    (hF : Measurable F) (hG : Measurable G) : randomConditionalEntropy μ F G ≤ randomEntropy μ F := by
  have h := rowEntropy_sum_le (fun b a => μ.real {x | G x = b ∧ F x = a})
    (fun _ _ => measureReal_nonneg)
  have hsum (a : A) : (∑ b, μ.real {x | G x = b ∧ F x = a}) = μ.real (F ⁻¹' {a}) := by
    have hh := sum_joint_mass μ G F hG hF a
    convert hh using 1
    apply Finset.sum_congr rfl
    intro b _
    congr 1
    ext x
    exact and_comm
  simp_rw [hsum] at h
  have hmass : (∑ a, μ.real (F ⁻¹' {a})) = 1 := by
    simpa using (sum_measureReal_preimage_singleton (μ := μ) Finset.univ
      (fun a _ => hF (measurableSet_singleton a)))
  simpa only [randomConditionalEntropy,conditionalShannon, rowEntropy,hmass,Real.negMulLog_one,
    sub_zero,randomEntropy] using h

lemma randomConditionalEntropy_refine (F : Ω → A) (G : Ω → B) (K : Ω → C)
    (hF : Measurable F) (hG : Measurable G) (hK : Measurable K) :
    randomConditionalEntropy μ F (fun x => (K x,G x)) ≤ randomConditionalEntropy μ F G := by
  have hp := conditionalShannon_refine
    (fun c b a => μ.real {x | K x = c ∧ G x = b ∧ F x = a}) (fun _ _ _ => measureReal_nonneg)
  have he (b : B) (a : A) : (∑ c, μ.real {x | K x = c ∧ G x = b ∧ F x = a}) =
      μ.real {x | G x = b ∧ F x = a} := by
    have hh := sum_joint_mass μ K (fun x => (G x,F x)) hK (hG.prodMk hF) (b,a)
    simpa only [Set.preimage,Set.mem_singleton_iff,Prod.mk.injEq,and_comm,and_left_comm] using hh
  simp_rw [he] at hp
  simpa only [randomConditionalEntropy,Prod.ext_iff,and_assoc] using hp

lemma randomEntropy_prod_le (F : Ω → A) (G : Ω → B) (hF : Measurable F) (hG : Measurable G) :
    randomEntropy μ (fun x => (G x,F x)) ≤ randomEntropy μ G + randomEntropy μ F := by
  rw [randomEntropy_pair μ F G hF hG]
  exact add_le_add_right (randomConditionalEntropy_le μ F G hF hG) _

lemma randomEntropy_recode (F : Ω → A) (hF : Measurable F) (e : A ≃ B) :
    randomEntropy μ (e ∘ F) = randomEntropy μ F := by
  apply le_antisymm (randomEntropy_comp_le F hF e)
  have h := randomEntropy_comp_le (η := μ) (e ∘ F) ((measurable_of_finite e).comp hF) e.symm
  simpa only [Function.comp_def,Equiv.symm_apply_apply] using h
end

section
open MeasureTheory Filter
open scoped Topology BigOperators symmDiff
variable {Ω A B : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    [Fintype A] [Fintype B] [MeasurableSpace A] [MeasurableSingletonClass A]
    [MeasurableSpace B] [MeasurableSingletonClass B]

omit [MeasurableSpace A] [MeasurableSingletonClass A] in
lemma continuous_shannonEntropy : Continuous (shannonEntropy (A := A)) := by
  unfold shannonEntropy
  exact continuous_finsetSum _ fun a _ => Real.continuous_negMulLog.comp (continuous_apply a)

omit [IsProbabilityMeasure μ] [MeasurableSpace A] [MeasurableSingletonClass A] in
lemma randomEntropy_congr_ae {F G : Ω → A} (h : F =ᵐ[μ] G) : randomEntropy μ F = randomEntropy μ G := by
  unfold randomEntropy
  congr 1
  funext a
  apply measureReal_congr
  filter_upwards [h] with x hx
  apply propext
  change F x = a ↔ G x = a
  rw [hx]

omit [IsProbabilityMeasure μ] in
lemma randomEntropy_measurePreserving {Υ : Type*} [MeasurableSpace Υ] (ν : Measure Υ)
    [IsProbabilityMeasure ν] {T : Ω → Υ} (hT : MeasurePreserving T μ ν)
    (F : Υ → A) (hF : Measurable F) : randomEntropy μ (F ∘ T) = randomEntropy ν F := by
  unfold randomEntropy
  congr 1
  funext a
  exact hT.measureReal_preimage (hF (measurableSet_singleton a)).nullMeasurableSet

omit [Fintype A] in
lemma atom_mass_disagreement {F G : Ω → A} (hF : Measurable F) (hG : Measurable G) (a : A) :
    |μ.real (F ⁻¹' {a}) - μ.real (G ⁻¹' {a})| ≤ μ.real {x | F x ≠ G x} := by
  apply (abs_measureReal_sub_le_measureReal_symmDiff
    (hF (measurableSet_singleton a)).nullMeasurableSet
    (hG (measurableSet_singleton a)).nullMeasurableSet).trans
  refine measureReal_mono ?_ (by finiteness)
  intro x hx
  simp only [Set.mem_symmDiff,Set.mem_preimage,Set.mem_singleton_iff,Set.mem_ofPred_eq] at hx ⊢
  rcases hx with hx | hx <;> aesop

lemma randomEntropy_tendsto_of_disagreement {ι : Type*} {l : Filter ι} {Fn : ι → Ω → A} {F : Ω → A}
    (hFn : ∀ n, Measurable (Fn n)) (hF : Measurable F)
    (h : Tendsto (fun n => μ.real {x | Fn n x ≠ F x}) l (𝓝 0)) :
    Tendsto (fun n => randomEntropy μ (Fn n)) l (𝓝 (randomEntropy μ F)) := by
  apply continuous_shannonEntropy.tendsto _ |>.comp
  apply tendsto_pi_nhds.mpr
  intro a
  apply (tendsto_iff_norm_sub_tendsto_zero).mpr
  exact squeeze_zero_norm (fun n => by simpa only [Real.norm_eq_abs,abs_abs] using atom_mass_disagreement μ (hFn n) hF a) h

lemma randomEntropy_self_pair (F : Ω → A) (hF : Measurable F) :
    randomEntropy μ (fun x => (F x,F x)) = randomEntropy μ F := by
  apply le_antisymm (randomEntropy_comp_le F hF (fun a => (a,a)))
  have h := randomEntropy_comp_le (η := μ) (fun x => (F x,F x)) (hF.prodMk hF) Prod.fst
  exact h

lemma randomConditionalEntropy_self (F : Ω → A) (hF : Measurable F) :
    randomConditionalEntropy μ F F = 0 := by
  have h := randomEntropy_pair μ F F hF hF
  rw [randomEntropy_self_pair μ F hF] at h
  linarith

lemma randomConditionalEntropy_tendsto_self {ι : Type*} {l : Filter ι} {Fn : ι → Ω → A} {F : Ω → A}
    (hFn : ∀ n, Measurable (Fn n)) (hF : Measurable F)
    (h : Tendsto (fun n => μ.real {x | Fn n x ≠ F x}) l (𝓝 0)) :
    Tendsto (fun n => randomConditionalEntropy μ F (Fn n)) l (𝓝 0) := by
  have hp : Tendsto (fun n => μ.real {x | (Fn n x,F x) ≠ (F x,F x)}) l (𝓝 0) := by
    have he : (fun n => μ.real {x | (Fn n x,F x) ≠ (F x,F x)}) =
        (fun n => μ.real {x | Fn n x ≠ F x}) := by
      funext n
      congr 1
      ext x
      constructor
      · intro hn he
        exact hn (congrArg (fun a => (a,F x)) he)
      · intro hn he
        exact hn (congrArg Prod.fst he)
    rwa [he]
  have ht := (randomEntropy_tendsto_of_disagreement μ (fun n => (hFn n).prodMk hF)
    (hF.prodMk hF) hp).sub (randomEntropy_tendsto_of_disagreement μ hFn hF h)
  have he n : randomEntropy μ (fun x => (Fn n x,F x)) - randomEntropy μ (Fn n) =
      randomConditionalEntropy μ F (Fn n) := by rw [randomEntropy_pair μ F (Fn n) hF (hFn n)]; ring
  simpa only [he,randomEntropy_self_pair μ F hF,sub_self] using ht
end

section
open MeasureTheory Filter
open scoped Topology BigOperators
variable {Ω A B C D : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [retained0 : IsProbabilityMeasure μ]
    [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    [retained1 : MeasurableSpace A] [retained2 : MeasurableSingletonClass A]
    [retained3 : MeasurableSpace B] [retained4 : MeasurableSingletonClass B]
    [MeasurableSpace C] [MeasurableSingletonClass C]
    [MeasurableSpace D] [MeasurableSingletonClass D]

lemma randomEntropy_mutual_factor (F : Ω → A) (G : Ω → B) (hF : Measurable F) (hG : Measurable G)
    (e : A → B) (r : B → A) (he : G = e ∘ F) (hr : F = r ∘ G) :
    randomEntropy μ F = randomEntropy μ G := by
  apply le_antisymm
  · rw [hr]
    exact randomEntropy_comp_le G hG r
  · rw [he]
    exact randomEntropy_comp_le F hF e

lemma randomEntropy_pair_factor (F : Ω → A) (hF : Measurable F) (e : A → B) :
    randomEntropy μ (fun x => (F x,e (F x))) = randomEntropy μ F := by
  apply randomEntropy_mutual_factor μ _ F (hF.prodMk ((measurable_of_finite e).comp hF)) hF
    Prod.fst (fun a => (a,e a)) rfl rfl

lemma randomConditionalEntropy_condition_redundant (F : Ω → A) (G : Ω → B)
    (hF : Measurable F) (hG : Measurable G) (e : B → C) :
    randomConditionalEntropy μ F (fun x => (G x,e (G x))) = randomConditionalEntropy μ F G := by
  have hp := randomEntropy_pair μ F (fun x => (G x,e (G x))) hF
    (hG.prodMk ((measurable_of_finite e).comp hG))
  have hq := randomEntropy_pair μ F G hF hG
  have hj : randomEntropy μ (fun x => ((G x,e (G x)),F x)) =
      randomEntropy μ (fun x => (G x,F x)) := by
    exact randomEntropy_mutual_factor μ _ _
      ((hG.prodMk ((measurable_of_finite e).comp hG)).prodMk hF) (hG.prodMk hF)
      (fun z => (z.1.1,z.2)) (fun z => ((z.1,e z.1),z.2)) rfl rfl
  rw [hj,randomEntropy_pair_factor μ G hG e] at hp
  linarith

lemma randomConditionalEntropy_condition_comp (F : Ω → A) (G : Ω → B)
    (hF : Measurable F) (hG : Measurable G) (e : B → C) :
    randomConditionalEntropy μ F G ≤ randomConditionalEntropy μ F (e ∘ G) := by
  have h := randomConditionalEntropy_refine μ F (e ∘ G) G hF
    ((measurable_of_finite e).comp hG) hG
  change randomConditionalEntropy μ F (fun x => (G x,e (G x))) ≤ _ at h
  rwa [randomConditionalEntropy_condition_redundant μ F G hF hG e] at h

lemma randomConditionalEntropy_measurable_factor (F : Ω → A) (G : Ω → B) (K : Ω → C)
    (hF : Measurable F) (hK : Measurable K) [Nonempty B]
    (hG : Measurable[MeasurableSpace.comap K inferInstance] G) :
    randomConditionalEntropy μ F K ≤ randomConditionalEntropy μ F G := by
  obtain ⟨e,he⟩ := (Function.factorsThrough_iff G).mp hG.factorsThrough
  rw [he]
  exact randomConditionalEntropy_condition_comp μ F K hF hK e

lemma randomConditionalEntropy_measurePreserving {Υ : Type*} [MeasurableSpace Υ] (ν : Measure Υ)
    [IsProbabilityMeasure ν] {T : Ω → Υ} (hT : MeasurePreserving T μ ν)
    (F : Υ → A) (G : Υ → B) (hF : Measurable F) (hG : Measurable G) :
    randomConditionalEntropy μ (F ∘ T) (G ∘ T) = randomConditionalEntropy ν F G := by
  have h := randomEntropy_pair μ (F ∘ T) (G ∘ T) (hF.comp hT.measurable) (hG.comp hT.measurable)
  have h' := randomEntropy_pair ν F G hF hG
  have hp := randomEntropy_measurePreserving μ ν hT (fun x => (G x,F x)) (hG.prodMk hF)
  have hg := randomEntropy_measurePreserving μ ν hT G hG
  change randomEntropy μ (fun x => ((G ∘ T) x,(F ∘ T) x)) = _ at hp
  rw [hp,hg] at h
  linarith

include retained0 retained1 retained2 retained3 retained4 in
lemma randomConditionalEntropy_congr_ae {F F' : Ω → A} {G G' : Ω → B}
    (hF : F =ᵐ[μ] F') (hG : G =ᵐ[μ] G') :
    randomConditionalEntropy μ F G = randomConditionalEntropy μ F' G' := by
  let _ := retained0
  let _ := retained1
  let _ := retained2
  let _ := retained3
  let _ := retained4
  unfold randomConditionalEntropy
  congr 1
  funext b a
  apply measureReal_congr
  filter_upwards [hF,hG] with x hx hy
  apply propext
  rw [hx,hy]
end

section
open MeasureTheory Filter
open scoped Topology BigOperators
variable {Ω A B C : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    [Fintype A] [Fintype B] [Fintype C]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    [MeasurableSpace B] [MeasurableSingletonClass B]
    [MeasurableSpace C] [MeasurableSingletonClass C]

lemma randomConditionalEntropy_chain (F : Ω → A) (G : Ω → B) (K : Ω → C)
    (hF : Measurable F) (hG : Measurable G) (hK : Measurable K) :
    randomConditionalEntropy μ (fun x => (G x,F x)) K =
      randomConditionalEntropy μ G K + randomConditionalEntropy μ F (fun x => (K x,G x)) := by
  have h1 := randomEntropy_pair μ (fun x => (G x,F x)) K (hG.prodMk hF) hK
  have h2 := randomEntropy_pair μ F (fun x => (K x,G x)) hF (hK.prodMk hG)
  have h3 := randomEntropy_pair μ G K hG hK
  have he : randomEntropy μ (fun x => (K x,(G x,F x))) =
      randomEntropy μ (fun x => ((K x,G x),F x)) := by
    exact randomEntropy_mutual_factor μ _ _ (hK.prodMk (hG.prodMk hF)) ((hK.prodMk hG).prodMk hF)
      (fun z => ((z.1,z.2.1),z.2.2)) (fun z => (z.1.1,(z.1.2,z.2))) rfl rfl
  linarith

lemma randomConditionalEntropy_pair_le (F : Ω → A) (G : Ω → B) (K : Ω → C)
    (hF : Measurable F) (hG : Measurable G) (hK : Measurable K) :
    randomConditionalEntropy μ (fun x => (G x,F x)) K ≤
      randomConditionalEntropy μ G K + randomConditionalEntropy μ F K := by
  rw [randomConditionalEntropy_chain μ F G K hF hG hK]
  have h := randomConditionalEntropy_condition_comp μ F (fun x => (K x,G x)) hF (hK.prodMk hG) Prod.fst
  exact add_le_add_right h _

lemma randomConditionalEntropy_mutual_factor (F : Ω → A) (G : Ω → B) (K : Ω → C)
    (hF : Measurable F) (hG : Measurable G) (hK : Measurable K)
    (e : A → B) (r : B → A) (he : G = e ∘ F) (hr : F = r ∘ G) :
    randomConditionalEntropy μ F K = randomConditionalEntropy μ G K := by
  have h1 := randomEntropy_pair μ F K hF hK
  have h2 := randomEntropy_pair μ G K hG hK
  have he' : (fun x => (K x,G x)) = (fun z : C × A => (z.1,e z.2)) ∘ (fun x => (K x,F x)) := by rw [he]; rfl
  have hr' : (fun x => (K x,F x)) = (fun z : C × B => (z.1,r z.2)) ∘ (fun x => (K x,G x)) := by rw [hr]; rfl
  have h := randomEntropy_mutual_factor μ _ _ (hK.prodMk hF) (hK.prodMk hG)
    (fun z : C × A => (z.1,e z.2)) (fun z : C × B => (z.1,r z.2)) he' hr'
  linarith

omit [MeasurableSpace A] [MeasurableSingletonClass A] in
lemma randomEntropy_fintype_one [Unique A] (F : Ω → A) : randomEntropy μ F = 0 := by
  classical
  have he : F = fun _ => default := funext fun x => Unique.eq_default _
  rw [he]
  simp [randomEntropy,shannonEntropy]

lemma randomConditionalEntropy_fintype_one [Unique A] (F : Ω → A) (G : Ω → B)
    (hF : Measurable F) (hG : Measurable G) : randomConditionalEntropy μ F G = 0 := by
  apply le_antisymm _ (randomConditionalEntropy_nonneg μ F G hF hG)
  have h := randomConditionalEntropy_le μ F G hF hG
  rwa [randomEntropy_fintype_one μ F] at h

def integerWord (F : ℤ → Ω → A) (t : ℤ) (n : ℕ) : Ω → Fin n → A :=
  fun x i => F (t+i.val) x

omit [Fintype A] [MeasurableSingletonClass A] in
lemma measurable_integerWord (F : ℤ → Ω → A) (hF : ∀ t, Measurable (F t)) (t : ℤ) (n : ℕ) :
    Measurable (integerWord F t n) := Measurable.of_eval fun _ => hF _

lemma integerWord_pair (F : ℤ → Ω → A) (hF : ∀ t, Measurable (F t)) (t : ℤ) (m n : ℕ) :
    randomEntropy μ (integerWord F t (m+n)) =
      randomEntropy μ (fun x => (integerWord F t m x,integerWord F (t+m) n x)) := by
  apply randomEntropy_mutual_factor μ _ _ (measurable_integerWord F hF _ _)
    ((measurable_integerWord F hF _ _).prodMk (measurable_integerWord F hF _ _))
    (fun z => (fun i => z (i.castAdd n),fun i => z (i.natAdd m)))
    (fun z => Fin.append z.1 z.2)
  · funext x
    apply Prod.ext
    · rfl
    · funext i
      simp only [integerWord,Function.comp_apply,Fin.val_natAdd,Nat.cast_add]
      congr 1
      ring
  · funext x i
    induction i using Fin.addCases with
    | left i => simp [integerWord]
    | right i => simp only [integerWord,Function.comp_apply,Fin.append_right,Fin.val_natAdd,Nat.cast_add]; congr 1; ring

lemma integerWord_add (F : ℤ → Ω → A) (hF : ∀ t, Measurable (F t)) (t : ℤ) (m n : ℕ) :
    randomEntropy μ (integerWord F t (m+n)) = randomEntropy μ (integerWord F t m) +
      randomConditionalEntropy μ (integerWord F (t+m) n) (integerWord F t m) := by
  rw [integerWord_pair μ F hF t m n,randomEntropy_pair μ _ _
    (measurable_integerWord F hF _ _) (measurable_integerWord F hF _ _)]

lemma integerWord_succ (F : ℤ → Ω → A) (hF : ∀ t, Measurable (F t)) (t : ℤ) (n : ℕ) :
    randomEntropy μ (integerWord F t (n+1)) = randomEntropy μ (integerWord F t n) +
      randomConditionalEntropy μ (F (t+n)) (integerWord F t n) := by
  rw [integerWord_add μ F hF t n 1]
  congr 1
  apply randomConditionalEntropy_mutual_factor μ _ _ _ (measurable_integerWord F hF _ _)
    (hF _) (measurable_integerWord F hF _ _) (fun z => z 0) (fun a _ => a)
  · funext x
    simp [integerWord]
  · funext x i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    simp only [integerWord,Fin.val_zero,Nat.cast_zero,add_zero,Function.comp_apply]

end

section
open Filter
open scoped Topology BigOperators

theorem entropy_rate_of_decreasing_increments (H : ℕ → ℝ) (h0 : H 0 = 0)
    (hmono : Antitone (fun n => H (n+1) - H n))
    (hpos : ∀ n, 0 ≤ H (n+1) - H n) :
    ∃ h : ℝ, 0 ≤ h ∧ (∀ n, h ≤ H (n+1) - H n) ∧
      Tendsto (fun n : ℕ => H n / n) atTop (𝓝 h) := by
  let a : ℕ → ℝ := fun n => H (n+1) - H n
  have hb : BddBelow (Set.range a) := ⟨0,by rintro _ ⟨n,rfl⟩; exact hpos n⟩
  refine ⟨⨅ n, a n,?_,fun n => ciInf_le hb n,?_⟩
  · exact le_ciInf (fun n => hpos n)
  · have ht := (tendsto_atTop_ciInf hmono hb).cesaro
    have he n : (∑ j ∈ Finset.range n, a j) = H n := by
      dsimp [a]
      rw [Finset.sum_range_sub,h0,sub_zero]
    simpa only [a,Finset.sum_range_sub,h0,sub_zero,div_eq_mul_inv,mul_comm] using ht

lemma entropy_block_lower (H : ℕ → ℝ) (h : ℝ)
    (ha : ∀ n, h ≤ H (n+1) - H n) (m n : ℕ) :
    (n : ℝ) * h ≤ H (m+n) - H m := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hh := ha (m+n)
    simp only [Nat.cast_add,Nat.cast_one]
    rw [show m + (n+1) = (m+n)+1 by omega]
    nlinarith

theorem entropy_zero_of_tail_bounds (H K : ℕ → ℝ) (h : ℝ)
    (hrate : Tendsto (fun n : ℕ => H n / n) atTop (𝓝 h))
    (hK : ∀ n, 0 ≤ K n)
    (hb : ∀ ε : ℝ, 0 < ε → ∃ c : ℕ, ∀ n : ℕ,
      K n + n * h ≤ H (n+c) + n * ε) :
    Tendsto (fun n : ℕ => K n / n) atTop (𝓝 0) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Eventually.of_forall fun n => ha.trans_le (div_nonneg (hK n) (Nat.cast_nonneg n))
  · intro ε hε
    obtain ⟨c,hc⟩ := hb (ε/2) (by positivity)
    have hd : Tendsto (fun n : ℕ => (n+c : ℝ) / n) atTop (𝓝 1) := by
      have ht : Tendsto (fun n : ℕ => (c:ℝ) / n) atTop (𝓝 0) := tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop (R := ℝ))
      have hh : Tendsto (fun n : ℕ => 1 + c / (n : ℝ)) atTop (𝓝 (1+0)) := tendsto_const_nhds.add ht
      simp only [add_zero] at hh
      apply hh.congr'
      filter_upwards [eventually_ge_atTop 1] with n hn
      have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
      field_simp
    have hsh : Tendsto (fun n : ℕ => H (n+c) / n) atTop (𝓝 h) := by
      have hh := (hrate.comp (tendsto_add_atTop_nat c)).mul hd
      rw [mul_one] at hh
      apply hh.congr'
      filter_upwards [eventually_ge_atTop 1] with n hn
      have hn' : (n+c : ℝ) ≠ 0 := by positivity
      simp only [Function.comp_def,Nat.cast_add]
      field_simp
    have hu := (hsh.sub_const h).add_const (ε/2)
    simp only [sub_self,zero_add] at hu
    filter_upwards [hu.eventually (gt_mem_nhds (show ε/2 < ε by linarith)),
      eventually_ge_atTop 1] with n hh hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    apply lt_of_le_of_lt _ hh
    apply (div_le_iff₀ hn').mpr
    have hf := hc n
    have he : (H (n+c) / n - h + ε/2) * n = H (n+c) - n*h + n*(ε/2) := by
      field_simp
    rw [he]
    linarith
end

section
open MeasureTheory Filter
open scoped Topology BigOperators
variable {Ω A : Type*} [retained5 : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]

omit [MeasurableSpace Ω] [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A] in
lemma integerWord_subword (F : ℤ → Ω → A) (s : ℤ) (l n m : ℕ) (h : l+n ≤ m) :
    integerWord F (s+l) n = (fun z : Fin m → A => fun i : Fin n =>
      z ⟨l+i.val,by omega⟩) ∘ integerWord F s m := by
  funext x i
  simp only [integerWord,Function.comp_apply,Nat.cast_add]
  congr 1
  ring

omit [MeasurableSpace Ω] in
lemma integerWord_subword_measurable (F : ℤ → Ω → A) (s : ℤ) (l n m : ℕ) (h : l+n ≤ m) :
    Measurable[MeasurableSpace.comap (integerWord F s m) inferInstance] (integerWord F (s+l) n) := by
  rw [integerWord_subword F s l n m h]
  exact (measurable_of_finite _).comp (comap_measurable _)

include retained5 in
lemma pastWord_comap_mono (F : ℤ → Ω → A) (t : ℤ) :
    Monotone (fun n : ℕ => MeasurableSpace.comap (integerWord F (t-n) n) inferInstance) := by
  let _ := retained5
  intro m n hmn
  have hh := integerWord_subword_measurable F (t-n) (n-m) m n (by omega)
  have he : t - (n:ℤ) + (n-m:ℕ) = t-m := by rw [Nat.cast_sub hmn]; ring
  rw [he] at hh
  exact hh.comap_le

include retained5 in
lemma windowWord_comap_mono (F : ℤ → Ω → A) :
    Monotone (fun n : ℕ => MeasurableSpace.comap (integerWord F (-(n:ℤ)) (2*n+1)) inferInstance) := by
  let _ := retained5
  intro m n hmn
  have hh := integerWord_subword_measurable F (-(n:ℤ)) (n-m) (2*m+1) (2*n+1) (by omega)
  have he : -(n:ℤ) + (n-m:ℕ) = -(m:ℤ) := by rw [Nat.cast_sub hmn]; ring
  rw [he] at hh
  exact hh.comap_le

variable (U : ℤ → Ω → Ω) (hU : ∀ s, MeasurePreserving (U s) μ μ)
    (F : ℤ → Ω → A) (hF : ∀ t, Measurable (F t))
    (htrans : ∀ t s x, F (t+s) x = F t (U s x))

omit [MeasurableSpace Ω] [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A] in
include htrans in
lemma integerWord_translate (t s : ℤ) (n : ℕ) :
    integerWord F (t+s) n = integerWord F t n ∘ U s := by
  funext x i
  change F ((t+s)+i.val) x = F (t+i.val) (U s x)
  rw [show (t+s)+(i.val:ℤ) = (t+i.val)+s by ring,htrans]

include hU hF htrans
lemma integerWord_entropy_translate (t : ℤ) (n : ℕ) :
    randomEntropy μ (integerWord F t n) = randomEntropy μ (integerWord F 0 n) := by
  rw [show t = 0+t by simp,integerWord_translate U F htrans]
  exact randomEntropy_measurePreserving μ μ (hU t) _ (measurable_integerWord F hF _ _)

lemma conditionalEntropy_past_translate (t : ℤ) (n : ℕ) :
    randomConditionalEntropy μ (F t) (integerWord F (t-n) n) =
      randomConditionalEntropy μ (F 0) (integerWord F (-(n:ℤ)) n) := by
  have he : integerWord F (t-n) n = integerWord F (-(n:ℤ)) n ∘ U t := by
    rw [show t - (n:ℤ) = -(n:ℤ)+t by ring,integerWord_translate U F htrans]
  have hf : F t = F 0 ∘ U t := by funext x; simpa using htrans 0 t x
  rw [he,hf]
  exact randomConditionalEntropy_measurePreserving μ μ (hU t) _ _ (hF _) (measurable_integerWord F hF _ _)

lemma entropy_increment_past (n : ℕ) :
    randomEntropy μ (integerWord F 0 (n+1)) - randomEntropy μ (integerWord F 0 n) =
      randomConditionalEntropy μ (F 0) (integerWord F (-(n:ℤ)) n) := by
  have hh := integerWord_succ μ F hF (-(n:ℤ)) n
  rw [integerWord_entropy_translate μ U hU F hF htrans (-(n:ℤ)) (n+1),
    integerWord_entropy_translate μ U hU F hF htrans (-(n:ℤ)) n] at hh
  simp only [neg_add_cancel] at hh
  linarith

theorem stationary_entropy_rate [Nonempty A] :
    ∃ h : ℝ, 0 ≤ h ∧
      (∀ (t : ℤ) (n : ℕ), h ≤ randomConditionalEntropy μ (F t) (integerWord F (t-n) n)) ∧
      Tendsto (fun n : ℕ => randomEntropy μ (integerWord F 0 n) / n) atTop (𝓝 h) := by
  let H : ℕ → ℝ := fun n => randomEntropy μ (integerWord F 0 n)
  have h0 : H 0 = 0 := randomEntropy_fintype_one μ _
  have he n : H (n+1) - H n = randomConditionalEntropy μ (F 0) (integerWord F (-(n:ℤ)) n) :=
    entropy_increment_past μ U hU F hF htrans n
  have hmono : Antitone (fun n => H (n+1) - H n) := by
    intro m n hmn
    change H (n+1) - H n ≤ H (m+1) - H m
    rw [he,he]
    apply randomConditionalEntropy_measurable_factor μ _ _ _ (hF 0) (measurable_integerWord F hF _ _)
    have hh := (pastWord_comap_mono F 0 hmn)
    simp only [zero_sub] at hh
    exact (comap_measurable _).mono hh le_rfl
  have hpos n : 0 ≤ H (n+1)-H n := by
    rw [he]
    exact randomConditionalEntropy_nonneg μ _ _ (hF _) (measurable_integerWord F hF _ _)
  obtain ⟨h,hpos,hle,ht⟩ := entropy_rate_of_decreasing_increments H h0 hmono hpos
  refine ⟨h,hpos,?_,ht⟩
  intro t n
  rw [conditionalEntropy_past_translate μ U hU F hF htrans,←he]
  exact hle n
end

section
open MeasureTheory Filter Set
variable {Ω : Type*} [m₀ : MeasurableSpace Ω] (μ : Measure Ω)

@[instance_reducible]
def completedFactor (m : MeasurableSpace Ω) : MeasurableSpace Ω where
  MeasurableSet' s := MeasurableSet[m₀] s ∧ ∃ t : Set Ω, MeasurableSet[m] t ∧
    ∀ᵐ x ∂μ, x ∈ s ↔ x ∈ t
  measurableSet_empty := ⟨@MeasurableSet.empty Ω m₀,∅,@MeasurableSet.empty Ω m,Eventually.of_forall fun _ => Iff.rfl⟩
  measurableSet_compl := by
    rintro s ⟨hs,t,ht,he⟩
    exact ⟨hs.compl,tᶜ,ht.compl,he.mono fun x hx => not_congr hx⟩
  measurableSet_iUnion := by
    intro s hs
    choose t ht he using fun n => (hs n).2
    refine ⟨MeasurableSet.iUnion fun n => (hs n).1,⋃ n, t n,MeasurableSet.iUnion ht,?_⟩
    filter_upwards [ae_all_iff.mpr he] with x hx
    simp only [mem_iUnion]
    exact exists_congr fun n => hx n

lemma completedFactor_le (m : MeasurableSpace Ω) : completedFactor (m₀ := m₀) μ m ≤ m₀ :=
  fun _ hs => hs.1

lemma le_completedFactor {m : MeasurableSpace Ω} (hm : m ≤ m₀) : m ≤ completedFactor (m₀ := m₀) μ m :=
  fun s hs => ⟨hm s hs,s,hs,Eventually.of_forall fun _ => Iff.rfl⟩

lemma completedFactor_mono : Monotone (completedFactor (m₀ := m₀) μ) := by
  intro m n h s hs
  obtain ⟨hs,t,ht,he⟩ := hs
  exact ⟨hs,t,h t ht,he⟩

lemma completedFactor_congr_set (m : MeasurableSpace Ω) (s t : Set Ω)
    (hs : MeasurableSet[m₀] s) (ht : MeasurableSet[completedFactor (m₀ := m₀) μ m] t)
    (he : ∀ᵐ x ∂μ, x ∈ s ↔ x ∈ t) : MeasurableSet[completedFactor (m₀ := m₀) μ m] s := by
  obtain ⟨_,r,hr,her⟩ := ht
  exact ⟨hs,r,hr,he.and her |>.mono fun x hx => hx.1.trans hx.2⟩

lemma measurable_completedFactor_of_ae {Y : Type*} [TopologicalSpace Y] [TopologicalSpace.PseudoMetrizableSpace Y]
    [MeasurableSpace Y] [BorelSpace Y]
    (m : MeasurableSpace Ω) {f : Ω → Y} (hf : Measurable[m₀] f)
    (h : AEStronglyMeasurable[m] f μ) : Measurable[completedFactor (m₀ := m₀) μ m] f := by
  intro s hs
  exact ⟨hf hs,(h.mk f) ⁻¹' s,h.stronglyMeasurable_mk.measurable hs,
    h.ae_eq_mk.mono fun x hx => by simp only [mem_preimage,hx]⟩

lemma completedFactor_iInf_measurable {Y : Type*} [TopologicalSpace Y] [TopologicalSpace.PseudoMetrizableSpace Y]
    [MeasurableSpace Y] [BorelSpace Y]
    (m : ℕ → MeasurableSpace Ω) {f : Ω → Y} (hf : Measurable[m₀] f)
    (h : ∀ n, AEStronglyMeasurable[m n] f μ) :
    Measurable[⨅ n, completedFactor (m₀ := m₀) μ (m n)] f := by
  intro s hs
  exact MeasurableSpace.measurableSet_iInf.mpr fun n =>
    measurable_completedFactor_of_ae μ (m n) hf (h n) hs
end

section
open MeasureTheory Filter Set
open scoped Topology BigOperators
variable {Ω : Type*} [m₀ : MeasurableSpace Ω] (μ : Measure Ω)

lemma aeStrong_limit_factor {E : Type*} [TopologicalSpace E] [Nonempty E]
    [TopologicalSpace.IsCompletelyMetrizableSpace E] (m : MeasurableSpace Ω)
    {f : ℕ → Ω → E} {g : Ω → E} (hf : ∀ n, AEStronglyMeasurable[m] (f n) μ)
    (ht : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x))) :
    AEStronglyMeasurable[m] g μ := by
  let F : ℕ → Ω → E := fun n => (hf n).mk (f n)
  have hF : ∀ n, StronglyMeasurable[m] (F n) := fun n => (hf n).stronglyMeasurable_mk
  refine ⟨fun x => limUnder atTop (fun n => F n x),StronglyMeasurable.limUnder hF,?_⟩
  filter_upwards [ht,ae_all_iff.mpr (fun n => (hf n).ae_eq_mk)] with x hx he
  have h : Tendsto (fun n => F n x) atTop (𝓝 (g x)) := by
    convert hx using 1
    funext n
    exact (he n).symm
  exact h.limUnder_eq.symm

lemma simpleFunc_aeStrong_of_completed (m : MeasurableSpace Ω)
    (g : @SimpleFunc Ω (completedFactor (m₀ := m₀) μ m) ℝ) :
    AEStronglyMeasurable[m] g μ := by
  classical
  have hsets : ∀ c : ℝ, ∃ t : Set Ω, MeasurableSet[m] t ∧
      ∀ᵐ x ∂μ, g x = c ↔ x ∈ t := fun c => (@SimpleFunc.measurableSet_fiber Ω ℝ (completedFactor (m₀ := m₀) μ m) g c).2
  choose t ht he using hsets
  let G : Ω → ℝ := fun x => ∑ c ∈ (@SimpleFunc.range Ω ℝ (completedFactor (m₀ := m₀) μ m) g), (t c).indicator (fun _ => c) x
  have hm : StronglyMeasurable[m] G :=
    Finset.stronglyMeasurable_fun_sum _ fun c _ => stronglyMeasurable_const.indicator (ht c)
  refine ⟨G,hm,?_⟩
  filter_upwards [ae_all_iff.mpr (fun c : (@SimpleFunc.range Ω ℝ (completedFactor (m₀ := m₀) μ m) g) => he c.val)] with x hx
  have hi (c : ℝ) (hc : c ∈ (@SimpleFunc.range Ω ℝ (completedFactor (m₀ := m₀) μ m) g)) :
      (t c).indicator (fun _ => c) x = if g x = c then c else 0 := by
    simp only [Set.indicator_apply]
    rw [←hx ⟨c,hc⟩]
  dsimp [G]
  simp_rw [Finset.sum_congr rfl hi]
  symm
  rw [Finset.sum_eq_single (g x)]
  · simp only [ite_true]
  · intro c hc hne
    exact ite_eq_right (Ne.symm hne)
  · intro hnot
    exact False.elim (hnot (@SimpleFunc.mem_range_self Ω ℝ (completedFactor (m₀ := m₀) μ m) g x))

lemma aeStrong_of_measurable_completed (m : MeasurableSpace Ω)
    {f : Ω → ℝ} (hf : Measurable[completedFactor (m₀ := m₀) μ m] f) :
    AEStronglyMeasurable[m] f μ := by
  have hs := hf.stronglyMeasurable
  exact aeStrong_limit_factor (m₀ := m₀) μ m (fun n => simpleFunc_aeStrong_of_completed (m₀ := m₀) μ m (hs.approx n))
    (Eventually.of_forall hs.tendsto_approx)
end

section
open MeasureTheory Filter Set
open scoped Topology BigOperators symmDiff
variable {Ω : Type*} [m₀ : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

lemma set_approx_iSup_completed (m : ℕ → MeasurableSpace Ω) (hm : ∀ n, m n ≤ m₀)
    (hmono : Monotone m) {s : Set Ω}
    (hs : MeasurableSet[completedFactor (m₀ := m₀) μ (⨆ n, m n)] s)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ n t, MeasurableSet[m n] t ∧ μ.real (s ∆ t) < ε := by
  have hle : (⨆ n, m n) ≤ m₀ := iSup_le hm
  let C : Set (Set Ω) := {t | ∃ n, MeasurableSet[m n] t}
  have hCalg : IsSetAlgebra C := by
    refine ⟨⟨0,@MeasurableSet.empty Ω (m 0)⟩,?_,?_⟩
    · rintro t ⟨n,hn⟩
      exact ⟨n,hn.compl⟩
    · rintro t t' ⟨n,hn⟩ ⟨k,hk⟩
      exact ⟨max n k,((hmono (le_max_left n k)) _ hn).union ((hmono (le_max_right n k)) _ hk)⟩
  have hCgen : (⨆ n, m n) = MeasurableSpace.generateFrom C := by
    apply le_antisymm
    · apply iSup_le
      intro n t ht
      exact MeasurableSpace.measurableSet_generateFrom ⟨n,ht⟩
    · apply MeasurableSpace.generateFrom_le
      rintro t ⟨n,hn⟩
      exact (le_iSup m n) _ hn
  have hdense := @Measure.MeasureDense.of_generateFrom_isSetAlgebra_finite Ω (⨆ n, m n) (μ.trim hle)
    C inferInstance hCalg hCgen
  obtain ⟨t,ht,he⟩ := hs.2
  obtain ⟨r,⟨n,hn⟩,hr⟩ := @Measure.MeasureDense.approx Ω (⨆ n, m n) (μ.trim hle) C hdense t ht (by finiteness) ε hε
  have hrAll : MeasurableSet[(⨆ n, m n)] r := (le_iSup m n) _ hn
  rw [trim_measurableSet_eq hle (ht.symmDiff hrAll)] at hr
  have he' : s ∆ r =ᵐ[μ] t ∆ r := by
    filter_upwards [he] with x hx
    apply propext
    simp only [Set.mem_symmDiff,hx]
  refine ⟨n,r,hn,?_⟩
  have her : μ.real (s ∆ r) = μ.real (t ∆ r) := measureReal_congr he'
  apply lt_of_eq_of_lt her
  have hh := ENNReal.toReal_lt_toReal (measure_ne_top μ (t ∆ r)) ENNReal.ofReal_ne_top |>.mpr hr
  simpa only [Measure.real,ENNReal.toReal_ofReal hε.le] using hh

variable {B : Type*} [Fintype B] [Nonempty B] [MeasurableSpace B] [MeasurableSingletonClass B]

def pickFiniteBit (v : B → Bool) : B :=
  if h : ∃ b, v b = true then Classical.choose h else Classical.choice ‹Nonempty B›

omit [MeasurableSpace B] [MeasurableSingletonClass B] in
lemma pickFiniteBit_eq (b : B) (v : B → Bool) (hv : ∀ a, v a = true ↔ a = b) :
    pickFiniteBit v = b := by
  have he : ∃ a, v a = true := ⟨b,(hv b).mpr rfl⟩
  simp only [pickFiniteBit,dite_eq_left he]
  exact (hv _).mp (Classical.choose_spec he)

lemma finite_approx_iSup_completed (m : ℕ → MeasurableSpace Ω) (hm : ∀ n, m n ≤ m₀)
    (hmono : Monotone m) (F : Ω → B)
    (hF : Measurable[completedFactor (m₀ := m₀) μ (⨆ n, m n)] F)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ n G, Measurable[m n] G ∧ μ.real {x | G x ≠ F x} < ε := by
  classical
  let δ := ε / (Fintype.card B + 1 : ℝ)
  have hδ : 0 < δ := div_pos hε (by positivity)
  have hsets (b : B) := set_approx_iSup_completed μ m hm hmono
    (hF (measurableSet_singleton b)) δ hδ
  choose n r hr hεr using hsets
  let N := Finset.univ.sup n
  have hrN (b : B) : MeasurableSet[m N] (r b) :=
    (hmono (Finset.le_sup (f := n) (Finset.mem_univ b))) _ (hr b)
  let code : Ω → B → Bool := fun x b => if x ∈ r b then true else false
  have hcode : Measurable[m N] code := by
    refine @Measurable.of_eval Ω B (fun _ => Bool) (m N) _ code ?_
    intro b
    exact Measurable.ite (hrN b) measurable_const measurable_const
  let G : Ω → B := pickFiniteBit ∘ code
  have hG : Measurable[m N] G := (measurable_of_finite pickFiniteBit).comp hcode
  have hsub : {x | G x ≠ F x} ⊆ ⋃ b, ((F ⁻¹' {b}) ∆ r b) := by
    intro x hx
    by_contra hn
    have hbits (b : B) : code x b = true ↔ b = F x := by
      have hh : x ∉ (F ⁻¹' {b}) ∆ r b := fun hh => hn (Set.mem_iUnion.mpr ⟨b,hh⟩)
      simp only [Set.mem_symmDiff,Set.mem_preimage,Set.mem_singleton_iff,not_or] at hh
      simp only [code,ite_eq_left_iff,Bool.false_eq_true,imp_false]
      aesop
    exact hx (pickFiniteBit_eq (F x) (code x) hbits)
  refine ⟨N,G,hG,lt_of_le_of_lt ((measureReal_mono hsub).trans (measureReal_iUnion_fintype_le _)) ?_⟩
  calc
    (∑ b, μ.real ((F ⁻¹' {b}) ∆ r b)) ≤ ∑ _ : B, δ := Finset.sum_le_sum fun b _ => (hεr b).le
    _ = (Fintype.card B : ℝ) * δ := by simp
    _ < ε := by
      have hd : (0 : ℝ) < Fintype.card B + 1 := by positivity
      dsimp [δ]
      rw [← mul_div_assoc]
      exact (div_lt_iff₀ hd).mpr (by nlinarith)
end

section
open MeasureTheory Filter
open scoped Topology BigOperators
variable {Ω A B : Type*} [m₀ : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    [Fintype A] [Fintype B] [MeasurableSpace A] [MeasurableSingletonClass A]
    [MeasurableSpace B] [MeasurableSingletonClass B]

lemma randomConditionalEntropy_tendsto_condition {ι : Type*} {l : Filter ι}
    (F : Ω → A) (hF : Measurable F) {Gn : ι → Ω → B} {G : Ω → B}
    (hGn : ∀ n, Measurable (Gn n)) (hG : Measurable G)
    (h : Tendsto (fun n => μ.real {x | Gn n x ≠ G x}) l (𝓝 0)) :
    Tendsto (fun n => randomConditionalEntropy μ F (Gn n)) l (𝓝 (randomConditionalEntropy μ F G)) := by
  have hp : Tendsto (fun n => μ.real {x | (Gn n x,F x) ≠ (G x,F x)}) l (𝓝 0) := by
    have he : (fun n => μ.real {x | (Gn n x,F x) ≠ (G x,F x)}) =
        (fun n => μ.real {x | Gn n x ≠ G x}) := by
      funext n
      congr 1
      ext x
      constructor
      · intro hn he
        exact hn (congrArg (fun a => (a,F x)) he)
      · intro hn he
        exact hn (congrArg Prod.fst he)
    rwa [he]
  have ht := (randomEntropy_tendsto_of_disagreement μ (fun n => (hGn n).prodMk hF)
    (hG.prodMk hF) hp).sub (randomEntropy_tendsto_of_disagreement μ hGn hG h)
  have he (H : Ω → B) (hH : Measurable H) : randomEntropy μ (fun x => (H x,F x)) - randomEntropy μ H =
      randomConditionalEntropy μ F H := by rw [randomEntropy_pair μ F H hF hH]; ring
  simpa only [he G hG,he _ (hGn _)] using ht

lemma finite_approx_completed_sequence [Nonempty B]
    (m : ℕ → MeasurableSpace Ω) (hm : ∀ n, m n ≤ m₀) (hmono : Monotone m)
    (G : Ω → B) (hG : Measurable[completedFactor (m₀ := m₀) μ (⨆ n, m n)] G) :
    ∃ n : ℕ → ℕ, ∃ Gn : ℕ → Ω → B, (∀ l, Measurable[m (n l)] (Gn l)) ∧
      Tendsto (fun l => μ.real {x | Gn l x ≠ G x}) atTop (𝓝 0) := by
  have hs (l : ℕ) := finite_approx_iSup_completed μ m hm hmono G hG (1 / (l+1 : ℝ)) (by positivity)
  choose n Gn hGn he using hs
  refine ⟨n,Gn,hGn,?_⟩
  have ht : Tendsto (fun l : ℕ => 1 / (l+1 : ℝ)) atTop (𝓝 0) := by
    exact tendsto_const_nhds.div_atTop ((tendsto_natCast_atTop_atTop (R := ℝ)).atTop_add tendsto_const_nhds)
  exact squeeze_zero (fun _ => measureReal_nonneg) (fun l => (he l).le) ht

lemma exists_conditional_entropy_lt_of_completed [Nonempty A]
    {C : ℕ → Type*} [∀ n, Fintype (C n)] [∀ n, MeasurableSpace (C n)]
    [∀ n, MeasurableSingletonClass (C n)] (K : ∀ n, Ω → C n)
    (hK : ∀ n, Measurable (K n))
    (hmono : Monotone (fun n => MeasurableSpace.comap (K n) inferInstance))
    (F : Ω → A) (hF : Measurable[completedFactor (m₀ := m₀) μ
      (⨆ n, MeasurableSpace.comap (K n) inferInstance)] F)
    (ε : ℝ) (hε : 0 < ε) : ∃ n, randomConditionalEntropy μ F (K n) < ε := by
  have hm n : MeasurableSpace.comap (K n) inferInstance ≤ m₀ := (hK n).comap_le
  obtain ⟨n,G,hG,ht⟩ := finite_approx_completed_sequence μ _ hm hmono F hF
  have hF0 : Measurable F := hF.mono (completedFactor_le μ _) le_rfl
  have hG0 l : Measurable (G l) := (hG l).mono (hm _) le_rfl
  have hcond := randomConditionalEntropy_tendsto_self μ hG0 hF0 ht
  obtain ⟨l,hl⟩ := (hcond.eventually (gt_mem_nhds hε)).exists
  refine ⟨n l,lt_of_le_of_lt ?_ hl⟩
  exact randomConditionalEntropy_measurable_factor μ F (G l) (K (n l)) hF0 (hK _) (hG l)

lemma conditional_entropy_lower_of_completed [Nonempty B]
    {C : ℕ → Type*} [∀ n, Fintype (C n)] [∀ n, MeasurableSpace (C n)]
    [∀ n, MeasurableSingletonClass (C n)] (K : ∀ n, Ω → C n)
    (hK : ∀ n, Measurable (K n))
    (hmono : Monotone (fun n => MeasurableSpace.comap (K n) inferInstance))
    (F : Ω → A) (hF : Measurable F) (G : Ω → B)
    (hG : Measurable[completedFactor (m₀ := m₀) μ
      (⨆ n, MeasurableSpace.comap (K n) inferInstance)] G)
    (r : ℝ) (hr : ∀ n, r ≤ randomConditionalEntropy μ F (K n)) :
    r ≤ randomConditionalEntropy μ F G := by
  have hm n : MeasurableSpace.comap (K n) inferInstance ≤ m₀ := (hK n).comap_le
  obtain ⟨n,Gn,hGn,ht⟩ := finite_approx_completed_sequence μ _ hm hmono G hG
  have hG0 : Measurable G := hG.mono (completedFactor_le μ _) le_rfl
  have hGn0 l : Measurable (Gn l) := (hGn l).mono (hm _) le_rfl
  have hcond := randomConditionalEntropy_tendsto_condition μ F hF hGn0 hG0 ht
  apply ge_of_tendsto hcond
  exact Eventually.of_forall fun l => (hr (n l)).trans
    (randomConditionalEntropy_measurable_factor μ F (Gn l) (K (n l)) hF (hK _) (hGn l))
end

section
open MeasureTheory Filter
open scoped Topology BigOperators
variable {Ω A B : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    [Fintype A] [Fintype B]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    [MeasurableSpace B] [MeasurableSingletonClass B]

lemma integerWord_conditional_succ (F : ℤ → Ω → A) (hF : ∀ t, Measurable (F t))
    (G : Ω → B) (hG : Measurable G) (t : ℤ) (n : ℕ) :
    randomConditionalEntropy μ (integerWord F t (n+1)) G =
      randomConditionalEntropy μ (integerWord F t n) G +
      randomConditionalEntropy μ (F (t+n)) (fun x => (G x,integerWord F t n x)) := by
  have he : randomConditionalEntropy μ (integerWord F t (n+1)) G =
      randomConditionalEntropy μ (fun x => (integerWord F t n x,F (t+n) x)) G := by
    apply randomConditionalEntropy_mutual_factor μ _ _ G (measurable_integerWord F hF _ _)
      ((measurable_integerWord F hF _ _).prodMk (hF _)) hG
      (fun z => (fun i : Fin n => z i.castSucc,z (Fin.last n))) (fun z => Fin.snoc z.1 z.2)
    · rfl
    · funext x i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp only [Function.comp_apply,Fin.snoc_last,integerWord,Fin.val_last]
      · simp only [Function.comp_apply,Fin.snoc_castSucc,integerWord,Fin.val_castSucc]
  rw [he,randomConditionalEntropy_chain μ _ _ _ (hF _) (measurable_integerWord F hF _ _) hG]

lemma integerWord_conditional_le_sum (F : ℤ → Ω → A) (hF : ∀ t, Measurable (F t))
    (G : Ω → B) (hG : Measurable G) (t : ℤ) (n : ℕ) :
    randomConditionalEntropy μ (integerWord F t n) G ≤
      ∑ j ∈ Finset.range n, randomConditionalEntropy μ (F (t+j)) G := by
  induction n with
  | zero => simp [randomConditionalEntropy_fintype_one μ _ G (measurable_integerWord F hF _ _) hG]
  | succ n ih =>
    rw [integerWord_conditional_succ μ F hF G hG t n,Finset.sum_range_succ]
    exact add_le_add ih
      (randomConditionalEntropy_condition_comp μ (F (t+n))
        (fun x => (G x,integerWord F t n x)) (hF _)
        (hG.prodMk (measurable_integerWord F hF _ _)) Prod.fst)

lemma integerWord_conditional_lower (F : ℤ → Ω → A) (hF : ∀ t, Measurable (F t))
    (G : Ω → B) (hG : Measurable G) (t : ℤ) (n : ℕ) (r : ℝ)
    (hr : ∀ j < n, r ≤ randomConditionalEntropy μ (F (t+j))
      (fun x => (G x,integerWord F t j x))) :
    (n : ℝ) * r ≤ randomConditionalEntropy μ (integerWord F t n) G := by
  induction n with
  | zero => simpa only [Nat.cast_zero,zero_mul] using randomConditionalEntropy_nonneg μ _ _ (measurable_integerWord F hF t 0) hG
  | succ n ih =>
    rw [integerWord_conditional_succ μ F hF G hG t n,Nat.cast_add,Nat.cast_one,add_mul,one_mul]
    exact add_le_add (ih (fun j hj => hr j (by omega))) (hr n (by omega))
end

section
open MeasureTheory Filter
open scoped Topology BigOperators
variable {Ω A B : Type*} [m₀ : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    [Fintype A] [Fintype B] [Nonempty A] [Nonempty B]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    [MeasurableSpace B] [MeasurableSingletonClass B]

abbrev processPast (F : ℤ → Ω → A) (t : ℤ) : MeasurableSpace Ω :=
  ⨆ n : ℕ, MeasurableSpace.comap (integerWord F (t-n) n) inferInstance

abbrev processFull (F : ℤ → Ω → A) : MeasurableSpace Ω :=
  ⨆ n : ℕ, MeasurableSpace.comap (integerWord F (-(n:ℤ)) (2*n+1)) inferInstance

omit [Fintype A] [Nonempty A] [MeasurableSingletonClass A] in
lemma processPast_le (F : ℤ → Ω → A) (hF : ∀ t, Measurable (F t)) (t : ℤ) :
    processPast F t ≤ m₀ := iSup_le fun _n => (measurable_integerWord F hF _ _).comap_le

omit [Fintype A] [Nonempty A] [MeasurableSingletonClass A] in
lemma processFull_le (F : ℤ → Ω → A) (hF : ∀ t, Measurable (F t)) :
    processFull F ≤ m₀ := iSup_le fun _n => (measurable_integerWord F hF _ _).comap_le

omit [Nonempty A] in
include m₀ in
lemma processPast_zero_le_full (F : ℤ → Ω → A) : processPast F 0 ≤ processFull F := by
  let _ := m₀
  apply iSup_le
  intro n
  have hh := integerWord_subword_measurable F (-(n:ℤ)) 0 n (2*n+1) (by omega)
  simp only [Nat.cast_zero,add_zero] at hh
  have hh' : MeasurableSpace.comap (integerWord F (0-(n:ℤ)) n) inferInstance ≤
      MeasurableSpace.comap (integerWord F (-(n:ℤ)) (2*n+1)) inferInstance := by
    simpa only [zero_sub] using hh.comap_le
  change _ ≤ ⨆ m : ℕ, MeasurableSpace.comap (integerWord F (-(m:ℤ)) (2*m+1)) inferInstance
  exact le_iSup_of_le n hh'

variable (U : ℤ → Ω → Ω) (hU : ∀ s, MeasurePreserving (U s) μ μ)
    (F : ℤ → Ω → A) (hF : ∀ t, Measurable (F t))
    (htrans : ∀ t s x, F (t+s) x = F t (U s x))
    (G : ℤ → Ω → B) (hG : ∀ t, Measurable (G t))
    (hGtrans : ∀ t s x, G (t+s) x = G t (U s x))
    (htail : ∀ t s, Measurable[completedFactor (m₀ := m₀) μ (processPast F t)] (G s))

include htail hF in
lemma tail_word_conditional_lower (n : ℕ) (r : ℝ)
    (hr : ∀ (t : ℤ) (m : ℕ), r ≤ randomConditionalEntropy μ (F t) (integerWord F (t-m) m)) :
    (n : ℝ) * r ≤ randomConditionalEntropy μ (integerWord F 0 n) (integerWord G 0 n) := by
  have hg s : Measurable (G s) := (htail 0 s).mono (completedFactor_le μ _) le_rfl
  apply integerWord_conditional_lower μ F hF (integerWord G 0 n) (measurable_integerWord G hg _ _) 0 n r
  intro j hj
  apply conditional_entropy_lower_of_completed μ (fun m => integerWord F ((0+(j:ℤ))-m) m)
    (fun m => measurable_integerWord F hF _ _) (pastWord_comap_mono F _) (F (0+(j:ℤ))) (hF _) _ ?_ r (hr _)
  apply Measurable.prodMk
  · exact @Measurable.of_eval Ω (Fin n) (fun _ => B)
      (completedFactor (m₀ := m₀) μ (processPast F (0+(j:ℤ)))) _
      (integerWord G 0 n) (fun i => htail _ _)
  · have hh : MeasurableSpace.comap (integerWord F 0 j) inferInstance ≤ processPast F (0+(j:ℤ)) := by
      have hh := le_iSup (fun m : ℕ => MeasurableSpace.comap (integerWord F ((0+(j:ℤ))-m) m) inferInstance) j
      simpa only [processPast,zero_add,sub_self] using hh
    exact (comap_measurable _).mono (hh.trans (le_completedFactor μ (processPast_le F hF _))) le_rfl

omit [Nonempty B] in
include hU hF htrans hG hGtrans in
lemma tail_word_conditional_upper (M n : ℕ) (ε : ℝ)
    (he : randomConditionalEntropy μ (G 0) (integerWord F (-(M:ℤ)) (2*M+1)) ≤ ε) :
    randomConditionalEntropy μ (integerWord G 0 n) (integerWord F (-(M:ℤ)) (n+2*M)) ≤ n*ε := by
  apply (integerWord_conditional_le_sum μ G hG _ (measurable_integerWord F hF _ _) 0 n).trans
  calc
    _ ≤ ∑ j ∈ Finset.range n, ε := by
      apply Finset.sum_le_sum
      intro j hj
      have hj' := Finset.mem_range.mp hj
      have hs := integerWord_subword_measurable F (-(M:ℤ)) j (2*M+1) (n+2*M) (by omega)
      have hc := randomConditionalEntropy_measurable_factor μ (G (0+(j:ℤ)))
        (integerWord F (-(M:ℤ)+(j:ℤ)) (2*M+1)) (integerWord F (-(M:ℤ)) (n+2*M))
        (hG _) (measurable_integerWord F hF _ _) hs
      have hf : G (0+(j:ℤ)) = G 0 ∘ U j := funext fun x => hGtrans 0 j x
      rw [integerWord_translate U F htrans,hf,
        randomConditionalEntropy_measurePreserving μ μ (hU j) _ _ (hG _) (measurable_integerWord F hF _ _)] at hc
      simpa only [hf] using hc.trans he
    _ = n*ε := by simp

include hU hF htrans hG hGtrans htail in

theorem tail_process_entropy_zero :
    Tendsto (fun n : ℕ => randomEntropy μ (integerWord G 0 n) / n) atTop (𝓝 0) := by
  obtain ⟨h,hpos,hlower,hrate⟩ := stationary_entropy_rate μ U hU F hF htrans
  apply entropy_zero_of_tail_bounds (fun n => randomEntropy μ (integerWord F 0 n))
    (fun n => randomEntropy μ (integerWord G 0 n)) h hrate
    (fun n => randomEntropy_nonneg μ _ (measurable_integerWord G hG _ _))
  intro ε hε
  have hfull : Measurable[completedFactor (m₀ := m₀) μ (processFull F)] (G 0) :=
    (htail 0 0).mono (completedFactor_mono μ (processPast_zero_le_full F)) le_rfl
  obtain ⟨M,hM⟩ := exists_conditional_entropy_lt_of_completed μ
    (fun m => integerWord F (-(m:ℤ)) (2*m+1)) (fun m => measurable_integerWord F hF _ _)
    (windowWord_comap_mono F) (G 0) hfull ε hε
  refine ⟨2*M,fun n => ?_⟩
  have hlo := tail_word_conditional_lower μ F hF G htail n h hlower
  have hup := tail_word_conditional_upper μ U hU F hF htrans G hG hGtrans M n ε hM.le
  have he : randomEntropy μ (fun x => (integerWord G 0 n x,integerWord F 0 n x)) ≤
      randomEntropy μ (fun x => (integerWord F (-(M:ℤ)) (n+2*M) x,integerWord G 0 n x)) := by
    let e : (Fin (n+2*M) → A) × (Fin n → B) → (Fin n → B) × (Fin n → A) :=
      fun z => (z.2,fun i => z.1 ⟨M+i.val,by omega⟩)
    have heq : (fun x => (integerWord G 0 n x,integerWord F 0 n x)) =
        e ∘ (fun x => (integerWord F (-(M:ℤ)) (n+2*M) x,integerWord G 0 n x)) := by
      funext x
      apply Prod.ext
      · rfl
      · funext i
        dsimp [e,integerWord]
        congr 1
        ring
    rw [heq]
    exact randomEntropy_comp_le _ ((measurable_integerWord F hF _ _).prodMk (measurable_integerWord G hG _ _)) e
  rw [randomEntropy_pair μ _ _ (measurable_integerWord F hF _ _) (measurable_integerWord G hG _ _),
    randomEntropy_pair μ _ _ (measurable_integerWord G hG _ _) (measurable_integerWord F hF _ _),
    integerWord_entropy_translate μ U hU F hF htrans] at he
  linarith
end

section
open Filter
open scoped Topology
variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
  [CompleteSpace H]
local instance complete_iInf (K : ℕ → Submodule 𝕜 H) [∀ n, CompleteSpace (K n)] :
    CompleteSpace ↥(⨅ n, K n) := by
  have h : IsClosed (↑(⨅ n, K n) : Set H) := by
    simp only [Submodule.coe_iInf]
    exact isClosed_iInter fun n => (completeSpace_coe_iff_isComplete.mp (inferInstance : CompleteSpace (K n))).isClosed
  exact h.completeSpace_coe

lemma antitone_projection_tendsto (K : ℕ → Submodule 𝕜 H)
    [∀ n, CompleteSpace (K n)] (hK : Antitone K) (x : H) :
    Tendsto (fun n => (K n).starProjection x) atTop
      (𝓝 ((⨅ n, K n).starProjection x)) := by
  have he : (⨆ n, (K n)ᗮ)ᗮ = ⨅ n, K n := by
    apply le_antisymm
    · apply le_iInf
      intro n
      simpa only [Submodule.orthogonal_orthogonal] using
        (Submodule.orthogonal_le (le_iSup (fun n => (K n)ᗮ) n))
    · intro x hx y hy
      have hy' : y ∈ (⨅ n, K n)ᗮ :=
        (iSup_le (fun n => Submodule.orthogonal_le (iInf_le K n))) hy
      exact inner_eq_zero_symm.mp (hy' x hx)
  have he' : (⨆ n, (K n)ᗮ).topologicalClosure = (⨅ n, K n)ᗮ := by
    rw [←Submodule.orthogonal_orthogonal_eq_closure,he]
  have ht := Submodule.starProjection_tendsto_closure_iSup
    (fun n => (K n)ᗮ) (fun a b h => Submodule.orthogonal_le (hK h)) x
  simp only [he'] at ht
  have hh := (tendsto_const_nhds (x := x) (f := atTop)).sub ht
  simpa only [Submodule.starProjection_orthogonal_val,sub_sub_cancel] using hh
end

section
open MeasureTheory Filter
open scoped ENNReal Topology
variable {Ω : Type*} [m₀ : MeasurableSpace Ω] (μ : Measure Ω)

lemma lpMeas_completed_eq (m : MeasurableSpace Ω) (hm : m ≤ m₀) :
    @lpMeas Ω ℝ ℝ _ _ _ (completedFactor (m₀ := m₀) μ m) m₀ 2 μ = @lpMeas Ω ℝ ℝ _ _ _ m m₀ 2 μ := by
  ext f
  simp only [mem_lpMeas_iff_aestronglyMeasurable]
  constructor
  · intro h
    have hm' : Measurable[completedFactor (m₀ := m₀) μ m] (h.mk f) := h.stronglyMeasurable_mk.measurable
    exact (aeStrong_of_measurable_completed (m₀ := m₀) μ m hm').congr h.ae_eq_mk.symm
  · exact fun h => h.mono (le_completedFactor (m₀ := m₀) μ hm)

lemma lpMeas_completed_iInf (m : ℕ → MeasurableSpace Ω) (hm : ∀ n, m n ≤ m₀) :
    @lpMeas Ω ℝ ℝ _ _ _ (⨅ n, completedFactor (m₀ := m₀) μ (m n)) m₀ 2 μ = ⨅ n, @lpMeas Ω ℝ ℝ _ _ _ (m n) m₀ 2 μ := by
  ext f
  simp only [Submodule.mem_iInf,mem_lpMeas_iff_aestronglyMeasurable]
  constructor
  · intro h n
    have h' := h.mono (iInf_le (fun n => completedFactor (m₀ := m₀) μ (m n)) n)
    have hh : f ∈ @lpMeas Ω ℝ ℝ _ _ _ (completedFactor (m₀ := m₀) μ (m n)) m₀ 2 μ := by
      exact mem_lpMeas_iff_aestronglyMeasurable.mpr h'
    rw [lpMeas_completed_eq μ (m n) (hm n)] at hh
    exact mem_lpMeas_iff_aestronglyMeasurable.mp hh
  · intro h
    exact (completedFactor_iInf_measurable μ m (Lp.stronglyMeasurable f).measurable h).stronglyMeasurable.aestronglyMeasurable

lemma reverse_conditional_L2 (m : ℕ → MeasurableSpace Ω) (hm : ∀ n, m n ≤ m₀)
    (hanti : Antitone m) (f : Lp ℝ 2 μ) :
    Tendsto (fun n => (condExpL2 ℝ ℝ (hm n) f : Lp ℝ 2 μ)) atTop
      (𝓝 (condExpL2 ℝ ℝ
        (show (⨅ n, completedFactor (m₀ := m₀) μ (m n)) ≤ m₀ from
          (iInf_le _ 0).trans (completedFactor_le μ (m 0))) f : Lp ℝ 2 μ)) := by
  let K : ℕ → Submodule ℝ (Lp ℝ 2 μ) := fun n => @lpMeas Ω ℝ ℝ _ _ _ (m n) m₀ 2 μ
  let (n : ℕ) : Fact (m n ≤ m₀) := ⟨hm n⟩
  have hK : Antitone K := by
    intro a b hab f hf
    exact mem_lpMeas_iff_aestronglyMeasurable.mpr
      ((mem_lpMeas_iff_aestronglyMeasurable.mp hf).mono (hanti hab))
  have h := antitone_projection_tendsto K hK f
  have ht : Fact ((⨅ n, completedFactor (m₀ := m₀) μ (m n)) ≤ m₀) :=
    ⟨(iInf_le _ 0).trans (completedFactor_le μ (m 0))⟩
  let := ht
  simpa only [K, ←lpMeas_completed_iInf μ m hm, Submodule.starProjection_apply,condExpL2] using h
end

section
open MeasureTheory Filter
open scoped Topology RealInnerProductSpace
variable {Ω : Type*} [m₀ : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in

lemma reverse_tail_pairing (m : ℕ → MeasurableSpace Ω) (hm : ∀ n, m n ≤ m₀)
    (hanti : Antitone m) (f : Lp ℝ 2 μ) (g : ℕ → Lp ℝ 2 μ)
    (hg : ∀ n, AEStronglyMeasurable[m n] (g n) μ)
    (hb : ∀ n, ‖g n‖ ≤ 1) :
    Tendsto (fun n => ⟪f - (condExpL2 ℝ ℝ
      (show (⨅ n, completedFactor (m₀ := m₀) μ (m n)) ≤ m₀ from
        (iInf_le _ 0).trans (completedFactor_le μ (m 0))) f : Lp ℝ 2 μ), g n⟫)
      atTop (𝓝 0) := by
  let ft : Lp ℝ 2 μ := condExpL2 ℝ ℝ
    (show (⨅ n, completedFactor (m₀ := m₀) μ (m n)) ≤ m₀ from
      (iInf_le _ 0).trans (completedFactor_le μ (m 0))) f
  have he n : ⟪f-ft,g n⟫ = ⟪(condExpL2 ℝ ℝ (hm n) f : Lp ℝ 2 μ)-ft,g n⟫ := by
    simp only [inner_sub_left,inner_condExpL2_eq_inner_fun (hm n) f (g n) (hg n)]
  have hbound n : |⟪f-ft,g n⟫| ≤ ‖(condExpL2 ℝ ℝ (hm n) f : Lp ℝ 2 μ)-ft‖ := by
    rw [he]
    exact (abs_real_inner_le_norm _ _).trans (by nlinarith [norm_nonneg ((condExpL2 ℝ ℝ (hm n) f : Lp ℝ 2 μ)-ft),hb n])
  have ht : Tendsto (fun n => ‖(condExpL2 ℝ ℝ (hm n) f : Lp ℝ 2 μ)-ft‖) atTop (𝓝 0) := by
    simpa only [ft,sub_self,norm_zero] using ((reverse_conditional_L2 μ m hm hanti f).sub (tendsto_const_nhds (x := ft))).norm
  exact squeeze_zero_norm (fun n => by simpa only [Real.norm_eq_abs] using hbound n) ht

lemma reverse_tail_pairing_of_bound (m : ℕ → MeasurableSpace Ω) (hm : ∀ n, m n ≤ m₀)
    (hanti : Antitone m) (f : Lp ℝ 2 μ) (g : ℕ → Lp ℝ 2 μ)
    (hg : ∀ n, AEStronglyMeasurable[m n] (g n) μ)
    (hb : ∀ n, ∀ᵐ x ∂μ, |g n x| ≤ 1) :
    Tendsto (fun n => ⟪f - (condExpL2 ℝ ℝ
      (show (⨅ n, completedFactor (m₀ := m₀) μ (m n)) ≤ m₀ from
        (iInf_le _ 0).trans (completedFactor_le μ (m 0))) f : Lp ℝ 2 μ), g n⟫)
      atTop (𝓝 0) := by
  apply reverse_tail_pairing μ m hm hanti f g hg
  intro n
  simpa only [measureUnivNNReal,measure_univ,ENNReal.toNNReal_one,NNReal.coe_one,Real.one_rpow,one_mul]
    using Lp.norm_le_of_ae_bound (f := g n) (by norm_num : (0 : ℝ) ≤ 1) (hb n)
end

section
open MeasureTheory Filter
variable {Ω A : Type*} [m₀ : MeasurableSpace Ω] (μ : Measure Ω)
    [MeasurableSpace A]

omit m₀ in
lemma processPast_eq_generators (F : ℤ → Ω → A) (t : ℤ) :
    processPast F t = ⨆ q : {q : ℤ // q < t}, MeasurableSpace.comap (F q) inferInstance := by
  change (⨆ n : ℕ, MeasurableSpace.comap (fun x (i : Fin n) => F (t-(n:ℤ)+(i.val:ℤ)) x) inferInstance) = _
  simp_rw [MeasurableSpace.comap_process_pi]
  apply le_antisymm
  · apply iSup_le
    intro n
    apply iSup_le
    intro i
    apply le_iSup_of_le ⟨t-(n:ℤ)+(i.val:ℤ),by omega⟩
    exact le_rfl
  · apply iSup_le
    intro q
    let n := (t-q.val).toNat
    have hn : (n:ℤ) = t-q.val := by dsimp [n]; omega
    have hnpos : 0 < n := by have := q.property; omega
    apply le_iSup_of_le n
    apply le_iSup_of_le (⟨0,hnpos⟩ : Fin n)
    simp only [Nat.cast_zero,add_zero,hn,sub_sub_cancel]
    exact le_rfl

omit m₀ in
lemma processPast_mono (F : ℤ → Ω → A) : Monotone (processPast F) := by
  intro s t h
  rw [processPast_eq_generators,processPast_eq_generators]
  apply iSup_le
  intro q
  exact le_iSup_of_le ⟨q.val,q.property.trans_le h⟩ le_rfl

lemma completedFactor_comap {f : Ω → Ω} (hf : MeasurePreserving f μ μ)
    {m n : MeasurableSpace Ω} (h : MeasurableSpace.comap f m ≤ n) :
    MeasurableSpace.comap f (completedFactor (m₀ := m₀) μ m) ≤ completedFactor (m₀ := m₀) μ n := by
  rintro s ⟨r,hr,rfl⟩
  obtain ⟨hr,v,hv,he⟩ := hr
  change MeasurableSet[m₀] (f ⁻¹' r) ∧ ∃ v, MeasurableSet[n] v ∧ ∀ᵐ x ∂μ, x ∈ f ⁻¹' r ↔ x ∈ v
  let : MeasurableSpace Ω := m₀
  have hfm : @Measurable Ω Ω m₀ m₀ f := hf.measurable
  have hea : ∀ᵐ x ∂μ, f x ∈ r ↔ f x ∈ v :=
    hf.quasiMeasurePreserving.ae he
  exact ⟨hfm hr,f ⁻¹' v,h _ ⟨v,hv,rfl⟩,hea⟩

omit m₀ in
lemma processPast_comap (U : ℤ → Ω → Ω) (F : ℤ → Ω → A)
    (htrans : ∀ t s x, F (t+s) x = F t (U s x)) (t s : ℤ) :
    MeasurableSpace.comap (U s) (processPast F t) ≤ processPast F (t+s) := by
  rw [processPast_eq_generators,MeasurableSpace.comap_iSup,processPast_eq_generators]
  apply iSup_le
  intro q
  rw [MeasurableSpace.comap_comp]
  have he : F (q.val+s) = F q ∘ U s := funext fun x => htrans q s x
  rw [←he]
  exact le_iSup_of_le ⟨q.val+s,by have := q.property; omega⟩ le_rfl

abbrev processTail (F : ℤ → Ω → A) : MeasurableSpace Ω :=
  ⨅ n : ℕ, completedFactor (m₀ := m₀) μ (processPast F (-(n:ℤ)))

lemma processTail_le (F : ℤ → Ω → A) : processTail μ F ≤ m₀ :=
  (iInf_le _ 0).trans (completedFactor_le μ _)

lemma processTail_le_past (F : ℤ → Ω → A) (t : ℤ) :
    processTail μ F ≤ completedFactor (m₀ := m₀) μ (processPast F t) := by
  have h : -(((-t).toNat : ℕ) : ℤ) ≤ t := by omega
  exact (iInf_le _ ((-t).toNat)).trans (completedFactor_mono μ (processPast_mono F h))

lemma processTail_comap (U : ℤ → Ω → Ω) (hU : ∀ s, MeasurePreserving (U s) μ μ)
    (F : ℤ → Ω → A) (htrans : ∀ t s x, F (t+s) x = F t (U s x)) (s : ℤ) :
    MeasurableSpace.comap (U s) (processTail μ F) ≤ processTail μ F := by
  apply le_iInf
  intro n
  have h := MeasurableSpace.comap_mono (g := U s) (processTail_le_past μ F (-(n:ℤ)-s))
  apply h.trans
  have ht := completedFactor_comap μ (hU s) (processPast_comap U F htrans (-(n:ℤ)-s) s)
  simpa only [sub_add_cancel] using ht

lemma measurable_tail_translate {B : Type*} [MeasurableSpace B]
    (U : ℤ → Ω → Ω) (hU : ∀ s, MeasurePreserving (U s) μ μ)
    (F : ℤ → Ω → A) (htrans : ∀ t s x, F (t+s) x = F t (U s x))
    (g : Ω → B) (hg : Measurable[processTail μ F] g) (s t : ℤ) :
    Measurable[completedFactor (m₀ := m₀) μ (processPast F t)] (g ∘ U s) := by
  have hu : @Measurable Ω Ω (processTail μ F) (processTail μ F) (U s) :=
    measurable_iff_comap_le.mpr (processTail_comap μ U hU F htrans s)
  exact (hg.comp hu).mono (processTail_le_past μ F t) le_rfl
end

section
open MeasureTheory Filter
open scoped Topology ENNReal NNReal

lemma antitone_starProjection_tendsto {𝕜 H : Type*} [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (V : ℕ → Submodule 𝕜 H) [∀ n, (V n).HasOrthogonalProjection]
    [(⨅ n, V n).HasOrthogonalProjection]
    (hV : Antitone V) (x : H) :
    Tendsto (fun n => (V n).starProjection x) atTop
      (𝓝 ((⨅ n, V n).starProjection x)) := by
  have hmono : Monotone (fun n => (V n)ᗮ) := fun _ _ h => Submodule.orthogonal_le (hV h)
  have he : (⨆ n, (V n)ᗮ).topologicalClosure = (⨅ n, V n)ᗮ := by
    rw [← Submodule.orthogonal_orthogonal_eq_closure, ← Submodule.iInf_orthogonal]
    simp only [Submodule.orthogonal_orthogonal]
  have ht := Submodule.starProjection_tendsto_closure_iSup (fun n => (V n)ᗮ) hmono x
  simp only [he] at ht
  have hh := (tendsto_const_nhds (x := x) (f := atTop)).sub ht
  simpa only [Submodule.starProjection_orthogonal, sub_apply,
    ContinuousLinearMap.id_apply, sub_sub_cancel] using hh

variable {Ω : Type*} {m₀ : MeasurableSpace Ω} {μ : Measure Ω}

lemma lpMeas_iInf_antitone (m : ℕ → MeasurableSpace Ω) (_hm : ∀ n, m n ≤ m₀)
    (hanti : Antitone m) :
    lpMeas ℝ ℝ (⨅ n, m n) 2 μ = ⨅ n, lpMeas ℝ ℝ (m n) 2 μ := by
  apply le_antisymm
  · apply le_iInf
    intro n f hf
    exact mem_lpMeas_iff_aestronglyMeasurable.mpr
      ((mem_lpMeas_iff_aestronglyMeasurable.mp hf).mono (iInf_le _ n))
  · intro f hf
    have hf' (n : ℕ) : AEStronglyMeasurable[m n] f μ :=
      mem_lpMeas_iff_aestronglyMeasurable.mp (((Submodule.mem_iInf _).mp hf) n)
    let g : ℕ → Ω → ℝ := fun n => (hf' n).mk f
    let F : Ω → ℝ := fun ω => limUnder atTop (fun n => g n ω)
    have hg (n : ℕ) : StronglyMeasurable[m n] (g n) := (hf' n).stronglyMeasurable_mk
    have hF (j : ℕ) : StronglyMeasurable[m j] F := by
      have hg' (n : ℕ) : StronglyMeasurable[m j] (g (n+j)) :=
        (hg (n+j)).mono (hanti (Nat.le_add_left j n))
      let : MeasurableSpace Ω := m j
      have hh := StronglyMeasurable.limUnder (l := atTop) hg'
      convert hh using 1
      funext ω
      dsimp [F]
      unfold limUnder
      rw [show (fun n => g (n+j) ω) = (fun n => g n ω) ∘ (fun n => n+j) from rfl,
        ← Filter.map_map, map_add_atTop_eq_nat]
    have hmeas : Measurable[⨅ n, m n] F := by
      intro S hS
      exact MeasurableSpace.measurableSet_iInf.mpr (fun j => (hF j).measurable hS)
    apply mem_lpMeas_iff_aestronglyMeasurable.mpr
    refine hmeas.stronglyMeasurable.aestronglyMeasurable.congr ?_
    filter_upwards [ae_all_iff.mpr (fun n => (hf' n).ae_eq_mk)] with ω hω
    have he : (fun n => g n ω) = fun _ => f ω := funext (fun n => (hω n).symm)
    change limUnder atTop (fun n => g n ω) = f ω
    rw [he]
    exact tendsto_const_nhds.limUnder_eq

lemma condExpL2_antitone_tendsto (m : ℕ → MeasurableSpace Ω) (hm : ∀ n, m n ≤ m₀)
    (hanti : Antitone m) (f : Lp ℝ 2 μ) :
    Tendsto (fun n => (condExpL2 ℝ ℝ (hm n) f : Lp ℝ 2 μ)) atTop
      (𝓝 (condExpL2 ℝ ℝ ((iInf_le m 0).trans (hm 0)) f : Lp ℝ 2 μ)) := by
  let V (n : ℕ) := lpMeas ℝ ℝ (m n) 2 μ
  have inst (n : ℕ) : (V n).HasOrthogonalProjection := by
    let : Fact (m n ≤ m₀) := ⟨hm n⟩
    dsimp [V]
    infer_instance
  have hme : (⨅ n, V n) = lpMeas ℝ ℝ (⨅ n, m n) 2 μ :=
    (lpMeas_iInf_antitone m hm hanti).symm
  have inst' : (⨅ n, V n).HasOrthogonalProjection := by
    rw [hme]
    let : Fact ((⨅ n, m n) ≤ m₀) := ⟨(iInf_le m 0).trans (hm 0)⟩
    infer_instance
  let := inst
  let := inst'
  have hV : Antitone V := by
    intro i j hij f hf
    exact mem_lpMeas_iff_aestronglyMeasurable.mpr
      ((mem_lpMeas_iff_aestronglyMeasurable.mp hf).mono (hanti hij))
  have h := antitone_starProjection_tendsto V hV f
  simp only [hme] at h
  exact h

lemma integral_norm_L2_le [IsProbabilityMeasure μ] (f : Lp ℝ 2 μ) :
    (∫ ω, ‖f ω‖ ∂μ) ≤ ‖f‖ := by
  rw [← lpNorm_one_eq_integral_norm (Lp.aestronglyMeasurable f), lpNorm, Lp.norm_def]
  exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top f)
    (eLpNorm_le_eLpNorm_of_exponent_le (by norm_num : (1 : ℝ≥0∞) ≤ 2))

lemma condExp_antitone_L1_tendsto [IsProbabilityMeasure μ]
    (m : ℕ → MeasurableSpace Ω) (hm : ∀ n, m n ≤ m₀)
    (hanti : Antitone m) {f : Ω → ℝ} (hf : MemLp f 2 μ) :
    Tendsto (fun n => ∫ ω, ‖μ[f | m n] ω - μ[f | ⨅ i, m i] ω‖ ∂μ) atTop (𝓝 0) := by
  let ht : (⨅ i, m i) ≤ m₀ := (iInf_le m 0).trans (hm 0)
  let c (n : ℕ) : Lp ℝ 2 μ := condExpL2 ℝ ℝ (hm n) hf.toLp
  let d : Lp ℝ 2 μ := condExpL2 ℝ ℝ ht hf.toLp
  have hc := condExpL2_antitone_tendsto m hm hanti hf.toLp
  change Tendsto c atTop (𝓝 d) at hc
  have hc' : Tendsto (fun n => ‖c n - d‖) atTop (𝓝 0) := by
    simpa using (hc.sub (tendsto_const_nhds (x := d) (f := atTop))).norm
  apply squeeze_zero (fun _ => integral_nonneg (fun _ => norm_nonneg _)) _ hc'
  intro n
  calc
    (∫ ω, ‖μ[f | m n] ω - μ[f | ⨅ i, m i] ω‖ ∂μ) = ∫ ω, ‖(c n - d) ω‖ ∂μ := by
      apply integral_congr_ae
      filter_upwards [hf.condExpL2_ae_eq_condExp (𝕜 := ℝ) (hm n), hf.condExpL2_ae_eq_condExp (𝕜 := ℝ) ht,
        Lp.coeFn_sub (c n) d] with ω hn hd he
      rw [he]
      change c n ω = μ[f | m n] ω at hn
      change d ω = μ[f | ⨅ i, m i] ω at hd
      simp only [Pi.sub_apply, hn, hd]
    _ ≤ ‖c n - d‖ := integral_norm_L2_le _

end

open MeasureTheory Filter
open scoped Topology
variable {Ω : Type*} [m₀ : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

def clippedConditional (m : MeasurableSpace Ω) (f : Ω → ℝ) : Ω → ℝ :=
  fun x => max 0 (min 1 (μ[f | m] x))

omit [IsProbabilityMeasure μ] in
lemma clippedConditional_bounds (m : MeasurableSpace Ω) (f : Ω → ℝ) (x : Ω) :
    clippedConditional (m₀ := m₀) μ m f x ∈ Set.Icc (0:ℝ) 1 := by
  exact ⟨le_max_left _ _,max_le (by norm_num) (min_le_left _ _)⟩

omit [IsProbabilityMeasure μ] in
lemma clippedConditional_measurable (m : MeasurableSpace Ω) (f : Ω → ℝ) :
    Measurable[m] (clippedConditional (m₀ := m₀) μ m f) := by
  exact measurable_const.max (measurable_const.min stronglyMeasurable_condExp.measurable)

omit [IsProbabilityMeasure μ] in
lemma clippedConditional_ae (m : MeasurableSpace Ω) (f : Ω → ℝ)
    (hf : ∀ᵐ x ∂μ, f x ∈ Set.Icc (0:ℝ) 1) :
    clippedConditional (m₀ := m₀) μ m f =ᵐ[μ] μ[f | m] := by
  let : MeasurableSpace Ω := m₀
  have hn := condExp_nonneg (m := m) (hf.mono fun _ h => h.1)
  have hb := condExp_le_nonneg_const (m := m) (show (0:ℝ) ≤ 1 by norm_num) (hf.mono fun _ h => h.2)
  filter_upwards [hn,hb] with x hx hy
  change (0:ℝ) ≤ μ[f | m] x at hx
  simp only [clippedConditional,min_eq_right hy,max_eq_right hx]

lemma clippedConditional_mean (m : MeasurableSpace Ω) (hm : m ≤ m₀) (f : Ω → ℝ)
    (hf : ∀ᵐ x ∂μ, f x ∈ Set.Icc (0:ℝ) 1) :
    (∫ x, clippedConditional (m₀ := m₀) μ m f x ∂μ) = ∫ x, f x ∂μ := by
  let : MeasurableSpace Ω := m₀
  rw [integral_congr_ae (clippedConditional_ae (m₀ := m₀) μ m f hf),integral_condExp hm]

lemma exists_simple_interval_approx (m : MeasurableSpace Ω) (hm : m ≤ m₀)
    (g : Ω → ℝ) (hg : Measurable[m] g) (hb : ∀ x, g x ∈ Set.Icc (0:ℝ) 1)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ s : @SimpleFunc Ω m ℝ, (∀ x, s x ∈ Set.Icc (0:ℝ) 1) ∧
      (∫ x, |s x-g x| ∂μ) < ε := by
  let s : ℕ → @SimpleFunc Ω m ℝ := fun n =>
    SimpleFunc.approxOn g hg (Set.Icc 0 1) 0 (by norm_num) n
  have hs n x : s n x ∈ Set.Icc (0:ℝ) 1 := SimpleFunc.approxOn_mem hg (by norm_num) n x
  have hsm n : Measurable[m₀] (s n) := (s n).measurable.mono hm le_rfl
  have hgm : Measurable[m₀] g := hg.mono hm le_rfl
  have hlim x : Tendsto (fun n => |s n x-g x|) atTop (𝓝 (0:ℝ)) := by
    have ht : Tendsto (fun n => s n x) atTop (𝓝 (g x)) :=
      SimpleFunc.tendsto_approxOn hg (by norm_num) (subset_closure (hb x))
    simpa only [sub_self,abs_zero] using (ht.sub_const (g x)).abs
  have hbound n : ∀ᵐ x ∂μ, ‖|s n x-g x|‖ ≤ (1:ℝ) := by
    filter_upwards with x
    rw [Real.norm_eq_abs,abs_abs]
    exact abs_le.mpr ⟨by have h1 := (hs n x).1; have h2 := (hb x).2; linarith,
      by have h1 := (hs n x).2; have h2 := (hb x).1; linarith⟩
  let : MeasurableSpace Ω := m₀
  have ht : Tendsto (fun n => ∫ x, |s n x-g x| ∂μ) atTop (𝓝 (0:ℝ)) := by
    simpa only [integral_zero,Pi.sub_apply] using tendsto_integral_of_dominated_convergence (μ := μ)
      (fun _ => (1:ℝ)) (fun n => ((hsm n).sub hgm).abs.aestronglyMeasurable)
      (integrable_const _) hbound (Eventually.of_forall hlim)
  obtain ⟨n,hn⟩ := (ht.eventually (gt_mem_nhds hε)).exists
  exact ⟨s n,hs n,hn⟩

lemma reverse_condExp_completed_L1 (m : ℕ → MeasurableSpace Ω) (hm : ∀ n, m n ≤ m₀)
    (hanti : Antitone m) {f : Ω → ℝ} (hf : MemLp f 2 μ) :
    Tendsto (fun n => ∫ x, ‖μ[f | m n] x - μ[f | ⨅ j, completedFactor (m₀ := m₀) μ (m j)] x‖ ∂μ)
      atTop (𝓝 (0:ℝ)) := by
  let ht : (⨅ j, completedFactor (m₀ := m₀) μ (m j)) ≤ m₀ :=
    (iInf_le _ 0).trans (completedFactor_le μ _)
  let c n : Lp ℝ 2 μ := condExpL2 ℝ ℝ (hm n) hf.toLp
  let d : Lp ℝ 2 μ := condExpL2 ℝ ℝ ht hf.toLp
  have hc := reverse_conditional_L2 μ m hm hanti hf.toLp
  change Tendsto c atTop (𝓝 d) at hc
  have hnorm : Tendsto (fun n => ‖c n-d‖) atTop (𝓝 (0:ℝ)) := by
    simpa only [sub_self,norm_zero] using (hc.sub (tendsto_const_nhds (x := d))).norm
  apply squeeze_zero (fun _ => integral_nonneg fun _ => norm_nonneg _) _ hnorm
  intro n
  have he : (∫ x, ‖μ[f | m n] x-μ[f | ⨅ j, completedFactor (m₀ := m₀) μ (m j)] x‖ ∂μ) =
      ∫ x, ‖(c n-d) x‖ ∂μ := by
    apply integral_congr_ae
    filter_upwards [hf.condExpL2_ae_eq_condExp (𝕜 := ℝ) (hm n),
      hf.condExpL2_ae_eq_condExp (𝕜 := ℝ) ht,Lp.coeFn_sub (c n) d] with x hx hy hz
    rw [hz]
    change c n x = _ at hx
    change d x = _ at hy
    simp only [Pi.sub_apply,hx,hy]
  rw [he]
  exact integral_norm_L2_le _

end Rokhlin

end

end OAI
