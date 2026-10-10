import OAI.Combinatorics.CycleDecomposition.EdgeSplitting

namespace OAI

universe cycleUniverse1 cycleUniverse2

section
open Filter Asymptotics Real
open scoped Topology
noncomputable section
open MeasureTheory ProbabilityTheory Finset
noncomputable section
namespace ErdosGallai.Representatives
noncomputable section
open Finset
variable {I : Type cycleUniverse1} {V : Type cycleUniverse2} [DecidableEq I] [DecidableEq V] [Nonempty V]

lemma choose_with_mates (A : Finset I) (mate : I → I)
    (hmate : Function.Involutive mate) (hfix : ∀ i, mate i ≠ i)
    (N : I → Finset V) (k : ℕ)
    (hroom : ∀ i ∈ A, A.card ≤ ((N i).card - 1) * k) :
    ∃ f : I → V, (∀ i ∈ A, f i ∈ N i) ∧
      (∀ i ∈ A, mate i ∈ A → f i ≠ f (mate i)) ∧
      (∀ v, (A.filter (fun i => f i = v)).card ≤ k) := by
  induction A using Finset.induction_on with
  | empty => exact ⟨fun _ => Classical.choice inferInstance, by simp⟩
  | @insert i A hi ih =>
    obtain ⟨f,hf,hsep,hcap⟩ := ih (by
      intro j hj
      exact (Finset.card_le_card (Finset.subset_insert i A)).trans (hroom j (by simp [hj])))
    have hlt : A.card < ((N i).erase (f (mate i))).card * k := by
      have h := hroom i (by simp)
      have hcard := Finset.pred_card_le_card_erase (s := N i) (a := f (mate i))
      have hmul := Nat.mul_le_mul_right k hcard
      rw [Finset.card_insert_of_notMem hi] at h
      omega
    obtain ⟨v,hv,hload⟩ := Finset.exists_card_fiber_lt_of_card_lt_mul (f := f) hlt
    have hvN := (Finset.mem_erase.mp hv).2
    have hvne := (Finset.mem_erase.mp hv).1
    let g := Function.update f i v
    have gi : g i = v := by simp [g]
    have gold : ∀ j, j ≠ i → g j = f j := by
      intro j hj
      simp [g, hj]
    refine ⟨g, ?_, ?_, ?_⟩
    · intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · simpa only [gi] using hvN
      · rw [gold j (ne_of_mem_of_not_mem hj hi)]
        exact hf j hj
    · intro j hj hmj
      by_cases hji : j = i
      · subst j
        rw [gi, gold (mate i) (hfix i)]
        exact hvne
      · rw [gold j hji]
        by_cases hmi : mate j = i
        · rw [hmi, gi]
          have hjm : j = mate i := by rw [← hmi, hmate]
          simpa [hjm] using hvne.symm
        · rw [gold (mate j) hmi]
          exact hsep j (Finset.mem_of_mem_insert_of_ne hj hji)
            (Finset.mem_of_mem_insert_of_ne hmj hmi)
    · intro w
      have hold : A.filter (fun j => g j = w) = A.filter (fun j => f j = w) := by
        apply Finset.filter_congr
        intro j hj
        rw [gold j (ne_of_mem_of_not_mem hj hi)]
      rw [Finset.filter_insert, hold]
      by_cases hvw : v = w
      · simp only [gi, hvw, ite_eq_left]
        rw [Finset.card_insert_of_notMem (fun h => hi (Finset.mem_filter.mp h).1)]
        simpa only [hvw] using Nat.succ_le_of_lt hload
      · simp only [gi, hvw, ite_false]
        exact hcap w

theorem two_distinct_representatives (S : Finset I) (N : I → Finset V) (k : ℕ)
    (hroom : ∀ i ∈ S, 2*S.card ≤ ((N i).card-1)*k) :
    ∃ f : I × Fin 2 → V,
      (∀ i ∈ S, ∀ t, f (i,t) ∈ N i) ∧
      (∀ i ∈ S, f (i,0) ≠ f (i,1)) ∧
      (∀ v, ((S ×ˢ Finset.univ).filter (fun i => f i = v)).card ≤ k) := by
  let mate : I × Fin 2 → I × Fin 2 := fun i => (i.1, 1-i.2)
  have hm : Function.Involutive mate := by
    rintro ⟨i,t⟩
    fin_cases t <;> rfl
  have hfix : ∀ i, mate i ≠ i := by
    rintro ⟨i,t⟩
    fin_cases t <;> (intro h; have hh := congrArg Prod.snd h; norm_num [mate] at hh)
  obtain ⟨f,hf,hsep,hcap⟩ := choose_with_mates (S ×ˢ Finset.univ) mate hm hfix
    (fun i => N i.1) k (by
      intro i hi
      simpa [Finset.card_product, mul_comm] using hroom i.1 (Finset.mem_product.mp hi).1)
  refine ⟨f, ?_, ?_, hcap⟩
  · intro i hi t
    exact hf (i,t) (by simp [hi])
  · intro i hi
    exact hsep (i,0) (by simp [hi]) (by simp [mate, hi])

theorem reservoir_representatives (S : Finset I) (N : I → Finset V)
    (r d : ℝ) (hr : (S.card : ℝ) ≤ r) (hd : 4 ≤ d)
    (hN : ∀ i ∈ S, d/2 ≤ ((N i).card : ℝ)) :
    ∃ f : I × Fin 2 → V,
      (∀ i ∈ S, ∀ t, f (i,t) ∈ N i) ∧
      (∀ i ∈ S, f (i,0) ≠ f (i,1)) ∧
      (∀ v, ((S ×ˢ Finset.univ).filter (fun i => f i = v)).card ≤ ⌈8*r/d⌉₊) := by
  apply two_distinct_representatives
  intro i hi
  have hd0 : 0 < d := by linarith
  have hr0 : 0 ≤ r := le_trans (Nat.cast_nonneg _) hr
  have hNi := hN i hi
  have hNi1 : 1 ≤ (N i).card := by exact_mod_cast (by linarith : (1 : ℝ) ≤ (N i).card)
  have hn : d/4 ≤ (((N i).card - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub hNi1]
    push_cast
    linarith
  have hk : 8*r/d ≤ (⌈8*r/d⌉₊ : ℝ) := Nat.le_ceil _
  have hk0 : 0 ≤ (⌈8*r/d⌉₊ : ℝ) := Nat.cast_nonneg _
  have hprod : 2*(S.card : ℝ) ≤ (((N i).card - 1 : ℕ) : ℝ)*(⌈8*r/d⌉₊ : ℝ) := by
    calc
      _ ≤ 2*r := by linarith
      _ = (d/4)*(8*r/d) := by field_simp; ring
      _ ≤ (d/4)*(⌈8*r/d⌉₊ : ℝ) := mul_le_mul_of_nonneg_left hk (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_right hn hk0
  exact_mod_cast hprod

end
end ErdosGallai.Representatives

namespace ErdosGallai
noncomputable section
open Finset Real Filter
attribute [local instance] Classical.propDecidable

noncomputable def reservoirProbability (η : ℝ) : ℝ := min (η/12) (1/12)
noncomputable def reservoirExpansionCoefficient (c : ℝ) : ℝ := min c 1 / 6

universe u

theorem reservoir_preparation (c η : ℝ) (hc : 0 < c) (hη : 0 < η) :
    ∃ D₀ : ℝ, ∀ D : ℝ, D₀ ≤ D → ∀ (V : Type u) [Fintype V] [DecidableEq V]
      (G P : SimpleGraph V) [DecidableRel P.Adj], P ≤ G →
      D^(9/10 : ℝ) ≤ (Fintype.card V : ℝ) →
      (Fintype.card V : ℝ) ≤ D^(51/50 : ℝ) →
      Splitting.CutExpansion P (c*D^(9/10 : ℝ)) →
      ∃ (ω : Sym2 V → Fin 3) (W : Fin 3 → Finset V) (f : Fin 3 → V × Fin 2 → V),
        (∀ i, Splitting.colorGraph P ω i ≤ G) ∧
        (∀ i j, i ≠ j → Disjoint (Splitting.colorGraph P ω i).edgeSet
            (Splitting.colorGraph P ω j).edgeSet) ∧
        (∀ i, Splitting.CutExpansion (Splitting.colorGraph P ω i)
          (reservoirExpansionCoefficient c * D^(9/10 : ℝ))) ∧
        (∀ i j, i ≠ j → Disjoint (W i) (W j)) ∧
        (∀ i, 2 ≤ (W i).card) ∧
        (∀ i, ((W i).card : ℝ) ≤ 2*reservoirProbability η*Fintype.card V) ∧
        (∀ i, (W i).card < Fintype.card V) ∧
        ((∑ i, (W i).card : ℕ) : ℝ) ≤ η * Fintype.card V ∧
        (∀ i, Sampling.CutExpansionOn (Splitting.colorGraph P ω i) (W i)
          (D^(37/50 : ℝ))) ∧
        (∀ i v, v ∉ W i → ∀ t, f i (v,t) ∈ W i ∧
          (Splitting.colorGraph P ω i).Adj v (f i (v,t))) ∧
        (∀ i v, v ∉ W i → f i (v,0) ≠ f i (v,1)) ∧
        (∀ i w, (((W i)ᶜ ×ˢ Finset.univ).filter (fun x => f i x = w)).card ≤
          ⌈8*(Fintype.card V : ℝ) /
            (reservoirProbability η * (reservoirExpansionCoefficient c * D^(9/10 : ℝ)))⌉₊) := by
  let c₀ := min c 1
  let a := reservoirExpansionCoefficient c
  let q := reservoirProbability η
  have hc₀ : 0 < c₀ := lt_min hc (by norm_num)
  have ha : 0 < a := by dsimp [a, reservoirExpansionCoefficient]; positivity
  have hq : 0 < q := by dsimp [q, reservoirProbability]; positivity
  have hq12 : q ≤ 1/12 := min_le_right _ _
  have hqη : q ≤ η/12 := min_le_left _ _
  have hq3 : 3*q ≤ 1 := by linarith
  have hq6 : 6*q ≤ η := by linarith
  have hq2 : 2*q < 1 := by linarith
  let p : unitInterval := ⟨q, hq.le, by linarith⟩
  obtain ⟨D₁,hD₁⟩ := Splitting.edge_splitting_uniform.{u} c₀ hc₀ 3 (by norm_num)
  obtain ⟨D₂,hD₂⟩ := Sampling.three_reservoirs_uniform.{u} a ha p hq hq3
  have ht : ∀ᶠ D : ℝ in atTop, 4/(q*a) ≤ D^(9/10 : ℝ) :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 9/10)).eventually
      (eventually_ge_atTop _)
  obtain ⟨D₃,hD₃⟩ := ht.exists_forall_of_atTop
  refine ⟨max 1 (max D₁ (max D₂ D₃)), ?_⟩
  intro D hD V _ _ G P _ hPG hlo hhi hexp
  have hD1 : 1 ≤ D := (le_max_left _ _).trans hD
  have hDsplit : D₁ ≤ D := (le_trans (le_max_left _ _) (le_max_right _ _)).trans hD
  have hDsample : D₂ ≤ D :=
    (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))).trans hD
  have hDpower : D₃ ≤ D :=
    (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))).trans hD
  have hpow : 0 < D^(9/10 : ℝ) := Real.rpow_pos_of_pos (by linarith) _
  have hd : 4 ≤ q*(a*D^(9/10 : ℝ)) := by
    have hh := (div_le_iff₀ (mul_pos hq ha)).mp (hD₃ D hDpower)
    nlinarith
  have hr : 0 < (Fintype.card V : ℝ) := hpow.trans_le hlo
  have : Nonempty V := Fintype.card_pos_iff.mp (by exact_mod_cast hr)
  have hexp₀ : Splitting.CutExpansion P (c₀*D^(9/10 : ℝ)) := by
    intro U
    exact (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (min_le_left c 1) hpow.le)
      (le_min (Nat.cast_nonneg _) (Nat.cast_nonneg _))).trans (hexp U)
  obtain ⟨ω,hcut,hcover,hdisj⟩ := hD₁ D hDsplit V P
    (c₀*D^(9/10 : ℝ)) le_rfl hlo hhi hexp₀
  have hcut' : ∀ i, Sampling.CutExpansion (Splitting.colorGraph P ω i)
      (a*D^(9/10 : ℝ)) := by
    intro i
    have heq : a*D^(9/10 : ℝ) = c₀*D^(9/10 : ℝ)/(2*(3 : ℝ)) := by
      dsimp [a, reservoirExpansionCoefficient, c₀]
      ring
    rw [heq]
    exact hcut i
  obtain ⟨W,hWdisj,hWsize,hWneigh,hWcut⟩ := hD₂ D hDsample V
    (fun i => Splitting.colorGraph P ω i) hlo hhi hcut'
  have hWtwo : ∀ i, 2 ≤ (W i).card := by
    intro i
    let v : V := Classical.choice inferInstance
    have hn := hWneigh i v
    have hsub : Sampling.neighborsIn (Splitting.colorGraph P ω i) v (W i) ⊆ W i :=
      Finset.filter_subset _ _
    have hh := Finset.card_le_card hsub
    have hn' : (2 : ℝ) ≤ (Sampling.neighborsIn (Splitting.colorGraph P ω i) v (W i)).card := by
      change q*(a*D^(9/10 : ℝ))/2 ≤ _ at hn
      linarith
    have hn'' : 2 ≤ (Sampling.neighborsIn (Splitting.colorGraph P ω i) v (W i)).card := by
      exact_mod_cast hn'
    omega
  have hWlt : ∀ i, (W i).card < Fintype.card V := by
    intro i
    have hh := (hWsize i).trans_lt (mul_lt_of_lt_one_left hr hq2)
    exact_mod_cast hh
  have hWsum : ((∑ i, (W i).card : ℕ) : ℝ) ≤ η * Fintype.card V := by
    have hh := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin 3))) => hWsize i)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hh
    rw [Nat.cast_sum]
    exact hh.trans (by dsimp [p]; nlinarith [mul_le_mul_of_nonneg_right hq6 hr.le])
  have hrep : ∀ i, ∃ f : V × Fin 2 → V,
      (∀ v ∈ (W i)ᶜ, ∀ t, f (v,t) ∈ Sampling.neighborsIn (Splitting.colorGraph P ω i) v (W i)) ∧
      (∀ v ∈ (W i)ᶜ, f (v,0) ≠ f (v,1)) ∧
      (∀ w, (((W i)ᶜ ×ˢ Finset.univ).filter (fun x => f x = w)).card ≤
        ⌈8*(Fintype.card V : ℝ)/(q*(a*D^(9/10 : ℝ)))⌉₊) := by
    intro i
    exact Representatives.reservoir_representatives (W i)ᶜ
      (fun v => Sampling.neighborsIn (Splitting.colorGraph P ω i) v (W i))
      (Fintype.card V) (q*(a*D^(9/10 : ℝ)))
      (by exact_mod_cast (Finset.card_le_univ ((W i)ᶜ))) hd
      (fun v _ => hWneigh i v)
  choose f hf hsep hcap using hrep
  refine ⟨ω,W,f,?_,hdisj,?_,hWdisj,hWtwo,hWsize,hWlt,hWsum,hWcut,?_,?_,hcap⟩
  · intro i x y hxy
    exact hPG hxy.1
  · exact hcut'
  · intro i v hv t
    exact Finset.mem_filter.mp (hf i v (Finset.mem_compl.mpr hv) t)
  · intro i v hv
    exact hsep i v (Finset.mem_compl.mpr hv)

end
end ErdosGallai

end
end
end

end OAI
