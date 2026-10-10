import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.KappaPos

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical

namespace OrdinaryCorrelations.GraphKernel.PrimeSystem
open OrdinaryCorrelations.FiniteIntegration OrdinaryCorrelations.SignedTrace
open Finset Classical
variable {S : PrimeSystem} {h ℓ : ℕ}

def treeVertices (w : ClosedLine h ℓ) : Finset ℤ := univ.image w.offset

lemma departure_mem_vertices (w : ClosedLine h ℓ) (i : Fin ℓ) :
    w.offset i.castSucc ∈ treeVertices w := mem_image.mpr ⟨i.castSucc, mem_univ _, rfl⟩

lemma endpoint_mem_vertices (w : ClosedLine h ℓ) (i : Fin ℓ) :
    w.offset i.succ ∈ treeVertices w := mem_image.mpr ⟨i.succ, mem_univ _, rfl⟩

lemma tree_normalization (w : ClosedLine h ℓ) (p : S.Index) (x : ZMod (p : ℕ)) :
    (∏ i ∈ w.treeSteps, S.beta p ^
      (if x + (w.offset i.castSucc : ZMod (p : ℕ)) = 0 then (1 : ℕ) else 0)) =
    ∏ v ∈ treeVertices w, if x + (v : ZMod (p : ℕ)) = 0 then
      S.beta p ^ w.children v else 1 := by
  rw [← prod_fiberwise_of_maps_to (fun i (_ : i ∈ w.treeSteps) => departure_mem_vertices w i)]
  apply prod_congr rfl
  intro v hv
  by_cases ha : x + (v : ZMod (p : ℕ)) = 0
  · simp only [ha, ite_true, ClosedLine.children]
    trans ∏ i ∈ w.treeSteps.filter (fun i => w.offset i.castSucc = v), S.beta p
    · apply prod_congr rfl
      intro i hi
      rw [(mem_filter.mp hi).2, ite_eq_left ha, pow_one]
    · rw [prod_const]
  · rw [ite_eq_right ha]
    apply prod_eq_one
    intro i hi
    rw [(mem_filter.mp hi).2, ite_eq_right ha, pow_zero]

lemma residue_product_mean {ι : Type*} {p : ℕ} [NeZero p]
    (V : Finset ι) (r : ι → ZMod p) (g : ι → ℝ)
    (hinj : Set.InjOn r V) :
    avg (fun a : ZMod p => ∏ v ∈ V, if a = r v then g v else 1) =
      1 - (∑ v ∈ V, (1 - g v)) / p := by
  have hpoint (a : ZMod p) :
      (∏ v ∈ V, if a = r v then g v else 1) =
        1 + ∑ v ∈ V, if a = r v then g v - 1 else 0 := by
    by_cases ha : ∃ v ∈ V, a = r v
    · obtain ⟨v,hv,ha⟩ := ha
      have hne (q : ι) (hq : q ∈ V) (hqv : q ≠ v) : a ≠ r q := by
        intro h
        exact hqv (hinj hq hv (h.symm.trans ha))
      rw [prod_eq_single_of_mem v hv (fun q hq hqv => ite_eq_right (hne q hq hqv)),
        sum_eq_single_of_mem v hv (fun q hq hqv => ite_eq_right (hne q hq hqv))]
      simp only [ite_eq_left ha]
      ring
    · have hne (v : ι) (hv : v ∈ V) : a ≠ r v := fun h => ha ⟨v,hv,h⟩
      rw [prod_eq_one (fun v hv => ite_eq_right (hne v hv)),
        sum_eq_zero (fun v hv => ite_eq_right (hne v hv))]
      ring
  simp_rw [hpoint]
  simp only [avg, sum_add_distrib, sum_const, card_univ, ZMod.card, nsmul_eq_mul]
  rw [sum_comm]
  simp only [sum_ite_eq', mem_univ, ite_true]
  have hp : (p : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne p
  rw [sum_sub_distrib, sum_const, nsmul_eq_mul]
  simp only [sum_sub_distrib, sum_const, nsmul_eq_mul]
  field_simp
  ring

def backgroundMultiplier (w : ClosedLine h ℓ) (U : Finset ℤ) (p : S.Index)
    (a : ZMod (p : ℕ)) : ℝ :=
  ∏ v ∈ treeVertices w, if a + (v : ZMod (p : ℕ)) = 0 then
    S.beta p ^ w.children v * (if S.IsCore p ∧ v ∈ U then Real.exp kappa else 1) else 1

def treeDefect (w : ClosedLine h ℓ) (p : S.Index) : ℝ :=
  ∑ v ∈ treeVertices w, (1 - S.beta p ^ w.children v)

lemma beta_nonneg (p : S.Index) : 0 ≤ S.beta p := by
  have ha := A_pos
  unfold beta amplitude
  split_ifs <;> positivity

lemma beta_le_one (p : S.Index) : S.beta p ≤ 1 := by
  unfold beta amplitude
  split_ifs
  · exact betaC_le_one
  · norm_num

lemma background_vertex_le_one (w : ClosedLine h ℓ) (U : Finset ℤ)
    (hU : ∀ v ∈ U, w.children v = 1) (p : S.Index) (v : ℤ) :
    S.beta p ^ w.children v * (if S.IsCore p ∧ v ∈ U then Real.exp kappa else 1) ≤ 1 := by
  by_cases hu : S.IsCore p ∧ v ∈ U
  · rw [ite_eq_left hu, hU v hu.2, pow_one]
    simpa only [beta, amplitude, hu.1, ite_true, betaC] using betaC_mul_exp_le_one
  · rw [ite_eq_right hu, mul_one]
    exact pow_le_one₀ (beta_nonneg p) (beta_le_one p)

lemma backgroundMultiplier_bounds (w : ClosedLine h ℓ) (U : Finset ℤ)
    (hU : ∀ v ∈ U, w.children v = 1) (p : S.Index) (a : ZMod (p : ℕ)) :
    0 ≤ backgroundMultiplier w U p a ∧ backgroundMultiplier w U p a ≤ 1 := by
  have hnon (v : ℤ) : 0 ≤ (if a + (v : ZMod (p : ℕ)) = 0 then
      S.beta p ^ w.children v * (if S.IsCore p ∧ v ∈ U then Real.exp kappa else 1) else 1) := by
    have hb := beta_nonneg p
    split_ifs <;> positivity
  constructor
  · exact prod_nonneg (fun v _ => hnon v)
  · apply prod_le_one₀ (fun v _ => hnon v)
    intro v hv
    by_cases ha : a + (v : ZMod (p : ℕ)) = 0
    · rw [ite_eq_left ha]
      exact background_vertex_le_one w U hU p v
    · rw [ite_eq_right ha]

lemma background_mean_exact (w : ClosedLine h ℓ) (U : Finset ℤ)
    (p : S.Index) (hinj : Set.InjOn (fun v : ℤ => (v : ZMod (p : ℕ))) (treeVertices w)) :
    avg (backgroundMultiplier w U p) = 1 -
      (∑ v ∈ treeVertices w,
        (1 - S.beta p ^ w.children v *
          (if S.IsCore p ∧ v ∈ U then Real.exp kappa else 1))) / (p : ℝ) := by
  change avg (fun a => ∏ v ∈ treeVertices w, if a + (v : ZMod (p : ℕ)) = 0 then _ else _) = _
  simp only [add_eq_zero_iff_eq_neg]
  apply residue_product_mean
  intro v hv u hu hneg
  exact hinj hv hu (neg_injective hneg)

end OrdinaryCorrelations.GraphKernel.PrimeSystem

end

end OAI
