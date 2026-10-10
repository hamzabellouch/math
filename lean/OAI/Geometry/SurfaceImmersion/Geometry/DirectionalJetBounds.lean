import OAI.Geometry.SurfaceImmersion.Correction.WeightedPolynomialBounds

namespace OAI

/-! Higher directional jets of a controlled second jet lose one scale per
additional derivative. These are the factors in the finite jet polynomials. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.WeightedEstimates

variable {A E : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

def iteratedDirectional : List A → (A → E) → A → E
  | [], f => f
  | v :: vs, f => fun x => fderiv ℝ (iteratedDirectional vs f) x v

lemma contDiffOn_iteratedDirectional {U : Set A} (hU : IsOpen U) {f : A → E}
    (hf : ContDiffOn ℝ ∞ f U) (vs : List A) :
    ContDiffOn ℝ ∞ (iteratedDirectional vs f) U := by
  induction vs with
  | nil => exact hf
  | cons v vs ih =>
    exact (ih.fderiv_of_isOpen hU (by simp)).clm_apply contDiffOn_const

lemma WeightedBound.iteratedDirectional {U : Set A} (hU : IsOpen U) {f : A → E}
    {s C : ℝ} (hs : 0 < s) (hC : 0 ≤ C) (hf : ContDiffOn ℝ ∞ f U)
    (vs : List A) (hv : ∀ v ∈ vs, ‖v‖ ≤ 1) (m : ℕ)
    (hb : WeightedBound U s (m + vs.length) C f) :
    WeightedBound U s m (C / s ^ vs.length) (iteratedDirectional vs f) := by
  induction vs generalizing m with
  | nil => simpa [ClosedSurfaceR4.WeightedEstimates.iteratedDirectional] using hb
  | cons v vs ih =>
    have he : m + (v :: vs).length = (m + 1) + vs.length := by simp; omega
    have ht := ih (fun w hw => hv w (List.mem_cons_of_mem v hw)) (m + 1) (he ▸ hb)
    have hd := ht.directional hU hs (contDiffOn_iteratedDirectional hU hf vs) v
    apply hd.mono_const
    have hn : ‖v‖ ≤ 1 := hv v (List.mem_cons_self ..)
    have hc : 0 ≤ C / s ^ vs.length / s := by positivity
    calc
      ‖v‖ * (C / s ^ vs.length / s) ≤ C / s ^ vs.length / s := mul_le_of_le_one_left hc hn
      _ = C / s ^ (v :: vs).length := by simp [pow_succ, div_div]

/-- Products of higher-jet factors have a loss equal to the sum of their
additional derivative orders. The sum is independent of the output order. -/
lemma weighted_higher_jet_monomial {ι : Type*} {U : Set A} (hU : IsOpen U)
    {s : ℝ} (hs : 0 < s) (a : Finset ι) (C : ι → ℝ) (vs : ι → List A)
    (f : ι → A → ℝ) (m : ℕ) (hC : ∀ i ∈ a, 0 ≤ C i)
    (hv : ∀ i ∈ a, ∀ v ∈ vs i, ‖v‖ ≤ 1)
    (hf : ∀ i ∈ a, ContDiffOn ℝ ∞ (f i) U)
    (hb : ∀ i ∈ a, WeightedBound U s (m + (vs i).length) (C i) (f i)) :
    WeightedBound U s m
      (((2 ^ m) ^ a.card * ∏ i ∈ a, C i) / s ^ (∑ i ∈ a, (vs i).length))
      (fun x => ∏ i ∈ a, iteratedDirectional (vs i) (f i) x) := by
  apply WeightedBound.finset_prod_losses hU.uniqueDiffOn hs a C (fun i => (vs i).length)
    (fun i => iteratedDirectional (vs i) (f i)) hC
  · intro i hi
    exact contDiffOn_iteratedDirectional hU (hf i hi) (vs i)
  · intro i hi
    exact (hb i hi).iteratedDirectional hU hs (hC i hi) (hf i hi) (vs i) (hv i hi) m

end ClosedSurfaceR4.WeightedEstimates

end

end OAI
