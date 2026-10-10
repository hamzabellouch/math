import OAI.Probability.FreeIsing.Estimates.FairSpin
import OAI.Probability.FreeIsing.Trees.Parents

namespace OAI

noncomputable section
open MeasureTheory
namespace Problem367
namespace RootedBroadcast

local instance rootedBroadcastMeasurableSingletonSpin :
    MeasurableSingletonClass IsingSpin := ⟨fun _ => trivial⟩

def spinMul (a b : IsingSpin) : IsingSpin :=
  if a = b then IsingSpin.pos else IsingSpin.neg

@[simp] lemma spinMul_pos (a : IsingSpin) : spinMul a IsingSpin.pos = a := by
  cases a <;> rfl
@[simp] lemma pos_spinMul (a : IsingSpin) : spinMul IsingSpin.pos a = a := by
  cases a <;> rfl
@[simp] lemma spinMul_self (a : IsingSpin) : spinMul a a = IsingSpin.pos := by
  simp [spinMul]
lemma spinMul_comm (a b : IsingSpin) : spinMul a b = spinMul b a := by
  cases a <;> cases b <;> rfl
lemma spinMul_assoc (a b c : IsingSpin) : spinMul (spinMul a b) c = spinMul a (spinMul b c) := by
  cases a <;> cases b <;> cases c <;> rfl
@[simp] lemma spinMul_cancel (a b : IsingSpin) : spinMul a (spinMul a b) = b := by
  rw [← spinMul_assoc, spinMul_self, pos_spinMul]

lemma measurable_spinMul : Measurable (fun p : IsingSpin × IsingSpin => spinMul p.1 p.2) :=
  measurable_of_finite _

def biasedSpin (p u : ℝ) : IsingSpin :=
  if u ≤ p then IsingSpin.pos else IsingSpin.neg

lemma measurable_biasedSpin (p : ℝ) : Measurable (biasedSpin p) := by
  exact measurable_const.ite measurableSet_Iic measurable_const

lemma biasedSpin_pos_mass {p : ℝ} (_hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    uniform01 ((biasedSpin p) ⁻¹' {IsingSpin.pos}) = ENNReal.ofReal p := by
  have hpre : (biasedSpin p) ⁻¹' {IsingSpin.pos} = Set.Iic p := by
    ext u
    simp [biasedSpin]
  rw [hpre, uniform01, Measure.restrict_apply measurableSet_Iic]
  have h : Set.Iic p ∩ Set.Icc 0 1 = Set.Icc 0 p := by
    ext u
    simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc]
    exact ⟨fun ⟨hu,h0,_⟩ => ⟨h0,hu⟩, fun ⟨h0,hu⟩ => ⟨hu,h0,hu.trans hp1⟩⟩
  rw [h, Real.volume_Icc, sub_zero]

lemma biasedSpin_neg_mass {p : ℝ} (hp0 : 0 ≤ p) (_hp1 : p ≤ 1) :
    uniform01 ((biasedSpin p) ⁻¹' {IsingSpin.neg}) = ENNReal.ofReal (1-p) := by
  have hpre : (biasedSpin p) ⁻¹' {IsingSpin.neg} = Set.Ioi p := by
    ext u
    simp [biasedSpin, not_le]
  rw [hpre, uniform01, Measure.restrict_apply measurableSet_Ioi]
  have h : Set.Ioi p ∩ Set.Icc 0 1 = Set.Ioc p 1 := by
    ext u
    simp only [Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Icc, Set.mem_Ioc]
    exact ⟨fun ⟨hu,_,h1⟩ => ⟨hu,h1⟩, fun ⟨hu,h1⟩ => ⟨hu,hp0.trans hu.le,h1⟩⟩
  rw [h, Real.volume_Ioc]

abbrev parent {d : ℕ} (v : TreeVertex d) : TreeVertex d := parentVertex v

def ofNoise {d : ℕ} (noise : TreeVertex d → IsingSpin) (v : TreeVertex d) : IsingSpin :=
  if _h : v.val = [] then noise v
  else spinMul (noise v) (ofNoise noise (parent v))
termination_by v.val.length
decreasing_by
  simp only [parent, parentVertex, List.length_dropLast]
  have : 0 < v.val.length := List.length_pos_iff.mpr _h
  omega

lemma ofNoise_root {d : ℕ} (noise : TreeVertex d → IsingSpin) :
    ofNoise noise ⟨[], List.isChain_nil⟩ = noise ⟨[], List.isChain_nil⟩ := by
  rw [ofNoise]
  simp

lemma ofNoise_nonroot {d : ℕ} (noise : TreeVertex d → IsingSpin) (v : TreeVertex d)
    (hv : v.val ≠ []) :
    ofNoise noise v = spinMul (noise v) (ofNoise noise (parent v)) := by
  rw [ofNoise, dite_eq_right hv]

lemma ofNoise_append {d : ℕ} (noise : TreeVertex d → IsingSpin)
    (v w : TreeVertex d) (c : Fin d) (hw : w.val = v.val ++ [c]) :
    ofNoise noise w = spinMul (noise w) (ofNoise noise v) := by
  have hn : w.val ≠ [] := by simp [hw]
  rw [ofNoise_nonroot noise w hn]
  have hp : parent w = v := by
    apply Subtype.ext
    simp [parent, parentVertex, hw]
  rw [hp]

lemma measurable_ofNoise_apply {d : ℕ} (v : TreeVertex d) :
    Measurable (fun noise : TreeVertex d → IsingSpin => ofNoise noise v) := by
  have h : ∀ n : ℕ, ∀ v : TreeVertex d, v.val.length = n →
      Measurable (fun noise : TreeVertex d → IsingSpin => ofNoise noise v) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro v hv
      by_cases hnil : v.val = []
      · have heq : (fun noise : TreeVertex d → IsingSpin => ofNoise noise v) =
            (fun noise => noise v) := by
          funext noise
          rw [ofNoise]
          simp [hnil]
        rw [heq]
        exact measurable_pi_apply v
      · have hlt : (parent v).val.length < n := by
          simp only [parent, parentVertex, List.length_dropLast, ← hv]
          have : 0 < v.val.length := List.length_pos_iff.mpr hnil
          omega
        have hm := ih _ hlt (parent v) rfl
        have heq : (fun noise : TreeVertex d → IsingSpin => ofNoise noise v) =
            (fun noise => spinMul (noise v) (ofNoise noise (parent v))) := by
          funext noise
          exact ofNoise_nonroot noise v hnil
        rw [heq]
        exact measurable_spinMul.comp ((measurable_pi_apply v).prodMk hm)
  exact h _ v rfl

lemma measurable_ofNoise (d : ℕ) : Measurable (@ofNoise d) := by
  exact Measurable.of_eval measurable_ofNoise_apply

def noiseFromSpins {d : ℕ} (x : TreeVertex d → IsingSpin) (v : TreeVertex d) : IsingSpin :=
  if v.val = [] then x v else spinMul (x v) (x (parent v))

lemma measurable_noiseFromSpins (d : ℕ) : Measurable (@noiseFromSpins d) := by
  apply Measurable.of_eval
  intro v
  by_cases hv : v.val = []
  · simpa only [noiseFromSpins, ite_eq_left hv] using measurable_pi_apply (X := fun _ : TreeVertex d => IsingSpin) v
  · simpa only [noiseFromSpins, ite_eq_right hv, Function.comp_def] using
      measurable_spinMul.comp ((measurable_pi_apply (X := fun _ : TreeVertex d => IsingSpin) v).prodMk (measurable_pi_apply (parent v)))

@[simp] lemma noiseFromSpins_ofNoise {d : ℕ} (noise : TreeVertex d → IsingSpin) :
    noiseFromSpins (ofNoise noise) = noise := by
  funext v
  by_cases hv : v.val = []
  · rw [noiseFromSpins, ite_eq_left hv, ofNoise]
    simp [hv]
  · rw [noiseFromSpins, ite_eq_right hv, ofNoise_nonroot noise v hv]
    rw [spinMul_assoc, spinMul_self, spinMul_pos]

@[simp] lemma ofNoise_noiseFromSpins {d : ℕ} (x : TreeVertex d → IsingSpin) :
    ofNoise (noiseFromSpins x) = x := by
  funext v
  have h : ∀ n : ℕ, ∀ v : TreeVertex d, v.val.length = n →
      ofNoise (noiseFromSpins x) v = x v := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro v hv
      by_cases hnil : v.val = []
      · rw [ofNoise]
        simp [hnil, noiseFromSpins]
      · have hlt : (parent v).val.length < n := by
          simp only [parent, parentVertex, List.length_dropLast, ← hv]
          have : 0 < v.val.length := List.length_pos_iff.mpr hnil
          omega
        rw [ofNoise_nonroot _ v hnil, ih _ hlt (parent v) rfl,
          noiseFromSpins, ite_eq_right hnil, spinMul_assoc, spinMul_self, spinMul_pos]
  exact h _ v rfl

def measurableEquiv (d : ℕ) : (TreeVertex d → IsingSpin) ≃ᵐ (TreeVertex d → IsingSpin) where
  toFun := ofNoise
  invFun := noiseFromSpins
  left_inv := noiseFromSpins_ofNoise
  right_inv := ofNoise_noiseFromSpins
  measurable_toFun := measurable_ofNoise d
  measurable_invFun := measurable_noiseFromSpins d

def edgeNoise (theta : ℝ) : ℝ → IsingSpin := biasedSpin ((1 + theta) / 2)

lemma measurable_edgeNoise (theta : ℝ) : Measurable (edgeNoise theta) :=
  measurable_biasedSpin _

lemma edgeNoise_mass {theta : ℝ} (h0 : -1 ≤ theta) (h1 : theta ≤ 1) (a : IsingSpin) :
    uniform01 ((edgeNoise theta) ⁻¹' {a}) =
      ENNReal.ofReal ((1 + (if a = IsingSpin.pos then theta else -theta)) / 2) := by
  have hp0 : 0 ≤ (1 + theta) / 2 := by linarith
  have hp1 : (1 + theta) / 2 ≤ 1 := by linarith
  cases a
  · rw [edgeNoise, biasedSpin_neg_mass hp0 hp1, ite_eq_right (by decide : IsingSpin.neg ≠ IsingSpin.pos)]
    congr 1
    ring
  · rw [edgeNoise, biasedSpin_pos_mass hp0 hp1]
    rfl

def inputNoise {d : ℕ} (theta : ℝ) (U : TreeVertex d → ℝ) (v : TreeVertex d) : IsingSpin :=
  if v.val = [] then fairSpin (U v) else edgeNoise theta (U v)

lemma measurable_inputNoise (d : ℕ) (theta : ℝ) : Measurable (@inputNoise d theta) := by
  apply Measurable.of_eval
  intro v
  by_cases hv : v.val = []
  · simpa only [inputNoise, ite_eq_left hv, Function.comp_def] using measurable_fairSpin.comp (measurable_pi_apply v)
  · simpa only [inputNoise, ite_eq_right hv, Function.comp_def] using (measurable_edgeNoise theta).comp (measurable_pi_apply v)

def factor {d : ℕ} (theta : ℝ) (U : TreeVertex d → ℝ) : TreeVertex d → IsingSpin :=
  ofNoise (inputNoise theta U)

lemma measurable_factor (d : ℕ) (theta : ℝ) : Measurable (@factor d theta) :=
  (measurable_ofNoise d).comp (measurable_inputNoise d theta)

lemma factor_append {d : ℕ} (theta : ℝ) (U : TreeVertex d → ℝ)
    (v w : TreeVertex d) (c : Fin d) (hw : w.val = v.val ++ [c]) :
    factor theta U w = spinMul (edgeNoise theta (U w)) (factor theta U v) := by
  rw [factor, ofNoise_append _ v w c hw]
  simp [inputNoise, hw]

def noiseWeight {d : ℕ} (theta : ℝ) (v : TreeVertex d) (a : IsingSpin) : ENNReal :=
  if v.val = [] then 1 / 2
  else ENNReal.ofReal ((1 + (if a = IsingSpin.pos then theta else -theta)) / 2)

lemma inputNoise_cylinder {d : ℕ} {theta : ℝ} (h0 : -1 ≤ theta) (h1 : theta ≤ 1)
    (D : Finset (TreeVertex d)) (eta : TreeVertex d → IsingSpin) :
    (Measure.map (inputNoise theta) (labelMeasure d))
      {x | ∀ v ∈ D, x v = eta v} = ∏ v ∈ D, noiseWeight theta v (eta v) := by
  classical
  have hm : MeasurableSet {x : TreeVertex d → IsingSpin | ∀ v ∈ D, x v = eta v} :=
    MeasurableSet.pi D.countable_toSet (fun v _ => measurableSet_singleton (eta v))
  rw [Measure.map_apply (measurable_inputNoise d theta) hm]
  change (Measure.infinitePi (fun _ : TreeVertex d => uniform01))
    (Set.pi (D : Set (TreeVertex d))
      (fun v => {u | (if v.val = [] then fairSpin u else edgeNoise theta u) = eta v})) = _
  rw [Measure.infinitePi_pi _ ?_]
  · apply Finset.prod_congr rfl
    intro v hv
    by_cases hnil : v.val = []
    · simpa only [hnil, ↓reduceIte, noiseWeight, Set.preimage, Set.mem_singleton_iff] using fairSpin_mass (eta v)
    · simpa only [hnil, ↓reduceIte, noiseWeight, Set.preimage, Set.mem_singleton_iff] using edgeNoise_mass h0 h1 (eta v)
  · intro v hv
    by_cases hnil : v.val = []
    · simpa only [hnil, ↓reduceIte, Set.preimage, Set.mem_singleton_iff] using measurable_fairSpin (measurableSet_singleton (eta v))
    · simpa only [hnil, ↓reduceIte, Set.preimage, Set.mem_singleton_iff] using (measurable_edgeNoise theta) (measurableSet_singleton (eta v))

end RootedBroadcast
end Problem367

end

end OAI
