import OAI.NumberTheory.DukePrimeDegree.Dynamics.HorosphereIsolatingFlow

namespace OAI

/-!
# Peripheral root limits of diagonal conjugates

The isolating flows send any shearing-horosphere element to the
transvection whose parameter is the selected matrix entry.
-/

noncomputable section
open Matrix Filter
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

theorem horosphere_isolated_root_limit
    (d : ℕ) {i j a b : Fin (d + 1)} (hab : a ≠ b)
    (w : Fin (d + 1) → ℝ) (hw : w a = w b)
    (hdecay : ∀ r s, r ≠ s → (r = i ∨ s = j) → ¬ (r = a ∧ s = b) →
      w r - w s < 0)
    (g : G (d + 1)) (hg : RootHorosphereShape i j g) :
    Tendsto (fun t : ℝ => diagonalOneParameter (centerWeights d w) (centerWeights_sum d w) t *
      g * diagonalOneParameter (centerWeights d w) (centerWeights_sum d w) (-t))
      atTop (𝓝 (Matrix.SpecialLinearGroup.transvection hab (g.val a b))) := by
  apply tendsto_subtype_rng.mpr
  apply tendsto_pi_nhds.mpr
  intro r
  apply tendsto_pi_nhds.mpr
  intro s
  have he (t : ℝ) :
      (diagonalOneParameter (centerWeights d w) (centerWeights_sum d w) t *
        g * diagonalOneParameter (centerWeights d w) (centerWeights_sum d w) (-t)).val r s =
      Real.exp ((w r - w s) * t) * g.val r s := by
    rw [conjugation_entry, centerWeights_sub]
  simp_rw [he]
  by_cases hrs : r = s
  · subst s
    have hd := hg r r (Or.inr rfl)
    simp only [sub_self, zero_mul, Real.exp_zero, one_mul, hd]
    convert (tendsto_const_nhds : Tendsto (fun _ : ℝ =>
      (1 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) r r) atTop (𝓝 _)) using 1
    by_cases hra : r = a
    · subst r
      simp [Matrix.SpecialLinearGroup.transvection_coe, hab.symm]
    · simp [Matrix.SpecialLinearGroup.transvection_coe, Ne.symm hra]
  by_cases hrab : r = a ∧ s = b
  · rcases hrab with ⟨hra, hsb⟩
    subst r
    subst s
    simp only [hw, sub_self, zero_mul, Real.exp_zero, one_mul]
    convert (tendsto_const_nhds : Tendsto (fun _ : ℝ => g.val a b) atTop (𝓝 _)) using 1
    simp [Matrix.SpecialLinearGroup.transvection_coe, hab]
  have htarget : (Matrix.SpecialLinearGroup.transvection hab (g.val a b)).val r s = 0 := by
    simp_all [Matrix.SpecialLinearGroup.transvection_coe, eq_comm]
  rw [htarget]
  by_cases hshape : r = i ∨ s = j
  · have hneg := hdecay r s hrs hshape hrab
    have ht := Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (Filter.Tendsto.const_mul_atTop (by linarith : 0 < w s - w r) tendsto_id)
    have hlim := ht.mul_const (g.val r s)
    have heq (t : ℝ) : -((w s - w r) * t) = (w r - w s) * t := by ring
    simpa only [Function.comp_def, id_eq, heq, zero_mul] using hlim
  · have hzero : g.val r s = 0 := by
      have hri : r ≠ i := fun h => hshape (Or.inl h)
      have hsj : s ≠ j := fun h => hshape (Or.inr h)
      simpa only [Matrix.one_apply, hrs, ite_false] using hg r s (Or.inl ⟨hri, hsj⟩)
    simp only [hzero, mul_zero]
    exact tendsto_const_nhds

theorem horosphere_row_root_limit
    (d : ℕ) {i j k : Fin (d + 1)} (hij : i ≠ j) (hik : i ≠ k) (hkj : k ≠ j)
    (g : G (d + 1)) (hg : RootHorosphereShape i j g) :
    Tendsto (fun t : ℝ =>
      diagonalOneParameter (centerWeights d (rowIsolatingRaw i j k))
        (centerWeights_sum d _) t * g *
      diagonalOneParameter (centerWeights d (rowIsolatingRaw i j k))
        (centerWeights_sum d _) (-t))
      atTop (𝓝 (Matrix.SpecialLinearGroup.transvection hik (g.val i k))) :=
  horosphere_isolated_root_limit d hik _ (rowIsolatingRaw_equal hij hkj)
    (fun _ _ => rowIsolatingRaw_negative hij hkj) g hg

theorem horosphere_column_root_limit
    (d : ℕ) {i j k : Fin (d + 1)} (hij : i ≠ j) (hki : k ≠ i) (hkj : k ≠ j)
    (g : G (d + 1)) (hg : RootHorosphereShape i j g) :
    Tendsto (fun t : ℝ =>
      diagonalOneParameter (centerWeights d (columnIsolatingRaw i j k))
        (centerWeights_sum d _) t * g *
      diagonalOneParameter (centerWeights d (columnIsolatingRaw i j k))
        (centerWeights_sum d _) (-t))
      atTop (𝓝 (Matrix.SpecialLinearGroup.transvection hkj (g.val k j))) :=
  horosphere_isolated_root_limit d hkj _ (columnIsolatingRaw_equal hij.symm hki)
    (fun _ _ => columnIsolatingRaw_negative hij hki) g hg

end DukePrimeDegree

end

end OAI
