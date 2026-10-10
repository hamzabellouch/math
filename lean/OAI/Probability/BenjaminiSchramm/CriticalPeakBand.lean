import OAI.Probability.BenjaminiSchramm.PeakHalfspaceTransport
import OAI.Probability.BenjaminiSchramm.CriticalNormalizedCrossing
import OAI.Probability.BenjaminiSchramm.NormalizedExponentComparison

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace Percolation.BenjaminiSchramm
variable {V E : Type*} [Encodable V] [Countable E] [Nontrivial V]
  (G : BondGraph V E) [Fintype (criticalModel G).VertexOrbit]

lemma critical_normalized_halfspace_exp_bound (hc : Connected G) (hl : LocallyFinite G)
    (hq : QuasiTransitive G) (hu : ¬(criticalModel G).CombinatoriallyUnimodular)
    (μ : (criticalModel G).VertexOrbit → ℝ) (hμ : ∀ i, 0 < μ i)
    (hstat : orbitChainStep ((criticalModel G).orbitWalkKernel hl) μ=μ) :
    ∃ C L : ℝ, 0 < C ∧ 0 < L ∧ ∀ r, 0 ≤ r → ∀ x t, 0 ≤ t →
      law (pc G) ((criticalModel G).adjustedHalfspaceHit
        ((criticalModel G).stationaryOrbitWeight μ) x (-r) t) ≤
          ENNReal.ofReal (C*Real.exp (L*r-t)) := by
  obtain ⟨A,B,hA,hB,hh⟩ := critical_normalized_halfspace_uniform G hc hl hq hu μ hμ hstat
  have hp : (0 : ℝ) < pc G := by exact_mod_cast pc_pos G hl hq
  let ell := -Real.log (pc G : ℝ)
  have hell : 0 ≤ ell := neg_nonneg.mpr (Real.log_nonpos hp.le (pc G).2.2)
  let C := Real.exp (ell*B)
  let L := ell*A+1
  have hL : 0 < L := by dsimp [L]; positivity
  refine ⟨C,L,Real.exp_pos _,hL,fun r hr x t ht => ?_⟩
  have hreal : (law (pc G)).real ((criticalModel G).adjustedHalfspaceHit
      ((criticalModel G).stationaryOrbitWeight μ) x (-r) t) ≤ C*Real.exp (L*r-t) := by
    apply (hh r hr x t ht).trans
    rw [Real.rpow_def_of_pos hp,←Real.exp_add]
    change Real.exp _ ≤ Real.exp (ell*B)*Real.exp (L*r-t)
    rw [←Real.exp_add]
    apply Real.exp_le_exp.mpr
    dsimp [ell,L]
    nlinarith
  calc
    _ = ENNReal.ofReal ((law (pc G)).real ((criticalModel G).adjustedHalfspaceHit
        ((criticalModel G).stationaryOrbitWeight μ) x (-r) t)) :=
      (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal hreal

theorem critical_peak_band_bound (hc : Connected G) (hl : LocallyFinite G)
    (hq : QuasiTransitive G) (hu : ¬(criticalModel G).CombinatoriallyUnimodular)
    (μ : (criticalModel G).VertexOrbit → ℝ) (hμ : ∀ i, 0 < μ i)
    (hstat : orbitChainStep ((criticalModel G).orbitWalkKernel hl) μ=μ) :
    ∃ C L : ℝ, 0 < C ∧ 0 < L ∧ ∀ r, 0 ≤ r → ∀ l u, u ≤ 0 →
      (∑ x ∈ ((criticalModel G).orbitRepresentatives
          (criticalModel_quasiTransitive G hq)).roots,
        ENNReal.ofReal ((criticalModel G).stationaryOrbitWeight μ x)*
          (∫⁻ ω, (criticalModel G).strictPeakSlabBandCount
            ((criticalModel G).stationaryOrbitWeight μ) r l u ω x ∂law (pc G))) ≤
      (∑ x ∈ ((criticalModel G).orbitRepresentatives
          (criticalModel_quasiTransitive G hq)).roots,
        ENNReal.ofReal ((criticalModel G).stationaryOrbitWeight μ x))*
          ENNReal.ofReal (C*Real.exp (L*r+u-l)) := by
  let H := criticalModel G
  let a := H.stationaryOrbitWeight μ
  let O := H.orbitRepresentatives (criticalModel_quasiTransitive G hq)
  have hHc := criticalModel_connected G hc
  obtain ⟨C,L,hC,hL,hup⟩ := critical_normalized_halfspace_exp_bound G hc hl hq hu μ hμ hstat
  refine ⟨C,L,hC,hL,fun r hr l u hu0 => ?_⟩
  have hb := H.expected_strictPeakSlabBandCount_bound O hHc hl a
    (H.stationaryOrbitWeight_pos hHc hl μ hμ) (H.stationaryOrbitWeight_aut μ) (pc G) r l u
  have hs : (∑ y ∈ O.roots, ENNReal.ofReal (a y)*H.law (pc G)
      (restrictedHit G (internalEdges G {z | -r ≤ H.orbitAdjustedHeight a y z}) y
        {z | -u ≤ H.orbitAdjustedHeight a y z})) ≤
      (∑ y ∈ O.roots, ENNReal.ofReal (a y))*ENNReal.ofReal (C*Real.exp (L*r+u)) := by
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro y _
    apply mul_le_mul' le_rfl
    change law (pc G) (H.adjustedHalfspaceHit a y (-r) (-u)) ≤ _
    simpa only [sub_neg_eq_add] using hup r hr y (-u) (neg_nonneg.mpr hu0)
  have he : ENNReal.ofReal (Real.exp (-l))*ENNReal.ofReal (Real.exp l)=1 := by
    rw [←ENNReal.ofReal_mul (Real.exp_pos _).le,←Real.exp_add]
    simp only [neg_add_cancel,Real.exp_zero,ENNReal.ofReal_one]
  calc
    _ = ENNReal.ofReal (Real.exp (-l))*(ENNReal.ofReal (Real.exp l)*
        (∑ x ∈ O.roots, ENNReal.ofReal (a x)*
          (∫⁻ ω, H.strictPeakSlabBandCount a r l u ω x ∂law (pc G)))) := by
      rw [←mul_assoc,he,one_mul]
    _ ≤ ENNReal.ofReal (Real.exp (-l))*
        ((∑ y ∈ O.roots, ENNReal.ofReal (a y))*ENNReal.ofReal (C*Real.exp (L*r+u))) :=
      mul_le_mul' le_rfl (hb.trans hs)
    _ = _ := by
      rw [mul_left_comm,←ENNReal.ofReal_mul (Real.exp_pos _).le]
      congr 2
      rw [mul_left_comm,←Real.exp_add]
      congr 2
      ring

lemma critical_normalized_halfspace_exp_bound_at_rate (hc : Connected G) (hl : LocallyFinite G)
    (hq : QuasiTransitive G) (hu : ¬(criticalModel G).CombinatoriallyUnimodular)
    (μ : (criticalModel G).VertexOrbit → ℝ) (hμ : ∀ i, 0 < μ i)
    (hstat : orbitChainStep ((criticalModel G).orbitWalkKernel hl) μ=μ)
    (α : ℝ) (hcross : ∀ t : ℝ, 0 ≤ t →
      ((criticalModel G).infimalAdjustedCrossing
        ((criticalModel G).stationaryOrbitWeight μ) (pc G) t).toReal ≤ Real.exp (-α*t)) :
    ∃ C L : ℝ, 0 < C ∧ 0 < L ∧ ∀ r, 0 ≤ r → ∀ x t, 0 ≤ t →
      law (pc G) ((criticalModel G).adjustedHalfspaceHit
        ((criticalModel G).stationaryOrbitWeight μ) x (-r) t) ≤
          ENNReal.ofReal (C*Real.exp (L*r-α*t)) := by
  have hp : (0 : ℝ) < pc G := by exact_mod_cast pc_pos G hl hq
  obtain ⟨A,B,hA,hB,hh⟩ := normalized_halfspace_uniform_of_infimal_bound G hc hl hq hu
    μ hμ hstat (pc G) hp α hcross
  let ell := -Real.log (pc G : ℝ)
  have hell : 0 ≤ ell := neg_nonneg.mpr (Real.log_nonpos hp.le (pc G).2.2)
  let C := Real.exp (ell*B)
  let L := ell*A+1
  have hL : 0 < L := by dsimp [L]; positivity
  refine ⟨C,L,Real.exp_pos _,hL,fun r hr x t ht => ?_⟩
  have hreal : (law (pc G)).real ((criticalModel G).adjustedHalfspaceHit
      ((criticalModel G).stationaryOrbitWeight μ) x (-r) t) ≤ C*Real.exp (L*r-α*t) := by
    apply (hh r hr x t ht).trans
    rw [Real.rpow_def_of_pos hp,←Real.exp_add]
    change Real.exp _ ≤ Real.exp (ell*B)*Real.exp (L*r-α*t)
    rw [←Real.exp_add]
    apply Real.exp_le_exp.mpr
    dsimp [ell,L]
    nlinarith
  calc
    _ = ENNReal.ofReal ((law (pc G)).real ((criticalModel G).adjustedHalfspaceHit
        ((criticalModel G).stationaryOrbitWeight μ) x (-r) t)) :=
      (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal hreal

theorem critical_peak_band_bound_at_rate (hc : Connected G) (hl : LocallyFinite G)
    (hq : QuasiTransitive G) (hu : ¬(criticalModel G).CombinatoriallyUnimodular)
    (μ : (criticalModel G).VertexOrbit → ℝ) (hμ : ∀ i, 0 < μ i)
    (hstat : orbitChainStep ((criticalModel G).orbitWalkKernel hl) μ=μ)
    (α : ℝ) (hcross : ∀ t : ℝ, 0 ≤ t →
      ((criticalModel G).infimalAdjustedCrossing
        ((criticalModel G).stationaryOrbitWeight μ) (pc G) t).toReal ≤ Real.exp (-α*t)) :
    ∃ C L : ℝ, 0 < C ∧ 0 < L ∧ ∀ r, 0 ≤ r → ∀ l u, u ≤ 0 →
      (∑ x ∈ ((criticalModel G).orbitRepresentatives
          (criticalModel_quasiTransitive G hq)).roots,
        ENNReal.ofReal ((criticalModel G).stationaryOrbitWeight μ x)*
          (∫⁻ ω, (criticalModel G).strictPeakSlabBandCount
            ((criticalModel G).stationaryOrbitWeight μ) r l u ω x ∂law (pc G))) ≤
      (∑ x ∈ ((criticalModel G).orbitRepresentatives
          (criticalModel_quasiTransitive G hq)).roots,
        ENNReal.ofReal ((criticalModel G).stationaryOrbitWeight μ x))*
          ENNReal.ofReal (C*Real.exp (L*r+α*u-l)) := by
  let H := criticalModel G
  let a := H.stationaryOrbitWeight μ
  let O := H.orbitRepresentatives (criticalModel_quasiTransitive G hq)
  have hHc := criticalModel_connected G hc
  obtain ⟨C,L,hC,hL,hup⟩ := critical_normalized_halfspace_exp_bound_at_rate G hc hl hq hu μ hμ hstat α hcross
  refine ⟨C,L,hC,hL,fun r hr l u hu0 => ?_⟩
  have hb := H.expected_strictPeakSlabBandCount_bound O hHc hl a
    (H.stationaryOrbitWeight_pos hHc hl μ hμ) (H.stationaryOrbitWeight_aut μ) (pc G) r l u
  have hs : (∑ y ∈ O.roots, ENNReal.ofReal (a y)*H.law (pc G)
      (restrictedHit G (internalEdges G {z | -r ≤ H.orbitAdjustedHeight a y z}) y
        {z | -u ≤ H.orbitAdjustedHeight a y z})) ≤
      (∑ y ∈ O.roots, ENNReal.ofReal (a y))*ENNReal.ofReal (C*Real.exp (L*r+α*u)) := by
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro y _
    apply mul_le_mul' le_rfl
    change law (pc G) (H.adjustedHalfspaceHit a y (-r) (-u)) ≤ _
    simpa only [mul_neg,sub_neg_eq_add] using hup r hr y (-u) (neg_nonneg.mpr hu0)
  have he : ENNReal.ofReal (Real.exp (-l))*ENNReal.ofReal (Real.exp l)=1 := by
    rw [←ENNReal.ofReal_mul (Real.exp_pos _).le,←Real.exp_add]
    simp only [neg_add_cancel,Real.exp_zero,ENNReal.ofReal_one]
  calc
    _ = ENNReal.ofReal (Real.exp (-l))*(ENNReal.ofReal (Real.exp l)*
        (∑ x ∈ O.roots, ENNReal.ofReal (a x)*
          (∫⁻ ω, H.strictPeakSlabBandCount a r l u ω x ∂law (pc G)))) := by
      rw [←mul_assoc,he,one_mul]
    _ ≤ ENNReal.ofReal (Real.exp (-l))*
        ((∑ y ∈ O.roots, ENNReal.ofReal (a y))*ENNReal.ofReal (C*Real.exp (L*r+α*u))) :=
      mul_le_mul' le_rfl (hb.trans hs)
    _ = _ := by
      rw [mul_left_comm,←ENNReal.ofReal_mul (Real.exp_pos _).le]
      congr 2
      rw [mul_left_comm,←Real.exp_add]
      congr 2
      ring

end Percolation.BenjaminiSchramm

end

end OAI
