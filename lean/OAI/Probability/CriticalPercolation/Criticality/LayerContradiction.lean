import Mathlib
import OAI.Probability.CriticalPercolation.Model
import OAI.Probability.CriticalPercolation.Criticality.LayerLocality
import OAI.Probability.CriticalPercolation.Criticality.PositiveCritical
import OAI.Probability.CriticalPercolation.Exploration.LayerExposure
import OAI.Probability.CriticalPercolation.Modular.CriticalHeavyNull
import OAI.Probability.CriticalPercolation.ProductMeasure.LayerExpectation

namespace OAI

section
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

theorem no_critical_percolation_of_all_light
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (hu : ¬G.CombinatoriallyUnimodular) (hpc : G.criticalProbability<1) (o : V)
    (hm : ∀ v, ∀ᵐ ω ∂G.law G.criticalProbability,
      G.modularMass v (G.cluster ω v)≠∞) :
    G.law G.criticalProbability G.percolates=0 := by
  let := G.countable_vertices hc hl
  let := G.countable_bonds hc hl
  by_contra hper
  obtain ⟨R,θ,hθ,M,hM,hblock⟩ := G.uniform_lower_nestedLayer_blocks hc hl hq hu o
    G.criticalProbability (G.criticalProbability_pos hc hl hq) hpc
    (lt_of_le_of_ne zero_le (Ne.symm hper)) hm
  obtain ⟨a,U,ha,hU,haU,hstart,hband⟩ := G.entrySeeds_weight_band_start hc hl hq R
  obtain ⟨d,hdpos,hd⟩ := G.uniform_incident_bound hq
  obtain ⟨K,hK⟩ := exists_nat_gt ((M:ℝ)/a)
  have hKpos : 0<K := by
    exact_mod_cast (lt_of_le_of_lt (div_nonneg (Nat.cast_nonneg M) ha.le) hK)
  have hMK : (M:ℝ)≤a*K := by
    have hh := (div_lt_iff₀ ha).mp hK
    linarith
  have hKdpos : (0:ℝ)<(K*d:ℕ) := by exact_mod_cast Nat.mul_pos hKpos (by omega : 0<d)
  obtain ⟨N,hN⟩ := exists_nat_gt (2*((K*d:ℕ):ℝ)/θ)
  have hNθ : 2*((K*d:ℕ):ℝ)≤(N:ℝ)*θ := ((div_lt_iff₀ hθ).mp hN).le
  obtain ⟨δ,hδ,hδ1,hδa,q,hqpos,hqc,hgood⟩ := hblock a ha N
  let T : ℕ → ℝ := fun n => δ^n*U
  let D : ℕ → Set V := fun n => G.safeBallDomain o (T n) R
  let S : ℕ → ℝ≥0∞ := fun n => G.seedExpectation q (D n) o
  have hTpos : ∀ n, 0<T n := fun n => mul_pos (pow_pos hδ n) hU
  have hTs : ∀ n, T (n+1)=δ*T n := by
    intro n
    dsimp [T]
    rw [pow_succ]
    ring
  have hTdec : ∀ n, T (n+1)≤T n := by
    intro n
    rw [hTs]
    exact mul_le_of_le_one_left (hTpos n).le hδ1.le
  have hTU : ∀ n, T n≤U := by
    intro n
    induction n with
    | zero => simp [T]
    | succ n ih => exact (hTdec n).trans ih
  have haT : ∀ n, a*T n≤1 := fun n =>
    (mul_le_mul_of_nonneg_left (hTU n) ha.le).trans haU
  have hD : ∀ n, D (n+1)⊆D n := fun n => G.safeBallDomain_mono o R (hTdec n)
  have hseed : ∀ n ω x, x∈G.entrySeeds (D n) o ω →
      x∉D (n+1) ∧ a*T n≤G.modularRatio x o ∧ G.modularRatio x o≤T n := by
    intro n ω x hx
    have hb := hband o (T n) (haT n) ω x hx
    refine ⟨?_,hb⟩
    intro hh
    have he := G.safeBallDomain_subset o (T (n+1)) R hh
    change G.modularRatio x o≤T (n+1) at he
    rw [hTs] at he
    nlinarith [hTpos n]
  have hprob : ∀ n x, (∃ ω, x∈G.entrySeeds (D n) o ω) →
      ENNReal.ofReal θ≤G.law q (G.boundedDomainFreshExitEvent (D n) (D (n+1))ᶜ x N M) := by
    rintro n x ⟨ω,hω⟩
    have hh := hgood (T n) (hTpos n) x hω.2 (hseed n ω x hω).2.1
    change θ<(G.law q (G.boundedDomainFreshExitEvent (D n)
      (G.safeBallDomain o (δ*T n) R)ᶜ x N M)).toReal at hh
    have he := ENNReal.ofReal_le_ofReal hh.le
    rw [ENNReal.ofReal_toReal (measure_ne_top _ _)] at he
    simpa only [D,hTs] using he
  obtain ⟨C,hC,hbound⟩ := G.subcritical_seedExpectation_bound hl hq q hqc o
  have hSFin : ∀ n, S n≠∞ := fun n => ne_top_of_le_ne_top hC (hbound (D n))
  have hstep : ∀ n, 2*(S n).toReal≤(S (n+1)).toReal := by
    intro n
    have he := G.expected_layer_expansion hc hl q hqc (D n) (D (n+1)) (hD n) o a (T n)
      ha (hTpos n) M N K d hMK hd (ENNReal.ofReal θ) (hseed n) (hprob n)
    have hf : ((K:ℝ≥0∞)*d)*S (n+1)≠∞ :=
      ENNReal.mul_ne_top (ENNReal.mul_ne_top (by simp) (by simp)) (hSFin (n+1))
    have hr := ENNReal.toReal_mono hf he
    change (((N:ℝ≥0∞)*ENNReal.ofReal θ)*S n).toReal≤
      (((K:ℝ≥0∞)*d)*S (n+1)).toReal at hr
    simp only [ENNReal.toReal_mul,ENNReal.toReal_natCast,ENNReal.toReal_ofReal hθ.le] at hr
    have hn := mul_le_mul_of_nonneg_right hNθ (ENNReal.toReal_nonneg (a := S n))
    push_cast at hn hKdpos
    nlinarith
  have hinit : 1≤(S 0).toReal := by
    have he := G.seedExpectation_self_le q (D 0) o (by simpa [D,T] using hstart o)
    have hh := ENNReal.toReal_mono (hSFin 0) he
    simpa using hh
  have hgrow : ∀ n : ℕ, (n:ℝ)+1≤(S n).toReal := by
    intro n
    induction n with
    | zero => simpa using hinit
    | succ n ih =>
      have hs := hstep n
      push_cast
      have hn : (0:ℝ)≤n := Nat.cast_nonneg n
      nlinarith
  obtain ⟨n,hn⟩ := exists_nat_gt C.toReal
  have hh := (hgrow n).trans (ENNReal.toReal_mono hC (hbound (D n)))
  linarith

theorem nonunimodular_no_percolation_at_criticality
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (hu : ¬G.CombinatoriallyUnimodular) (hpc : G.criticalProbability<1) :
    G.law G.criticalProbability G.percolates=0 := by
  let := G.countable_vertices hc hl
  let := G.countable_bonds hc hl
  obtain ⟨o⟩ := hc.nonempty
  apply G.no_critical_percolation_of_all_light hc hl hq hu hpc o
  intro v
  exact (G.nonunimodular_critical_mass_finite_ae hc hl hq hpc hu v).mono (fun _ h => (h v).ne)

end CriticalPercolation.BondGraph
end
end

end OAI
