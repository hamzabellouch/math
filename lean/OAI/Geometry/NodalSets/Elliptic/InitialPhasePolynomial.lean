import OAI.Geometry.NodalSets.Elliptic.PhaseJet
import OAI.Geometry.NodalSets.Elliptic.UniformEikonal

namespace OAI

namespace Yau.Jets
open MvPolynomial
noncomputable section

def linearPhase (v : Fin 4 → ℂ) : CPoly := ∑ i, C (v i) * X i

def quadraticPhase (H : Fin 4 → Fin 4 → ℂ) : CPoly :=
  C (1/2 : ℂ) * ∑ i, ∑ j, C (H i j) * X i * X j

lemma linearPhase_homogeneous (v : Fin 4 → ℂ) : (linearPhase v).IsHomogeneous 1 := by
  apply IsHomogeneous.sum
  intro i _
  exact isHomogeneous_C_mul_X _ _

lemma quadraticPhase_homogeneous (H : Fin 4 → Fin 4 → ℂ) :
    (quadraticPhase H).IsHomogeneous 2 := by
  unfold quadraticPhase
  apply IsHomogeneous.C_mul
  apply IsHomogeneous.sum
  intro i _
  apply IsHomogeneous.sum
  intro j _
  exact (isHomogeneous_C_mul_X _ _).mul (isHomogeneous_X ℂ j)

lemma pderiv_linearPhase (v : Fin 4 → ℂ) (i : Fin 4) :
    pderiv i (linearPhase v) = C (v i) := by
  simp [linearPhase, pderiv_X, Pi.single_apply]

lemma pderiv_quadraticPhase (H : Fin 4 → Fin 4 → ℂ)
    (hH : ∀ i j, H i j = H j i) (i : Fin 4) :
    pderiv i (quadraticPhase H) = ∑ j, C (H i j) * X j := by
  simp only [quadraticPhase, pderiv_mul, map_sum, pderiv_C, pderiv_X, Pi.single_apply,
    zero_mul, zero_add, Finset.sum_add_distrib]
  simp only [mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  have he : (∑ j, C (H j i) * X j) = ∑ j, C (H i j) * X j := by
    apply Finset.sum_congr rfl
    intro j _
    rw [hH j i]
  rw [he]
  have hs : (∑ x, ∑ j, if x = i then C (H x j) * X j else 0) =
      ∑ j, C (H i j) * X j := by
    rw [Finset.sum_comm]
    simp
  rw [hs, ← two_mul, ← mul_assoc]
  have hc : C (1/2 : ℂ) * (2:CPoly) = 1 := by
    calc
      _ = C ((1/2 : ℂ)*2) := by rw [map_mul]; congr 1
      _ = _ := by norm_num
  rw [hc, one_mul]

lemma pderiv_twice_quadraticPhase (H : Fin 4 → Fin 4 → ℂ)
    (hH : ∀ i j, H i j = H j i) (i j : Fin 4) :
    pderiv j (pderiv i (quadraticPhase H)) = C (H i j) := by
  rw [pderiv_quadraticPhase H hH]
  exact pderiv_linearPhase (H i) j

def initialPhaseJet (S : ℝ) (v : Fin 4 → ℂ) (H : Fin 4 → Fin 4 → ℂ) : Jet :=
  fun k ↦ if k = 0 then C (S : ℂ) else if k = 1 then linearPhase v
    else if k = 2 then quadraticPhase H else 0

lemma initialPhaseJet_homogeneous (S : ℝ) (v : Fin 4 → ℂ) (H : Fin 4 → Fin 4 → ℂ)
    (k : ℕ) : (initialPhaseJet S v H k).IsHomogeneous k := by
  unfold initialPhaseJet
  split_ifs with h0 h1 h2
  · subst k; exact isHomogeneous_C _ _
  · subst k; exact linearPhase_homogeneous v
  · subst k; exact quadraticPhase_homogeneous H
  · exact isHomogeneous_zero (Fin 4) ℂ k

lemma initialPhaseJet_first (S : ℝ) (v : Fin 4 → ℂ) (H : Fin 4 → Fin 4 → ℂ) (i : Fin 4) :
    pderiv i (initialPhaseJet S v H 1) = C (v i) := by
  simpa [initialPhaseJet] using pderiv_linearPhase v i

theorem initialPhaseJet_second (S : ℝ) (v : Fin 4 → ℂ)
    (H : Fin 4 → Fin 4 → ℂ) (hH : ∀ i j, H i j = H j i)
    (hcontract : ∀ j, ∑ i, v i * H i j = 0)
    (g : ℕ → Fin 4 → Fin 4 → CPoly) (hg : ∀ i j, g 1 i j = 0) :
    eikonalCoefficient v g 0 (initialPhaseJet S v H) = 0 := by
  have hd : (∑ i, C (v i) * pderiv i (quadraticPhase H)) = 0 := by
    simp_rw [pderiv_quadraticPhase H hH, Finset.mul_sum, ← mul_assoc, ← map_mul]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul, ← map_sum, hcontract, map_zero, zero_mul]
    simp
  rw [eikonalCoefficient_split, direction_two]
  simp [initialPhaseJet, eikonalKnown, hg, hd]

variable {T : Type*} [TopologicalSpace T]

lemma initialPhaseJet_continuous (S : T → ℝ) (v : T → Fin 4 → ℂ)
    (H : T → Fin 4 → Fin 4 → ℂ) (hS : Continuous S)
    (hv : ∀ i, Continuous (fun t ↦ v t i))
    (hH : ∀ i j, Continuous (fun t ↦ H t i j)) (k : ℕ) :
    ContinuousPolyFamily (fun t ↦ initialPhaseJet (S t) (v t) (H t) k) := by
  by_cases h0 : k = 0
  · subst k
    simpa [initialPhaseJet] using ContinuousPolyFamily.C (Complex.continuous_ofReal.comp hS)
  by_cases h1 : k = 1
  · subst k
    simp only [initialPhaseJet, Nat.one_ne_zero, ite_false, ite_true]
    exact ContinuousPolyFamily.sum Finset.univ (fun i _ ↦
      (ContinuousPolyFamily.C (hv i)).mul (.const (X i)))
  by_cases h2 : k = 2
  · subst k
    simp only [initialPhaseJet, show (2:ℕ) ≠ 0 by omega, show (2:ℕ) ≠ 1 by omega, ite_false, ite_true]
    exact (ContinuousPolyFamily.const (C (1/2 : ℂ))).mul
      (ContinuousPolyFamily.sum Finset.univ (fun i _ ↦
        ContinuousPolyFamily.sum Finset.univ (fun j _ ↦
          ((ContinuousPolyFamily.C (hH i j)).mul (.const (X i))).mul (.const (X j)))))
  · simpa [initialPhaseJet, h0, h1, h2] using (ContinuousPolyFamily.const (0:CPoly) :
      ContinuousPolyFamily (fun _ : T ↦ (0:CPoly)))

end
end Yau.Jets

end OAI
