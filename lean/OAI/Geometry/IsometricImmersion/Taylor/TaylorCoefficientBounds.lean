import OAI.Geometry.IsometricImmersion.Taylor.TaylorQJetBounds

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology BigOperators Matrix

namespace SmoothLocal.Taylor
open SmoothLocal.Geometry SmoothLocal.HighEquation

def initialAxisCLM : ℝ →L[ℝ] Coord :=
  ContinuousLinearMap.pi (fun i => if i = 0 then ContinuousLinearMap.id ℝ ℝ else 0)

theorem initialAxisCLM_eq (x : ℝ) : initialAxisCLM x = (![x, 0] : Coord) := by
  ext i
  fin_cases i <;> simp [initialAxisCLM]

theorem initialAxisCLM_norm_le : ‖initialAxisCLM‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  rw [one_mul, initialAxisCLM_eq]
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg x)).mpr
  intro i
  fin_cases i
  · exact le_rfl
  · simp

theorem initialAxis_add (x a : ℝ) : initialAxisCLM x + (![0, a] : Coord) = ![x, a] := by
  rw [initialAxisCLM_eq]
  ext i
  fin_cases i <;> simp

theorem norm_initial_slice_jet_le {f : Coord → ℝ} {V : Set Coord}
    (hf : ContDiffOn ℝ ∞ f V) (hV : IsOpen V) (a x : ℝ)
    (hp : (![x, a] : Coord) ∈ V) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (fun y => f ![y, a]) x‖ ≤ ‖iteratedFDeriv ℝ k f ![x, a]‖ := by
  let shift : Coord → Coord := fun p => p + ![0, a]
  have hshift : ContDiff ℝ ∞ shift := contDiff_id.add contDiff_const
  have hpre : IsOpen (shift ⁻¹' V) := hV.preimage hshift.continuous
  have hfs : ContDiffOn ℝ ∞ (f ∘ shift) (shift ⁻¹' V) :=
    hf.comp hshift.contDiffOn (fun _ hp => hp)
  have hpoint : initialAxisCLM x ∈ shift ⁻¹' V := by
    change initialAxisCLM x + ![0, a] ∈ V
    rw [initialAxis_add]
    exact hp
  have hb := norm_iteratedFDeriv_comp_contraction initialAxisCLM hfs hpre
    initialAxisCLM_norm_le hpoint k
  have he : (f ∘ shift) ∘ initialAxisCLM = (fun y => f ![y, a]) := by
    funext y
    change f (initialAxisCLM y + ![0, a]) = f ![y, a]
    rw [initialAxis_add]
  rw [he] at hb
  change ‖iteratedFDeriv ℝ k (fun y => f ![y, a]) x‖ ≤
    ‖iteratedFDeriv ℝ k (fun p => f (p + ![0, a])) (initialAxisCLM x)‖ at hb
  rw [iteratedFDeriv_comp_add_right, initialAxis_add] at hb
  exact hb

theorem norm_verticalJet_fullJet_le {f : Coord → ℝ} {V : Set Coord}
    (hf : ContDiffOn ℝ ∞ f V) (hV : IsOpen V) {p : Coord} (hp : p ∈ V)
    (n k : ℕ) :
    ‖iteratedFDeriv ℝ k (verticalJet f n) p‖ ≤ ‖iteratedFDeriv ℝ (k + n) f p‖ := by
  induction n generalizing k with
  | zero => simpa only [verticalJet, Nat.add_zero] using le_rfl
  | succ n hn =>
    have hb := (norm_iteratedFDeriv_coordPartial_le (verticalJet_contDiffOn hV hf n)
      hV hp 1 k).trans (hn (k + 1))
    have he : k + 1 + n = k + (n + 1) := by omega
    rw [he] at hb
    exact hb

theorem nextTaylorCoefficient_fullJet_le {g : MetricField} {U : Set Coord}
    {P : Coord → ℝ} {I : Set ℝ} (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (hI : IsOpen I) (hP : ContDiffOn ℝ ∞ P (spatialStrip I))
    (a x : ℝ) (hx : x ∈ I) (hpU : (![x, a] : Coord) ∈ U)
    (hxx : covHessian g P ![x, a] 0 0 ≠ 0) (n k : ℕ) :
    ‖iteratedFDeriv ℝ k (nextTaylorCoefficient g a P n) x‖ ≤
      ‖iteratedFDeriv ℝ (k + n) (qResidual g P) ![x, a]‖ := by
  have hD := comparisonDomain_isOpen hg hU hI hP
  have hR := qResidual_contDiffOn hg hU hI hP
  have hp := mem_comparisonDomain hx hpU hxx
  change ‖iteratedFDeriv ℝ k (-(fun y => verticalJet (qResidual g P) n ![y, a])) x‖ ≤ _
  rw [iteratedFDeriv_neg_apply, norm_neg]
  exact (norm_initial_slice_jet_le (verticalJet_contDiffOn hD hR n) hD a x hp k).trans
    (norm_verticalJet_fullJet_le hR hD hp n k)

theorem exists_uniform_nextTaylorCoefficient_bound {g : MetricField} {U S : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hS : IsCompact S) (hSU : S ⊆ U)
    (M : ℝ) (hM : 0 ≤ M) {c : ℝ} (hc : 0 < c) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (P : Coord → ℝ) (I : Set ℝ), IsOpen I →
      ContDiffOn ℝ ∞ P (spatialStrip I) → ∀ a x : ℝ, x ∈ I → (![x, a] : Coord) ∈ S →
      ‖qSolutionJet P ![x, a]‖ ≤ M → c ≤ |covHessian g P ![x, a] 0 0| →
      ∀ n k : ℕ, k + n ≤ N → ∀ B : ℝ,
      (∀ j ≤ k + n + 2, ‖iteratedFDeriv ℝ j P ![x, a]‖ ≤ B) →
      ‖iteratedFDeriv ℝ k (nextTaylorCoefficient g a P n) x‖ ≤
        B + ((k + n).factorial : ℝ) * C * (max 1 B)^(k + n) := by
  obtain ⟨C, hC, hbound⟩ := exists_uniform_qResidual_fullJet_bound hg hU hS hSU M hM hc N
  refine ⟨C, hC, ?_⟩
  intro P I hI hP a x hx hpS hstate hden n k hkn B hB
  have hxx : covHessian g P ![x, a] 0 0 ≠ 0 := by
    intro h
    rw [h, abs_zero] at hden
    linarith
  exact (nextTaylorCoefficient_fullJet_le hg hU hI hP a x hx (hSU hpS) hxx n k).trans
    (hbound P I hI hP ![x, a] hx hpS hstate hden (k + n) hkn B hB)

end SmoothLocal.Taylor

end

end OAI
