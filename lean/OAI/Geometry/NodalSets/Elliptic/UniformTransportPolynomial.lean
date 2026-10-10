import OAI.Geometry.NodalSets.Elliptic.FiniteAmplitude
import OAI.Geometry.NodalSets.Elliptic.UniformTransport

namespace OAI

namespace Yau.Jets
open MvPolynomial
noncomputable section
variable {T : Type*} [TopologicalSpace T]

theorem finite_transport_polynomials_continuous
    (w : T → Fin 4 → ℂ) (hw : ∀ j, Continuous (fun t ↦ w t j))
    (i : Fin 4) (hi : ∀ t, w t i ≠ 0)
    (W : T → ℕ → Fin 4 → CPoly) (c : T → Jet)
    (g : T → ℕ → Fin 4 → Fin 4 → CPoly) (b : T → ℕ → Fin 4 → CPoly)
    (hW : ∀ r i, ContinuousPolyFamily (fun t ↦ W t r i))
    (hc : ∀ r, ContinuousPolyFamily (fun t ↦ c t r))
    (hg : ∀ r i j, ContinuousPolyFamily (fun t ↦ g t r i j))
    (hb : ∀ r i, ContinuousPolyFamily (fun t ↦ b t r i)) (m J : ℕ) :
    ∃ P : ℕ → T → CPoly,
      (∀ j, ContinuousPolyFamily (P j)) ∧
      (∀ j t, polynomialJet (P j t) 0 = if j = 0 then 1 else 0) ∧
      (∀ j t k, m + 1 + 2 * (J - j) < k → polynomialJet (P j t) k = 0) ∧
      (∀ t n, n < m + 1 + 2 * J →
        transportCoefficient (w t) (W t) (c t) 0 n (polynomialJet (P 0 t)) = 0) ∧
      ∀ j, j < J → ∀ t n, n < m + 1 + 2 * (J - (j + 1)) →
        transportCoefficient (w t) (W t) (c t)
          (fun k ↦ -secondOrderCoefficient (g t) (b t) (polynomialJet (P j t)) k)
          n (polynomialJet (P (j + 1) t)) = 0 := by
  obtain ⟨A, hA, hAc, hzero, hfirst, hnext⟩ :=
    transport_tower_continuous w hw i hi W c g b hW hc hg hb m J
  let d : ℕ → ℕ := fun j ↦ m + 1 + 2 * (J - j)
  let P : ℕ → T → CPoly := fun j t ↦ truncateJet (A j t) (d j)
  have heq (j : ℕ) (t : T) (k : ℕ) (hk : k ≤ d j) :
      polynomialJet (P j t) k = A j t k := polynomialJet_truncate_eq _ (hA j t) _ _ hk
  refine ⟨P, fun j ↦ ContinuousPolyFamily.sum _ (fun k _ ↦ hAc j k), ?_, ?_, ?_, ?_⟩
  · intro j t
    rw [heq j t 0 (Nat.zero_le _), hzero]
  · intro j t k hk
    exact (polynomialJet_truncate (A j t) (hA j t) _ _).trans (ite_eq_right (by dsimp [d]; omega))
  · intro t n hn
    rw [transportCoefficient_congr (w t) (W t) (c t) 0 0 n _ (A 0 t)
      (fun k hk ↦ heq 0 t k (by dsimp [d]; omega)) rfl]
    exact hfirst t n hn
  · intro j hj t n hn
    have hd : d j = d (j + 1) + 2 := (wave_degree_budgets m J j hj).1
    have hforce : -secondOrderCoefficient (g t) (b t) (polynomialJet (P j t)) n =
        -secondOrderCoefficient (g t) (b t) (A j t) n := by
      rw [secondOrderCoefficient_congr (g t) (b t) _ (A j t) n
        (fun k hk ↦ heq j t k (by dsimp [d] at *; omega))]
    rw [transportCoefficient_congr (w t) (W t) (c t) _
      (fun k ↦ -secondOrderCoefficient (g t) (b t) (A j t) k) n _ (A (j + 1) t)
      (fun k hk ↦ heq (j + 1) t k (by dsimp [d]; omega)) hforce]
    exact hnext j t n hn

lemma ContinuousPolyFamily.comp {S : Type*} [TopologicalSpace S]
    {P : T → CPoly} (hp : ContinuousPolyFamily P) {f : S → T} (hf : Continuous f) :
    ContinuousPolyFamily (fun s ↦ P (f s)) := by
  obtain ⟨r, hr⟩ := hp.2
  exact ⟨fun d ↦ (hp.1 d).comp hf, r, fun s ↦ hr (f s)⟩

lemma finiteAmplitude_reval (A : ℕ → CPoly) (J : ℕ) (N : ℝ) :
    finiteAmplitude A J N = reval (∑ j : Fin (J + 1), ((N⁻¹ : ℝ) : ℂ)^j.val • A j.val) := by
  funext x
  simp [finiteAmplitude, polynomialFamily, reval, Algebra.smul_def]

theorem finiteAmplitude_parameter_uniform_derivative_bound
    (A : ℕ → T → CPoly) (hA : ∀ j, ContinuousPolyFamily (A j))
    (J k : ℕ) (s : Set T) (hs : IsCompact s) (R : ℝ) :
    ∃ C > 0, ∀ t ∈ s, ∀ N : ℝ, 1 ≤ N → ∀ x : Coord, ‖x‖ ≤ R →
      ‖iteratedFDeriv ℝ k (finiteAmplitude (fun j ↦ A j t) J N) x‖ ≤ C := by
  let P : T × ℝ → CPoly := fun z ↦
    ∑ j : Fin (J + 1), (z.2 : ℂ)^j.val • A j.val z.1
  have hP : ContinuousPolyFamily P := by
    apply ContinuousPolyFamily.sum
    intro j _
    exact ((hA j.val).comp continuous_fst).smul
      ((Complex.continuous_ofReal.comp continuous_snd).pow j.val)
  obtain ⟨C, hC, hb⟩ := hP.uniform_derivative_bound
    (s ×ˢ Set.Icc (0 : ℝ) 1) (hs.prod isCompact_Icc) R k
  refine ⟨C, hC, ?_⟩
  intro t ht N hN x hx
  rw [finiteAmplitude_reval]
  exact hb (t, N⁻¹) ⟨ht, inv_nonneg.mpr (le_trans zero_le_one hN), inv_le_one_of_one_le₀ hN⟩ x hx

end
end Yau.Jets

end OAI
