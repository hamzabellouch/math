import OAI.GroupTheory.PolycyclicRecognition.Algebra.EigenlineCones
import OAI.GroupTheory.PolycyclicRecognition.Geometry.LinearContractingPingPong

namespace OAI

/-! # Ping-pong from transverse eigenline cones

The source-cone constants are constructed from the actual functionals and
vectors. Only the spectral gaps, transversality and disjointness of the
specified cones remain as geometric data.
-/

noncomputable section
namespace PolycyclicRecognition

variable {G V : Type} [Group G] [NormedAddCommGroup V] [NormedSpace ℝ V]
    [MulAction G V]

theorem free_powers_of_transverse_eigenline_cones
    (ρ : G →* (V →L[ℝ] V)) (hact : ∀ g x, ρ g x = g • x)
    (a : Bool → G) (φ : Bool → Bool → V →L[ℝ] ℝ) (v : Bool → Bool → V)
    (μ b : Bool → Bool → ℝ) (ε : ℝ) (hε : 0 < ε)
    (hv : ∀ i s, ρ (signedPingPongGenerator a i s) (v i s) = μ i s • v i s)
    (hφv : ∀ i s, φ i s (v i s) = 1)
    (hφ : ∀ i s x, φ i s (ρ (signedPingPongGenerator a i s) x) = μ i s * φ i s x)
    (hb : ∀ i s, 0 ≤ b i s) (hgap : ∀ i s, b i s < |μ i s|)
    (hker : ∀ i s x, φ i s x = 0 →
      ‖ρ (signedPingPongGenerator a i s) x‖ ≤ b i s * ‖x‖)
    (htrans : ∀ i s j t, i ≠ j → ‖φ i s‖ * ε < |φ i s (v j t)|)
    (hsep : ∀ i j, i ≠ j → ∀ s t,
      Disjoint (eigenlineCone (φ i s) (v i s) ε) (eigenlineCone (φ j t) (v j t) ε)) :
    ∃ N : ℕ, 0 < N ∧ Function.Injective (FreeGroup.lift (fun i => (a i) ^ N)) := by
  let D (i : Bool) := eigenlineCone (φ i false) (v i false) ε ∪
    eigenlineCone (φ i true) (v i true) ε
  let Q (i s : Bool) (p : Bool × Bool) : ℝ :=
    (‖v p.1 p.2‖ + ε) / (|φ i s (v p.1 p.2)| - ‖φ i s‖ * ε) + ‖v i s‖
  let M (i s : Bool) := sSup (Set.range (Q i s))
  have hM (i s j t : Bool) : Q i s (j, t) ≤ M i s :=
    le_csSup (Set.finite_range (Q i s)).bddAbove (Set.mem_range_self (j, t))
  apply free_powers_of_dominant_eigenlines ρ hact a D φ v μ b M (fun _ _ => ε)
  · intro i
    have hv0 : v i false ≠ 0 := by
      intro hz
      have h := hφv i false
      rw [hz, map_zero] at h
      exact zero_ne_one h
    refine ⟨v i false, Or.inl ⟨hv0, ?_⟩⟩
    simp only [eigenlineRemainder, hφv, one_smul, sub_self, norm_zero, abs_one, mul_one]
    exact le_of_lt hε
  · intro i j hij
    exact Disjoint.union_left
      (Disjoint.union_right (hsep i j hij false false) (hsep i j hij false true))
      (Disjoint.union_right (hsep i j hij true false) (hsep i j hij true true))
  · exact hv
  · exact hφv
  · exact hφ
  · exact hb
  · exact hgap
  · exact hker
  · exact fun _ _ => hε
  · intro i s j hij x hx
    have ht : ∃ t, x ∈ eigenlineCone (φ j t) (v j t) ε := by
      rcases hx with hx | hx
      · exact ⟨false, hx⟩
      · exact ⟨true, hx⟩
    obtain ⟨t, hxt⟩ := ht
    refine ⟨eigenline_cone_transverse_nonzero (φ j t) (φ i s) (v j t) ε
      (htrans i s j t hij) hxt, ?_⟩
    have hn := eigenline_cone_transverse_bound (φ j t) (φ i s) (v j t) x ε
      (le_of_lt hε) (htrans i s j t hij) hxt.2
    calc
      ‖eigenlineRemainder (φ i s) (v i s) x‖ ≤ ‖x‖ + |φ i s x| * ‖v i s‖ := by
        simpa only [eigenlineRemainder, norm_smul, Real.norm_eq_abs] using
          norm_sub_le x (φ i s x • v i s)
      _ ≤ Q i s (j, t) * |φ i s x| := by
        dsimp only [Q]
        nlinarith only [hn]
      _ ≤ M i s * |φ i s x| :=
        mul_le_mul_of_nonneg_right (hM i s j t) (abs_nonneg _)
  · intro i s x hx0 hx
    have hxn : x ≠ 0 := by
      intro hz
      exact hx0 (by rw [hz, map_zero])
    cases s
    · exact Or.inl ⟨hxn, hx⟩
    · exact Or.inr ⟨hxn, hx⟩

end PolycyclicRecognition

end

end OAI
