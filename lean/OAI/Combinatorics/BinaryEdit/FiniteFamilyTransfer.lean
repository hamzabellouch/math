import OAI.Combinatorics.BinaryEdit.FiniteCapTransfer
import OAI.Combinatorics.BinaryEdit.EncodedImage

namespace OAI

noncomputable section
namespace TreeEdit.BinaryLower

universe u

/-- Original word length before the quadratic-width binary conversion. -/
def finiteSourceLength (k : ℕ) : ℕ := (20 * k * k ^ (20 * k)) ^ k

lemma le_finiteSourceLength {k : ℕ} (hk : 0 < k) : k ≤ finiteSourceLength k := by
  have hp : 1 ≤ k ^ (20 * k) := Nat.one_le_pow _ _ hk
  have hb : k ≤ 20 * k * k ^ (20 * k) := by
    have := Nat.mul_le_mul_left (20 * k) hp
    nlinarith
  exact hb.trans (Nat.le_pow hk)

lemma finiteSourceLength_mul_sq (k : ℕ) :
    finiteSourceLength k * finiteSourceLength k ^ 2 = Parameters.finiteLength k := by
  unfold finiteSourceLength Parameters.finiteLength
  calc
    _ = ((20 * k * k ^ (20 * k)) ^ k) ^ 3 := by ring
    _ = (20 * k * k ^ (20 * k)) ^ (k * 3) := (pow_mul _ _ _).symm
    _ = _ := by rw [Nat.mul_comm k 3]

/-- A finite-alphabet lower bound transfers to the all-cap binary lower bound
through a fixed-width binary code. -/
theorem binary_lower_bound_of_finite_source_family
    (hcode : ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
      ∀ (Γ : Type u) [Fintype Γ],
        1 ≤ Fintype.card Γ → Fintype.card Γ ≤ M →
        ∃ c : Γ → Word Bool (M ^ 2), ∀ x y : Word Γ M,
          (((M ^ 2 : ℕ) : ℝ) / 804) * (ed x.val y.val : ℝ) ≤
            (ed (encode c x.val) (encode c y.val) : ℝ))
    (hfamily : ∃ c₀ : ℝ, 0 < c₀ ∧ ∃ K : ℕ, ∀ k : ℕ, K ≤ k →
      ∃ Γ : Type u, ∃ inst : Fintype Γ,
        1 ≤ @Fintype.card Γ inst ∧ @Fintype.card Γ inst ≤ finiteSourceLength k ∧
        ∃ W : Finset (Word Γ (finiteSourceLength k)), 2 ≤ W.card ∧
          c₀ * ((k : ℝ) / 4) ^ k ≤
            c1 {x : Word Γ (finiteSourceLength k) // x ∈ W}
              (fun x y => (ed x.val.val y.val.val : ℝ))) :
    ∃ c : ℝ, 0 < c ∧ ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
      ∃ n : ℕ, 1 ≤ n ∧ n ≤ d ∧
        ∃ W : Finset (Word Bool n), 2 ≤ W.card ∧
          growth c d ≤ binarySetDistortion W := by
  obtain ⟨M₀, hcode⟩ := hcode
  obtain ⟨c₀, hc₀, K, hfamily⟩ := hfamily
  apply binary_lower_bound_of_finite_family
  refine ⟨c₀ / 804, by positivity, max K (max M₀ 1), ?_⟩
  intro k hk
  have hkK : K ≤ k := (le_max_left _ _).trans hk
  have hkM : M₀ ≤ k := (le_max_left M₀ 1).trans ((le_max_right _ _).trans hk)
  have hk1 : 1 ≤ k := (le_max_right M₀ 1).trans ((le_max_right _ _).trans hk)
  have hMk : k ≤ finiteSourceLength k := le_finiteSourceLength hk1
  obtain ⟨Γ, inst, hΓ1, hΓM, W, hW, hdist⟩ := hfamily k hkK
  let : Fintype Γ := inst
  obtain ⟨c, hc⟩ := hcode (finiteSourceLength k) (hkM.trans hMk) Γ hΓ1 hΓM
  have hP : 0 < finiteSourceLength k ^ 2 := by
    have : 0 < finiteSourceLength k := hk1.trans hMk
    positivity
  obtain ⟨V, hV, hVdist⟩ := exists_binary_image_of_code c hP W hW hc
  have hresult : ∃ V : Finset (Word Bool (finiteSourceLength k * finiteSourceLength k ^ 2)),
      2 ≤ V.card ∧ (c₀ / 804) * ((k : ℝ) / 4) ^ k ≤ binarySetDistortion V := by
    refine ⟨V, hV, ?_⟩
    calc
      _ = (c₀ * ((k : ℝ) / 4) ^ k) / 804 := by ring
      _ ≤ c1 {x : Word Γ (finiteSourceLength k) // x ∈ W}
          (fun x y => (ed x.val.val y.val.val : ℝ)) / 804 :=
        div_le_div_of_nonneg_right hdist (by norm_num)
      _ ≤ binarySetDistortion V := hVdist
  rw [finiteSourceLength_mul_sq] at hresult
  exact hresult

end TreeEdit.BinaryLower

end

end OAI
