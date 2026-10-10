import OAI.Probability.FreeIsing.Trees.Shells

namespace OAI

noncomputable section

namespace Problem367

def restrictedTreeCut {d : ℕ} (allowed : Finset (Fin d)) (k : ℕ) :
    Finset (TreeShell d (k + 1)) :=
  (allowed.sigma (fun c => (Finset.univ : Finset (ReducedTail c k)))).map
    (treeShellSuccEquiv d k).symm.toEmbedding

@[simp] theorem mem_restrictedTreeCut {d k : ℕ} (allowed : Finset (Fin d))
    (v : TreeShell d (k + 1)) :
    v ∈ restrictedTreeCut allowed k ↔ (treeShellSuccEquiv d k v).1 ∈ allowed := by
  classical
  simp [restrictedTreeCut]

@[simp] theorem card_restrictedTreeCut {d : ℕ} (allowed : Finset (Fin d)) (k : ℕ) :
    (restrictedTreeCut allowed k).card = allowed.card * (d - 1) ^ k := by
  classical
  simp [restrictedTreeCut, Finset.card_sigma]

def avoidingTreeCut {d : ℕ} (forbidden : Finset (Fin d)) (k : ℕ) :
    Finset (TreeShell d (k + 1)) :=
  restrictedTreeCut (Finset.univ \ forbidden) k

@[simp] theorem mem_avoidingTreeCut {d k : ℕ} (forbidden : Finset (Fin d))
    (v : TreeShell d (k + 1)) :
    v ∈ avoidingTreeCut forbidden k ↔ (treeShellSuccEquiv d k v).1 ∉ forbidden := by
  classical
  simp [avoidingTreeCut]

@[simp] theorem card_avoidingTreeCut {d : ℕ} (forbidden : Finset (Fin d)) (k : ℕ) :
    (avoidingTreeCut forbidden k).card = (d - forbidden.card) * (d - 1) ^ k := by
  classical
  simp [avoidingTreeCut, Finset.card_sdiff]

theorem pow_le_card_avoidingTreeCut {d : ℕ} (forbidden : Finset (Fin d))
    (hF : forbidden.card ≤ 1) (k : ℕ) :
    (d - 1) ^ (k + 1) ≤ (avoidingTreeCut forbidden k).card := by
  rw [card_avoidingTreeCut, pow_succ, Nat.mul_comm]
  exact Nat.mul_le_mul_right _ (by omega)

theorem avoidingTreeCut_nonempty {d : ℕ} (hd : 2 ≤ d)
    (forbidden : Finset (Fin d)) (hF : forbidden.card ≤ 1) (k : ℕ) :
    (avoidingTreeCut forbidden k).Nonempty := by
  apply Finset.card_pos.mp
  exact lt_of_lt_of_le (pow_pos (by omega : 0 < d - 1) _)
    (pow_le_card_avoidingTreeCut forbidden hF k)

theorem rpow_le_card_avoidingTreeCut {d : ℕ} (hd : 2 ≤ d)
    (forbidden : Finset (Fin d)) (hF : forbidden.card ≤ 1) (k : ℕ)
    {ℓ : ℝ} (hlevel : ℓ / 2 - 1 ≤ (k + 1 : ℕ)) :
    ((d : ℝ) - 1) ^ (ℓ / 2 - 1) ≤ ((avoidingTreeCut forbidden k).card : ℝ) := by
  have hd1 : 1 ≤ (d : ℝ) - 1 := by
    have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hcast : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 :=
    by rw [Nat.cast_sub (show 1 ≤ d by omega), Nat.cast_one]
  calc
    ((d : ℝ) - 1) ^ (ℓ / 2 - 1) ≤ ((d : ℝ) - 1) ^ ((k + 1 : ℕ) : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hd1 hlevel
    _ = (((d - 1) ^ (k + 1) : ℕ) : ℝ) := by
      rw [Real.rpow_natCast, Nat.cast_pow, hcast]
    _ ≤ _ := by exact_mod_cast pow_le_card_avoidingTreeCut forbidden hF k

theorem half_length_rpow_le_card_avoidingTreeCut {d : ℕ} (hd : 2 ≤ d)
    (forbidden : Finset (Fin d)) (hF : forbidden.card ≤ 1)
    (ℓ : ℕ) (hℓ : 2 ≤ ℓ) :
    ((d : ℝ) - 1) ^ ((ℓ : ℝ) / 2 - 1) ≤
      ((avoidingTreeCut forbidden (ℓ / 2 - 1)).card : ℝ) := by
  apply rpow_le_card_avoidingTreeCut hd forbidden hF
  have hn : ℓ / 2 - 1 + 1 = ℓ / 2 := by omega
  rw [hn]
  have hround : ℓ ≤ 2 * (ℓ / 2) + 1 := by omega
  have hr : (ℓ : ℝ) ≤ 2 * (ℓ / 2 : ℕ) + 1 := by exact_mod_cast hround
  linarith

theorem attenuation_le_quarter_threshold {c η x : ℝ}
    (hx : 0 ≤ x) (hη : η ≤ c / 4) (hlength : 8 * Real.log 2 ≤ c * x) :
    Real.exp (-c * x / 2) ≤ Real.exp (-η * x) / 4 := by
  have hlog : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  apply (le_div_iff₀ (show (0 : ℝ) < 4 by norm_num)).mpr
  conv_lhs => rhs; rw [← Real.exp_log (show (0 : ℝ) < 4 by norm_num)]
  rw [← Real.exp_add, hlog]
  apply Real.exp_le_exp.mpr
  nlinarith [mul_le_mul_of_nonneg_right hη hx]

end Problem367

end

end OAI
