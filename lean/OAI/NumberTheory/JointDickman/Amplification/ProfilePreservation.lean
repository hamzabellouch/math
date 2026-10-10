import OAI.NumberTheory.JointDickman.Probability.ResidueProfiles

namespace OAI

/-! # Preservation of every bounded residue profile by moving-prime weights -/

namespace JointDickman
open Finset Filter
open scoped Topology

namespace ResidueProfile

noncomputable def mean (W : ResidueProfile) : ℂ := residueMean (W.value 1)

noncomputable def correlation (W : ResidueProfile) (q : ℕ+) (f : ZMod (q : ℕ) → ℂ) : ℂ :=
  residueMean (fun a => W.value q a * f a)

theorem mean_eq (W : ResidueProfile) (q : ℕ+) : residueMean (W.value q) = W.mean := by
  have h := W.compatible 1 q (one_dvd _) (fun _ => 1)
  simpa only [residueLift, mul_one, mean] using h

theorem correlation_error (W : ResidueProfile) (d q : ℕ+) (f : ZMod (q : ℕ) → ℂ)
    (hcop : (d : ℕ).Coprime q) :
    W.correlation q f - W.mean * residueMean f =
      residueMean (fun a : ZMod ((d*q : ℕ+) : ℕ) =>
        (W.value (d*q) a - residueLift (W.value d) a) * residueLift f a) := by
  have hc := W.compatible q (d*q) (dvd_mul_left _ _) f
  have hi := residueMean_crt hcop (W.value d) f
  have he (a : ZMod ((d : ℕ) * (q : ℕ))) :
      (ZMod.chineseRemainder hcop) a = ((a.val : ZMod (d : ℕ)), (a.val : ZMod (q : ℕ))) := by
    calc
      _ = (ZMod.chineseRemainder hcop) (a.val : ZMod ((d : ℕ) * (q : ℕ))) :=
        congrArg _ (ZMod.natCast_zmod_val a).symm
      _ = _ := by simp only [map_natCast]; rfl
  simp only [he] at hi
  rw [W.mean_eq d] at hi
  change residueMean (fun a => W.value q a * f a) - W.mean * residueMean f = _
  rw [← hc, ← hi]
  simp only [residueMean, residueLift, sub_mul, sum_sub_distrib, sub_div, PNat.mul_coe]
  rfl

theorem preservation (W : ResidueProfile) (Q : ℕ → ℕ+)
    (f : (B : ℕ) → ZMod (Q B : ℕ) → ℂ)
    (hcop : ∀ d : ℕ+, ∀ᶠ B : ℕ in atTop, (d : ℕ).Coprime (Q B))
    (hmoment : ∃ K : ℝ, 0 < K ∧ ∀ᶠ B : ℕ in atTop, residueEnergy (f B) ≤ K) :
    Tendsto (fun B => W.correlation (Q B) (f B) - W.mean * residueMean (f B))
      atTop (nhds 0) := by
  obtain ⟨K,hK,hb⟩ := hmoment
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨d,hd⟩ := W.exists_approximation (div_pos (sq_pos_of_pos hε) hK)
  filter_upwards [hcop d, hb] with B hcopB hB
  rw [dist_zero_right, W.correlation_error d (Q B) (f B) hcopB]
  have hcs := residueMean_mul_norm_sq
    (fun a : ZMod ((d*Q B : ℕ+) : ℕ) =>
      W.value (d*Q B) a - residueLift (W.value d) a)
    (residueLift (q := ((d*Q B : ℕ+) : ℕ)) (f B))
  have hel : residueEnergy (residueLift (q := ((d*Q B : ℕ+) : ℕ)) (f B)) =
      residueEnergy (f B) := residueEnergy_lift (d := (Q B : ℕ))
        (q := ((d*Q B : ℕ+) : ℕ)) (dvd_mul_left _ _) (f B)
  rw [hel] at hcs
  have he := hd (d*Q B) (dvd_mul_right _ _)
  have hm := mul_le_mul_of_nonneg_left hB
    (residueEnergy_nonneg (fun a => W.value (d*Q B) a - residueLift (W.value d) a))
  have hlt := mul_lt_mul_of_pos_right he hK
  rw [div_mul_cancel₀ _ (ne_of_gt hK)] at hlt
  nlinarith [norm_nonneg (residueMean (fun a : ZMod ((d*Q B : ℕ+) : ℕ) =>
    (W.value (d*Q B) a - residueLift (W.value d) a) * residueLift (f B) a))]

end ResidueProfile
end JointDickman

end OAI
