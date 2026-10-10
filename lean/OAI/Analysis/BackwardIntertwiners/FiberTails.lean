import OAI.Analysis.BackwardIntertwiners.WeightSeparation

namespace OAI

namespace BackwardIntertwiners
open Filter
open scoped Topology
noncomputable section

abbrev Fiber := lp (fun _ : ℤ => ℂ) 2


def coordinateTail (h : ℤ) : Submodule ℂ Fiber where
  carrier := {v | ∀ j : ℤ, j < h → v j = 0}
  zero_mem' := by simp
  add_mem' := by intro v z hv hz j hj; simp [hv j hj, hz j hj]
  smul_mem' := by intro a v hv j hj; simp [hv j hj]

lemma fiber_exists_coordinate {v : Fiber} (hv : v ≠ 0) : ∃ j : ℤ, v j ≠ 0 := by
  by_contra! h
  apply hv
  ext j
  exact h j

lemma weighted_shift_pow {w : ℤ → ℝ} (hw : ∀ j, 0 < w j)
    {T : Fiber →L[ℂ] Fiber}
    (hT : ∀ v j, T v j = (w j / w (j-1) : ℂ) * v (j-1))
    (n : ℕ) (v : Fiber) (j : ℤ) :
    (T^n) v j = (w j / w (j-(n:ℤ)) : ℂ) * v (j-(n:ℤ)) := by
  have hwC (k : ℤ) : (w k:ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (hw k))
  induction n generalizing j with
  | zero => simp [hwC]
  | succ n ih =>
    rw [pow_succ']
    change T ((T^n) v) j = _
    rw [hT, ih]
    have hi : j-1-(n:ℤ) = j-((n+1:ℕ):ℤ) := by omega
    rw [hi]
    field_simp [hwC]

lemma invariant_pow {T : Fiber →L[ℂ] Fiber} {L : Submodule ℂ Fiber}
    (hi : ∀ v ∈ L, T v ∈ L) {v : Fiber} (hv : v ∈ L) (n : ℕ) : (T^n) v ∈ L := by
  induction n with
  | zero => simpa using hv
  | succ n ih => simpa only [pow_succ', mul_apply_eq_comp] using hi _ ih



lemma SupportSeparation.strict_order {w : ℤ → ℝ} (hsep : SupportSeparation w)
    {b c : ℤ → ℂ} (hbn : ∃ j, b j ≠ 0) (hcn : ∃ j, c j ≠ 0)
    {B C : ℝ} (hB : 0 < B) (hC : 0 < C)
    (hb : ∀ j, ‖b j‖ ≤ B*w j) (hc : ∀ j, ‖c j‖*w j ≤ C)
    (hz : ∀ r : ℕ, (∑' j : ℤ, b j * c (j-r)) = 0)
    {i j : ℤ} (hbi : b i ≠ 0) (hcj : c j ≠ 0) : i < j := by
  obtain ⟨t, h, hbt, hch, hbmax, hcmin, hth⟩ :=
    hsep.of_bounded hbn hcn hB hC hb hc (fun r _ => hz r)
  have hit : i ≤ t := by by_contra! hh; exact hbi (hbmax i hh)
  have hhj : h ≤ j := by by_contra! hh; exact hcj (hcmin j hh)
  have hstrict : t < h := by
    by_contra! hht
    have he : t = h := le_antisymm hth hht
    have hsingle : (∑' k : ℤ, b k*c k) = b t*c h := by
      rw [tsum_eq_single t, he]
      intro k hk
      by_cases hkt : t < k
      · simp [hbmax k hkt]
      · rw [hcmin k (by omega), mul_zero]
    have hzero := hz 0
    simp only [Nat.cast_zero, sub_zero] at hzero
    rw [hsingle] at hzero
    exact (mul_ne_zero hbt hch) hzero
  omega



lemma fiber_orthogonal_order {w : ℤ → ℝ} (hw : QuadraticWeights w)
    {T : Fiber →L[ℂ] Fiber}
    (hT : ∀ v j, T v j = (w j / w (j-1) : ℂ) * v (j-1))
    {L : Submodule ℂ Fiber} (hinvariant : ∀ v ∈ L, T v ∈ L)
    {v z : Fiber} (hv : v ∈ L) (hz : z ∈ L.orthogonal)
    {i j : ℤ} (hzi : z i ≠ 0) (hvj : v j ≠ 0) : i < j := by
  let b := fun k : ℤ => star (z k) * (w k:ℂ)
  let c := fun k : ℤ => v k / (w k:ℂ)
  have hwC (k : ℤ) : (w k:ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (hw.positive k))
  have hbi : b i ≠ 0 := mul_ne_zero (by simpa using hzi) (hwC i)
  have hcj : c j ≠ 0 := div_ne_zero hvj (hwC j)
  have hb (k : ℤ) : ‖b k‖ ≤ (‖z‖+1)*w k := by
    dsimp [b]
    rw [norm_mul, RCLike.norm_conj, Complex.norm_real, Real.norm_of_nonneg (hw.positive k).le]
    apply mul_le_mul_of_nonneg_right _ (hw.positive k).le
    exact (lp.norm_apply_le_norm (by norm_num : (2 : ENNReal) ≠ 0) z k).trans (by linarith)
  have hc (k : ℤ) : ‖c k‖*w k ≤ ‖v‖+1 := by
    dsimp [c]
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (hw.positive k).le,
      div_mul_cancel₀ _ (ne_of_gt (hw.positive k))]
    exact (lp.norm_apply_le_norm (by norm_num : (2 : ENNReal) ≠ 0) v k).trans (by linarith)
  have hcor (r : ℕ) : (∑' k : ℤ, b k*c (k-r)) = 0 := by
    calc (∑' k : ℤ, b k*c (k-r)) = inner ℂ z ((T^r) v) := by
          rw [lp.inner_eq_tsum]
          apply tsum_congr
          intro k
          rw [RCLike.inner_apply, weighted_shift_pow hw.positive hT]
          dsimp [b, c]
          simp only [← Complex.star_def]
          ring
      _ = 0 := Submodule.inner_left_of_mem_orthogonal (invariant_pow hinvariant hv r) hz
  exact (quadratic_support_separation w hw).strict_order ⟨i,hbi⟩ ⟨j,hcj⟩
    (by positivity : 0 < ‖z‖+1) (by positivity : 0 < ‖v‖+1) hb hc hcor hbi hcj


theorem quadratic_fiber_tails (w : ℤ → ℝ) (hw : QuadraticWeights w)
    (T : Fiber →L[ℂ] Fiber)
    (hT : ∀ v j, T v j = (w j / w (j-1) : ℂ) * v (j-1))
    (L : Submodule ℂ Fiber) (hclosed : IsClosed (L : Set Fiber))
    (hinvariant : ∀ v ∈ L, T v ∈ L) :
    L = ⊥ ∨ L = ⊤ ∨ ∃ h : ℤ, L = coordinateTail h := by
  by_cases hbot : L = ⊥
  · exact Or.inl hbot
  by_cases htop : L = ⊤
  · exact Or.inr (Or.inl htop)
  have hOO : L.orthogonal.orthogonal = L := by
    rw [Submodule.orthogonal_orthogonal_eq_closure, hclosed.submodule_topologicalClosure_eq]
  have hnotOrth : L.orthogonal ≠ ⊥ := by
    intro hh
    rw [hh, Submodule.bot_orthogonal_eq_top] at hOO
    exact htop hOO.symm
  obtain ⟨z, hz, hzne⟩ := (Submodule.ne_bot_iff L.orthogonal).mp hnotOrth
  obtain ⟨i, hzi⟩ := fiber_exists_coordinate hzne
  obtain ⟨v, hv, hvne⟩ := (Submodule.ne_bot_iff L).mp hbot
  obtain ⟨j, hvj⟩ := fiber_exists_coordinate hvne
  let P := fun k : ℤ => ∃ c : Fiber, c ∈ L ∧ c k ≠ 0
  have hPnonempty : ∃ k, P k := ⟨j, v, hv, hvj⟩
  have hPbound : ∃ a : ℤ, ∀ k : ℤ, P k → a ≤ k := by
    refine ⟨i+1, ?_⟩
    rintro k ⟨c, hc, hck⟩
    have hh := fiber_orthogonal_order hw hT hinvariant hc hz hzi hck
    omega
  obtain ⟨h, hhP, hhmin⟩ := Int.exists_least_of_bdd hPbound hPnonempty
  obtain ⟨v₀, hv₀, hv₀h⟩ := hhP
  refine Or.inr (Or.inr ⟨h, le_antisymm ?_ ?_⟩)
  · intro c hc k hk
    by_contra hck
    have hh := hhmin k ⟨c, hc, hck⟩
    omega
  · intro c hc
    rw [← hOO]
    apply (Submodule.mem_orthogonal _ c).mpr
    intro u hu
    rw [lp.inner_eq_tsum]
    apply Eq.trans (tsum_congr (g := fun _ : ℤ => (0:ℂ)) ?_) tsum_zero
    intro k
    rw [RCLike.inner_apply]
    by_cases hkh : k < h
    · rw [hc k hkh, zero_mul]
    · have huk : u k = 0 := by
        by_contra hne
        have hh := fiber_orthogonal_order hw hT hinvariant hv₀ hu hne hv₀h
        exact hkh hh
      simp [huk]


end
end BackwardIntertwiners

end OAI
