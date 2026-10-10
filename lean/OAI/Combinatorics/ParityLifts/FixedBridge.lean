import OAI.Combinatorics.ParityLifts.SATRates

namespace OAI

namespace ParityWL.Complexity

noncomputable def reductionRate (P j t : ℕ) (r : ℝ) : ℝ :=
  4/(j : ℝ)+2*(P : ℝ)*(r+1)*leafSlope t (12*j)

noncomputable def fixedSATCode (j t : ℕ) [NeZero t] (M : Machine) : FCode :=
  satCode (postCode j (leafDecisionCode t M))

/-- A fully specified finite-alphabet SAT machine, with a parser degree independent
of all fixed parameters. Every matrix and sparse leaf is actually written. -/
theorem fixed_reduction_rate : ∃ P : ℕ, 0<P ∧ ∀ (j : ℕ), 0<j →
    ∀ (k : ℕ), 4 ≤ k → ∀ (c : Convention), ∀ [NeZero (bagParameter c k)],
    ∀ (i : Implementation) (M : Machine) (r : ℝ), 0 ≤ r → FixedWLBound M c i k r →
      ∀ ε : ℝ, 0<ε → ∃ C : ℝ, 0<C ∧
        SATTimeBound (fixedSATCode j (bagParameter c k) M).decision (fun N L =>
          C*(L+1 : ℝ)^(2*normalizeProgram.degree+2)*
            2^((reductionRate P j (bagParameter c k) r+ε)*N)) := by
  obtain ⟨P,hP,h⟩ := leafCost_rate
  refine ⟨P,hP,?_⟩
  intro j hj k hk c _ i M r hr hm ε hε
  obtain ⟨C,hC,hRun⟩ := leafMachine_run k hk c i M r hr hm
  obtain ⟨W,hW,hWF⟩ := h (bagParameter c k) (12*j) M C r hC hr
  have hpos : 0 ≤ (P : ℝ)*(r+1)*leafSlope (bagParameter c k) (12*j) :=
    mul_nonneg (by positivity) (leafSlope_nonneg _ _)
  have hp := @postCode_run j hj (leafDecisionCode (bagParameter c k) M) W hW.1 (by
    intro N F hsz hlen hw
    obtain ⟨b,hb,he⟩ := hRun F hw
    exact ⟨b,hb.mono (hWF N F hsz hlen),he⟩)
  have hRate := postBudget_rate j W _ hpos hW
  have hpos' : 0 ≤ 2/(j : ℝ)+(P : ℝ)*(r+1)*leafSlope (bagParameter c k) (12*j) := by positivity
  obtain ⟨D,hD,hDtime⟩ := sat_code_rate _ _ _ hpos' hRate hp ε hε
  refine ⟨D,hD,?_⟩
  dsimp only [fixedSATCode]
  convert hDtime using 1
  funext N L
  dsimp only [reductionRate]
  congr 2
  ring

lemma SATTimeBound.mono {M : Machine} {B D : ℕ → ℕ → ℝ}
    (h : SATTimeBound M B) (hd : ∀ N L,B N L ≤ D N L) : SATTimeBound M D := by
  intro N F
  obtain ⟨s,b,hs,hb,ht⟩ := h N F
  exact ⟨s,b,hs,hb,ht.trans (hd N (encodeFormula F).length)⟩

lemma SATTimeBound.rate_mono {M : Machine} {C a b : ℝ} {d : ℕ}
    (hC : 0 ≤ C) (hab : a ≤ b)
    (h : SATTimeBound M (fun N L => C*(L+1 : ℝ)^d*2^(a*N))) :
    SATTimeBound M (fun N L => C*(L+1 : ℝ)^d*2^(b*N)) :=
  h.mono (by
    intro N L
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num)
      (mul_le_mul_of_nonneg_right hab (Nat.cast_nonneg N)))
end ParityWL.Complexity

end OAI
