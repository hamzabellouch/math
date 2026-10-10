import OAI.Analysis.AncientFlat.Kernel.SymbolBounds

namespace OAI
noncomputable section
open Set Filter
open scoped ContDiff
namespace FlatSimilarity
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
lemma SymbolBounds.A_jets [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    {c : ℝ} {Af Bf : V → ℝ} (h : SymbolBounds c Af Bf) (n : ℕ) :
    ∃ C : ℝ, 0≤C ∧ ∀ x, ‖iteratedFDeriv ℝ n Af x‖≤C := by
  by_cases hn : n=0
  · subst n
    obtain ⟨M,hM,hA,hB⟩ := h.absolute_bound
    exact ⟨M,hM,fun x => by simpa only [norm_iteratedFDeriv_zero] using hA x⟩
  · obtain ⟨C,hC,hA,hB⟩ := h.deviation_jets n
    refine ⟨C,hC,fun x => ?_⟩
    have he : iteratedFDeriv ℝ n (fun y => Af y-c^2) x=iteratedFDeriv ℝ n Af x := by
      rw [fun_iteratedFDeriv_sub (h.2.2.1.of_le (by exact_mod_cast (le_top : (n:ℕ∞)≤⊤))) contDiff_const,
        iteratedFDeriv_const_of_ne hn]
      simp
    simpa only [he] using hA x
lemma iteratedFDeriv_scale_real [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (r : ℝ) (f : V → ℝ) (hf : ContDiff ℝ ∞ f)
    (n : ℕ) (x : V) :
    iteratedFDeriv ℝ n (fun y => f (r • y)) x=
      r^n • iteratedFDeriv ℝ n f (r • x) := by
  let g : V →L[ℝ] V := r • ContinuousLinearMap.id ℝ V
  have hg := g.iteratedFDeriv_comp_right hf x (show (n : WithTop ℕ∞)≤∞ by exact_mod_cast (le_top : (n:ℕ∞)≤⊤))
  change iteratedFDeriv ℝ n (f ∘ g) x=_
  rw [hg]
  ext m
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply,
    smul_apply,g,
    ContinuousLinearMap.id_apply]
  simpa using (iteratedFDeriv ℝ n f (r • x)).map_smul_univ (fun _ => r) m
variable [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
lemma SymbolBounds.moving_A_jets {c : ℝ} {Af Bf : V → ℝ} (h : SymbolBounds c Af Bf) (n : ℕ) :
    ∃ C : ℝ, 0≤C ∧ ∀ t ∈ Icc (0:ℝ) 1, ∀ x,
      ‖iteratedFDeriv ℝ n (fun y => Real.exp (-t)/16*Af (Real.exp (t/4) • y)) x‖≤C := by
  obtain ⟨C,hC,hA⟩ := h.A_jets n
  refine ⟨Real.exp (1/4)^n*C,by positivity,fun t ht x => ?_⟩
  have hf : ContDiff ℝ ∞ (fun y : V => Af (Real.exp (t/4) • y)) :=
    h.2.2.1.comp (contDiff_const.smul contDiff_id)
  have he : Real.exp (t/4)≤Real.exp (1/4) := Real.exp_le_exp.mpr (by linarith [ht.2])
  have hw : ‖Real.exp (-t)/16‖≤1 := by
    rw [Real.norm_of_nonneg (by positivity)]
    have hh : Real.exp (-t)≤1 := by simpa using Real.exp_le_exp.mpr (neg_nonpos.mpr ht.1)
    linarith
  change ‖iteratedFDeriv ℝ n (fun y => (Real.exp (-t)/16) • Af (Real.exp (t/4) • y)) x‖≤_
  rw [iteratedFDeriv_const_smul_apply' (hf.of_le (by exact_mod_cast (le_top : (n:ℕ∞)≤⊤))).contDiffAt,
    iteratedFDeriv_scale_real _ _ h.2.2.1,norm_smul,norm_smul,
    Real.norm_of_nonneg (by positivity : 0≤Real.exp (t/4)^n)]
  calc
    _≤1*(Real.exp (1/4)^n*C) := mul_le_mul hw
      (mul_le_mul (pow_le_pow_left₀ (Real.exp_pos _).le he n) (hA _)
        (norm_nonneg _) (by positivity)) (by positivity) zero_le_one
    _=_ := one_mul _
lemma SymbolBounds.moving_A_two_jets {c : ℝ} {Af Bf : V → ℝ} (h : SymbolBounds c Af Bf) :
    ∃ C : ℝ, 0≤C ∧ ∀ t ∈ Icc (0:ℝ) 1, ∀ n : ℕ, n≤2 → ∀ x,
      ‖iteratedFDeriv ℝ n (fun y => Real.exp (-t)/16*Af (Real.exp (t/4) • y)) x‖≤C := by
  obtain ⟨C0,h0,H0⟩ := h.moving_A_jets 0
  obtain ⟨C1,h1,H1⟩ := h.moving_A_jets 1
  obtain ⟨C2,h2,H2⟩ := h.moving_A_jets 2
  refine ⟨C0+C1+C2,by positivity,fun t ht n hn x => ?_⟩
  have hn' : n=0 ∨ n=1 ∨ n=2 := by omega
  rcases hn' with rfl|rfl|rfl
  · exact (H0 t ht x).trans (by linarith)
  · exact (H1 t ht x).trans (by linarith)
  · exact (H2 t ht x).trans (by linarith)
end FlatSimilarity

end

end OAI
