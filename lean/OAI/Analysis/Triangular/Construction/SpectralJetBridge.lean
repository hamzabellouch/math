import OAI.Analysis.Triangular.Construction.NormalizedJets

namespace OAI

noncomputable section
open scoped BigOperators lp
open Complex Set MeasureTheory
namespace AtomicTriangular.Construction
lemma spectralCVector_map {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    (L : E →L[ℂ] F) (n : ℤ) (f : ℝ → E) (hf : Continuous f) :
    L (spectralCVector n f)=spectralCVector n (fun t => L (f t)) := by
  unfold spectralCVector
  simp only [map_sum,map_smul]
  apply Finset.sum_congr rfl
  intro l _
  congr 2
  rw [←L.intervalIntegral_comp_comm ((by fun_prop : Continuous (fun t : ℝ =>
    (frequency l-t) • (exp (-I*Real.pi*(t:ℂ)*n) • f t))).intervalIntegrable 0 (frequency l))]
  apply intervalIntegral.integral_congr
  intro t _
  change L (((frequency l-t:ℝ):ℂ) • (exp (-I*Real.pi*(t:ℂ)*n) • f t)) =
    ((frequency l-t:ℝ):ℂ) • (exp (-I*Real.pi*(t:ℂ)*n) • L (f t))
  simp only [map_smul]
lemma spectralDVector_map {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    (L : E →L[ℂ] F) (n : ℤ) (f : ℝ → E) (hf : Continuous f) :
    L (spectralDVector n f)=spectralDVector n (fun t => L (f t)) := by
  unfold spectralDVector
  simp only [map_sum,map_smul]
  apply Finset.sum_congr rfl
  intro l _
  congr 2
  rw [←L.intervalIntegral_comp_comm ((by fun_prop : Continuous (fun t : ℝ => exp (-I*Real.pi*(t:ℂ)*n) • f t)).intervalIntegrable 0 (frequency l))]
  apply intervalIntegral.integral_congr
  intro t _
  simp only [map_smul]
lemma spectralC_of_restriction (n : Node) (f : C(Spectrum,ℂ)) (g : ℝ → ℂ)
    (hg : ∀ t (ht : t∈Spectrum), f ⟨t,ht⟩=g t) : spectralC n f=spectralCVector n.val g := by
  unfold spectralC spectralCVector
  apply Finset.sum_congr rfl
  intro l _
  simp only [smul_eq_mul]
  congr 2
  apply intervalIntegral.integral_congr
  intro t ht
  dsimp only
  change ((frequency l:ℂ)-(t:ℂ))*exp (-I*Real.pi*(t:ℂ)*(n.val:ℂ))*extend f t =
    (frequency l-t) • (exp (-I*Real.pi*(t:ℂ)*(n.val:ℂ))*g t)
  have hm := interval_frequency_subset l ht
  rw [extend_on f t hm,hg]
  simp only [Complex.real_smul,ofReal_sub]
  ring
lemma spectralD_of_restriction (n : Node) (f : C(Spectrum,ℂ)) (g : ℝ → ℂ)
    (hg : ∀ t (ht : t∈Spectrum), f ⟨t,ht⟩=g t) : spectralD n f=spectralDVector n.val g := by
  unfold spectralD spectralDVector
  apply Finset.sum_congr rfl
  intro l _
  simp only [smul_eq_mul]
  congr 2
  apply intervalIntegral.integral_congr
  intro t ht
  dsimp only
  have hm := interval_frequency_subset l ht
  rw [extend_on f t hm,hg]
lemma spectralC_jetFunction (q : Fin 2) (v : ℝ) (m : ℤ) (d : Fin 2) (n : Node) :
    spectralC n (jetFunction q v m d)=(tailJetVector (damping q) v m n.val 0 d) := by
  rw [spectralC_of_restriction n _ (jetMultiplier (damping q) v m d) (fun _ _ => rfl)]
  symm
  exact spectralCVector_map (PiLp.proj 1 (fun _ : Fin 2 => ℂ) d) n.val _ (continuous_jetVector (damping_pos q) v m)
lemma spectralD_jetFunction (q : Fin 2) (v : ℝ) (m : ℤ) (d : Fin 2) (n : Node) :
    spectralD n (jetFunction q v m d)=(tailJetVector (damping q) v m n.val 1 d) := by
  rw [spectralD_of_restriction n _ (jetMultiplier (damping q) v m d) (fun _ _ => rfl)]
  symm
  exact spectralDVector_map (PiLp.proj 1 (fun _ : Fin 2 => ℂ) d) n.val _ (continuous_jetVector (damping_pos q) v m)
end AtomicTriangular.Construction
end

end OAI
