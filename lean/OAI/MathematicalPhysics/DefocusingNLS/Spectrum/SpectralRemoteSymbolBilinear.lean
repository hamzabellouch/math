import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRemoteSymbolProduct

namespace OAI

/-! Uniform symbol bounds for the varying Sylvester operator. -/

open Set Filter Topology
open scoped ContDiff
namespace DefocusingNLS
namespace HasUniformLogJetBound

variable {L : ℕ → ℝ}

theorem const {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    (c : A) : HasUniformLogJetBound L 0 (fun _ _ => c) := by
  refine ⟨Eventually.of_forall (fun _ => contDiffOn_const),?_⟩
  intro k
  refine ⟨‖c‖,norm_nonneg _,Eventually.of_forall (fun _ t _ => ?_)⟩
  by_cases hk : k = 0
  · subst k; simp
  · simp [iteratedDeriv_const,hk]

theorem zero {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A] (sigma : ℝ) :
    HasUniformLogJetBound L sigma (fun _ _ => (0 : A)) := by
  refine ⟨Eventually.of_forall (fun _ => contDiffOn_const),?_⟩
  intro k
  exact ⟨0,le_rfl,Eventually.of_forall (fun _ t _ => by simp)⟩

theorem norm_jet_within {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    (v : ℝ → D) {b t : ℝ} (hs : ContDiffOn ℝ ∞ v (Ioi b)) (ht : t ∈ Ioi b) (i : ℕ) :
    ‖iteratedFDerivWithin ℝ i v (Ioi b) t‖ = ‖iteratedDeriv i v t‖ := by
  rw [iteratedFDerivWithin_eq_iteratedFDeriv isOpen_Ioi.uniqueDiffOn
    (((hs t ht).contDiffAt (Ioi_mem_nhds ht)).of_le (by simp)) ht,
    norm_iteratedFDeriv_eq_norm_iteratedDeriv]

theorem bilinear {A B C : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup C] [NormedSpace ℝ C]
    {sigma tau : ℝ} {f : ℕ → ℝ → A} {g : ℕ → ℝ → B}
    (hf : HasUniformLogJetBound L sigma f) (hg : HasUniformLogJetBound L tau g)
    (T : A →L[ℝ] B →L[ℝ] C) :
    HasUniformLogJetBound L (sigma+tau) (fun n t => T (f n t) (g n t)) := by
  have hsm : ∀ᶠ n in atTop, ContDiffOn ℝ ∞ (fun t => T (f n t) (g n t)) (Ioi (L n)) := by
    filter_upwards [hf.smooth,hg.smooth] with n hn hn'
    exact T.isBoundedBilinearMap.contDiff.comp_contDiffOn (hn.prodMk hn')
  refine ⟨hsm,?_⟩
  intro k
  choose U hU hu using hf.bound
  choose V hV hv using hg.bound
  let K := ∑ i ∈ Finset.range (k+1), (k.choose i : ℝ)*U i*V (k-i)
  have hK : 0 ≤ K := Finset.sum_nonneg (fun i _ =>
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hU i)) (hV (k-i)))
  refine ⟨‖T‖*K,mul_nonneg (norm_nonneg T) hK,?_⟩
  have hfb : ∀ᶠ n in atTop, ∀ i ∈ Finset.range (k+1), ∀ t ∈ Ioi (L n),
      ‖iteratedDeriv i (f n) t‖ ≤ U i*Real.exp (sigma*t) :=
    (eventually_all_finset _).mpr (fun i _ => hu i)
  have hgb : ∀ᶠ n in atTop, ∀ i ∈ Finset.range (k+1), ∀ t ∈ Ioi (L n),
      ‖iteratedDeriv (k-i) (g n) t‖ ≤ V (k-i)*Real.exp (tau*t) :=
    (eventually_all_finset _).mpr (fun i _ => hv (k-i))
  filter_upwards [hfb,hgb,hf.smooth,hg.smooth,hsm] with n hn hn' hfn hgn htn
  intro t ht
  have hh := T.norm_iteratedFDerivWithin_le_of_bilinear hfn hgn
    isOpen_Ioi.uniqueDiffOn ht (by simp : (k : ℕ∞ω) ≤ ∞)
  rw [norm_jet_within _ htn ht k] at hh
  simp_rw [norm_jet_within _ hfn ht,norm_jet_within _ hgn ht] at hh
  apply hh.trans
  calc
    _ ≤ ‖T‖ * ∑ i ∈ Finset.range (k+1),
        ((k.choose i : ℝ)*U i*V (k-i))*Real.exp ((sigma+tau)*t) := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg T)
      apply Finset.sum_le_sum
      intro i hi
      have hb := mul_le_mul_of_nonneg_left
        (mul_le_mul (hn i hi t ht) (hn' i hi t ht) (norm_nonneg _)
          (mul_nonneg (hU i) (Real.exp_pos _).le)) (Nat.cast_nonneg (k.choose i) : (0 : ℝ) ≤ _)
      convert hb using 1 <;> (try rw [add_mul,Real.exp_add]) <;> ring
    _ = (‖T‖*K)*Real.exp ((sigma+tau)*t) := by rw [← Finset.sum_mul]; ring

theorem apply {A B : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℝ B]
    {sigma tau : ℝ} {f : ℕ → ℝ → (A →L[ℝ] B)} {g : ℕ → ℝ → A}
    (hf : HasUniformLogJetBound L sigma f) (hg : HasUniformLogJetBound L tau g) :
    HasUniformLogJetBound L (sigma+tau) (fun n t => f n t (g n t)) := by
  exact hf.bilinear hg (ContinuousLinearMap.id ℝ (A →L[ℝ] B))

end HasUniformLogJetBound
end DefocusingNLS

end OAI
