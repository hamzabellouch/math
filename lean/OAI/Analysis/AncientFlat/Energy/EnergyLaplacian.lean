import OAI.Analysis.AncientFlat.Energy.EnergyProducts

namespace OAI
noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology Laplacian
namespace ParametrixUniqueness
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
lemma BoundedJets.sum {ι : Type*} (s : Finset ι) (f : ι → V → E) (n : ℕ)
    (hf : ∀ i ∈ s, ContDiff ℝ n (f i)) (hb : ∀ i ∈ s, BoundedJets n (f i)) :
    BoundedJets n (fun x => ∑ i ∈ s, f i x) := by
  intro k hk
  have he : iteratedFDeriv ℝ k (fun x => ∑ i ∈ s, f i x) =
      fun x => ∑ i ∈ s, iteratedFDeriv ℝ k (f i) x := by
    funext x
    exact iteratedFDeriv_fun_sum_apply (fun i hi => (hf i hi).contDiffAt.of_le (by exact_mod_cast hk))
  rw [he]
  exact Bounded.sum s _ (fun i hi => hb i hi k hk)
variable [FiniteDimensional ℝ V]
lemma laplacian_eq_sum_dir (f : V → ℂ) (hf : ContDiff ℝ 2 f) :
    Δ f = fun x => ∑ i, dir (stdOrthonormalBasis ℝ V i) (dir (stdOrthonormalBasis ℝ V i) f) x :=
  ClassicalIBP.laplacian_eq_sum_D f hf
lemma BoundedJets.laplacian {f : V → ℂ} (n : ℕ) (hc : ContDiff ℝ (n+2) f)
    (hb : BoundedJets (n+2) f) : BoundedJets n (Δ f) := by
  rw [laplacian_eq_sum_dir f (hc.of_le (by exact_mod_cast Nat.le_add_left 2 n))]
  apply BoundedJets.sum
  · intro i _
    apply contDiff_dir
    apply contDiff_dir
    convert hc using 1; ring
  · intro i _
    have hc' : ContDiff ℝ ((n+1)+1) f := by convert hc using 1; ring
    have hb' : BoundedJets ((n+1)+1) f := by simpa only [Nat.add_assoc] using hb
    exact (hb'.dir hc' _).dir (contDiff_dir _ _ hc') _
omit [InnerProductSpace ℝ V] [NormedSpace ℝ E] [FiniteDimensional ℝ V] in
lemma Decays.sum {ι : Type*} (s : Finset ι) (f : ι → V → E) (hf : ∀ i ∈ s, Decays (f i)) :
    Decays (fun x => ∑ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0,le_rfl,by simp⟩
  | @insert i s hi ih =>
    simpa only [Finset.sum_insert hi] using (hf i (by simp)).add
      (ih (fun j hj => hf j (by simp [hj])))
variable [MeasurableSpace V] [BorelSpace V]
lemma integral_inner_laplacian (f g : V → ℂ) (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (h0 : Decays f) (h1 : ∀ v, Decays (dir v f))
    (h2 : ∀ v, Decays (dir v (dir v f))) (hb : BoundedJets 2 g) :
    (∫ x, inner ℝ (f x) (Δ g x)) = ∫ x, inner ℝ (Δ f x) (g x) := by
  rw [laplacian_eq_sum_dir _ hg,laplacian_eq_sum_dir _ hf]
  simp_rw [inner_sum,sum_inner]
  rw [integral_finsetSum,integral_finsetSum]
  · exact Finset.sum_congr rfl (fun i _ => integral_inner_dir_dir _ _ _ hf hg h0 (h1 _) (h2 _) hb)
  · intro i _
    exact ((h2 _).inner hb.zero).integrable
      ((contDiff_dir (n := 0) _ _ (contDiff_dir (n := 1) _ _ hf)).continuous.inner hg.continuous)
  · intro i _
    exact (h0.inner ((hb.dir hg _).dir (contDiff_dir _ _ hg) _).zero).integrable
      (hf.continuous.inner (contDiff_dir (n := 0) _ _ (contDiff_dir (n := 1) _ _ hg)).continuous)
lemma integral_weight_bilaplacian (a : V → ℝ) (u : V → ℂ)
    (ha : ContDiff ℝ 2 a) (hab : BoundedJets 2 a)
    (hu : ContDiff ℝ 4 u) (hub : BoundedJets 4 u) :
    (∫ x, (weight x*a x)*inner ℝ (u x) (Δ (Δ u) x)) =
      ∫ x, inner ℝ (Δ (fun y => (weight y*a y) • u y) x) (Δ u x) := by
  have hwa : ContDiff ℝ 2 (fun x => weight x*a x) := (contDiff_weight 2).mul ha
  have hu2 : ContDiff ℝ 2 u := hu.of_le (by norm_num)
  have hb2 : BoundedJets 2 u := hub.of_le (by norm_num)
  have h0 := decays_weight_mul hab.zero
  have h1 := decays_dir_weight_mul ha hab
  have h2 := decays_dir_dir_weight_mul ha hab
  simp_rw [←real_inner_smul_left]
  exact integral_inner_laplacian _ _ (hwa.smul hu2) (ClassicalIBP.contDiff_laplacian _ 2 hu)
    (h0.smul hb2.zero) (fun v => decays_dir_smul v hwa hu2 h0 (h1 v) hb2)
    (fun v => decays_dir_dir_smul v hwa hu2 h0 (h1 v) (h2 v) hb2)
    (hub.laplacian 2 hu)
end ParametrixUniqueness

end

end OAI
