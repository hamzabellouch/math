import OAI.Analysis.AncientFlat.Evolution.EvolutionUniqueness
import OAI.Analysis.AncientFlat.Evolution.SourceClassical

namespace OAI
noncomputable section
open Set Filter
open scoped ContDiff ZeroAtInfty BoundedContinuousFunction Laplacian
namespace ParametrixEvolution
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]
variable {α β s T C B : ℝ} {A : C(ℝ,V →ᵇ Icc α β)} {b : C(ℝ,V →ᵇ ℂ)}
  {d e : C₀(V,ℂ)} {u v : ℝ → C₀(V,ℂ)} {f g : ℝ → C₀(V,ℂ)}
def SourceEvolves (A : C(ℝ,V →ᵇ Icc α β)) (b : C(ℝ,V →ᵇ ℂ))
    (f : ℝ → C₀(V,ℂ)) (s T : ℝ) (d : C₀(V,ℂ)) (u : ℝ → C₀(V,ℂ)) : Prop :=
  u s=d ∧ ContinuousOn u (Icc s T) ∧
  (∀ t ∈ Ioo s T, ContDiff ℝ 4 (fun x => u t x)) ∧
  (∀ t ∈ Ioo s T, ∀ n : ℕ, n≤4 → ∃ M : ℝ, ∀ x,
    ‖iteratedFDeriv ℝ n (fun y => u t y) x‖≤M) ∧
  (∀ t ∈ Ioo s T, ∃ p : V →ᵇ ℂ, HasDerivAt (fun r => (u r).toBCF) p t ∧
    ∀ x, p x=f t x-((A t x).val : ℂ)*Δ (Δ (fun y => u t y)) x-b t x*u t x)
lemma SourceEvolves.sub (hu : SourceEvolves A b f s T d u)
    (hv : SourceEvolves A b g s T e v) :
    SourceEvolves A b (fun t => f t-g t) s T (d-e) (fun t => u t-v t) := by
  refine ⟨by simp [hu.1,hv.1],hu.2.1.sub hv.2.1,?_,?_,?_⟩
  · intro t ht; exact (hu.2.2.1 t ht).sub (hv.2.2.1 t ht)
  · intro t ht n hn
    obtain ⟨M,hM⟩ := hu.2.2.2.1 t ht n hn
    obtain ⟨N,hN⟩ := hv.2.2.2.1 t ht n hn
    refine ⟨M+N,fun x => ?_⟩
    have hcu : ContDiff ℝ n (fun y => u t y) := (hu.2.2.1 t ht).of_le (by exact_mod_cast hn)
    have hcv : ContDiff ℝ n (fun y => v t y) := (hv.2.2.1 t ht).of_le (by exact_mod_cast hn)
    change ‖iteratedFDeriv ℝ n (fun y => u t y-v t y) x‖≤_
    rw [fun_iteratedFDeriv_sub hcu hcv]
    exact (norm_sub_le _ _).trans (add_le_add (hM x) (hN x))
  · intro t ht
    obtain ⟨p,hp,hpe⟩ := hu.2.2.2.2 t ht
    obtain ⟨q,hq,hqe⟩ := hv.2.2.2.2 t ht
    refine ⟨p-q,hp.sub hq,fun x => ?_⟩
    change p x-q x= (f t x-g t x)-((A t x).val : ℂ)*Δ (Δ (fun y => u t y-v t y)) x-b t x*(u t x-v t x)
    have he : (fun y => u t y-v t y)=(fun y => u t y+(-1:ℂ)•v t y) := by ext; simp [sub_eq_add_neg]
    rw [he,hpe,hqe,bilaplacian_add (hu.2.2.1 t ht) ((hv.2.2.1 t ht).const_smul (-1)),bilaplacian_smul (hv.2.2.1 t ht) (-1)]
    simp only [smul_eq_mul]
    ring
lemma SourceEvolves.zero_iff : SourceEvolves A b (fun _ => 0) s T d u ↔ Evolves A b s T d u := by
  unfold SourceEvolves Evolves
  simp only [ZeroAtInftyContinuousMap.zero_apply,zero_sub,neg_mul]
lemma Evolves.with_zero_source (hu : Evolves A b s T d u) :
    SourceEvolves A b (fun _ => 0) s T d u := SourceEvolves.zero_iff.mpr hu
variable [MeasurableSpace V] [BorelSpace V]
lemma SourceEvolves.unique (hu : SourceEvolves A b f s T d u)
    (hv : SourceEvolves A b f s T d v)
    (hsT : s≤T) (hα : 0<α) (hC : 0≤C) (hB : 0≤B)
    (hb : ∀ t ∈ Icc s T, ‖b t‖≤B)
    (hA : ∀ t ∈ Icc s T, ContDiff ℝ 2 (fun x => (A t x).val))
    (hAj : ∀ t ∈ Icc s T, ∀ n : ℕ, n≤2 → ∀ x,
      ‖iteratedFDeriv ℝ n (fun y => (A t y).val) x‖≤C) :
    ∀ t ∈ Icc s T, u t=v t := by
  have hz : Evolves A b s T 0 (fun t => u t-v t) := SourceEvolves.zero_iff.mp (by simpa using hu.sub hv)
  rcases hsT.eq_or_lt with he|hlt
  · subst T
    intro t ht
    have he : t=s := le_antisymm ht.2 ht.1
    subst t
    exact hu.1.trans hv.1.symm
  · have hh := hz.zero_unique hlt hα hC hB hb hA hAj
    intro t ht
    simpa only [sub_eq_zero] using hh t ht
omit [MeasurableSpace V] [BorelSpace V] in
lemma SourceEvolves.end_mono (hu : SourceEvolves A b f s T d u) {R : ℝ} (hR : R≤T) :
    SourceEvolves A b f s R d u := by
  refine ⟨hu.1,hu.2.1.mono (Icc_subset_Icc_right hR),?_,?_,?_⟩
  · intro t ht; exact hu.2.2.1 t ⟨ht.1,ht.2.trans_le hR⟩
  · intro t ht; exact hu.2.2.2.1 t ⟨ht.1,ht.2.trans_le hR⟩
  · intro t ht; exact hu.2.2.2.2 t ⟨ht.1,ht.2.trans_le hR⟩
end ParametrixEvolution

end

end OAI
