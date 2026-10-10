import OAI.Analysis.AncientFlat.Evolution.EvolutionCore

namespace OAI
noncomputable section
open Set Filter
open scoped ContDiff ZeroAtInfty BoundedContinuousFunction Laplacian
namespace ParametrixEvolution
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]
variable {α β : ℝ}
lemma bilaplacian_add {f g : V → ℂ} (hf : ContDiff ℝ 4 f) (hg : ContDiff ℝ 4 g) :
    Δ (Δ (fun x => f x+g x))=fun x => Δ (Δ f) x+Δ (Δ g) x := by
  have hh : Δ (fun x => f x+g x)=fun x => Δ f x+Δ g x :=
    funext (fun x => (hf.of_le (by norm_num)).contDiffAt.laplacian_add
      (hg.of_le (by norm_num)).contDiffAt)
  rw [hh]
  exact funext (fun x => (ClassicalIBP.contDiff_laplacian f 2 hf).contDiffAt.laplacian_add
    (ClassicalIBP.contDiff_laplacian g 2 hg).contDiffAt)
lemma bilaplacian_smul {f : V → ℂ} (hf : ContDiff ℝ 4 f) (c : ℂ) :
    Δ (Δ (fun x => c • f x))=fun x => c • Δ (Δ f) x := by
  have hh : Δ (fun x => c • f x)=fun x => c • Δ f x :=
    funext (fun x => InnerProductSpace.laplacian_smul c (hf.of_le (by norm_num)).contDiffAt)
  rw [hh]
  exact funext (fun x => InnerProductSpace.laplacian_smul c
    (ClassicalIBP.contDiff_laplacian f 2 hf).contDiffAt)
variable {A : C(ℝ,V →ᵇ Icc α β)} {b : C(ℝ,V →ᵇ ℂ)}
  {s T : ℝ} {d e : C₀(V,ℂ)} {u v : ℝ → C₀(V,ℂ)}
lemma Evolves.add (hu : Evolves A b s T d u) (hv : Evolves A b s T e v) :
    Evolves A b s T (d+e) (fun t => u t+v t) := by
  refine ⟨by simp [hu.1,hv.1],hu.2.1.add hv.2.1,?_,?_,?_⟩
  · intro t ht
    exact (hu.2.2.1 t ht).add (hv.2.2.1 t ht)
  · intro t ht n hn
    obtain ⟨M,hM⟩ := hu.2.2.2.1 t ht n hn
    obtain ⟨N,hN⟩ := hv.2.2.2.1 t ht n hn
    refine ⟨M+N,fun x => ?_⟩
    have hcu : ContDiff ℝ n (fun y => u t y) := (hu.2.2.1 t ht).of_le (by exact_mod_cast hn)
    have hcv : ContDiff ℝ n (fun y => v t y) := (hv.2.2.1 t ht).of_le (by exact_mod_cast hn)
    change ‖iteratedFDeriv ℝ n (fun y => u t y+v t y) x‖≤_
    rw [fun_iteratedFDeriv_add hcu hcv]
    exact (norm_add_le _ _).trans (add_le_add (hM x) (hN x))
  · intro t ht
    obtain ⟨p,hp,hpe⟩ := hu.2.2.2.2 t ht
    obtain ⟨q,hq,hqe⟩ := hv.2.2.2.2 t ht
    refine ⟨p+q,hp.add hq,fun x => ?_⟩
    change p x+q x= -((A t x).val : ℂ)*Δ (Δ (fun y => u t y+v t y)) x-b t x*(u t x+v t x)
    rw [hpe,hqe,bilaplacian_add (hu.2.2.1 t ht) (hv.2.2.1 t ht)]
    ring
lemma Evolves.smul (hu : Evolves A b s T d u) (c : ℂ) :
    Evolves A b s T (c•d) (fun t => c•u t) := by
  refine ⟨by simp [hu.1],hu.2.1.const_smul c,?_,?_,?_⟩
  · intro t ht
    exact (hu.2.2.1 t ht).const_smul c
  · intro t ht n hn
    obtain ⟨M,hM⟩ := hu.2.2.2.1 t ht n hn
    refine ⟨‖c‖*M,fun x => ?_⟩
    have hc : ContDiff ℝ n (fun y => u t y) := (hu.2.2.1 t ht).of_le (by exact_mod_cast hn)
    change ‖iteratedFDeriv ℝ n (fun y => c • u t y) x‖≤_
    rw [iteratedFDeriv_const_smul_apply' hc.contDiffAt]
    simpa only [Pi.smul_apply,norm_smul] using mul_le_mul_of_nonneg_left (hM x) (norm_nonneg c)
  · intro t ht
    obtain ⟨p,hp,hpe⟩ := hu.2.2.2.2 t ht
    refine ⟨c•p,hp.const_smul c,fun x => ?_⟩
    change c • p x= -((A t x).val : ℂ)*Δ (Δ (fun y => c•u t y)) x-b t x*(c•u t x)
    rw [hpe,bilaplacian_smul (hu.2.2.1 t ht) c]
    simp only [smul_eq_mul]
    ring
end ParametrixEvolution

end

end OAI
