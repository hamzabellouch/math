import OAI.Analysis.AncientFlat.Evolution.SimilaritySource
import OAI.Analysis.AncientFlat.Geometry.NormalizedWindow

namespace OAI
noncomputable section
open Set Filter
open scoped ContDiff ZeroAtInfty BoundedContinuousFunction Laplacian Topology
namespace FlatSimilarity
open ParametrixDilation ParametrixEvolution
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]
def renormalized (γ : ℝ) (u : ℝ → C₀(V,ℂ)) (t : ℝ) : C₀(V,ℂ) :=
  (Real.exp (γ*t) : ℂ) • dil t (u t)
lemma MovesWithSource.renormalized_contDiff {Af Bf : V → ℝ} {f : ℝ →ᵇ C₀(V,ℂ)}
    {d : C₀(V,ℂ)} {u : ℝ → C₀(V,ℂ)} (hu : MovesWithSource Af Bf f d u)
    (γ : ℝ) {t : ℝ} (ht : t ∈ Ioo (0:ℝ) 1) :
    ContDiff ℝ 4 (fun x => renormalized γ u t x) := by
  have hc : ContDiff ℝ 4 (fun x => dil t (u t) x) :=
    (hu.2.2.1 t ht).comp (contDiff_const.smul contDiff_id)
  exact hc.const_smul (Real.exp (γ*t) : ℂ)
lemma MovesWithSource.renormalized_jets {Af Bf : V → ℝ} {f : ℝ →ᵇ C₀(V,ℂ)}
    {d : C₀(V,ℂ)} {u : ℝ → C₀(V,ℂ)} (hu : MovesWithSource Af Bf f d u)
    (γ : ℝ) {t : ℝ} (ht : t ∈ Ioo (0:ℝ) 1) :
    ∀ n : ℕ, n≤4 → ∃ M : ℝ, ∀ x,
      ‖iteratedFDeriv ℝ n (fun y => renormalized γ u t y) x‖≤M := by
  have hc : ContDiff ℝ 4 (fun x => dil t (u t) x) :=
    (hu.2.2.1 t ht).comp (contDiff_const.smul contDiff_id)
  intro n hn
  obtain ⟨M,hM⟩ := bounded_jets_scale (Real.exp (-t/4)) (fun x => u t x)
    (hu.2.2.1 t ht) (hu.2.2.2.1 t ht) n hn
  refine ⟨‖(Real.exp (γ*t) : ℂ)‖*M,fun x => ?_⟩
  have hcn : ContDiff ℝ n (fun x => dil t (u t) x) := hc.of_le (by exact_mod_cast hn)
  change ‖iteratedFDeriv ℝ n (fun y => (Real.exp (γ*t) : ℂ) • dil t (u t) y) x‖≤_
  rw [iteratedFDeriv_const_smul_apply' hcn.contDiffAt]
  simpa only [Pi.smul_apply,norm_smul,dil_apply] using mul_le_mul_of_nonneg_left (hM x) (norm_nonneg _)
lemma MovesWithSource.renormalized_deriv {Af Bf : V → ℝ} {f : ℝ →ᵇ C₀(V,ℂ)}
    {d : C₀(V,ℂ)} {u : ℝ → C₀(V,ℂ)} (hu : MovesWithSource Af Bf f d u)
    (γ : ℝ) {t : ℝ} (ht : t ∈ Ioo (0:ℝ) 1) (x : V) :
    HasDerivAt (fun r => renormalized γ u r x)
      ((Real.exp (γ*t) : ℂ) • f t x-(Af x/16 : ℝ) • Δ (Δ (fun y => renormalized γ u t y)) x-
        (1/2-γ+Bf x : ℝ) • renormalized γ u t x-
        (1/4 : ℝ) • (fderiv ℝ (fun y => renormalized γ u t y) x x)) t := by
  have hc : ContDiff ℝ 4 (fun x => dil t (u t) x) :=
    (hu.2.2.1 t ht).comp (contDiff_const.smul contDiff_id)
  have hf := hc.differentiable (by norm_num)
  have he := (((hasDerivAt_id t).const_mul γ).exp).ofReal_comp
  have hh := he.mul (hu.autonomous ht x)
  change HasDerivAt (fun r => (Real.exp (γ*r) : ℂ) * dil r (u r) x) _ t
  convert hh using 1 <;> try rfl
  change (Real.exp (γ*t) : ℂ) • f t x-(Af x/16 : ℝ) •
    Δ (Δ (fun y => (Real.exp (γ*t) : ℂ) • dil t (u t) y)) x-
    (1/2-γ+Bf x : ℝ) • ((Real.exp (γ*t) : ℂ) • dil t (u t) x)-
    (1/4 : ℝ) • (fderiv ℝ (fun y => (Real.exp (γ*t) : ℂ) • dil t (u t) y) x x)=_
  rw [bilaplacian_smul hc,fderiv_fun_const_smul (hf x)]
  simp only [smul_apply,Complex.real_smul,smul_eq_mul,
    Complex.ofReal_mul,Complex.ofReal_sub,Complex.ofReal_add,Complex.ofReal_div,
    Complex.ofReal_one,Complex.ofReal_ofNat,id_eq,mul_one]
  ring
end FlatSimilarity

end

end OAI
