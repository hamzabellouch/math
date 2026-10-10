import OAI.Analysis.Triangular.Energy.GaussianPoisson
import OAI.Analysis.Triangular.Energy.Schwartz
import OAI.Analysis.Triangular.Energy.Lattice
import OAI.Analysis.Triangular.Energy.Definitions

namespace OAI

noncomputable section
open scoped BigOperators Topology ENNReal
open Complex MeasureTheory
namespace AtomicTriangular

lemma schwartzLP_integral {α : ℝ} (p : GaussianPair α) :
    (∫ z, schwartzLP p.first z)=(p.second 0:ℂ) := by
  rw [←TriangularUniversal.fourier_zero_eq_integral,schwartzLP_fourier,p.fourier_first]

def gaussPot (α : ℝ) (s : ℝ) : ℝ := Real.exp (-Real.pi*α*s)
lemma triangularPoint_zero : triangularPoint (0 : ℤ × ℤ)=0 := by
  rw [triangularPoint_eq_support]
  exact TriangularUniversal.triangularPoint_zero
lemma triangularPoint_ne_zero {v : ℤ × ℤ} (hv : v≠0) : triangularPoint v≠0 := by
  rw [triangularPoint_eq_support]
  exact mt (TriangularUniversal.triangularPoint_eq_zero_iff v).mp hv
lemma GaussianPair.lattice_contact {α : ℝ} (p : GaussianPair α) (v : ℤ × ℤ) (hv : v≠0) :
    p.first (triangularPoint v)=gaussPot α (‖triangularPoint v‖^2) := by
  obtain ⟨n,hn⟩ := A_radial_node (show triangularPoint v∈A from ⟨v,rfl⟩) (triangularPoint_ne_zero hv)
  exact p.contact _ n hn
lemma GaussianPair.lattice_zeros {α : ℝ} (p : GaussianPair α) (v : ℤ × ℤ) (hv : v≠0) :
    p.second (triangularPoint v)=0 := by
  obtain ⟨n,hn⟩ := A_radial_node (show triangularPoint v∈A from ⟨v,rfl⟩) (triangularPoint_ne_zero hv)
  exact p.zeros _ n hn
lemma latticeEnergy_eq_support (g : ℝ → ℝ) : latticeEnergy g=TriangularUniversal.latticeEnergy g := by
  unfold latticeEnergy TriangularUniversal.latticeEnergy
  rw [A_eq_support]
lemma GaussianPair.sharp_value {α : ℝ} (p : GaussianPair α) (hp : GaussianLatticePoisson p) :
    latticeEnergy (gaussPot α)=ENNReal.ofReal (p.second 0-p.first 0) := by
  classical
  have hsum : (∑' v : ℤ × ℤ, p.first (triangularPoint v))=p.second 0 := by
    rw [hp.poisson,tsum_eq_single 0 (fun v hv => p.lattice_zeros v hv),triangularPoint_zero]
  have hadd : p.first 0+(∑' v : {v : ℤ × ℤ // v≠0},p.first (triangularPoint v.val))=p.second 0 := by
    have hh := hp.first_summable.sum_add_tsum_subtype_compl ({0}:Finset (ℤ × ℤ))
    simp only [Finset.sum_singleton,triangularPoint_zero,hsum] at hh
    let e : {x : ℤ × ℤ // x ∉ ({0} : Finset (ℤ × ℤ))} ≃ {v : ℤ × ℤ // v≠0} :=
      Equiv.subtypeEquivRight (fun v => by simp only [Finset.mem_singleton])
    have he : (∑' x : {x : ℤ × ℤ // x ∉ ({0} : Finset (ℤ × ℤ))},p.first (triangularPoint x.val))=
        ∑' v : {v : ℤ × ℤ // v≠0},p.first (triangularPoint v.val) :=
      e.tsum_eq (fun v => p.first (triangularPoint v.val))
    exact he ▸ hh
  have hs := hp.first_summable.subtype (fun v : ℤ × ℤ => v≠0)
  have he (v : {v : ℤ × ℤ // v≠0}) : p.first (triangularPoint v.val)=gaussPot α (‖triangularPoint v.val‖^2) :=
    p.lattice_contact v.val v.property
  have hs' : Summable (fun v : {v : ℤ × ℤ // v≠0} => gaussPot α (‖triangularPoint v.val‖^2)) := by
    exact hs.congr (fun v => he v)
  rw [latticeEnergy_eq_support,TriangularUniversal.latticeEnergy_nonzero_index]
  simp_rw [←triangularPoint_eq_support]
  rw [←ENNReal.ofReal_tsum_of_nonneg (f := fun v : {v : ℤ × ℤ // v≠0} => gaussPot α (‖triangularPoint v.val‖^2)) (fun v : {v : ℤ × ℤ // v≠0} => (Real.exp_pos (-Real.pi*α*‖triangularPoint v.val‖^2)).le) hs']
  congr 1
  simp_rw [he] at hadd
  linarith
lemma GaussianPair.energy_bound {α : ℝ} (p : GaussianPair α) (hp : GaussianLatticePoisson p)
    {C : Set Plane} (hD : DensityOne C) : latticeEnergy (gaussPot α)≤energy (gaussPot α) C := by
  rw [p.sharp_value hp]
  have he : (∫ z,schwartzLP p.first z).re-(schwartzLP p.first 0).re=p.second 0-p.first 0 := by
    rw [schwartzLP_integral,schwartzLP_apply]
    rfl
  rw [←he]
  apply TriangularUniversal.density_lp (schwartzLP p.first)
  · intro w
    rw [schwartzLP_fourier,p.fourier_first]
    rfl
  · intro w
    rw [schwartzLP_fourier,p.fourier_first]
    exact p.positive w
  · intro x _
    rw [schwartzLP_apply]
    exact p.minorant x
  · exact hD
lemma gaussian_energy_bound {C : Set Plane} (hD : DensityOne C) (α : ℝ) (hα : 0<α) :
    latticeEnergy (gaussPot α)≤energy (gaussPot α) C :=
  (gaussianPair α hα).energy_bound (gaussianPair_poisson α hα) hD
end AtomicTriangular
end

end OAI
